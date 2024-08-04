use proc_generics::normalize;
use proc_generics::normalize::WherePredicateBinding;
use proc_generics::substitute::{Substitute, SubstituteEnvironment};
use proc_macro::TokenStream as TokenStream1;
use proc_macro2::TokenStream;
use proc_macro_error::{abort, proc_macro_error};
use std::collections::{HashMap, HashSet};
use syn::spanned::Spanned;
use syn::visit_mut::VisitMut;
use syn::*;
use template_quote::quote;

fn check_defaultness(item_impl: &ItemImpl) -> Option<bool> {
    let mut ret = false;
    // does not support impl-level default keyword
    if item_impl.defaultness.is_some() {
        return None;
    }
    for item in item_impl.items.iter() {
        match item {
            ImplItem::Const(item_const) if item_const.defaultness.is_some() => {
                return None;
            }
            ImplItem::Fn(item_method) if item_method.defaultness.is_some() => {
                ret = true;
            }
            ImplItem::Type(item_type) if item_type.defaultness.is_some() => {
                return None;
            }
            _ => (),
        }
    }
    Some(ret)
}

fn normalize_params_and_predicates(
    impl_: &ItemImpl,
) -> (HashSet<GenericParam>, HashSet<WherePredicateBinding>) {
    let (mut gps, mut wps) = (HashSet::new(), HashSet::new());
    for gp in impl_.generics.params.iter() {
        let (gp, nwps) = normalize::normalize_generic_param(gp.clone());
        gps.insert(gp);
        wps.extend(nwps);
    }
    if let Some(wc) = &impl_.generics.where_clause {
        for p in wc.predicates.iter() {
            let nwps = normalize::normalize_where_predicate(p.clone());
            wps.extend(nwps);
        }
    }
    (gps, wps)
}

fn get_param_ident(p: GenericParam) -> Option<Ident> {
    match p {
        GenericParam::Type(tp) => Some(tp.ident),
        _ => None,
    }
}

fn get_type_ident(ty: Type) -> Option<Ident> {
    match ty {
        Type::Path(tp) if tp.qself.is_none() => tp.path.get_ident().cloned(),
        _ => None,
    }
}

fn find_type_ident(ty: &Type, ident: &Ident) -> bool {
    use syn::visit::Visit;
    struct Visitor<'a>(&'a Ident, bool);
    impl<'ast, 'a> Visit<'ast> for Visitor<'a> {
        fn visit_type(&mut self, i: &'ast Type) {
            match i {
                Type::Path(tp) if tp.qself.is_none() && tp.path.get_ident() == Some(&self.0) => {
                    self.1 = true;
                }
                _ => {
                    syn::visit::visit_type(self, i);
                }
            }
        }
    }
    let mut vis = Visitor(ident, false);
    vis.visit_type(ty);
    vis.1
}

fn get_trivial_substitutions(
    special_params: &HashSet<Ident>,
    substitution: &HashMap<Ident, Type>,
) -> Vec<(Ident, Ident)> {
    substitution
        .iter()
        .filter_map(|(d, s)| {
            get_type_ident(s.clone())
                .and_then(|i| special_params.iter().find(|ii| &&i == ii).cloned())
                .map(|s| (d.clone(), s))
        })
        .collect()
}

fn substitute_impl(
    default_impl: &ItemImpl,
    special_impl: &ItemImpl,
) -> Vec<(HashMap<Ident, Type>, usize)> {
    let (d_ps, d_ws) = normalize_params_and_predicates(default_impl);
    let (s_ps, s_ws) = normalize_params_and_predicates(special_impl);
    let s_ps: HashSet<_> = s_ps.into_iter().filter_map(get_param_ident).collect();
    let env = SubstituteEnvironment {
        general_params: d_ps.into_iter().filter_map(get_param_ident).collect(),
    };
    let s = env.substitute(&d_ws, &s_ws)
        * env.substitute(
            &default_impl.trait_.as_ref().unwrap().1,
            &special_impl.trait_.as_ref().unwrap().1,
        )
        * env.substitute(&*default_impl.self_ty, &*special_impl.self_ty);
    // Filter substitutions, which has parameters in replacement
    s.0.into_iter()
        .filter(|m| {
            m.iter().all(|(_, ty)| {
                s_ps.iter().all(|i| {
                    &get_type_ident(ty.clone()).as_ref() == &Some(i) || !find_type_ident(ty, &i)
                })
            })
        })
        .map(|r| {
            (
                r.clone(),
                r.len() - get_trivial_substitutions(&s_ps, &r).len(),
            )
        })
        .collect()
}

fn replace_type_params(map: HashMap<Ident, Ident>, mut ifn: ImplItemFn) -> ImplItemFn {
    fn filter_map_with_generics(
        map: &HashMap<Ident, Ident>,
        generics: &Generics,
    ) -> HashMap<Ident, Ident> {
        map.clone()
            .into_iter()
            .filter(|(k, _)| {
                generics
                    .params
                    .iter()
                    .filter_map(|o| {
                        if let GenericParam::Type(pt) = o {
                            Some(&pt.ident)
                        } else {
                            None
                        }
                    })
                    .all(|id| k != id)
            })
            .collect()
    }
    #[derive(Clone)]
    struct Visitor(HashMap<Ident, Ident>);
    impl VisitMut for Visitor {
        fn visit_type_mut(&mut self, i: &mut Type) {
            if let Type::Path(tp) = i {
                if let Some(id) = tp.path.get_ident() {
                    if let Some(replaced) = self.0.get(id) {
                        tp.path = Path {
                            leading_colon: None,
                            segments: Some(PathSegment {
                                ident: replaced.clone(),
                                arguments: PathArguments::None,
                            })
                            .into_iter()
                            .collect(),
                        };
                        return;
                    }
                }
            }
            syn::visit_mut::visit_type_mut(self, i)
        }
        fn visit_item_fn_mut(&mut self, i: &mut ItemFn) {
            let mut this = Visitor(filter_map_with_generics(&self.0, &i.sig.generics));
            syn::visit_mut::visit_item_fn_mut(&mut this, i);
        }
        fn visit_item_impl_mut(&mut self, i: &mut ItemImpl) {
            let mut this = Visitor(filter_map_with_generics(&self.0, &i.generics));
            syn::visit_mut::visit_item_impl_mut(&mut this, i);
        }
        fn visit_item_trait_mut(&mut self, i: &mut ItemTrait) {
            let mut this = Visitor(filter_map_with_generics(&self.0, &i.generics));
            syn::visit_mut::visit_item_trait_mut(&mut this, i);
        }
        fn visit_item_struct_mut(&mut self, i: &mut ItemStruct) {
            let mut this = Visitor(filter_map_with_generics(&self.0, &i.generics));
            syn::visit_mut::visit_item_struct_mut(&mut this, i);
        }
        fn visit_item_enum_mut(&mut self, i: &mut ItemEnum) {
            let mut this = Visitor(filter_map_with_generics(&self.0, &i.generics));
            syn::visit_mut::visit_item_enum_mut(&mut this, i);
        }
        fn visit_item_type_mut(&mut self, i: &mut ItemType) {
            let mut this = Visitor(filter_map_with_generics(&self.0, &i.generics));
            syn::visit_mut::visit_item_type_mut(&mut this, i);
        }
        fn visit_item_union_mut(&mut self, i: &mut ItemUnion) {
            let mut this = Visitor(filter_map_with_generics(&self.0, &i.generics));
            syn::visit_mut::visit_item_union_mut(&mut this, i);
        }
    }
    let mut visitor = Visitor(map);
    visitor.visit_impl_item_fn_mut(&mut ifn);
    ifn
}

fn specialize_item_fn(
    ifn: ImplItemFn,
    specials: Vec<(HashMap<Ident, Type>, ImplItemFn)>,
) -> ImplItemFn {
    let specials_out = specials
        .into_iter()
        .enumerate()
        .map(|(n, (m, mut sfn))| {
            sfn.sig.ident = Ident::new(
                &format!("__min_specialization_inner_fn_{}", n),
                sfn.sig.ident.span(),
            );
            let mut condition = quote! {true};
            let mut replacement = HashMap::new();
            for (lhs, rhs) in m.into_iter() {
                if let Some(rhs) = get_type_ident(rhs.clone()) {
                    replacement.insert(rhs, lhs);
                } else {
                    condition.extend(quote! {
                        && __min_specialization_id::<#lhs> as *const ()
                            == __min_specialization_id::<#rhs> as *const ()
                    });
                }
            }
            let sfn = replace_type_params(replacement, sfn);
            quote! {
                if #condition {
                    #sfn
                    #{&sfn.sig.ident} (
                        #(for arg in &ifn.sig.inputs), {
                            #(if let FnArg::Receiver(_) = arg) {
                                self
                            }
                            #(if let FnArg::Typed(pt) = arg) {
                                #{&pt.pat}
                            }
                        }
                    )
                } else
            }
        })
        .collect::<Vec<_>>();
    let inner = quote! {
        #(for attr in &ifn.attrs) {#attr}
        #{&ifn.vis}
        #{&ifn.sig}
        {
            fn __min_specialization_id<T>() {}
            #( #specials_out)*
            { #(for stmt in &ifn.block.stmts) {#stmt} }
        }
    };
    parse2(inner).unwrap()
}

fn specialize_impl(
    mut default_impl: ItemImpl,
    special_impls: Vec<(ItemImpl, HashMap<Ident, Type>)>,
) -> ItemImpl {
    if special_impls.len() == 0 {
        return default_impl;
    }
    let mut fn_map: HashMap<Ident, Vec<(HashMap<Ident, Type>, ImplItemFn)>> = HashMap::new();
    for (simpl, ssub) in special_impls.into_iter() {
        for item in simpl.items.into_iter() {
            match item {
                ImplItem::Fn(ifn) => {
                    fn_map
                        .entry(ifn.sig.ident.clone())
                        .or_insert(Vec::new())
                        .push((ssub.clone(), ifn));
                }
                o => abort!(o.span(), "This item cannot be specialized"),
            }
        }
    }
    let mut out = Vec::new();
    for item in default_impl.items.into_iter() {
        match item {
            ImplItem::Fn(ifn) => {
                let specials = fn_map.get(&ifn.sig.ident).cloned().unwrap_or(Vec::new());
                out.push(ImplItem::Fn(specialize_item_fn(ifn, specials)));
            }
            o => out.push(o),
        }
    }
    default_impl.items = out;
    default_impl
}

fn specialize_trait(
    default_impls: HashSet<ItemImpl>,
    special_impls: HashSet<ItemImpl>,
) -> (Vec<ItemImpl>, Vec<ItemImpl>) {
    let mut default_map: HashMap<_, _> = default_impls
        .iter()
        .cloned()
        .map(|d| (d, Vec::new()))
        .collect();
    let mut orphan_impls = Vec::new();
    for s in special_impls.into_iter() {
        if let Some((d, a, _)) = default_impls
            .iter()
            .map(|d| {
                substitute_impl(d, &s)
                    .into_iter()
                    .map(move |(sub, n)| (d, sub, n))
            })
            .flatten()
            .min_by_key(|(_, _, n)| *n)
        {
            default_map
                .entry(d.clone())
                .or_insert_with(|| unreachable!())
                .push((s, a));
        } else {
            orphan_impls.push(s);
        }
    }
    (
        default_map
            .into_iter()
            .map(|(d, s)| specialize_impl(d, s))
            .collect(),
        orphan_impls,
    )
}

fn specialization_mod(module: ItemMod) -> TokenStream {
    let (_, content) = if let Some(inner) = module.content {
        inner
    } else {
        abort!(module.span(), "Require mod content")
    };
    let (mut defaults, mut specials): (HashSet<_>, HashSet<_>) = Default::default();
    let mut generated_content = Vec::new();
    for item in content.into_iter() {
        if let Item::Impl(item_impl) = &item {
            if item_impl.trait_.is_some() {
                if let Some(defaultness) = check_defaultness(&item_impl) {
                    if defaultness {
                        defaults.insert(item_impl.clone());
                    } else {
                        specials.insert(item_impl.clone());
                    }
                    continue;
                }
            }
        }
        generated_content.push(item);
    }
    let (impls, orphans) = specialize_trait(defaults, specials);
    generated_content.extend(impls.into_iter().map(Item::Impl));
    generated_content.extend(orphans.into_iter().map(Item::Impl));

    quote! {
        #(for attr in &module.attrs) { #attr }
        #{&module.vis}
        #{&module.mod_token}
        #{&module.ident}
        {
            #(#generated_content)*
        }
    }
}

#[proc_macro_error]
#[proc_macro_attribute]
pub fn specialization(_attr: TokenStream1, input: TokenStream1) -> TokenStream1 {
    let module = parse_macro_input!(input);
    specialization_mod(module).into()
}
