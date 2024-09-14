use proc_generics::normalize;
use proc_generics::normalize::WherePredicateBinding;
use proc_generics::substitute::{Substitute, SubstituteEnvironment};
use proc_macro::TokenStream as TokenStream1;
use proc_macro2::{Span, TokenStream};
use proc_macro_error::{abort, proc_macro_error};
use std::collections::{HashMap, HashSet};
use syn::punctuated::Punctuated;
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

trait ReplaceTypeParams {
    fn replace_type_params(self, map: HashMap<Ident, Type>) -> Self;
}

const _: () = {
    fn filter_map_with_generics(
        map: &HashMap<Ident, Type>,
        generics: &Generics,
    ) -> HashMap<Ident, Type> {
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
    struct Visitor(HashMap<Ident, Type>);
    impl VisitMut for Visitor {
        fn visit_type_mut(&mut self, i: &mut Type) {
            if let Type::Path(tp) = i {
                if let Some(id) = tp.path.get_ident() {
                    if let Some(replaced) = self.0.get(id) {
                        *i = replaced.clone();
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
    impl ReplaceTypeParams for ImplItemFn {
        fn replace_type_params(mut self, map: HashMap<Ident, Type>) -> Self {
            let mut visitor = Visitor(map);
            visitor.visit_impl_item_fn_mut(&mut self);
            self
        }
    }
    impl ReplaceTypeParams for Type {
        fn replace_type_params(mut self, map: HashMap<Ident, Type>) -> Self {
            let mut visitor = Visitor(map);
            visitor.visit_type_mut(&mut self);
            self
        }
    }
};

fn contains_generics_param(param: &GenericParam, ty: &Type) -> bool {
    use syn::visit::Visit;
    struct Visitor<'a>(&'a GenericParam, bool);
    impl<'ast, 'a> Visit<'ast> for Visitor<'a> {
        fn visit_lifetime(&mut self, i: &Lifetime) {
            if matches!(&self.0, GenericParam::Lifetime(l) if &l.lifetime == i) {
                self.1 = true;
            }
        }
        fn visit_type_path(&mut self, i: &TypePath) {
            if matches!(
                (&self.0, &i.qself, i.path.get_ident()),
                (GenericParam::Type(TypeParam {ident, ..}), &None, Some(id)) |
                (GenericParam::Const(ConstParam {ident, ..}), &None, Some(id))
                if ident == id
            ) {
                self.1 = true;
            } else {
                syn::visit::visit_type_path(self, i)
            }
        }
    }
    let mut visitor = Visitor(param, false);
    visitor.visit_type(ty);
    visitor.1
}

fn specialize_item_fn_trait(
    impl_: &ItemImpl,
    ident: &Ident,
    fn_ident: &Ident,
    impl_item_fn: &ImplItemFn,
    needs_sized_bound: bool,
    self_ty: &Type,
) -> (TokenStream, Punctuated<GenericParam, Token![,]>) {
    let trait_path = &impl_.trait_.as_ref().unwrap().1;
    let impl_generics: Punctuated<_, Token![,]> = impl_
        .generics
        .params
        .iter()
        .filter(|p| {
            contains_generics_param(
                p,
                &Type::Path(TypePath {
                    qself: None,
                    path: trait_path.clone(),
                }),
            ) || contains_generics_param(p, self_ty)
        })
        .cloned()
        .collect();
    let ty_generics: Punctuated<_, Token![,]> = impl_
        .generics
        .params
        .iter()
        .filter(|p| {
            contains_generics_param(
                p,
                &Type::Path(TypePath {
                    qself: None,
                    path: trait_path.clone(),
                }),
            )
        })
        .map(|p| {
            let mut p = p.clone();
            match &mut p {
                GenericParam::Lifetime(p) => {
                    p.attrs = Vec::new();
                    p.colon_token = None;
                    p.bounds = Punctuated::new();
                }
                GenericParam::Type(t) => {
                    t.attrs = Vec::new();
                    t.colon_token = None;
                    t.bounds = Punctuated::new();
                    t.eq_token = None;
                    t.default = None;
                }
                GenericParam::Const(c) => {
                    c.attrs = Vec::new();
                    c.eq_token = None;
                    c.default = None;
                }
            }
            p
        })
        .collect();
    let mut item_fn = TraitItemFn {
        attrs: vec![],
        sig: impl_item_fn.sig.clone(),
        default: None,
        semi_token: Some(Default::default()),
    };
    item_fn.sig.ident = fn_ident.clone();
    let mut impl_item_fn = impl_item_fn.clone();
    impl_item_fn.defaultness = None;
    impl_item_fn.sig.ident = fn_ident.clone();
    let out = quote! {
        trait #ident<#ty_generics>: #trait_path
            #(if needs_sized_bound) { + ::core::marker::Sized }
        {
            #item_fn
        }
        impl<#impl_generics> #ident<#ty_generics> for #self_ty
        #{&impl_.generics.where_clause}
        {
            #impl_item_fn
        }
    };
    (out, ty_generics)
}

fn set_argument_named(sig: &mut Signature) {
    for (n, arg) in sig.inputs.iter_mut().enumerate() {
        if let FnArg::Typed(PatType { pat, .. }) = arg {
            if let Pat::Wild(_) = &**pat {
                *pat = Box::new(Pat::Ident(PatIdent {
                    attrs: Vec::new(),
                    by_ref: None,
                    mutability: None,
                    ident: Ident::new(&format!("_min_specialization_v{}", n), pat.span()),
                    subpat: None,
                }));
            }
        }
    }
}

fn specialize_item_fn(
    default_impl: &ItemImpl,
    mut ifn: ImplItemFn,
    specials: Vec<(HashMap<Ident, Type>, ItemImpl, ImplItemFn)>,
    needs_sized_bound: bool,
) -> ImplItemFn {
    let itrait_name = Ident::new("__MinSpecialization_InnerTrait", Span::call_site());
    let ifn_name = Ident::new("__min_specialization__inner_fn", Span::call_site());
    set_argument_named(&mut ifn.sig);
    let specials_out = specials
        .into_iter()
        .enumerate()
        .map(|(n, (m, simpl, mut sfn))| {
            let strait_name = Ident::new(
                &format!("__MinSpecialization_InnerTrait_{}", n),
                Span::call_site(),
            );
            let sfn_name = Ident::new(
                &format!("__min_specialization__inner_fn_{}", n),
                Span::call_site(),
            );
            sfn.sig.ident = sfn_name.clone();
            let mut condition = quote! {true};
            let mut replacement = HashMap::new();
            for (lhs, rhs) in m.iter() {
                if let Some(rhs) = get_type_ident(rhs.clone()) {
                    if simpl
                        .generics
                        .params
                        .iter()
                        .filter_map(|p| {
                            if let GenericParam::Type(p) = p {
                                Some(&p.ident)
                            } else {
                                None
                            }
                        })
                        .any(|p| p == &rhs)
                    {
                        let lhs = Type::Path(TypePath {
                            qself: None,
                            path: Path {
                                leading_colon: None,
                                segments: Some(PathSegment {
                                    ident: lhs.clone(),
                                    arguments: PathArguments::None,
                                })
                                .into_iter()
                                .collect(),
                            },
                        });
                        replacement.insert(rhs, lhs);
                        continue;
                    }
                }
                condition.extend(quote! {
                    && __min_specialization_id::<#lhs> as *const ()
                        == __min_specialization_id::<#rhs> as *const ()
                });
            }
            let sfn = sfn.replace_type_params(replacement.clone());
            let replaced_self_ty = default_impl.self_ty.clone().replace_type_params(m.clone());
            let (special_trait_impl, special_trait_params) = specialize_item_fn_trait(
                default_impl,
                &strait_name,
                &sfn_name,
                &sfn,
                needs_sized_bound,
                &replaced_self_ty,
            );
            quote! {
                if #condition {
                    #special_trait_impl
                    __min_specialization_transmute(
                        <#replaced_self_ty as #strait_name<
                            #(for par in &special_trait_params), {
                                #(if let GenericParam::Type(TypeParam{ident, ..}) = par) {
                                    #(if let Some(ident) = replacement.get(ident)) {
                                        #ident
                                    }
                                    #(else) {
                                        #ident
                                    }
                                } #(else) {
                                    #par
                                }
                            }
                        >>::#sfn_name(
                            #(for arg in &ifn.sig.inputs), {
                                #(if let FnArg::Receiver(_) = arg) {
                                    __min_specialization_transmute(self)
                                }
                                #(if let FnArg::Typed(pt) = arg) {
                                    #(if &*pt.ty == &Type::Path(parse_quote!(Self))) {
                                        __min_specialization_transmute(#{&pt.pat})
                                    } #(else) {
                                        #{&pt.pat}
                                    }
                                }
                            }
                        )
                    )
                } else
            }
        })
        .collect::<Vec<_>>();
    let (default_trait_impl, default_trait_params) = specialize_item_fn_trait(
        default_impl,
        &itrait_name,
        &ifn_name,
        &ifn,
        needs_sized_bound,
        &default_impl.self_ty,
    );
    let inner = quote! {
        #(for attr in &ifn.attrs) {#attr}
        #{&ifn.vis}
        #{&ifn.sig}
        {
            fn __min_specialization_id<T>(input: &T) -> ! {
                unsafe {
                    let _ = ::core::mem::MaybeUninit::new(
                        ::core::ptr::read_volatile(input as *const _)
                    );
                }
                ::core::panic!()
            }
            fn __min_specialization_transmute<T, U>(input: T) -> U {
                ::core::assert_eq!(
                    ::core::mem::size_of::<T>(),
                    ::core::mem::size_of::<U>()
                );
                ::core::assert_eq!(
                    ::core::mem::align_of::<T>(),
                    ::core::mem::align_of::<U>()
                );
                let mut rhs = ::core::mem::MaybeUninit::new(input);
                let mut lhs = ::core::mem::MaybeUninit::<U>::uninit();
                unsafe {
                    let rhs = ::core::mem::transmute::<
                        _, &mut ::core::mem::MaybeUninit<U>
                    >(&mut rhs);
                    ::core::ptr::swap(lhs.as_mut_ptr(), rhs.as_mut_ptr());
                    lhs.assume_init()
                }
            }
            #( #specials_out)*
            {
                #default_trait_impl
                <#{&default_impl.self_ty} as #itrait_name<#default_trait_params>>::#ifn_name(
                    #(for arg in &ifn.sig.inputs),{
                        #(if let FnArg::Receiver(Receiver{self_token, ..}) = arg) {
                            #self_token
                        }
                        #(if let FnArg::Typed(PatType{pat, ..}) = arg) {
                            #pat
                        }
                    }
                )
            }
        }
    };
    parse2(inner).unwrap()
}

fn check_needs_sized_bound(impl_: &ItemImpl) -> bool {
    impl_
        .items
        .iter()
        .filter_map(|item| {
            if let ImplItem::Fn(item) = item {
                Some(item)
            } else {
                None
            }
        })
        .any(|item| {
            item.sig
                .inputs
                .iter()
                .filter_map(|item| {
                    if let FnArg::Typed(PatType { ty, .. }) = item {
                        Some(&*ty)
                    } else {
                        None
                    }
                })
                .chain(if let ReturnType::Type(_, ty) = &item.sig.output {
                    Some(&*ty)
                } else {
                    None
                })
                .any(|ty| ty == &impl_.self_ty || ty == &parse_quote!(Self))
        })
}

fn specialize_impl(
    mut default_impl: ItemImpl,
    special_impls: Vec<(ItemImpl, HashMap<Ident, Type>)>,
) -> ItemImpl {
    if special_impls.len() == 0 {
        return default_impl;
    }
    let needs_sized_bound = check_needs_sized_bound(&default_impl);
    let mut fn_map = HashMap::new();
    for (simpl, ssub) in special_impls.into_iter() {
        for item in simpl.items.iter() {
            match item {
                ImplItem::Fn(ifn) => {
                    fn_map
                        .entry(ifn.sig.ident.clone())
                        .or_insert(Vec::new())
                        .push((ssub.clone(), simpl.clone(), ifn.clone()));
                }
                o => abort!(o.span(), "This item cannot be specialized"),
            }
        }
    }
    let mut out = Vec::new();
    for item in &default_impl.items {
        match item {
            ImplItem::Fn(ifn) => {
                let specials = fn_map.get(&ifn.sig.ident).cloned().unwrap_or(Vec::new());
                out.push(ImplItem::Fn(specialize_item_fn(
                    &default_impl,
                    ifn.clone(),
                    specials,
                    needs_sized_bound,
                )));
            }
            o => out.push(o.clone()),
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
