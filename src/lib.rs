#![doc = include_str!("../README.md")]

mod normalize;
mod substitute;

use normalize::WherePredicateBinding;
use proc_macro::TokenStream as TokenStream1;
use proc_macro2::{Span, TokenStream};
use proc_macro_error::{abort, proc_macro_error};
use std::collections::{HashMap, HashSet};
use substitute::{Substitute, SubstituteEnvironment};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::visit_mut::VisitMut;
use syn::*;
use template_quote::quote;

fn replace_type_of_trait_item_fn(mut ty: TraitItemFn, from: &Type, to: &Type) -> TraitItemFn {
    use syn::visit_mut::VisitMut;
    struct Visitor<'a>(&'a Type, &'a Type);
    impl<'a> VisitMut for Visitor<'a> {
        fn visit_type_mut(&mut self, ty: &mut Type) {
            if &ty == &self.0 {
                *ty = self.1.clone();
            }
            syn::visit_mut::visit_type_mut(self, ty)
        }
    }
    let mut visitor = Visitor(from, to);
    visitor.visit_trait_item_fn_mut(&mut ty);
    ty
}

/// Replace every named lifetime (other than `'static`) in a type with `to`.
/// Used to refer to a specialization's self type from inside the (lifetime-agnostic)
/// dispatcher: `'static` for the type-id comparison (which erases lifetimes anyway),
/// and `'_` for the actual call (so the lifetime is inferred and the transmute stays
/// an identity conversion at the caller's lifetime).
fn map_lifetimes(mut ty: Type, to: Lifetime) -> Type {
    struct V(Lifetime);
    impl VisitMut for V {
        fn visit_lifetime_mut(&mut self, i: &mut Lifetime) {
            if i.ident != "static" {
                *i = self.0.clone();
            }
        }
    }
    V(to).visit_type_mut(&mut ty);
    ty
}

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
    // Remove `Self` type
    let self_ident = Ident::new("Self", Span::call_site());
    let d_ws = d_ws
        .into_iter()
        .map(|w| {
            w.replace_type_params(
                core::iter::once((self_ident.clone(), default_impl.self_ty.as_ref().clone()))
                    .collect(),
            )
        })
        .collect::<HashSet<_>>();
    let s_ws = s_ws
        .into_iter()
        .map(|w| {
            w.replace_type_params(
                core::iter::once((self_ident.clone(), special_impl.self_ty.as_ref().clone()))
                    .collect(),
            )
        })
        .collect::<HashSet<_>>();
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

    impl ReplaceTypeParams for WherePredicateBinding {
        fn replace_type_params(self, map: HashMap<Ident, Type>) -> Self {
            match self {
                WherePredicateBinding::Lifetime(lt) => {
                    WherePredicateBinding::Lifetime(lt.replace_type_params(map))
                }
                WherePredicateBinding::Type(pt) => {
                    WherePredicateBinding::Type(pt.replace_type_params(map))
                }
                WherePredicateBinding::Eq {
                    lhs_ty,
                    eq_token,
                    rhs_ty,
                } => WherePredicateBinding::Eq {
                    lhs_ty: lhs_ty.replace_type_params(map.clone()),
                    eq_token,
                    rhs_ty: rhs_ty.replace_type_params(map),
                },
            }
        }
    }
    impl ReplaceTypeParams for PredicateType {
        fn replace_type_params(mut self, map: HashMap<Ident, Type>) -> Self {
            let mut visitor = Visitor(map);
            visitor.visit_predicate_type_mut(&mut self);
            self
        }
    }
    impl ReplaceTypeParams for PredicateLifetime {
        fn replace_type_params(mut self, map: HashMap<Ident, Type>) -> Self {
            let mut visitor = Visitor(map);
            visitor.visit_predicate_lifetime_mut(&mut self);
            self
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

/// A name key for de-duplicating generic parameters by what they introduce.
fn generic_param_key(p: &GenericParam) -> String {
    match p {
        GenericParam::Lifetime(l) => format!("'{}", l.lifetime.ident),
        GenericParam::Type(t) => t.ident.to_string(),
        GenericParam::Const(c) => c.ident.to_string(),
    }
}

/// Whether a generic parameter is referenced anywhere in a function signature's
/// argument or return types (used to decide which params the inner impl must declare).
fn param_in_sig(p: &GenericParam, sig: &Signature) -> bool {
    let used = |ty: &Type| contains_generics_param(p, ty);
    sig.inputs.iter().any(|arg| match arg {
        FnArg::Typed(pt) => used(&pt.ty),
        FnArg::Receiver(r) => used(&r.ty),
    }) || matches!(&sig.output, ReturnType::Type(_, ty) if used(ty))
}

fn specialize_item_fn_trait(
    impl_: &ItemImpl,
    extra_generics: &Punctuated<GenericParam, Token![,]>,
    ident: &Ident,
    fn_ident: &Ident,
    impl_item_fn: &ImplItemFn,
    needs_sized_bound: bool,
    self_ty: &Type,
) -> (TokenStream, Punctuated<GenericParam, Token![,]>) {
    let trait_path = &impl_.trait_.as_ref().unwrap().1;
    let trait_ty = Type::Path(TypePath {
        qself: None,
        path: trait_path.clone(),
    });

    let mut item_fn = replace_type_of_trait_item_fn(
        TraitItemFn {
            attrs: vec![],
            sig: impl_item_fn.sig.clone(),
            default: None,
            semi_token: Some(Default::default()),
        },
        &impl_.self_ty,
        &parse_quote!(Self),
    );
    item_fn.sig.ident = fn_ident.clone();
    // The inner trait method is a *declaration* (no body), so its argument patterns
    // must be plain identifiers; the implementing method below keeps the original
    // patterns and body. Trait/impl signatures only need matching types, not names.
    set_argument_named(&mut item_fn.sig);

    // Candidate generics: this impl's own parameters plus the specialization's
    // parameters (e.g. lifetimes appearing in a specialized type like `Foo<'a>` or
    // `&'a str`), de-duplicated by name. We then keep only those actually referenced.
    let mut pool: Vec<GenericParam> = Vec::new();
    for p in impl_.generics.params.iter().chain(extra_generics.iter()) {
        let key = generic_param_key(p);
        if !pool.iter().any(|q| generic_param_key(q) == key) {
            pool.push(p.clone());
        }
    }

    // Parameters referenced by the self type or trait path are declared on the inner
    // impl (e.g. `impl<'a> .. for Foo<'a>`).
    let impl_generics: Punctuated<_, Token![,]> = pool
        .iter()
        .filter(|p| contains_generics_param(p, &trait_ty) || contains_generics_param(p, self_ty))
        .cloned()
        .collect();
    // A specialization lifetime that appears only in the *method signature* (not the
    // self type or trait path) is declared as a method-level lifetime instead, e.g.
    // `impl Tr<&'a str>`'s method becomes `fn inner<'a>(&self, u: &'a str)`.
    let mut method_extra_lifetimes: Vec<GenericParam> = pool
        .iter()
        .filter(|p| matches!(p, GenericParam::Lifetime(_)))
        .filter(|p| {
            param_in_sig(p, &item_fn.sig)
                && !impl_generics
                    .iter()
                    .any(|q| generic_param_key(q) == generic_param_key(p))
        })
        .cloned()
        .collect();
    for p in &mut method_extra_lifetimes {
        if let GenericParam::Lifetime(l) = p {
            l.attrs.clear();
            l.colon_token = None;
            l.bounds = Punctuated::new();
        }
    }
    let ty_generics: Punctuated<_, Token![,]> = pool
        .iter()
        .filter(|p| contains_generics_param(p, &trait_ty))
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
    let mut impl_item_fn = impl_item_fn.clone();
    impl_item_fn.defaultness = None;
    impl_item_fn.sig.ident = fn_ident.clone();
    // Declare the method-level lifetimes on both the trait declaration and the impl
    // method (their signatures must match), in front of any existing generics.
    for lt in method_extra_lifetimes.into_iter().rev() {
        item_fn.sig.generics.params.insert(0, lt.clone());
        impl_item_fn.sig.generics.params.insert(0, lt);
    }
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

/// Replace every by-value argument pattern with a fresh, plain identifier.
///
/// This is applied to the signatures that are *re-emitted* by the macro: the
/// outer dispatcher's signature (whose body only forwards its arguments) and the
/// generated inner-trait method *declarations* (which are bodyless, where any
/// non-trivial pattern is rejected by `E0642`). It must NOT be applied to the
/// method bodies, which keep their original patterns. Forwarding a fresh
/// identifier is always a valid expression, which avoids the historical panics on
/// `mut x` / `ref x` and the `E0642` on tuple/struct patterns.
fn set_argument_named(sig: &mut Signature) {
    for (n, arg) in sig.inputs.iter_mut().enumerate() {
        if let FnArg::Typed(PatType { pat, .. }) = arg {
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

fn specialize_item_fn(
    default_impl: &ItemImpl,
    mut ifn: ImplItemFn,
    specials: Vec<(HashMap<Ident, Type>, ItemImpl, ImplItemFn)>,
    needs_sized_bound: bool,
) -> ImplItemFn {
    let itrait_name = Ident::new("__MinSpecialization_InnerTrait", Span::call_site());
    let ifn_name = Ident::new("__min_specialization__inner_fn", Span::call_site());
    // Keep the original method (patterns + body) for the inner default-trait impl;
    // the outer dispatcher uses freshly-named arguments so it can forward them.
    let orig_ifn = ifn.clone();
    set_argument_named(&mut ifn.sig);
    // A method may have its own generic parameters. Inside the dispatcher those are
    // in scope (the outer method declares them), so we forward them to the inner
    // method as an explicit turbofish. This pins the inner method's generics across
    // the type-erasing transmute (otherwise they could not be inferred -> `E0282`).
    // Forwarding is positional, so the inner method's parameter names are irrelevant.
    let method_turbofish: TokenStream = {
        let args: Vec<&Ident> = ifn
            .sig
            .generics
            .params
            .iter()
            .filter_map(|p| match p {
                GenericParam::Type(t) => Some(&t.ident),
                GenericParam::Const(c) => Some(&c.ident),
                GenericParam::Lifetime(_) => None,
            })
            .collect();
        if args.is_empty() {
            quote! {}
        } else {
            quote! { ::<#(#args),*> }
        }
    };
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
                // The type-id check is lifetime-agnostic, so erase the special's
                // lifetimes to `'static` (which is always nameable) to avoid
                // referencing the special impl's lifetimes, which are not in scope
                // in this dispatcher.
                let rhs = map_lifetimes(rhs.clone(), parse_quote!('static));
                condition.extend(quote! {
                    && __min_specialization_type_id::<#lhs>()
                        == __min_specialization_type_id::<#rhs>()
                });
            }
            let sfn = sfn.replace_type_params(replacement.clone());
            let replaced_self_ty = default_impl.self_ty.clone().replace_type_params(m.clone());
            // For the actual call, refer to the self type with inferred (`'_`)
            // lifetimes so they unify with the caller's; the inner impl below is
            // generic over those lifetimes, keeping the transmute an identity.
            let replaced_self_ty_call = map_lifetimes(replaced_self_ty.clone(), parse_quote!('_));
            let (special_trait_impl, special_trait_params) = specialize_item_fn_trait(
                default_impl,
                &simpl.generics.params,
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
                        <#replaced_self_ty_call as #strait_name<
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
                        >>::#sfn_name #{&method_turbofish}(
                            #(for arg in &ifn.sig.inputs), {
                                #(if let FnArg::Receiver(_) = arg) {
                                    __min_specialization_transmute(self)
                                }
                                #(if let FnArg::Typed(pt) = arg) {
                                    __min_specialization_transmute(#{&pt.pat})
                                }
                            }
                        )
                    )
                } else
            }
        })
        .collect::<Vec<_>>();
    let no_extra_generics = Punctuated::new();
    let (default_trait_impl, default_trait_params) = specialize_item_fn_trait(
        default_impl,
        &no_extra_generics,
        &itrait_name,
        &ifn_name,
        &orig_ifn,
        needs_sized_bound,
        &default_impl.self_ty,
    );
    let inner = quote! {
        #(for attr in &ifn.attrs) {#attr}
        #{&ifn.vis}
        #{&ifn.sig}
        {
            // Sound, lifetime-erased type identity. `TypeId::of` requires `'static`,
            // which would forbid specializing on borrowed types such as `&str`. We
            // instead obtain the `TypeId` of the *lifetime-erased* type via a trait
            // object whose existential lifetime is widened to `'static` (the value is
            // a ZST `PhantomData`, so no non-`'static` data is ever accessed). The
            // result identifies a type up to its lifetimes, which is exactly the
            // granularity specialization needs — `min_specialization` never dispatches
            // on lifetimes. `TypeId` is collision-free, so this has neither the false
            // positives (identical-code-folding) nor the false negatives of comparing
            // function-pointer addresses.
            fn __min_specialization_type_id<T: ?::core::marker::Sized>() -> ::core::any::TypeId {
                trait __MinSpecializationNonStaticAny {
                    fn __min_specialization_type_id(&self) -> ::core::any::TypeId
                    where
                        Self: 'static;
                }
                impl<T: ?::core::marker::Sized> __MinSpecializationNonStaticAny
                    for ::core::marker::PhantomData<T>
                {
                    fn __min_specialization_type_id(&self) -> ::core::any::TypeId
                    where
                        Self: 'static,
                    {
                        ::core::any::TypeId::of::<T>()
                    }
                }
                let it = ::core::marker::PhantomData::<T>;
                let it: &dyn __MinSpecializationNonStaticAny = &it;
                let it: &(dyn __MinSpecializationNonStaticAny + 'static) =
                    unsafe { ::core::mem::transmute(it) };
                it.__min_specialization_type_id()
            }
            // Whenever a branch is taken, the generic `T` and the concrete branch type
            // are the same type (up to lifetimes), so the transmutes below are identity
            // conversions. The size/align assertions are retained purely as cheap
            // defense-in-depth; they always hold.
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
                <#{&default_impl.self_ty} as #itrait_name<#default_trait_params>>::#ifn_name #{&method_turbofish}(
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
    parse2(inner).unwrap_or_else(|e| {
        abort!(
            e.span(),
            "#[specialization] generated code that failed to parse: {}", e;
            note = "this is a bug in min-specialization; please report it with the offending impl"
        )
    })
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

/// Remove every `default` keyword from an impl and its items, turning it into an
/// ordinary impl. Leaving a stray `default fn` behind triggers `E0658`
/// ("specialization is unstable") on stable.
fn strip_defaultness(impl_: &mut ItemImpl) {
    impl_.defaultness = None;
    for item in impl_.items.iter_mut() {
        match item {
            ImplItem::Fn(f) => f.defaultness = None,
            ImplItem::Const(c) => c.defaultness = None,
            ImplItem::Type(t) => t.defaultness = None,
            _ => {}
        }
    }
}

fn specialize_impl(
    mut default_impl: ItemImpl,
    special_impls: Vec<(ItemImpl, HashMap<Ident, Type>)>,
) -> ItemImpl {
    if special_impls.len() == 0 {
        // A default impl with no matching specialization is just an ordinary impl;
        // strip the `default` keyword so it does not leak `E0658` on stable.
        strip_defaultness(&mut default_impl);
        return default_impl;
    }
    let needs_sized_bound = check_needs_sized_bound(&default_impl);
    let default_fn_idents: HashSet<Ident> = default_impl
        .items
        .iter()
        .filter_map(|item| match item {
            ImplItem::Fn(ifn) => Some(ifn.sig.ident.clone()),
            _ => None,
        })
        .collect();
    let mut fn_map = HashMap::new();
    for (simpl, ssub) in special_impls.into_iter() {
        for item in simpl.items.iter() {
            match item {
                ImplItem::Fn(ifn) => {
                    // A specialization may only override methods that the default impl
                    // itself defines; otherwise the override would be silently dropped.
                    if !default_fn_idents.contains(&ifn.sig.ident) {
                        abort!(
                            ifn.sig.ident.span(),
                            "`{}` is overridden in a specialization but is not defined in the \
                             default impl, so it cannot be specialized",
                            ifn.sig.ident;
                            help = "give the default impl a `default fn {}` to specialize",
                            ifn.sig.ident
                        );
                    }
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
    default_impls: Vec<ItemImpl>,
    special_impls: Vec<ItemImpl>,
) -> (Vec<ItemImpl>, Vec<ItemImpl>) {
    let mut default_specials: Vec<Vec<(ItemImpl, HashMap<Ident, Type>)>> =
        default_impls.iter().map(|_| Vec::new()).collect();
    let mut orphan_impls = Vec::new();
    for s in special_impls.into_iter() {
        // Attach each specialization to the default impl it refines: the one needing
        // the fewest non-trivial substitutions. `min_by_key` keeps the first such
        // default on ties, so the choice follows source order and is deterministic.
        let best = default_impls
            .iter()
            .enumerate()
            .flat_map(|(i, d)| substitute_impl(d, &s).into_iter().map(move |(sub, n)| (i, sub, n)))
            .min_by_key(|(_, _, n)| *n);
        if let Some((i, sub, _)) = best {
            default_specials[i].push((s, sub));
        } else {
            orphan_impls.push(s);
        }
    }
    // Reject literally-overlapping specializations (same trait + same self type
    // refining the same default impl). Real specialization rejects these as a
    // coherence error (`E0119`); without this check they would silently fold into
    // the dispatch chain with a nondeterministic winner.
    for specials in &default_specials {
        for (i, (a, _)) in specials.iter().enumerate() {
            for (b, _) in specials.iter().skip(i + 1) {
                if a.trait_.as_ref().map(|t| &t.1) == b.trait_.as_ref().map(|t| &t.1)
                    && a.self_ty == b.self_ty
                {
                    abort!(
                        b.span(),
                        "conflicting specializations: this impl overlaps another \
                         specialization of the same trait for the same type";
                        note = "min-specialization cannot order overlapping specializations"
                    );
                }
            }
        }
    }
    let impls = default_impls
        .into_iter()
        .zip(default_specials)
        .map(|(d, specials)| specialize_impl(d, specials))
        .collect();
    (impls, orphan_impls)
}

fn specialization_mod(module: ItemMod) -> TokenStream {
    let (_, content) = if let Some(inner) = module.content {
        inner
    } else {
        abort!(module.span(), "Require mod content")
    };
    // Source order is preserved (plain `Vec`s, not `HashSet`s) so that codegen —
    // and in particular the order of the runtime dispatch chain — is deterministic
    // across compilations.
    let (mut defaults, mut specials): (Vec<ItemImpl>, Vec<ItemImpl>) = (Vec::new(), Vec::new());
    let mut generated_content = Vec::new();
    for item in content.into_iter() {
        if let Item::Impl(item_impl) = &item {
            if item_impl.trait_.is_some() {
                if let Some(defaultness) = check_defaultness(&item_impl) {
                    if defaultness {
                        defaults.push(item_impl.clone());
                    } else {
                        specials.push(item_impl.clone());
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
