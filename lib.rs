use proc_generics::normalize;
use proc_generics::normalize::WherePredicateBinding;
use proc_generics::substitute::{Substitute, SubstituteEnvironment};
use proc_macro::TokenStream as TokenStream1;
use proc_macro2::TokenStream;
use proc_macro_error::{abort, proc_macro_error};
use std::collections::{HashMap, HashSet};
use syn::spanned::Spanned;
use syn::*;
use template_quote::quote;

// fn split_path_args<
//     I: IntoIterator<Item = &GenericArgument>,
//     A: Default + Extend<&GenericArgument>,
//     B: Default + Extend<&Binding>,
//     C: Default + Extend<Constraint>,
// >(
//     input: I,
// ) -> (A, B, C) {
//     inout.into_iter().fold(
//         Default::default(),
//         |(mut a, mut b, mut c), item| match item {
//             GenericArgument::Binding(binding) => b.extend(Some(binding)),
//             GenericArgument::Constraint(constraint) => c.extend(Some(constraint)),
//             o => a.extend(Some(o)),
//         },
//     )
// }
//
// #[derive(Default, Clone, PartialEq, Eq)]
// struct Assignment<'a>(HashMap<&'a Ident, &'a Type>);
//
// impl<'a> Assignment<'a> {
//     fn new(key: &'a Ident, val: &'a Type) -> Self {
//         let mut result = HashMap::with_capacity(1);
//         result.insert(key, val);
//         Assignment(result)
//     }
//     fn product(mut self, other: Self) -> Option<Self> {
//         other
//             .0
//             .into_iter()
//             .map(|(k, v)| self.0.insert(k, v).is_none())
//             .product()
//             .then_some(self)
//     }
// }
//
// // remove bounds from generic parameters and path arguments and associated type bounds from path
// // arguments.
// //
// // before
// // ```ignore
// // impl<A: Iterator<Item: Debug>> Tr for T<A>
// // where
// // A: Add<Output = usize> { ... }
// // ```
// //
// // after
// // ```ignore
// // impl<A> Tr for T<A>
// // where
// // A: Iterator<>,
// // <A as Iterator<>>::Item: Debug,
// // A: Add,
// // <A as Add>::Output = usize, { ... }
// // ```
// fn normalize_generics(mut generics: Generics) -> Generics {
//     use GenericParam as GP;
//     let where_clause = generics.make_where_clause();
//     for item in generics.params.iter_mut() {
//         match item {
//             GP::Type(tp) => {
//                 if let Some((colon_token, bounds)) = tp.colon_token.take().zip(tp.bounds.take()) {
//                     where_clause
//                         .predicates
//                         .push(WherePredicate::Type(PredicateType {
//                             lifetimes: None,
//                             bounded_ty: TypePath {
//                                 qself: None,
//                                 path: tp.ident.clone().into(),
//                             },
//                             colon_token,
//                             bounds,
//                         }));
//                 }
//             }
//             GP::Lifetime(ld) => {
//                 if let Some((colon_token, bounds)) = ld.colon_token.take().zip(ld.bounds.take()) {
//                     where_clause
//                         .predicates
//                         .push(WherePredicate::Lifetime(PredicateLifetime {
//                             lifetime: ld.lifetime.clone(),
//                             colon_token,
//                             bounds,
//                         }));
//                 }
//             }
//             _ => (),
//         }
//     }
//     let mut additional_predicates = Vec::new();
//     for pred in where_clause.predicates.iter_mut() {
//         if let WherePredicate::Type(pt) = pred {
//             for bound in pt.bounds.iter_mut() {
//                 if let TypeParamBound::Trait(tb) = bound {
//                     if let Some(last_ps) = tb.path.segments.last_mut() {
//                         if let PathArguments::AngleBracketed(ga) = &mut last_ps.arguments {
//                             let old_args = std::mem::replace(&mut ga.args, Default::default());
//                             let mut constraints = Vec::new();
//                             for arg in old_args.into_iter() {
//                                 match arg {
//                                     GenericArgument::Binding(Binding {
//                                         ident,
//                                         eq_token,
//                                         ty,
//                                     }) => {
//                                         let lhs_ty = parse(
//                                             quote! {<#{&pt.bounded_ty} as #tb>::#ident}.into(),
//                                         )
//                                         .unwrap();
//                                         additional_predicates.push(WherePredicate::Eq(
//                                             PredicateEq {
//                                                 lhs_ty,
//                                                 eq_token,
//                                                 rhs_ty: ty,
//                                             },
//                                         ))
//                                     }
//                                     GenericArgument::Constraint(PredicateConst {
//                                         ident,
//                                         colon_token,
//                                         bounds,
//                                     }) => {
//                                         let bounded_ty = parse(
//                                             quote! {<#{&pt.bounded_ty} as #tb>::#ident}.into(),
//                                         )
//                                         .unwrap();
//                                         additional_predicates.push(WherePredicate::Type(
//                                             PredicateType {
//                                                 lifetimes: None,
//                                                 bounded_ty,
//                                                 colon_token,
//                                                 bounds,
//                                             },
//                                         ));
//                                     }
//                                     o => ga.args.push(o),
//                                 }
//                             }
//                         }
//                     }
//                 }
//             }
//         }
//     }
//     where_clause.predicates.extend(additional_predicates);
//     generics
// }
//
// // compare paths, returns assignment if it is assignable.
// fn assign_path(
//     generic_params: &HashMap<&TypeParam>,
//     default_path: &Path,
//     path: &Path,
// ) -> Option<Assignment<'_>> {
//     let _ = default_path
//         .leading_colon
//         .zip(path.leading_colon.as_ref())?;
//     let mut assignment = Defaut::default();
//     (default_path.segments.len() == path.segments.len()).then_some(())?;
//     for (seg0, seg1) in default_path.segments.zip(&path.segments) {
//         (&seg0.ident == &seg1.ident).then_some(())?;
//         match (&seg0.arguments, &seg1.arguments) {
//             (PathArguments::None, PathArguments::None) => (),
//             (PathArguments::AngleBracketed(arg0), PathArguments::AngleBracketed(arg1)) => {
//                 use GenericArgument as GA;
//                 let (a0s, b0s, c1s) = split_path_args(&arg0.args) as (Vec<_>, Vec<_>, Vec<_>);
//                 let (a1s, b1s, c1s) = split_path_args(&arg1.args) as (Vec<_>, Vec<_>, Vec<_>);
//                 assert_eq!(b0s.len(), 0);
//                 assert_eq!(b1s.len(), 0);
//                 assert_eq!(c0s.len(), 0);
//                 assert_eq!(c1s.len(), 0);
//                 (a0s.len() == a1s.len()).then_some(())?;
//                 for (a0, a1) in a0s.iter().zip(a1s) {
//                     match (a0, a1) {
//                         (GA::Lifetime(lt0), GA::Lifetime(lt1)) if &lt.ident == &lt1.ident => {}
//                         (GA::Type(typ0), GA::Type(typ1)) => {
//                             assignment =
//                                 assign_type(generic_params, typ0, typ1)?.product(assignment)?;
//                         }
//                         // We do not support specialization in exprs
//                         (GA::Const(expr0), GA::Const(expr1)) if &expr0 == &expr1 => {}
//                         (GA::Binding(_), GA::Binding(_))
//                         | (GA::Constraint(_), GA::Constraint(_)) => unreachable!(),
//                         _ => return None,
//                     }
//                 }
//             }
//             (PathArguments::Parenthesized(arg0), PathArguments::Parenthesized(arg1)) => {
//                 (arg0.inputs.len() == arg1.inputs.len()).then_some(())?;
//                 for (t0, t1) in arg0.inputs.iter().zip(&arg1.inputs) {
//                     assignment = assign_type(generic_params, t0, t1)?.product(assignment)?;
//                 }
//                 let rt0 = match &arg0.output {
//                     ReturnType::Default => Type::Tuple(Default::default()),
//                     ReturnType::Type(_, btyp) => btyp.clone(),
//                 };
//                 let rt1 = match &arg1.output {
//                     ReturnType::Default => Type::Tuple(Default::default()),
//                     ReturnType::Type(_, btyp) => btyp.clone(),
//                 };
//                 return assign_type(generic_params, &rt0, &rt1)?.product(assignment);
//             }
//             _ => return None,
//         }
//     }
//     Some(assignment)
// }
//
// fn assign_type(
//     generic_params: &HashMap<&TypeParam>,
//     default_typ: &Path,
//     typ: &Path,
// ) -> Option<Assignment<'_>> {
//     match (default_typ, typ) {
//         (Type::Array(ta0), Type::Array(ta1)) => {
//             // We do not allow specialization in const expr
//             (&ta0.len == &ta1.len).then_some(())?;
//             assign_type(generic_params, &ta0.elem, &ta1.elem)
//         }
//         (Type::BareFn(tb0), Type::BareFn(tb1)) => {
//             (&tb0.lifetimes == &tb1.lifetimes).then_some(())?;
//             (&tb0.unsafety == &tb1.unsafety).then_some(())?;
//             (&tb0.abi == &tb1.abi).then_some(())?;
//             (&tb0.inputs.len() == &tb1.inputs.len()).then_some(())?;
//             let mut assignment = Default::default();
//             for (arg0, arg1) in tb0.inputs.iter().zip(&tb1.inputs) {
//                 assignment = assign_type(generic_params, &arg0.ty, &arg1.ty)?.product(assignment)
//             }
//             (&tb0.variadic == &tb1.variadic).then_some(())?;
//             Some(assignment)
//         }
//         (Type::Group(g0), Type::Group(g1)) => assign_type(generic_params, &g0.elem, &g1.elem),
//         (Type::Paren(p0), Type::Paren(p1)) => assign_type(generic_params, &p0.elem, &p1.elem),
//         (Type::Path(p0), o1)
//             if p0.is_ident()
//                 && generic_params
//                     .left
//                     .values()
//                     .any(|tp| p0.is_ident(&tp.ident)) =>
//         {
//             let ident = p0.get_ident().unwrap();
//             Some(Assignment::new(ident, o1))
//         }
//         (Type::Path(p0), Type::Path(p1)) => {
//             (&p0.qself.is_some() == &p1.qself.is_some()).then_some(())?;
//             assign_type(generic_params, &p0.path, &p1.path)
//         }
//         (Type::Ptr(p0), Type::Ptr(p1)) => {
//             (&p0.const_token == &p1.const_token).then_some(())?;
//             (&p0.mutability == &p1.mutability).then_some(())?;
//             assign_type(generic_params, &p0.elem, &p1.elem)
//         }
//         (Type::Reference(p0), Type::Reference(p1)) => {
//             (&p0.lifetime == &p1.lifetime).then_some(())?;
//             (&p0.mutability == &p1.mutability).then_some(())?;
//             assign_type(generic_params, &p0.elem, &p1.elem)
//         }
//         (Type::Slice(s0), Type::Slice(s1)) => assign_type(generic_params, &s0.elem, &s1.elem),
//         (Type::Tuple(t0), Type::Tuple(t1)) => {
//             (t0.elems.len() == t1.elems.len()).then_some(())?;
//             let mut assignment = Default::default();
//             for (ty0, ty1) in t0.elems.iter().zip(&t1.elems) {
//                 assignment =
//                     assign_type(generic_params, &ty0.elem, &ty1.elem)?.product(assignment)?;
//             }
//             Some(assignment)
//         }
//         // we do not support specialization in impl Trait
//         (o1, o2) => (o1 == o2).then_some(HashMap::new()),
//     }
// }
//
// fn normalize_sig(input: &mut Signature) {
//     for arg in input.inputs.iter_mut() {
//         match arg {
//             FnArg::Receiver(r) => {
//                 r.mutability = None;
//             }
//             FnArg::Typed(pt) => {
//                 if let Pat::Ident(pi) = &mut pt.pat {
//                     pi.mutability = None;
//                     pi.ident = Ident::new("_", Span::call_site());
//                 }
//             }
//         }
//     }
// }
//
// fn assign_impl(
//     default_impl: &ItemImpl,
//     non_default_impl: &ItemImpl,
// ) -> Option<(Assignment<'_>, HashMap<&Ident, ImplItemFn>)> {
//     let _ = default_impl.unsafety.zip(non_default_impl.unsafety)?;
//     let ((bang0, path0, _), (bang1, path1, _)) =
//         default_impl.trait_.zip(non_default_impl.trait_.as_ref())?;
//     let _ = bang0.zip(bang1.as_ref())?;
//     let mut generics_left = normalize_generics(default_impl.generics.clone());
//     let generics_right = normalize_generics(non_default_impl.generics.clone());
//     let generic_params = generics_left
//         .params
//         .iter()
//         .filter_map(|item| {
//             if let GenericParam::Type(tp) = item {
//                 Some(tp)
//             } else {
//                 None
//             }
//         })
//         .collect();
//     let mut assignment = assign_path(&generic_params, &path0, &path1)?.product(assign_type(
//         &generic_params,
//         &path0.self_ty,
//         &path1.self_ty,
//     )?);
//     use syn::visit_mut::VisitMut;
//     struct Visitor<'a>(HashMap<&'a Ident, &'a Type>);
//     impl<'a> VisitMut for Visitor<'a> {
//         fn visit_type_mut(&mut self, i: &mut Type) {
//             if let Type::Path(tp) = i {
//                 if let Some(id) = tp.path.get_ident() {
//                     if let Some(replaced) = self.0.get(id) {
//                         *i = replaced.clone();
//                         return;
//                     }
//                 }
//             }
//             syn::visit_mut::visit_type_mut(self, i)
//         }
//     }
//
//     let mut visitor = Visitor(assignment.0);
//     visitor.visit_generics_mut(&mut generics_left);
//     (&generics_left == &generics_right).then_some(())?;
//
//     let mut default_methods_left: HashMap<_, _> = default_impl
//         .items
//         .iter()
//         .filter_map(|item| match item {
//             ImplItem::Method(itm) if itm.defaultness.is_some() => Some((&itm.sig.ident, itm)),
//             ImplItem::Const(ic) if ic.defaultness.is_some() => {
//                 abort!(ic.span(), "defaultness not allowed in const")
//             }
//             ImplItem::Type(it) if it.defaultness.is_some() => {
//                 abort!(it.span(), "defaultness not allowed in type")
//             }
//             _ => None,
//         })
//         .collect();
//
//     Some((
//         assignment,
//         non_default_impl
//             .items
//             .iter()
//             .map(|item| {
//                 match item {
//                     ImplItem::Method(meth_right) => {
//                         if let Some(meth_left) = default_methods_left.get(&im.sig.ident) {
//                             let mut meth_left_replaced = meth_left.clone();
//                             let mut meth_right_replaced = meth_right.clone();
//                             visitor.visit_impl_item_method_mut(&mut meth_left_replaced);
//                             let returning_meth_right = meth_right_replaced.clone();
//                             normalize_sig(&mut meth_left_replaced.sig);
//                             normalize_sig(&mut meth_right_replaced.sig);
//                             meth_left_replaced.block.stmts = Vec::new();
//                             meth_right_replaced.block.stmts = Vec::new();
//                             if &meth_left_replaced != &meth_right_replaced {
//                                 abort!(meth_right.span(), "Has incorrect signature");
//                             }
//                             return (&im.sig.ident, returning_meth_right);
//                         }
//                     }
//                     _ => (),
//                 }
//                 abort!(item.span(), "Bad specialization");
//             })
//             .collect(),
//     ))
// }
//
// fn emit_method(
//     default_method: &ImplItemMethod,
//     specialized_methods: &[(&ImplItemMethod, &HashMap<&'a Ident, &'a Type>)],
// ) -> TokenStream {
//     let (impl_generics, ty_generics, where_clause) = default_method.sig.generics.split_for_impl();
//     let mut default_block = default_method.block.clone();
//     quote! {
//         #(for attr in &default_method.attrs) {#attr}
//         #{&default_method.vis}
//         #{&default_method.sig.constness}
//         #{&default_method.sig.asyncness}
//         #{&default_method.sig.unsafety}
//         #{&default_method.sig.abi}
//         #{&default_method.sig.fn_token}
//         #{&default_method.sig.ident}
//         #impl_generics
//         ( #{&default_method.sig.inputs} #{&default_method.sig.variadic} )
//         #{&default_method.sig.output}
//         {
//             fn _identify_type<T>() {}
//
//
//         }
//     }
// }
//
// fn emit_impl<'a>(
//     default_impl: &'a ItemImpl,
//     specialized_impls: &[(&'a ItemImpl, HashMap<&'a Ident, &'a Type>)],
// ) -> TokenStream {
//     // TODO: rename generics in each
//     let (impl_generics, ty_generics, where_clause) = default_impl.generics.split_for_impl();
//     let mut content = quote!();
//     for item in &default_impl.items {
//         match item {
//             ImplItem::Method(meth) => {
//                 let mut specialized_methods = Vec::new();
//                 for (specialized_impl, map) in specialized_impls {
//                     for specialized_item in &specialized_impl.items {
//                         if let ImplItem::Method(specialized_method) = specialized_item {
//                             if &specialized_method.sig.ident == &meth.sig.ident {
//                                 specialized_methods.push((specialized_method, map));
//                             }
//                         }
//                     }
//                 }
//                 content.extend(emit_method(meth, &specialized_methods));
//             }
//             _ => content.extend(quote! {#item}),
//         }
//     }
//     quote! {
//         #(for attr in &default_impl.attrs)(#attr)
//         #{&default_impl.unsafety}
//         #{&default_impl.impl_token}
//         #impl_generics
//         #{&default_impl.trait_}
//         #{&default_impl.self_ty}
//         #where_clause
//         { #content }
//
//     }
// }

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
    let s = env.substitute(&d_ws, &s_ws).0;
    // Filter substitutions, which has parameters in replacement
    s.into_iter()
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

fn specialize_trait(
    trait_: Path,
    default_impls: &HashSet<&mut ItemImpl>,
    special_impls: &HashSet<&mut ItemImpl>,
) {
    let mut default_map: HashMap<_, _> = default_impls.iter().map(|d| (&**d, Vec::new())).collect();
    let mut orphan_impls = Vec::new();
    for s in special_impls.iter() {
        if let Some((d, a, _)) = default_impls
            .iter()
            .map(|d| {
                substitute_impl(d, s)
                    .into_iter()
                    .map(move |(sub, n)| (d, sub, n))
            })
            .flatten()
            .min_by_key(|(_, _, n)| *n)
        {
            default_map
                .entry(d)
                .or_insert_with(|| unreachable!())
                .push((s, a));
        } else {
            orphan_impls.push(s);
        }
    }
    todo!()
}

fn specialization_mod(module: ItemMod) -> TokenStream {
    let (brace, mut content) = if let Some(inner) = module.content {
        inner
    } else {
        abort!(module.span(), "Require mod content")
    };
    let mut specialize_map: HashMap<Path, (HashSet<&mut ItemImpl>, HashSet<&mut ItemImpl>)> =
        HashMap::new();

    for item in content.iter_mut() {
        if let Item::Impl(item_impl) = item {
            if let Some((_, path, _)) = item_impl.trait_.clone() {
                if let Some(defaultness) = check_defaultness(item_impl) {
                    let (defaults, specials) =
                        specialize_map.entry(path).or_insert(Default::default());
                    if defaultness {
                        defaults.insert(item_impl);
                    } else {
                        specials.insert(item_impl);
                    }
                }
            }
        }
    }
    for (trait_, (d, s)) in specialize_map.iter() {
        specialize_trait(trait_.clone(), d, s);
    }
    // let (mut default_impls, specialized_impls): (Vec<_>, Vec<_>) = content.iter().enumerate().fold(
    //     Default::default(),
    //     |(mut default_impl_ids, mut specialized_impl_ids), (id, item)| {
    //         match item {
    //             Item::Impl(item_impl) if item_impl.defaultness.is_none() => {
    //                 // This crate does not support impl level defaultness.
    //                 let unsupported_defaultness = item_impl.items.iter().any(|item| match item {
    //                     ImplItem::Const(c) => c.defaultness.is_some(),
    //                     ImplItem::Type(t) => t.defaultness.is_some(),
    //                     _ => false,
    //                 });
    //                 let supported_defaultness = item_impl.items.iter().any(|item| match item {
    //                     ImplItem::Fn(f) => f.defaultness.is_some(),
    //                     _ => false,
    //                 });
    //                 match (supported_defaultness, unsupported_defaultness) {
    //                     (true, false) => default_impls.push((id, item_impl)),
    //                     (false, false) => specialized_impls.push((id, item_impl)),
    //                     _ => (),
    //                 }
    //             }
    //             _ => (),
    //         }
    //         (default_impls, specialized_impls)
    //     },
    // );
    // let mut specialize_map: HashMap<usize, Vec<(&ImplItem, HashMap<&Ident, &Type>)>> =
    //     HashMap::new();
    // let mut used_specialized_impl: HashSet<usize> = HashSet::new();

    // for (default_impl_id, default_impl) in &default_impls {
    //     for (specialized_impl_id, specialized_impl) in &specialized_impls {
    //         if let Some((assignment, map)) = assign_impl(default_impl, specialized_impl) {
    //             used_specialized_impl.push(specialized_impl_id);
    //             specialize_map
    //                 .entry(default_impl_id)
    //                 .or_insert(Vec::new())
    //                 .push((specialized_impl, map.0));
    //         }
    //     }
    // }

    // for (item, counter) in non_default_impl.iter().zip(counters) {
    //     if counter == &0 {
    //         out.extend(quote! {#item});
    //     }
    // }

    // let mut generated_content = quote!();

    // for (id, item) in content.into_iter().enumerate() {
    //     if let Item::Impl(impl_item) = item {
    //         if let Some(v) = specialize_map.get(id) {
    //             if v.len() > 0 {
    //                 generated_content.extend(emit_impl(&impl_item, &v));
    //                 continue;
    //             }
    //         }
    //     }
    //     generated_content.extend(quote! {#item});
    // }

    quote! {
        #(for attr in &module.attrs) { #attr }
        #{&module.vis}
        #{&module.mod_token}
        #{&module.ident}
        {}
    }
}

#[proc_macro_error]
#[proc_macro_attribute]
pub fn specialization(_attr: TokenStream1, input: TokenStream1) -> TokenStream1 {
    let module = parse_macro_input!(input);
    specialization_mod(module).into()
}
