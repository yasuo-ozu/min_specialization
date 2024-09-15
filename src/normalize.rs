use syn::punctuated::Punctuated;
use syn::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum WherePredicateBinding {
    Lifetime(PredicateLifetime),
    Type(PredicateType),
    Eq {
        lhs_ty: Type,
        eq_token: Token![=],
        rhs_ty: Type,
    },
}

pub fn normalize_where_predicate(pred: WherePredicate) -> Vec<WherePredicateBinding> {
    let mut ret = Vec::new();
    match pred {
        WherePredicate::Type(pt) => {
            for mut bound in pt.bounds.into_iter() {
                let additives = if let TypeParamBound::Trait(tb) = &mut bound {
                    remove_path_predicates(&mut tb.path)
                } else {
                    Vec::new()
                };
                for (bound_trait, bindings, constraints) in additives.into_iter() {
                    for AssocType {
                        ident,
                        ty,
                        eq_token,
                        ..
                    } in bindings.into_iter()
                    {
                        let mut path = bound_trait.clone();
                        path.segments.push(ident.into());
                        let lhs_ty = Type::Path(TypePath {
                            qself: Some(QSelf {
                                lt_token: Default::default(),
                                ty: Box::new(pt.bounded_ty.clone()),
                                position: bound_trait.segments.len() - 1,
                                as_token: Default::default(),
                                gt_token: Default::default(),
                            }),
                            path,
                        });
                        ret.push(WherePredicateBinding::Eq {
                            lhs_ty,
                            eq_token,
                            rhs_ty: ty,
                        });
                    }
                    for Constraint {
                        ident,
                        bounds,
                        colon_token,
                        ..
                    } in constraints.into_iter()
                    {
                        for bound in bounds.into_iter() {
                            let mut path = bound_trait.clone();
                            path.segments.push(ident.clone().into());
                            let bounded_ty = Type::Path(TypePath {
                                qself: Some(QSelf {
                                    lt_token: Default::default(),
                                    ty: Box::new(pt.bounded_ty.clone()),
                                    position: bound_trait.segments.len() - 1,
                                    as_token: Default::default(),
                                    gt_token: Default::default(),
                                }),
                                path,
                            });
                            ret.push(WherePredicateBinding::Type(PredicateType {
                                lifetimes: Default::default(),
                                bounded_ty,
                                colon_token: colon_token.clone(),
                                bounds: Some(bound).into_iter().collect(),
                            }));
                        }
                    }
                }
                ret.push(WherePredicateBinding::Type(PredicateType {
                    lifetimes: pt.lifetimes.clone(),
                    bounded_ty: pt.bounded_ty.clone(),
                    colon_token: pt.colon_token.clone(),
                    bounds: Some(bound.clone()).into_iter().collect(),
                }));
            }
        }
        WherePredicate::Lifetime(lt) => {
            for bound in lt.bounds.iter() {
                ret.push(WherePredicateBinding::Lifetime(PredicateLifetime {
                    lifetime: lt.lifetime.clone(),
                    colon_token: lt.colon_token.clone(),
                    bounds: Some(bound.clone()).into_iter().collect(),
                }));
            }
        } // WherePredicate::Eq(pe) => {
        //     ret.push(WherePredicate::Eq(PredicateEq {
        //         lhs_ty: pe.lhs_ty,
        //         eq_token: pe.eq_token,
        //         rhs_ty: pe.rhs_ty,
        //     }));
        // }
        _ => panic!(),
    }
    ret
}

pub fn normalize_generic_param(param: GenericParam) -> (GenericParam, Vec<WherePredicateBinding>) {
    match param {
        GenericParam::Type(mut pt) => {
            let mut preds = Vec::new();
            if let Some(colon_token) = pt.colon_token {
                for mut bound in pt.bounds.into_iter() {
                    if let TypeParamBound::Trait(tb) = &mut bound {
                        let ret = remove_path_predicates(&mut tb.path);
                        assert!(ret.is_empty());
                    }
                    preds.push(WherePredicateBinding::Type(PredicateType {
                        lifetimes: None,
                        bounded_ty: Type::Path(TypePath {
                            path: pt.ident.clone().into(),
                            qself: None,
                        }),
                        colon_token: colon_token.clone(),
                        bounds: Some(bound).into_iter().collect(),
                    }));
                }
            }
            pt.colon_token = None;
            pt.bounds = Punctuated::new();
            (GenericParam::Type(pt), preds)
        }
        GenericParam::Lifetime(mut pl) => {
            let mut preds = Vec::new();
            if let Some(colon_token) = pl.colon_token {
                for bound in pl.bounds.into_iter() {
                    preds.push(WherePredicateBinding::Lifetime(PredicateLifetime {
                        lifetime: pl.lifetime.clone(),
                        colon_token: colon_token.clone(),
                        bounds: Some(bound).into_iter().collect(),
                    }));
                }
            }
            pl.colon_token = None;
            pl.bounds = Punctuated::new();
            (GenericParam::Lifetime(pl), preds)
        }
        o => (o, Vec::new()),
    }
}

fn remove_path_predicates(path: &mut Path) -> Vec<(Path, Vec<AssocType>, Vec<Constraint>)> {
    trait Take: Sized {
        fn take_owned(&mut self, closure: impl FnOnce(Self) -> Self) -> &mut Self;
    }

    impl<T> Take for T {
        fn take_owned(&mut self, closure: impl FnOnce(Self) -> Self) -> &mut Self {
            use core::ptr;
            use std::panic;

            unsafe {
                let oldval = ptr::read(self);
                let newval = panic::catch_unwind(panic::AssertUnwindSafe(|| closure(oldval)))
                    .unwrap_or_else(|_| ::std::process::abort());
                ptr::write(self, newval);
            }
            self
        }
    }
    struct PathVisitor;
    use syn::visit_mut::VisitMut;

    impl VisitMut for PathVisitor {
        fn visit_path_mut(&mut self, i: &mut Path) {
            let ret = remove_path_predicates(i);
            assert!(ret.is_empty());
            syn::visit_mut::visit_path_mut(self, i);
        }
    }
    let mut ret = Vec::new();
    let mut current_path = Path {
        leading_colon: path.leading_colon.clone(),
        segments: Punctuated::new(),
    };
    for seg in path.segments.iter_mut() {
        let mut bindings = Vec::new();
        let mut constraints = Vec::new();
        match &mut seg.arguments {
            PathArguments::AngleBracketed(args) => {
                args.args.take_owned(|args| {
                    let mut new_args = Punctuated::new();
                    for mut arg in args.into_iter() {
                        PathVisitor.visit_generic_argument_mut(&mut arg);
                        match arg {
                            GenericArgument::AssocType(binding) => bindings.push(binding),
                            GenericArgument::Constraint(constraint) => constraints.push(constraint),
                            o => new_args.push(o),
                        }
                    }
                    new_args
                });
            }
            o => PathVisitor.visit_path_arguments_mut(o),
        }
        current_path.segments.push(seg.clone());
        if bindings.len() > 0 || constraints.len() > 0 {
            ret.push((current_path.clone(), bindings, constraints));
        }
    }
    ret
}
