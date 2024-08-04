use crate::normalize::WherePredicateBinding;
use std::collections::{HashMap, HashSet};
use syn::*;

// For now, the right hand side should not contais any unbounded type parameter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Substitution(pub Vec<HashMap<Ident, Type>>);

impl Substitution {
    pub fn empty() -> Self {
        Self(Vec::new())
    }

    pub fn some() -> Self {
        Self(vec![HashMap::new()])
    }

    pub fn new(param: Ident, ty: Type) -> Self {
        Self(vec![Some((param, ty)).into_iter().collect()])
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn into_option(self) -> Option<Self> {
        if self.is_empty() {
            None
        } else {
            Some(self)
        }
    }

    fn merge(
        mut lhs: HashMap<Ident, Type>,
        rhs: HashMap<Ident, Type>,
    ) -> Option<HashMap<Ident, Type>> {
        for (param, ty) in rhs.into_iter() {
            if let Some(l_ty) = lhs.get(&param) {
                if l_ty != &ty {
                    return None;
                }
            } else {
                lhs.insert(param, ty);
            }
        }
        Some(lhs)
    }
}

impl core::ops::Add for Substitution {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        for record in rhs.0.into_iter() {
            if !self.0.contains(&record) {
                self.0.push(record);
            }
        }
        self
    }
}

impl core::ops::AddAssign for Substitution {
    fn add_assign(&mut self, rhs: Self) {
        core::mem::swap(self, &mut (self.clone() + rhs))
    }
}

impl core::ops::Mul for Substitution {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut ret = Vec::new();
        for l in self.0.into_iter() {
            for r in rhs.0.iter() {
                if let Some(item) = Self::merge(l.clone(), r.clone()) {
                    ret.push(item);
                }
            }
        }
        Self(ret)
    }
}

impl core::ops::MulAssign for Substitution {
    fn mul_assign(&mut self, rhs: Self) {
        core::mem::swap(self, &mut (self.clone() * rhs))
    }
}

impl core::iter::Product for Substitution {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        let mut ret = Substitution::some();
        for item in iter {
            ret *= item;
        }
        ret
    }
}

pub trait Substitute<T: ?Sized> {
    fn substitute(&self, general: &T, special: &T) -> Substitution;
}

pub struct SubstituteEnvironment {
    pub general_params: HashSet<Ident>,
}

impl Substitute<GenericArgument> for SubstituteEnvironment {
    fn substitute(&self, general: &GenericArgument, special: &GenericArgument) -> Substitution {
        match (general, special) {
            (GenericArgument::Type(g_ty), GenericArgument::Type(s_ty)) => {
                self.substitute(g_ty, s_ty)
            }
            (GenericArgument::AssocType(g_bind), GenericArgument::AssocType(s_bind)) => {
                if &g_bind.ident != &s_bind.ident {
                    return Substitution::empty();
                }
                self.substitute(&g_bind.ty, &s_bind.ty)
            }
            (GenericArgument::Constraint(g_ct), GenericArgument::Constraint(s_ct)) => {
                if &g_ct.ident != &s_ct.ident {
                    return Substitution::empty();
                }
                self.substitute(
                    g_ct.bounds.iter().cloned().collect::<Vec<_>>().as_slice(),
                    s_ct.bounds.iter().cloned().collect::<Vec<_>>().as_slice(),
                )
            }
            (g, s) => {
                if g == s {
                    Substitution::some()
                } else {
                    Substitution::empty()
                }
            }
        }
    }
}

impl Substitute<Path> for SubstituteEnvironment {
    fn substitute(&self, general: &Path, special: &Path) -> Substitution {
        if let Some(g_ident) = general.get_ident() {
            if self.general_params.contains(g_ident) {
                return Substitution::new(
                    g_ident.clone(),
                    Type::Path(TypePath {
                        qself: None,
                        path: special.clone(),
                    }),
                );
            }
        }
        if &general.leading_colon != &special.leading_colon
            || general.segments.len() != special.segments.len()
        {
            return Substitution::empty();
        }

        let mut subst = Substitution::some();
        for (i, (g_seg, s_seg)) in general.segments.iter().zip(&special.segments).enumerate() {
            if i == 0
                && &g_seg.arguments == &PathArguments::None
                && self.general_params.contains(&g_seg.ident)
            {
                subst *= Substitution::new(
                    g_seg.ident.clone(),
                    Type::Path(TypePath {
                        qself: None,
                        path: Path {
                            leading_colon: None,
                            segments: Some(s_seg.clone()).into_iter().collect(),
                        },
                    }),
                );
            } else {
                if &g_seg.ident != &s_seg.ident {
                    return Substitution::empty();
                }
                match (&g_seg.arguments, &s_seg.arguments) {
                    (PathArguments::None, PathArguments::None) => (),
                    (
                        PathArguments::AngleBracketed(g_args),
                        PathArguments::AngleBracketed(s_args),
                    ) => {
                        // TODO: consider order
                        if g_args.args.len() != s_args.args.len() {
                            return Substitution::empty();
                        }
                        for (g_arg, s_arg) in g_args.args.iter().zip(&s_args.args) {
                            subst *= self.substitute(g_arg, s_arg);
                        }
                    }
                    (
                        PathArguments::Parenthesized(g_args),
                        PathArguments::Parenthesized(s_args),
                    ) => {
                        let mut g_tys: Vec<_> = g_args.inputs.iter().cloned().collect();
                        let mut s_tys: Vec<_> = s_args.inputs.iter().cloned().collect();
                        match (&g_args.output, &s_args.output) {
                            (ReturnType::Default, ReturnType::Default) => (),
                            (ReturnType::Type(_, g_ty), ReturnType::Type(_, s_ty)) => {
                                g_tys.push(g_ty.as_ref().clone());
                                s_tys.push(s_ty.as_ref().clone());
                            }
                            _ => {
                                return Substitution::empty();
                            }
                        }

                        subst *= self.substitute(g_tys.as_slice(), s_tys.as_slice());
                    }
                    _ => {
                        return Substitution::empty();
                    }
                }
            }
        }
        subst
    }
}

impl<T> Substitute<[T]> for SubstituteEnvironment
where
    Self: Substitute<T>,
{
    fn substitute(&self, general: &[T], special: &[T]) -> Substitution {
        if general.len() != special.len() {
            return Substitution::empty();
        }
        general
            .iter()
            .zip(special)
            .map(|(g, s)| self.substitute(g, s))
            .product()
    }
}

impl Substitute<TraitBound> for SubstituteEnvironment {
    fn substitute(&self, general: &TraitBound, special: &TraitBound) -> Substitution {
        // TODO: consider lifetime order (assignment)
        if &general.paren_token != &special.paren_token
            || &general.modifier != &special.modifier
            || &general.lifetimes == &special.lifetimes
        {
            return Substitution::empty();
        }
        self.substitute(&general.path, &special.path)
    }
}

fn substitute_by_set<T>(
    env: &SubstituteEnvironment,
    general: &HashSet<T>,
    special: &HashSet<T>,
) -> Substitution
where
    T: PartialEq + Eq + core::hash::Hash,
    SubstituteEnvironment: Substitute<T>,
{
    assert!(general.len() > special.len());

    let mut subst = Substitution::some();
    for g in general.iter() {
        let mut next_subst = Substitution::empty();
        for s in special.iter() {
            next_subst += subst.clone() * env.substitute(g, s);
        }
        let _ = core::mem::replace(&mut subst, next_subst);
    }
    subst
}

impl<T: Eq + core::hash::Hash> Substitute<HashSet<T>> for SubstituteEnvironment
where
    Self: Substitute<T>,
{
    fn substitute(&self, general: &HashSet<T>, special: &HashSet<T>) -> Substitution {
        substitute_by_set(self, general, special)
    }
}

impl Substitute<Lifetime> for SubstituteEnvironment {
    fn substitute(&self, general: &Lifetime, special: &Lifetime) -> Substitution {
        if general == special {
            Substitution::some()
        } else {
            Substitution::empty()
        }
    }
}

impl Substitute<TypeParamBound> for SubstituteEnvironment {
    fn substitute(&self, general: &TypeParamBound, special: &TypeParamBound) -> Substitution {
        match (general, special) {
            (TypeParamBound::Trait(g_tb), TypeParamBound::Trait(s_tb)) => {
                self.substitute(g_tb, s_tb)
            }
            (TypeParamBound::Lifetime(g_l), TypeParamBound::Lifetime(s_l)) => {
                self.substitute(g_l, s_l)
            }
            _ => Substitution::empty(),
        }
    }
}

impl Substitute<QSelf> for SubstituteEnvironment {
    fn substitute(&self, general: &QSelf, special: &QSelf) -> Substitution {
        if (general.position, &general.as_token) != (special.position, &special.as_token) {
            return Substitution::empty();
        }
        self.substitute(general.ty.as_ref(), special.ty.as_ref())
    }
}

impl<T> Substitute<Option<T>> for SubstituteEnvironment
where
    Self: Substitute<T>,
{
    fn substitute(&self, general: &Option<T>, special: &Option<T>) -> Substitution {
        match (general, special) {
            (None, None) => Substitution::some(),
            (Some(g), Some(s)) => self.substitute(g, s),
            _ => Substitution::empty(),
        }
    }
}

impl Substitute<Type> for SubstituteEnvironment {
    fn substitute(&self, general: &Type, special: &Type) -> Substitution {
        match (general, special) {
            (
                Type::Array(TypeArray {
                    elem: g_elem,
                    len: g_len,
                    ..
                }),
                Type::Array(TypeArray {
                    elem: s_elem,
                    len: s_len,
                    ..
                }),
            ) => {
                if g_len != s_len {
                    return Substitution::empty();
                }
                self.substitute(g_elem.as_ref(), s_elem.as_ref())
            }
            (Type::BareFn(g_fn), Type::BareFn(s_fn)) => {
                if (&g_fn.lifetimes, &g_fn.unsafety, &g_fn.abi, &g_fn.variadic)
                    != (&s_fn.lifetimes, &s_fn.unsafety, &s_fn.abi, &s_fn.variadic)
                    || g_fn.inputs.len() != s_fn.inputs.len()
                {
                    return Substitution::empty();
                }
                let mut subst = g_fn
                    .inputs
                    .iter()
                    .zip(&s_fn.inputs)
                    .map(|(g_arg, s_arg)| {
                        if &g_arg.attrs != &s_arg.attrs {
                            Substitution::empty()
                        } else {
                            self.substitute(&g_arg.ty, &s_arg.ty)
                        }
                    })
                    .product();

                match (&g_fn.output, &s_fn.output) {
                    (ReturnType::Default, ReturnType::Default) => (),
                    (ReturnType::Type(_, g_ty), ReturnType::Type(_, s_ty)) => {
                        subst *= self.substitute(g_ty.as_ref(), s_ty.as_ref());
                    }
                    _ => {
                        return Substitution::empty();
                    }
                }
                subst
            }
            (Type::Group(g_gr), Type::Group(s_gr)) => {
                self.substitute(g_gr.elem.as_ref(), s_gr.elem.as_ref())
            }
            (Type::ImplTrait(g_it), Type::ImplTrait(s_it)) => self.substitute(
                g_it.bounds.iter().cloned().collect::<Vec<_>>().as_slice(),
                s_it.bounds.iter().cloned().collect::<Vec<_>>().as_slice(),
            ),
            (Type::Paren(g_p), Type::Paren(s_p)) => {
                self.substitute(g_p.elem.as_ref(), s_p.elem.as_ref())
            }
            (Type::Path(g_path), Type::Path(s_path)) => {
                self.substitute(&g_path.qself, &s_path.qself)
                    * self.substitute(&g_path.path, &s_path.path)
            }
            (Type::Ptr(g_ptr), Type::Ptr(s_ptr)) => {
                if &g_ptr.mutability != &s_ptr.mutability {
                    Substitution::empty()
                } else {
                    self.substitute(g_ptr.elem.as_ref(), s_ptr.elem.as_ref())
                }
            }
            (Type::Reference(g_ref), Type::Reference(s_ref)) => {
                if (&g_ref.lifetime, &g_ref.mutability) != (&s_ref.lifetime, &s_ref.mutability) {
                    Substitution::empty()
                } else {
                    self.substitute(g_ref.elem.as_ref(), s_ref.elem.as_ref())
                }
            }
            (Type::Slice(g_slice), Type::Slice(s_slice)) => {
                self.substitute(g_slice.elem.as_ref(), s_slice.elem.as_ref())
            }
            (Type::TraitObject(g_to), Type::TraitObject(s_to)) => {
                // TODO: consider freedom of the order
                self.substitute(
                    g_to.bounds.iter().cloned().collect::<Vec<_>>().as_slice(),
                    s_to.bounds.iter().cloned().collect::<Vec<_>>().as_slice(),
                )
            }
            (Type::Tuple(g_tup), Type::Tuple(s_tup)) => self.substitute(
                g_tup.elems.iter().cloned().collect::<Vec<_>>().as_slice(),
                s_tup.elems.iter().cloned().collect::<Vec<_>>().as_slice(),
            ),
            (g, s) => {
                if &g == &s {
                    Substitution::some()
                } else {
                    Substitution::empty()
                }
            }
        }
    }
}

impl Substitute<WherePredicateBinding> for SubstituteEnvironment {
    fn substitute(
        &self,
        general: &WherePredicateBinding,
        special: &WherePredicateBinding,
    ) -> Substitution {
        match (general, special) {
            (
                WherePredicateBinding::Type(PredicateType {
                    lifetimes: g_lifetimes,
                    bounded_ty: g_bounded_ty,
                    bounds: g_bounds,
                    ..
                }),
                WherePredicateBinding::Type(PredicateType {
                    lifetimes: s_lifetimes,
                    bounded_ty: s_bounded_ty,
                    bounds: s_bounds,
                    ..
                }),
            ) => {
                if &g_lifetimes != &s_lifetimes {
                    return Substitution::empty();
                }
                self.substitute(g_bounded_ty, s_bounded_ty)
                    * self.substitute(
                        &g_bounds.into_iter().cloned().collect::<HashSet<_>>(),
                        &s_bounds.into_iter().cloned().collect::<HashSet<_>>(),
                    )
            }
            (
                WherePredicateBinding::Eq {
                    lhs_ty: g_lhs_ty,
                    rhs_ty: g_rhs_ty,
                    ..
                },
                WherePredicateBinding::Eq {
                    lhs_ty: s_lhs_ty,
                    rhs_ty: s_rhs_ty,
                    ..
                },
            ) => self.substitute(g_lhs_ty, s_lhs_ty) * self.substitute(g_rhs_ty, s_rhs_ty),
            (g, s) => {
                if g == s {
                    Substitution::some()
                } else {
                    Substitution::empty()
                }
            }
        }
    }
}

#[test]
fn test_unit() {
    use proc_macro2::Span;

    // Ident "A*" are unbounded type params in general side
    let env = SubstituteEnvironment {
        general_params: vec![Ident::new("A0", Span::call_site())]
            .into_iter()
            .collect(),
    };

    macro_rules! unittest {
        ($env:ident [$typ:ty] { $($t0:tt)* } { $($t1:tt)* } None) => {
            assert_eq!(
                <_ as Substitute<$typ>>::substitute(
                    &$env,
                    &parse_quote!($($t0)*),
                    &parse_quote!($($t1)*),
                ),
                Substitution::empty()
            );
        };
        ($env:ident [$typ:ty] { $($t0:tt)* } { $($t1:tt)* } Some [ $($name:expr => { $($t2:tt)* }),* $(,)? ]) => {
            assert_eq!(
                <_ as Substitute<$typ>>::substitute(
                    &$env,
                    &parse_quote!($($t0)*),
                    &parse_quote!($($t1)*),
                ),
                Substitution(
                    vec![
                        vec![$((Ident::new($name, Span::call_site()), parse_quote!($($t2)*)))*]
                        .into_iter()
                        .collect()
                    ]
                )
            );
        };
    }

    unittest! { env [Type] { [A0; 32] } { [A0; 32] } Some ["A0" => {A0}] }
    unittest! { env [Type] { [B0; 32] } { [B0; 32] } Some [] }
    unittest! { env [Type] { [A0; 32] } { [B0; 32] } Some ["A0" => {B0}] }
    unittest! { env [Type] { [A0; 32] } { [B0; 48] } None }
    unittest! { env [Type] {
        *mut ([A0; 1], (Option<A0>, &mut [(A0, B0)]))
    } {
        *mut ([Vec<B0>; 1], (Option<Vec<B0>>, &mut [(Vec<B0>, B0)]))
    } Some [
        "A0" => { Vec<B0> }
    ]}
    unittest! { env [Type] {
        *mut ([A0; 1], (Option<A0>, &mut [(A0, B0)]))
    } {
        *mut ([Vec<B0>; 1], (Option<Vec<B0>>, &mut [(BTreeSet<B0>, B0)]))
    } None }
    unittest! { env [Type] {
        (<A0 as std::iter::Iterator<Item = (Vec<A0>,)>>::Item)
    } {
        (<B0 as std::iter::Iterator<Item = (Vec<B0>,)>>::Item)
    } Some [
        "A0" => { B0 }
    ] }
    unittest! { env [Type] {
        (<A0 as std::iter::Iterator<Item = (Vec<A0>,)>>::Item)
    } {
        (<B1 as std::iter::Iterator<Item = (Vec<B0>,)>>::Item)
    } None }
}
