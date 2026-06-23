//! AUDIT — finding T1 (CRITICAL, "testing-gap"): the crate's existing integration
//! tests (`tests/large.rs`, `tests/large2.rs`, `tests/no_self_arg.rs`) contain a
//! `fn main()` and `assert!`s but **zero `#[test]` functions**, so under
//! `cargo test` every one of those files reports "running 0 tests" — the asserts
//! and `println!`s never execute. The suite therefore only ever checked that the
//! macro *compiles*, never that its runtime dispatch is *correct*.
//!
//! This file turns those examples into real `#[test]`s that assert the actual
//! specialized vs. default dispatch, and exercises argument patterns that used to
//! be mishandled. Dispatch is now sound in debug, `--release`, and Miri alike (see
//! `tests/audit_soundness.rs`).

use min_specialization::specialization;

#[specialization]
mod data_size {
    pub trait DataSize {
        fn size(&self) -> usize;
    }
    impl<T> DataSize for T {
        default fn size(&self) -> usize {
            std::mem::size_of::<T>()
        }
    }
    impl DataSize for &str {
        fn size(&self) -> usize {
            self.len()
        }
    }
    impl DataSize for i32 {
        fn size(&self) -> usize {
            4
        }
    }
    impl DataSize for f64 {
        fn size(&self) -> usize {
            8
        }
    }
}

#[test]
fn data_size_dispatches_to_specializations() {
    use data_size::DataSize;
    // specialized impls
    assert_eq!(42i32.size(), 4);
    assert_eq!(3.14f64.size(), 8);
    assert_eq!("Hello, Rust!".size(), 12); // &str specialization returns .len()
    // blanket default (size_of)
    assert_eq!(7u8.size(), 1);
    assert_eq!(0u16.size(), 2);
    assert_eq!((0u32, 0u32).size(), 8);
}

#[specialization]
mod serialize {
    pub trait Serialize {
        fn serialize(&self) -> String;
    }
    impl<T: core::fmt::Debug> Serialize for T {
        default fn serialize(&self) -> String {
            format!("Generic serialization: {:?}", self)
        }
    }
    impl Serialize for i32
    where
        Self: core::fmt::Debug,
    {
        fn serialize(&self) -> String {
            format!("Integer serialization: {}", self)
        }
    }
    impl Serialize for &str
    where
        Self: core::fmt::Debug,
    {
        fn serialize(&self) -> String {
            format!("String serialization: '{}'", self)
        }
    }
}

#[test]
fn serialize_dispatches_to_specializations() {
    use serialize::Serialize;
    assert_eq!(42i32.serialize(), "Integer serialization: 42");
    assert_eq!(
        "Hello, world!".serialize(),
        "String serialization: 'Hello, world!'"
    );
    // no specialization for () -> blanket default
    assert_eq!(().serialize(), "Generic serialization: ()");
}

#[specialization]
mod assoc_fn {
    #[allow(unused)]
    pub trait Trait<U> {
        type Ty;
        fn number(_: U) -> Self::Ty;
    }
    impl<T, U> Trait<U> for T {
        type Ty = usize;
        default fn number(_: U) -> Self::Ty {
            0
        }
    }
    impl<U> Trait<U> for () {
        fn number(_: U) -> Self::Ty {
            1
        }
    }
}

#[test]
fn associated_fn_with_no_self_dispatches() {
    use assoc_fn::Trait;
    assert_eq!(<() as Trait<u8>>::number(0u8), 1); // specialized
    assert_eq!(<i32 as Trait<u8>>::number(0u8), 0); // default
}

#[specialization]
mod by_value_self {
    #[allow(unused)]
    pub trait MyTrait {
        fn f(a: Self) -> Self;
    }
    impl<T> MyTrait for T {
        default fn f(a: T) -> T {
            a
        }
    }
    impl MyTrait for () {
        fn f(_: ()) -> () {
            ()
        }
    }
}

#[test]
fn self_by_value_and_return_dispatches() {
    use by_value_self::MyTrait;
    assert_eq!(<i32 as MyTrait>::f(5), 5); // default identity
    let _: () = <() as MyTrait>::f(()); // specialized
}

#[specialization]
mod arg_patterns {
    // Non-trivial argument patterns in the *default* method: `mut`, a destructuring
    // tuple pattern, and a wildcard. The macro must forward these correctly to both
    // the default and the specialized implementation.
    pub trait Args {
        fn f(&self, x: u8, p: (u8, u8), w: u8) -> u32;
    }
    impl<T> Args for T {
        default fn f(&self, mut x: u8, (a, b): (u8, u8), _w: u8) -> u32 {
            x += 1;
            x as u32 + a as u32 + b as u32
        }
    }
    impl Args for () {
        fn f(&self, x: u8, p: (u8, u8), w: u8) -> u32 {
            1000 + x as u32 + p.0 as u32 + p.1 as u32 + w as u32
        }
    }
}

#[test]
fn nontrivial_argument_patterns_dispatch() {
    use arg_patterns::Args;
    // default: mut x -> x+1 (=11), tuple destructure 3+4, wildcard ignored => 18
    assert_eq!(5u8.f(10, (3, 4), 99), 18);
    // specialized: 1000 + 10 + 3 + 4 + 99 => 1116
    assert_eq!(().f(10, (3, 4), 99), 1116);
}

#[specialization]
mod generic_methods {
    // Methods may carry their own type/const generic parameters; they are forwarded
    // to both the default and specialized implementation.
    pub trait Tr {
        fn count<G: IntoIterator>(&self, g: G) -> usize; // generic in argument
        fn make<G: Default>(&self) -> G; // generic only in return position
        fn nth<const N: usize>(&self) -> usize; // const generic
    }
    impl<T> Tr for T {
        default fn count<G: IntoIterator>(&self, g: G) -> usize {
            g.into_iter().count()
        }
        default fn make<G: Default>(&self) -> G {
            G::default()
        }
        default fn nth<const N: usize>(&self) -> usize {
            N
        }
    }
    impl Tr for () {
        fn count<G: IntoIterator>(&self, g: G) -> usize {
            g.into_iter().count() + 1000
        }
        fn make<G: Default>(&self) -> G {
            G::default()
        }
        fn nth<const N: usize>(&self) -> usize {
            N + 1000
        }
    }
}

#[test]
fn generic_method_parameters_dispatch() {
    use generic_methods::Tr;
    // default (i32)
    assert_eq!(5i32.count(vec![1, 2, 3]), 3);
    assert_eq!(5i32.make::<u32>(), 0u32);
    assert_eq!(5i32.nth::<7>(), 7);
    // specialized (())
    assert_eq!(().count(vec![1, 2, 3]), 1003);
    assert_eq!(().nth::<7>(), 1007);
}

#[specialization]
mod lifetime_methods {
    // Methods with several generic parameters, including lifetimes. Lifetimes are
    // handled by elision (the forwarded turbofish only carries type/const params),
    // including the case of returning a borrow tied to a method lifetime.
    pub trait Tr {
        fn longest<'a>(&self, x: &'a str, y: &'a str) -> &'a str; // lifetime in args + return
        fn pair<'a, 'b, A, B>(&self, a: &'a A, b: &'b B) -> (usize, usize); // 2 lifetimes + 2 types
        fn mix<'a, G, const N: usize>(&self, g: &'a G) -> usize; // lifetime + type + const
        fn keep<'a, G: 'a + Clone>(&self, g: &'a G) -> G; // lifetime bound on a type param
    }
    impl<T> Tr for T {
        default fn longest<'a>(&self, x: &'a str, y: &'a str) -> &'a str {
            if x.len() >= y.len() {
                x
            } else {
                y
            }
        }
        default fn pair<'a, 'b, A, B>(&self, _a: &'a A, _b: &'b B) -> (usize, usize) {
            (core::mem::size_of::<A>(), core::mem::size_of::<B>())
        }
        default fn mix<'a, G, const N: usize>(&self, _g: &'a G) -> usize {
            N + core::mem::size_of::<G>()
        }
        default fn keep<'a, G: 'a + Clone>(&self, g: &'a G) -> G {
            g.clone()
        }
    }
    impl Tr for () {
        fn longest<'a>(&self, x: &'a str, _y: &'a str) -> &'a str {
            x // specialization always returns the first
        }
        fn pair<'a, 'b, A, B>(&self, _a: &'a A, _b: &'b B) -> (usize, usize) {
            (1000 + core::mem::size_of::<A>(), core::mem::size_of::<B>())
        }
        fn mix<'a, G, const N: usize>(&self, _g: &'a G) -> usize {
            1000 + N + core::mem::size_of::<G>()
        }
        fn keep<'a, G: 'a + Clone>(&self, g: &'a G) -> G {
            g.clone()
        }
    }
}

#[test]
fn lifetime_and_multiple_generic_params_dispatch() {
    use lifetime_methods::Tr;
    let (short, long) = (String::from("aa"), String::from("bbbb"));

    // default (i32)
    assert_eq!(5i32.longest(short.as_str(), long.as_str()), "bbbb");
    assert_eq!(5i32.pair(&1u8, &1u64), (1, 8));
    assert_eq!(5i32.mix::<u16, 7>(&0u16), 9); // 7 + size_of::<u16>()
    assert_eq!(5i32.keep(&99u8), 99);

    // specialized (())
    assert_eq!(().longest(short.as_str(), long.as_str()), "aa");
    assert_eq!(().pair(&1u8, &1u64), (1001, 8));
    assert_eq!(().mix::<u16, 7>(&0u16), 1009); // 1000 + 7 + 2
    assert_eq!(().keep(&99u8), 99);
}

#[specialization]
mod trait_generics {
    // A trait with multiple generic parameters of its own, used by the method.
    // The specialization keeps the trait generics and refines the blanket impl.
    pub trait Combine<A, B> {
        fn combine(&self, a: A, b: B) -> usize;
    }
    impl<T, A, B> Combine<A, B> for T {
        default fn combine(&self, _a: A, _b: B) -> usize {
            core::mem::size_of::<A>() + core::mem::size_of::<B>()
        }
    }
    impl<A, B> Combine<A, B> for () {
        fn combine(&self, _a: A, _b: B) -> usize {
            1000
        }
    }
}

#[test]
fn trait_with_multiple_generics_dispatches() {
    use trait_generics::Combine;
    assert_eq!(Combine::combine(&5i32, 1u8, 1u64), 9); // default: size_of::<u8>() + size_of::<u64>()
    assert_eq!(Combine::combine(&(), 1u8, 1u64), 1000); // specialized
}

#[specialization]
mod associated_type {
    // A trait with an associated type used in return position. Specializations
    // override the method (the associated type itself is inherited from the
    // default impl — specializing the type is rejected; see compile_fail).
    pub trait Describe {
        type Out;
        fn describe(&self) -> Self::Out;
    }
    impl<T> Describe for T {
        type Out = &'static str;
        default fn describe(&self) -> Self::Out {
            "generic"
        }
    }
    impl Describe for bool {
        fn describe(&self) -> Self::Out {
            "boolean"
        }
    }
    impl Describe for i32 {
        fn describe(&self) -> Self::Out {
            "integer"
        }
    }
}

#[test]
fn trait_with_associated_type_dispatches() {
    use associated_type::Describe;
    assert_eq!(true.describe(), "boolean"); // specialized
    assert_eq!(7i32.describe(), "integer"); // specialized
    assert_eq!(7u8.describe(), "generic"); // default; Self::Out == &'static str
}

#[specialization]
mod associated_const {
    // A trait with an associated const (with a trait-level default) that the default
    // method reads via `Self::BYTES`; specializations override the method.
    pub trait ByteSize {
        const BYTES: usize;
        fn byte_size(&self) -> usize;
    }
    impl<T> ByteSize for T {
        const BYTES: usize = core::mem::size_of::<T>();
        default fn byte_size(&self) -> usize {
            Self::BYTES
        }
    }
    impl ByteSize for &str {
        fn byte_size(&self) -> usize {
            999
        }
    }
}

#[test]
fn trait_with_associated_const_dispatches() {
    use associated_const::ByteSize;
    assert_eq!(0u64.byte_size(), 8); // default reads BYTES = size_of::<u64>()
    assert_eq!(0u32.byte_size(), 4); // default reads BYTES = size_of::<u32>()
    assert_eq!("x".byte_size(), 999); // specialized
}

#[specialization]
mod trait_lifetime_param {
    // The trait itself carries a lifetime parameter.
    pub trait Borrow<'a> {
        fn take(&self, x: &'a str) -> usize;
    }
    impl<'a, T> Borrow<'a> for T {
        default fn take(&self, x: &'a str) -> usize {
            x.len()
        }
    }
    impl<'a> Borrow<'a> for () {
        fn take(&self, x: &'a str) -> usize {
            x.len() + 1000
        }
    }
}

#[test]
fn trait_with_lifetime_parameter_dispatches() {
    use trait_lifetime_param::Borrow;
    let s = String::from("hello");
    assert_eq!(5i32.take(s.as_str()), 5); // default
    assert_eq!(().take(s.as_str()), 1005); // specialized
}

#[specialization]
mod lifetime_self_type {
    // The specialized self type carries a lifetime (`Holder<'a>`), so the generated
    // inner impl must declare it: `impl<'a> .. for Holder<'a>`.
    pub struct Holder<'a>(pub &'a str);
    pub trait Len {
        fn len2(&self) -> usize;
    }
    impl<T> Len for T {
        default fn len2(&self) -> usize {
            0
        }
    }
    impl<'a> Len for Holder<'a> {
        fn len2(&self) -> usize {
            self.0.len()
        }
    }
}

#[test]
fn specialized_self_type_with_lifetime_dispatches() {
    use lifetime_self_type::{Holder, Len};
    assert_eq!(5i32.len2(), 0); // default
    let s = String::from("borrowed");
    assert_eq!(Holder(s.as_str()).len2(), 8); // specialized; &'a str lives as long as `s`
}

#[specialization]
mod lifetime_trait_param {
    // The specialization fixes a *trait type parameter* to a lifetime-bearing type
    // (`Convert<&'a str>`); the lifetime appears only in the method signature and is
    // promoted to a method-level lifetime in the generated dispatch.
    pub trait Convert<U> {
        fn convert(&self, u: U) -> usize;
    }
    impl<U> Convert<U> for i32 {
        default fn convert(&self, _u: U) -> usize {
            0
        }
    }
    impl<'a> Convert<&'a str> for i32 {
        fn convert(&self, u: &'a str) -> usize {
            u.len()
        }
    }
}

#[test]
fn specialized_trait_param_with_lifetime_dispatches() {
    use lifetime_trait_param::Convert;
    let s = String::from("hello");
    assert_eq!(Convert::<u8>::convert(&5i32, 1u8), 0); // default (U = u8)
    assert_eq!(Convert::<&str>::convert(&5i32, s.as_str()), 5); // specialized (U = &str)
}

#[specialization]
mod non_static_assoc_type {
    // The associated type is bound to a NON-'static lifetime (`type Out = &'a str`),
    // and both impls *return a borrow* of that type. This checks that dispatch
    // preserves the non-'static lifetime through the transmute rather than laundering
    // it (Miri verifies the latter).
    pub trait Slice<'a> {
        type Out;
        fn slice(&self, x: &'a str) -> Self::Out;
    }
    impl<'a, T> Slice<'a> for T {
        type Out = &'a str;
        default fn slice(&self, x: &'a str) -> Self::Out {
            x // whole borrow
        }
    }
    impl<'a> Slice<'a> for () {
        fn slice(&self, x: &'a str) -> Self::Out {
            &x[1..] // a sub-borrow, still tied to 'a
        }
    }
}

#[test]
fn non_static_lifetime_in_associated_type_dispatches() {
    use non_static_assoc_type::Slice;
    // `borrowed` is owned locally, so the `&str` (and thus the associated type
    // `Out = &'a str`) is genuinely non-'static.
    fn run<'a>(x: &'a str) -> (&'a str, &'a str) {
        (Slice::slice(&5i32, x), Slice::slice(&(), x))
    }
    let borrowed = String::from("hello");
    let (default_out, special_out) = run(borrowed.as_str());
    assert_eq!(default_out, "hello"); // default: whole borrow
    assert_eq!(special_out, "ello"); // specialized: &x[1..]
}
