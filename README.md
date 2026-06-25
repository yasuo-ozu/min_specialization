<p align="center">
  <img src="https://raw.githubusercontent.com/yasuo-ozu/min_specialization/main/logo.png" alt="min-specialization logo" width="200">
</p>

# min-specialization [![Latest Version]][crates.io] [![Documentation]][docs.rs] [![GitHub Actions]][actions]

[Latest Version]: https://img.shields.io/crates/v/min-specialization.svg
[crates.io]: https://crates.io/crates/min-specialization
[Documentation]: https://img.shields.io/docsrs/min-specialization
[docs.rs]: https://docs.rs/min-specialization/latest/min_specialization/
[GitHub Actions]: https://github.com/yasuo-ozu/min_specialization/actions/workflows/rust.yml/badge.svg
[actions]: https://github.com/yasuo-ozu/min_specialization/actions/workflows/rust.yml

Rust's specialization feature allows you to provide a default implementation of a trait for generic types and then specialize it for specific types. This feature is currently unstable and only available on the nightly version of Rust.

This crate emulates Rust's `#[feature(min_specialization)]` unstable feature on stable Rust.

# Example

Annotate a module with `#[specialization]`. Inside it, write a trait, one
*blanket* implementation that provides the default behaviour (its specializable
methods are marked `default`), and any number of concrete implementations that
override those methods for specific types:

```rust
use min_specialization::specialization;

#[specialization]
mod inner {
    #[allow(unused)]
    trait Trait<U> {
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
```

# A more complex example

A blanket impl can have several specializations, including ones for borrowed
types such as `&str` (which `TypeId`-based dispatch normally forbids, since it
requires `'static`). Associated types are defined once by the blanket impl and
shared by every specialization — only methods are specialized. Dispatch happens
at run time and picks the most specific matching impl:

```rust
use min_specialization::specialization;

#[specialization]
mod describe {
    pub trait Describe {
        type Out;
        fn describe(&self) -> Self::Out;
    }

    // The blanket impl defines the associated type and the `default` method
    // used by every type that is not specialized below.
    impl<T> Describe for T {
        type Out = &'static str;
        default fn describe(&self) -> Self::Out {
            "something else"
        }
    }

    // Specializations override the method for concrete types...
    impl Describe for bool {
        fn describe(&self) -> Self::Out {
            "a boolean"
        }
    }
    impl Describe for i32 {
        fn describe(&self) -> Self::Out {
            "an integer"
        }
    }

    // ...including borrowed types.
    impl Describe for &str {
        fn describe(&self) -> Self::Out {
            "a string slice"
        }
    }
}

use describe::Describe;

assert_eq!(true.describe(), "a boolean");         // specialized
assert_eq!(7i32.describe(), "an integer");        // specialized
assert_eq!("hi".describe(), "a string slice");    // specialized (borrowed type)
assert_eq!(2.5f64.describe(), "something else");  // blanket default
```

Specialization also supports generic methods (including `const` generics),
generic associated types (GATs), trait lifetime parameters, and non-trivial
argument patterns; see `tests` for more.
