# min-specialization [![Latest Version]][crates.io] [![Documentation]][docs.rs] [![GitHub Actions]][actions]

[Latest Version]: https://img.shields.io/crates/v/min-specialization.svg
[crates.io]: https://crates.io/crates/min-specialization
[Documentation]: https://img.shields.io/docsrs/min-specialization
[docs.rs]: https://docs.rs/min-specialization/latest/min-specialization/
[GitHub Actions]: https://github.com/yasuo-ozu/min-specialization/actions/workflows/rust.yml/badge.svg
[actions]: https://github.com/yasuo-ozu/min-specialization/actions/workflows/rust.yml

Rust's specialization feature allows you to provide a default implementation of a trait for generic types and then specialize it for specific types. This feature is currently unstable and only available on the nightly version of Rust.

This crate emulates Rust's `#[feature(min_specialization)]` unstable feature on stable Rust.

# Example

```
# use min_specialization::specialization;
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

see `tests` for more.
