//! Soundness regression tests for the dispatch mechanism.
//!
//! Dispatch picks a specialization by comparing a *lifetime-erased* `TypeId`
//! (`core::any::TypeId` obtained through a trait object whose existential lifetime
//! is widened to `'static`, so non-`'static` types such as `&str` are supported).
//! `TypeId` is collision-free, so — unlike the previous function-pointer-address
//! comparison — it has neither false positives (it is immune to the optimizer's
//! identical-code-folding) nor false negatives. The transmute that follows a match
//! is therefore an identity conversion between the same type (up to lifetimes).
//!
//! These tests previously FAILED in `--release` (and silently mis-dispatched under
//! Miri). They must now pass in debug, release, and Miri:
//!
//! ```text
//! cargo test --test audit_soundness
//! cargo test --release --test audit_soundness
//! cargo +nightly miri test --test audit_soundness
//! ```

use min_specialization::specialization;

#[specialization]
mod zst {
    pub trait Kind {
        fn kind(&self) -> u32;
    }
    impl<T> Kind for T {
        default fn kind(&self) -> u32 {
            100
        }
    }
    impl Kind for () {
        fn kind(&self) -> u32 {
            200
        }
    }
}

#[specialization]
mod samesize {
    pub trait Tag {
        fn tag(&self) -> u64;
    }
    impl<T> Tag for T {
        default fn tag(&self) -> u64 {
            0
        }
    }
    impl Tag for Wrapper {
        fn tag(&self) -> u64 {
            self.0
        }
    }
    #[derive(Clone, Copy)]
    pub struct Wrapper(pub u64);
}

#[specialization]
mod bits {
    pub trait B {
        fn b(&self) -> bool;
    }
    impl<T> B for T {
        default fn b(&self) -> bool {
            false
        }
    }
    impl B for MyBool {
        fn b(&self) -> bool {
            self.0
        }
    }
    pub struct MyBool(pub bool); // size 1, align 1 — same layout as u8
}

#[specialization]
mod borrowed {
    pub trait Name {
        fn name(&self) -> &'static str;
    }
    impl<T> Name for T {
        default fn name(&self) -> &'static str {
            "other"
        }
    }
    impl Name for &str {
        fn name(&self) -> &'static str {
            "str"
        }
    }
}

/// A distinct zero-sized type that must use the blanket default, NOT the `()`
/// specialization. Under the old fn-pointer scheme this folded with `()` in release.
struct Unit;

#[test]
fn zst_distinct_type_uses_default() {
    use zst::Kind;
    assert_eq!(().kind(), 200, "() is the specialized one");
    assert_eq!(Unit.kind(), 100, "a distinct ZST must use the blanket default");
}

#[test]
fn samesize_distinct_type_uses_default() {
    use samesize::Tag;
    let w = samesize::Wrapper(0xDEAD_BEEF_DEAD_BEEF);
    assert_eq!(w.tag(), 0xDEAD_BEEF_DEAD_BEEF, "Wrapper is specialized");
    let plain: u64 = 0xDEAD_BEEF_DEAD_BEEF;
    assert_eq!(plain.tag(), 0, "a plain u64 must use the blanket default");
}

#[test]
fn transmute_never_constructs_invalid_bool() {
    use bits::B;
    let x: u8 = 7; // not a valid bool
    assert_eq!(x.b(), false, "u8 must use the default; it must never be read as a bool");
}

#[test]
fn non_static_borrowed_type_specializes_soundly() {
    use borrowed::Name;
    // genuinely non-'static borrow
    fn check(s: &str) -> &'static str {
        s.name()
    }
    let owned = String::from("hello");
    assert_eq!(check(owned.as_str()), "str", "&str (any lifetime) is specialized");
    assert_eq!(42i32.name(), "other", "i32 uses the blanket default");
}
