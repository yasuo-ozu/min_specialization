use min_specialization::specialization;

#[specialization]
mod test_mod {
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

    // struct S<T>(T);
    // impl<T> core::ops::AddAssign for S<T> {
    //     default fn add_assign(&mut self, rhs: Self) {}
    // }
    // impl core::ops::AddAssign for S<usize> {
    //     fn add_assign(&mut self, rhs: Self) {}
    // }
}
