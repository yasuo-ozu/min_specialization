use min_specialization::specialization;

#[specialization]
mod test_mod {
    #[allow(unused)]
    trait Trait {
        fn number() -> usize;
    }

    impl<T> Trait for T {
        default fn number() -> usize {
            0
        }
    }

    impl Trait for () {
        fn number() -> usize {
            1
        }
    }
}
