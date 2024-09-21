#[min_specialization::specialization]
mod test1 {
    #[allow(unused)]
    trait MyTrait {
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
