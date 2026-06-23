use min_specialization::specialization;
#[specialization]
mod m {
    pub trait Ser { fn s(&self) -> String; }
    impl<T: core::fmt::Debug> Ser for T { default fn s(&self) -> String { format!("{:?}", self) } }
    impl Ser for i32 { fn s(&self) -> String { "int".into() } } // omits `T: Debug`
}
fn main() {}
