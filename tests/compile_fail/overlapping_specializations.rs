use min_specialization::specialization;
#[specialization]
mod m {
    pub trait Tr { fn f(&self) -> u32; }
    impl<T> Tr for T { default fn f(&self) -> u32 { 0 } }
    impl Tr for i32 { fn f(&self) -> u32 { 100 } }
    impl Tr for i32 { fn f(&self) -> u32 { 200 } }
}
fn main() {}
