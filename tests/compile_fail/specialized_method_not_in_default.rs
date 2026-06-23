use min_specialization::specialization;
#[specialization]
mod m {
    pub trait Tr { fn a(&self) -> u32 { 0 } fn b(&self) -> u32 { 0 } }
    impl<T> Tr for T { default fn a(&self) -> u32 { 1 } }
    impl Tr for i32 { fn a(&self) -> u32 { 10 } fn b(&self) -> u32 { 20 } }
}
fn main() {}
