use min_specialization::specialization;
#[specialization]
mod m {
    pub trait Tr { type T; fn f(&self) -> usize; }
    impl<X> Tr for X { type T = u8; default fn f(&self) -> usize { 0 } }
    impl Tr for () { type T = u16; fn f(&self) -> usize { 1 } }
}
fn main() {}
