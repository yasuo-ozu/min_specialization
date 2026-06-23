use min_specialization::specialization;
#[specialization]
mod m {
    pub trait Tr { fn f(&self) -> usize; }
    impl<T> Tr for T where T: IntoIterator<Item: IntoIterator<Item = u8>> {
        default fn f(&self) -> usize { 0 }
    }
    impl Tr for () { fn f(&self) -> usize { 1 } }
}
fn main() {}
