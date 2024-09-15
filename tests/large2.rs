use min_specialization::specialization;
#[specialization]
mod test_mod {
    pub trait Serialize {
        fn serialize(&self) -> String;
    }

    impl<T: core::fmt::Debug> Serialize for T {
        default fn serialize(&self) -> String {
            format!("Generic serialization: {:?}", self)
        }
    }

    impl Serialize for i32
    where
        Self: core::fmt::Debug,
    {
        fn serialize(&self) -> String {
            format!("Integer serialization: {}", self)
        }
    }

    impl Serialize for &str
    where
        Self: core::fmt::Debug,
    {
        fn serialize(&self) -> String {
            format!("String serialization: '{}'", self)
        }
    }
}

use test_mod::Serialize;

fn main() {
    let x = 42;
    let y = "Hello, world!";
    let z = ();
    assert!(x.serialize().starts_with("Integer"));
    assert!(y.serialize().starts_with("String"));
    assert!(z.serialize().starts_with("Generic"));
}
