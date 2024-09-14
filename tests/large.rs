use min_specialization::specialization;

#[specialization]
mod test_mod {
    pub trait DataSize {
        fn size(&self) -> usize;
    }

    impl<T> DataSize for T {
        default fn size(&self) -> usize {
            std::mem::size_of::<T>()
        }
    }

    impl DataSize for &str {
        fn size(&self) -> usize {
            self.len()
        }
    }

    impl DataSize for i32 {
        fn size(&self) -> usize {
            4
        }
    }

    // 特殊化された実装：f64 型の場合
    impl DataSize for f64 {
        fn size(&self) -> usize {
            8 // f64 は 8 バイト固定
        }
    }
}

use test_mod::DataSize;

fn main() {
    let integer = 42;
    let floating_point = 3.14;
    let text = "Hello, Rust!";

    println!("Size of i32: {}", integer.size());
    println!("Size of f64: {}", floating_point.size());
    println!("Size of &str: {}", text.size());
    println!("Size of f64 default: {}", (5.0f64).size());
}
