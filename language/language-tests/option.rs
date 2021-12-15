use hacspec_lib::*;

pub fn foo(x: Option<Option<U32>>) -> U32 {
    let y = Option::<U32>::None;
    let _z = Option::<Option<U32>>::Some(y);
    match x {
        Option::<Option<U32>>::None => U32(0u32),
        Option::<Option<U32>>::Some(x) => x.unwrap(),
    }
}

pub type MySingleOptionType =  Option<U32>;
pub type MyDoubleOptionType =  Option<Option<U32>>;

pub fn bar(x: MyDoubleOptionType) -> U32 {
    let y = MySingleOptionType::None;
    let _z = MyDoubleOptionType::Some(y);
    match x {
        MyDoubleOptionType::None => U32(0u32),
        MyDoubleOptionType::Some(x) =>
            match x {
                MySingleOptionType::None => U32(0u32),
                MySingleOptionType::Some(x) => x
            },
    }
}
