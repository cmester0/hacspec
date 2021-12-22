use hacspec_lib::*;

fn test_casting () {
    let U8v = U8(5u8);
    let U16v = U16(5u16);
    let U32v = U32(5u32);
    let U64v = U64(5u64);
    let U128v = U128(5u128);

    let I8v = I8(5i8);
    let I16v = I16(5i16);
    let I32v = I32(5i32);
    let I64v = I64(5i64);
    let I128v = I128(5i128);

    let usizev : usize = 5usize;

    let u8v : u8 = 5u8;
    let u16v : u16 = 5u16;
    let u32v : u32 = 5u32;
    let u64v : u64 = 5u64;
    let u128v : u128 = 5u128;

    let i8v : i8 = 5i8;
    let i16v : i16 = 5i16;
    let i32v : i32 = 5i32;
    let i64v : i64 = 5i64;
    let i128v : i128 = 5i128;
    
    U128_from_U8 (U8v);
    U8_from_U128 (U128v);
    U128_from_U16 (U16v);
    U16_from_U128 (U128v);
    U128_from_U32 (U32v);
    U32_from_U128 (U128v);
    U128_from_U64 (U64v);
    U64_from_U128 (U128v);

    U64_from_U8 (U8v);
    U8_from_U64 (U64v);

    U64_from_U16 (U16v);
    U16_from_U64 (U64v);

    U64_from_U32 (U32v);
    U32_from_U64 (U64v);
    
    U32_from_U8 (U8v);
    U8_from_U32 (U32v);

    U32_from_U16 (U16v);
    U16_from_U32 (U32v);

    U16_from_U8 (U8v);
    U8_from_U16 (U16v);

    declassify_u8_from_U8 (U8v);
    declassify_u16_from_U8 (U8v);
    declassify_u32_from_U8 (U8v);
    declassify_u64_from_U8 (U8v);
    declassify_u128_from_U8 (U8v);
    declassify_usize_from_U8 (U8v);

    U8_from_usize (usizev);

    declassify_u16_from_U16 (U16v);
    declassify_u32_from_U16 (U16v);
    declassify_u64_from_U16 (U16v);

    u128_from_U16 (U16v);

    declassify_u32_from_U32 (U32v);
    declassify_u64_from_U32 (U32v);
    declassify_u128_from_U32 (U32v);

    declassify_u64_from_U64 (U64v);
    declassify_u128_from_U64 (U64v);
    
    declassify_u128_from_U128 (U128v);

    // u8_from_U16 (U16v);
    // u8_from_U32 (U32v);
    // u16_from_U32 (U32v);
    // u8_from_U64 (U64v);
    // u16_from_U64 (U64v);
    // u32_from_U64 (U64v);
    
    U64_from_usize (usizev);

    // u8_from_U128 (U128v);
    // u16_from_U128 (U128v);
    // u32_from_U128 (U128v);
    // u64_from_U128 (U128v);
    
    U128_from_usize (usizev);

    I128_from_I8 (I8v);
    I8_from_I128 (I128v);

    I128_from_I16 (I16v);
    I16_from_I128 (I128v);

    I128_from_I32 (I32v);
    I32_from_I128 (I128v);

    I128_from_I64 (I64v);
    I64_from_I128 (I128v);

    I64_from_I8 (I8v);
    I8_from_I64 (I64v);

    I64_from_I16 (I16v);
    I16_from_I64 (I64v);

    I64_from_I32 (I32v);
    I32_from_I64 (I64v);

    I32_from_I8 (I8v);
    I8_from_I32 (I32v);

    I32_from_I16 (I16v);
    I16_from_I32 (I32v);
    
    I16_from_I8 (I8v);
    I8_from_I16 (I16v);
}
