use hacspec_lib::*;

/////////////////////
// Primitive types //
/////////////////////

// Bool

pub fn t () -> bool {
    true
}

pub fn f () -> bool {
    false
}

// Unsigned integer

pub fn ui () -> usize {
    123
}

pub fn ui8 () -> u8 {
    123_u8
}

pub fn ui16 () -> u16 {
    123_u16
}

pub fn ui32 () -> u32 {
    123_u32
}

pub fn ui64 () -> u64 {
    123_u64
}

pub fn ui128 () -> u128 {
    123_u128
}

// Signed integer

pub fn si () -> isize {
    123_isize
}

pub fn si8 () -> i8 {
    123_i8
}

pub fn si16 () -> i16 {
    123_i16
}

pub fn si32 () -> i32 {
    123_i32
}

pub fn si64 () -> i64 {
    123_i64
}

pub fn si128 () -> i128 {
    123_i128
}


// Float not allowed in hacspec

// pub fn fl32 () -> f32 {
//     0.98_f32
// }

// pub fn fl64 () -> f64 {
//     0.98_f64
// }


// Char not allowed

// pub fn ch () -> char {
//     'a'
// }


// String
//// Fails

// pub fn strex () {
//     // "" == "2";
//     "2";
//     // String::from("")
// }

// pub fn strexa (a : String) -> String {
//     a
// }


// Never not allowed in hacspec

// pub fn a () -> ! {
//     panic!()
// }


////////////////////
// Sequence types //
////////////////////

// Tuples
pub fn sequnit () -> () {
    ()
}

pub fn seqtup () -> (bool, u8, u64) {
    (true, 12_u8, 93_u64)
}

// Array
array!(arri32, 3, i32);
pub fn arr () -> arri32 {
    arri32([0_i32,21_i32,42_i32])
}

// Seq is hacspec version of slices
pub fn seqslice () -> Seq<i32> {
    arri32([0_i32,21_i32,42_i32]).slice(0,3)
}

////////////////////////
// User defined types //
////////////////////////

// // Struct not yet supported
// struct point {
//     x : i32,
//     y : i32
// }

// pub fn structtyp () -> point {
//     point { x : 32_i32 , y : 32_i32 }
// }


// Enum
pub enum Enm {
    FirstEnum,
    SecondEnum(bool),
}
pub fn enmfun () -> Enm {
    Enm::SecondEnum(false)
}

// Union declaration not allowed in hacspec
// union MyUnion {
//     f1: i32,
//     f2: i32,
// }

////////////////////
// Function types //
////////////////////


///////////////////
// Pointer types //
///////////////////


/////////////////
// Trait types //
/////////////////

// Traits are not allowed in hacspec

// trait Printable {
//     fn stringify(&self) -> String;
// }

// impl Printable for i32 {
//     fn stringify(&self) -> String { self.to_string() }
// }

// Translation, pull out function

/////////////
// Library //
/////////////

// Either call outside of hacspec or reimplement using binary sequences.

////////////////
// Equalities //
////////////////

pub fn eqs () {
    false == true;
    
    0_u8 == 4_u8;
    0_u16 == 0_u16;
    4_u32 == 7_u32;
    4_u64 == 4_u64;
    4_u128 == 4_u128;
    4 == 4;
    
    0_i8 == 4_i8;
    0_i16 == 0_i16;
    4_i32 == 7_i32;
    4_i64 == 4_i64;
    4_i128 == 4_i128;
    4_isize == 4_isize;

    (true, 12_u8, 93_u64) == (true, 12_u8, 92_u64);
    
    arri32([0_i32,21_i32,42_i32]) ==
        arri32([0_i32,21_i32,42_i32]);

    // Enm::SecondEnum(false) == Enm::SecondEnum(true) // not doable
}
