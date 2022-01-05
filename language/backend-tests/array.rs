use hacspec_lib::*;

array!(ArrT, 4, u8);

pub fn array_test () {
    let a = ArrT::new();
    ArrT::length();
    // ArrT::from_array([1_u8,2_u8,3_u8,4_u8]); // [1_u8,2_u8,3_u8,4_u8] array values not allowed in hacspec
    // from_native_slice // not hacspec
    ArrT::from_slice(&PublicByteSeq::new(4), 0, 4);
    a.concat(&PublicByteSeq::new(4));
    ArrT::from_slice_range(&PublicByteSeq::new(4), 0..4);
    a.slice(0, 4);
    a.slice_range(0..4);
    a.num_chunks(2);
    a.get_chunk_len(3,1);
    let (n,s) = a.get_chunk(2,1);
    a.set_chunk(2,1,&s);
    ArrT::default();
    ArrT::create(4);
    a.len();
    // iter not hacspec
    a.update_slice(0,&PublicByteSeq::new(4), 0, 2);
    a.update(2,&PublicByteSeq::new(4));
    a.update_start(&PublicByteSeq::new(4));
    // a.index(0); // known but not in hacspec
    // a.index_mut(0); // cannot borrow as mutable  // known but not in hacspec
    // ArrT::from_vec // not hacspec
    ArrT::from_seq(&PublicByteSeq::new(4));
    // ArrT::hex_string_to_vec("0x27"); // known but not in hacspec
    // ArrT::from_hex("0x27"); // known but not in hacspec
}
