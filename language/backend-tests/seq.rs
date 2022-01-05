use hacspec_lib::*;

pub fn seq_test () {
    let mut a = ByteSeq::new(10);
    let b = ByteSeq::with_capacity(10);
    a = a.reserve(5);
    a.len();
    a.slice(0, 4);
    // a.native_slice(); // Not hacspec
    a = a.into_slice(0,4);
    a = a.slice_range( 0..4 );
    a = a.into_slice_range( 0..4 );
    let (mut a, c) = a.split_off(4);
    a = a.truncate(2);
    ByteSeq::from_slice(&ByteSeq::new(4), 0, 1);
    a = a.concat(&c);
    a = a.concat_owned(b);
    a = a.push(&U8(4_u8));
    a = a.push_owned(U8(5_u8));
    ByteSeq::from_slice_range(&ByteSeq::new(4), 0..4 );
    a.num_chunks(3);
    a.num_exact_chunks(3);
    let (n, mut a) = a.get_chunk(3,1);
    a = a.get_exact_chunk(3,1);
    a = a.get_remainder_chunk(3);
    a = a.set_chunk(3,1,&ByteSeq::new(3));
    a = a.set_exact_chunk(3,1,&ByteSeq::new(3));
    ByteSeq::create(10);
    // a.iter(); // Not hacspec
    a = a.update_slice(10,&ByteSeq::new(1),0,1);
    a = a.update(2,&ByteSeq::new(1));
    a = a.update_start(&ByteSeq::new(1));
    // PublicByteSeq::new(10).index(3); // Not known ???
    // PublicByteSeq::new(10).index_mut(3); // Not known ???
    // a.from_vec(); // Not hacspec
    // a.from_native_slice(); // Not hacspec
    ByteSeq::from_seq(&a);
}

bytes!(Word, 4);

pub fn seq_loop_result_test (key : &ByteSeq, word : Word) -> Result<ByteSeq, ()> {
    let mut byte_seq = ByteSeq::new(10);
    byte_seq = byte_seq.update_start(key);

    for j in 0..10 {
        let _ = Word::from_slice(&byte_seq, 4 * 1, 4);
        byte_seq = Result::<ByteSeq, ()>::Ok(byte_seq.update(4, &word))?;
    }
    Result::<ByteSeq, ()>::Ok(byte_seq)
}
