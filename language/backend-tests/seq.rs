use hacspec_lib::*;

bytes!(Word, 4);

pub fn seq_test (key : &ByteSeq, word : Word) -> Result<ByteSeq, ()> {
    let mut byte_seq = ByteSeq::new(10);
    byte_seq = byte_seq.update_start(key);

    for j in 0..10 {
        let _ = Word::from_slice(&byte_seq, 4 * 1, 4);
        byte_seq = Result::<ByteSeq, ()>::Ok(byte_seq.update(4, &word))?;
    }
    Result::<ByteSeq, ()>::Ok(byte_seq)
}

// ) -> ByteSeqResult {
//     let mut key_ex = ByteSeq::new(key_schedule_length);
//     key_ex = key_ex.update_start(key);
//     let word_size = key_length;
//     for j in 0..iterations {
//         let i = j + word_size;
//         let word = key_expansion_word(
//             Word::from_slice(&key_ex, 4 * (i - word_size), 4),
//             Word::from_slice(&key_ex, 4 * i - 4, 4),
//             i,
//             nk,
//             nr,
//         )?;
//         key_ex = key_ex.update(4 * i, &word);
//     }
//     ByteSeqResult::Ok(key_ex)
// }
