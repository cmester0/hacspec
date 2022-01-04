(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Definition state_t := nseq (uint32) (usize 12).

Definition state_idx_t :=
  nat_mod (usize 12).
Definition uint_size_in_state_idx_t(n : uint_size) : state_idx_t := int_in_nat_mod n.
Coercion uint_size_in_state_idx_t : uint_size >-> state_idx_t.

Definition swap
  (s_0 : state_t)
  (i_1 : state_idx_t)
  (j_2 : state_idx_t)
  : state_t :=
  let tmp_3 : uint32 :=
    array_index (s_0) (i_1) in 
  let s_0 :=
    array_upd s_0 (i_1) (array_index (s_0) (j_2)) in 
  let s_0 :=
    array_upd s_0 (j_2) (tmp_3) in 
  s_0.

Definition gimli_round (s_4 : state_t) (r_5 : int32) : state_t :=
  let s_4 :=
    foldi (usize 0) (usize 4) (fun col_6 s_4 =>
      let x_7 : uint32 :=
        uint32_rotate_left (array_index (s_4) (col_6)) (usize 24) in 
      let y_8 : uint32 :=
        uint32_rotate_left (array_index (s_4) ((col_6) + (usize 4))) (
          usize 9) in 
      let z_9 : uint32 :=
        array_index (s_4) ((col_6) + (usize 8)) in 
      let s_4 :=
        array_upd s_4 ((col_6) + (usize 8)) (((x_7) .^ ((z_9) shift_left (
                usize 1))) .^ (((y_8) .& (z_9)) shift_left (usize 2))) in 
      let s_4 :=
        array_upd s_4 ((col_6) + (usize 4)) (((y_8) .^ (x_7)) .^ (((x_7) .| (
                z_9)) shift_left (usize 1))) in 
      let s_4 :=
        array_upd s_4 (col_6) (((z_9) .^ (y_8)) .^ (((x_7) .& (
                y_8)) shift_left (usize 3))) in 
      (s_4))
    s_4 in 
  let '(s_4) :=
    if ((r_5) .& (@repr WORDSIZE32 3)) =.? (@repr WORDSIZE32 0):bool then (
      let s_4 :=
        swap (s_4) (usize 0) (usize 1) in 
      let s_4 :=
        swap (s_4) (usize 2) (usize 3) in 
      (s_4)) else ((s_4)) in 
  let '(s_4) :=
    if ((r_5) .& (@repr WORDSIZE32 3)) =.? (@repr WORDSIZE32 2):bool then (
      let s_4 :=
        swap (s_4) (usize 0) (usize 2) in 
      let s_4 :=
        swap (s_4) (usize 1) (usize 3) in 
      (s_4)) else ((s_4)) in 
  let '(s_4) :=
    if ((r_5) .& (@repr WORDSIZE32 3)) =.? (@repr WORDSIZE32 0):bool then (
      let s_4 :=
        array_upd s_4 (usize 0) ((array_index (s_4) (usize 0)) .^ ((secret (
                @repr WORDSIZE32 2654435584) : int32) .| (secret (
                r_5) : int32))) in 
      (s_4)) else ((s_4)) in 
  s_4.

Definition gimli (s_10 : state_t) : state_t :=
  let s_10 :=
    foldi (usize 0) (usize 24) (fun rnd_11 s_10 =>
      let rnd_12 : int32 :=
        pub_u32 ((usize 24) - (rnd_11)) in 
      let s_10 :=
        gimli_round (s_10) (rnd_12) in 
      (s_10))
    s_10 in 
  s_10.

Definition block_t := nseq (uint8) (usize 16).

Definition digest_t := nseq (uint8) (usize 32).

Definition absorb_block (input_block_13 : block_t) (s_14 : state_t) : state_t :=
  let input_bytes_15 : seq uint32 :=
    array_to_le_uint32s (input_block_13) in 
  let s_14 :=
    array_upd s_14 (usize 0) ((array_index (s_14) (usize 0)) .^ (seq_index (
          input_bytes_15) (usize 0))) in 
  let s_14 :=
    array_upd s_14 (usize 1) ((array_index (s_14) (usize 1)) .^ (seq_index (
          input_bytes_15) (usize 1))) in 
  let s_14 :=
    array_upd s_14 (usize 2) ((array_index (s_14) (usize 2)) .^ (seq_index (
          input_bytes_15) (usize 2))) in 
  let s_14 :=
    array_upd s_14 (usize 3) ((array_index (s_14) (usize 3)) .^ (seq_index (
          input_bytes_15) (usize 3))) in 
  gimli (s_14).

Definition squeeze_block (s_16 : state_t) : block_t :=
  let block_17 : block_t :=
    array_new_ (default) (16) in 
  let block_17 :=
    foldi (usize 0) (usize 4) (fun i_18 block_17 =>
      let s_i_19 : uint32 :=
        array_index (s_16) (i_18) in 
      let s_i_bytes_20 : seq uint8 :=
        uint32_to_le_bytes (s_i_19) in 
      let block_17 :=
        array_upd block_17 ((usize 4) * (i_18)) (seq_index (s_i_bytes_20) (
            usize 0)) in 
      let block_17 :=
        array_upd block_17 (((usize 4) * (i_18)) + (usize 1)) (seq_index (
            s_i_bytes_20) (usize 1)) in 
      let block_17 :=
        array_upd block_17 (((usize 4) * (i_18)) + (usize 2)) (seq_index (
            s_i_bytes_20) (usize 2)) in 
      let block_17 :=
        array_upd block_17 (((usize 4) * (i_18)) + (usize 3)) (seq_index (
            s_i_bytes_20) (usize 3)) in 
      (block_17))
    block_17 in 
  block_17.

Definition gimli_hash_state (input_21 : byte_seq) (s_22 : state_t) : state_t :=
  let rate_23 : uint_size :=
    16  in 
  let chunks_24 : uint_size :=
    seq_num_exact_chunks (input_21) (rate_23) in 
  let s_22 :=
    foldi (usize 0) (chunks_24) (fun i_25 s_22 =>
      let input_block_26 : seq uint8 :=
        seq_get_exact_chunk (input_21) (rate_23) (i_25) in 
      let full_block_27 : block_t :=
        array_from_seq (16) (input_block_26) in 
      let s_22 :=
        absorb_block (full_block_27) (s_22) in 
      (s_22))
    s_22 in 
  let input_block_28 : seq uint8 :=
    seq_get_remainder_chunk (input_21) (rate_23) in 
  let input_block_padded_29 : block_t :=
    array_new_ (default) (16) in 
  let input_block_padded_30 : block_t :=
    array_update_start (input_block_padded_29) (input_block_28) in 
  let input_block_padded_30 :=
    array_upd input_block_padded_30 (seq_len (input_block_28)) (secret (
        @repr WORDSIZE8 1) : int8) in 
  let s_22 :=
    array_upd s_22 (usize 11) ((array_index (s_22) (usize 11)) .^ (secret (
          @repr WORDSIZE32 16777216) : int32)) in 
  let s_22 :=
    absorb_block (input_block_padded_30) (s_22) in 
  s_22.

Definition gimli_hash (input_bytes_31 : byte_seq) : digest_t :=
  let s_32 : state_t :=
    array_new_ (default) (12) in 
  let s_33 : state_t :=
    gimli_hash_state (input_bytes_31) (s_32) in 
  let output_34 : digest_t :=
    array_new_ (default) (32) in 
  let output_35 : digest_t :=
    array_update_start (output_34) (squeeze_block (s_33)) in 
  let s_36 : state_t :=
    gimli (s_33) in 
  array_update (output_35) (16 ) (squeeze_block (s_36)).

Definition nonce_t := nseq (uint8) (usize 16).

Definition key_t := nseq (uint8) (usize 32).

Definition tag_t := nseq (uint8) (usize 16).

Definition process_ad (ad_37 : byte_seq) (s_38 : state_t) : state_t :=
  gimli_hash_state (ad_37) (s_38).

Definition process_msg
  (message_39 : byte_seq)
  (s_40 : state_t)
  : (state_t × byte_seq) :=
  let ciphertext_41 : seq uint8 :=
    seq_new_ (default) (seq_len (message_39)) in 
  let rate_42 : uint_size :=
    16  in 
  let num_chunks_43 : uint_size :=
    seq_num_exact_chunks (message_39) (rate_42) in 
  let '(s_40, ciphertext_41) :=
    foldi (usize 0) (num_chunks_43) (fun i_44 '(s_40, ciphertext_41) =>
      let key_block_45 : block_t :=
        squeeze_block (s_40) in 
      let msg_block_46 : seq uint8 :=
        seq_get_exact_chunk (message_39) (rate_42) (i_44) in 
      let msg_block_47 : block_t :=
        array_from_seq (16) (msg_block_46) in 
      let ciphertext_41 :=
        seq_set_exact_chunk (ciphertext_41) (rate_42) (i_44) ((
            msg_block_47) array_xor (key_block_45)) in 
      let s_40 :=
        absorb_block (msg_block_47) (s_40) in 
      (s_40, ciphertext_41))
    (s_40, ciphertext_41) in 
  let key_block_48 : block_t :=
    squeeze_block (s_40) in 
  let last_block_49 : seq uint8 :=
    seq_get_remainder_chunk (message_39) (rate_42) in 
  let block_len_50 : uint_size :=
    seq_len (last_block_49) in 
  let msg_block_padded_51 : block_t :=
    array_new_ (default) (16) in 
  let msg_block_padded_52 : block_t :=
    array_update_start (msg_block_padded_51) (last_block_49) in 
  let ciphertext_41 :=
    seq_set_chunk (ciphertext_41) (rate_42) (num_chunks_43) (array_slice_range (
        (msg_block_padded_52) array_xor (key_block_48)) ((usize 0, block_len_50
        ))) in 
  let msg_block_padded_52 :=
    array_upd msg_block_padded_52 (block_len_50) ((array_index (
          msg_block_padded_52) (block_len_50)) .^ (secret (
          @repr WORDSIZE8 1) : int8)) in 
  let s_40 :=
    array_upd s_40 (usize 11) ((array_index (s_40) (usize 11)) .^ (secret (
          @repr WORDSIZE32 16777216) : int32)) in 
  let s_40 :=
    absorb_block (msg_block_padded_52) (s_40) in 
  (s_40, ciphertext_41).

Definition process_ct
  (ciphertext_53 : byte_seq)
  (s_54 : state_t)
  : (state_t × byte_seq) :=
  let message_55 : seq uint8 :=
    seq_new_ (default) (seq_len (ciphertext_53)) in 
  let rate_56 : uint_size :=
    16  in 
  let num_chunks_57 : uint_size :=
    seq_num_exact_chunks (ciphertext_53) (rate_56) in 
  let '(s_54, message_55) :=
    foldi (usize 0) (num_chunks_57) (fun i_58 '(s_54, message_55) =>
      let key_block_59 : block_t :=
        squeeze_block (s_54) in 
      let ct_block_60 : seq uint8 :=
        seq_get_exact_chunk (ciphertext_53) (rate_56) (i_58) in 
      let ct_block_61 : block_t :=
        array_from_seq (16) (ct_block_60) in 
      let msg_block_62 : block_t :=
        (ct_block_61) array_xor (key_block_59) in 
      let message_55 :=
        seq_set_exact_chunk (message_55) (rate_56) (i_58) ((
            ct_block_61) array_xor (key_block_59)) in 
      let s_54 :=
        absorb_block (msg_block_62) (s_54) in 
      (s_54, message_55))
    (s_54, message_55) in 
  let key_block_63 : block_t :=
    squeeze_block (s_54) in 
  let ct_final_64 : seq uint8 :=
    seq_get_remainder_chunk (ciphertext_53) (rate_56) in 
  let block_len_65 : uint_size :=
    seq_len (ct_final_64) in 
  let ct_block_padded_66 : block_t :=
    array_new_ (default) (16) in 
  let ct_block_padded_67 : block_t :=
    array_update_start (ct_block_padded_66) (ct_final_64) in 
  let msg_block_68 : block_t :=
    (ct_block_padded_67) array_xor (key_block_63) in 
  let message_55 :=
    seq_set_chunk (message_55) (rate_56) (num_chunks_57) (array_slice_range (
        msg_block_68) ((usize 0, block_len_65))) in 
  let msg_block_69 : block_t :=
    array_from_slice_range (default) (16) (msg_block_68) ((usize 0, block_len_65
      )) in 
  let msg_block_69 :=
    array_upd msg_block_69 (block_len_65) ((array_index (msg_block_69) (
          block_len_65)) .^ (secret (@repr WORDSIZE8 1) : int8)) in 
  let s_54 :=
    array_upd s_54 (usize 11) ((array_index (s_54) (usize 11)) .^ (secret (
          @repr WORDSIZE32 16777216) : int32)) in 
  let s_54 :=
    absorb_block (msg_block_69) (s_54) in 
  (s_54, message_55).

Definition nonce_to_u32s (nonce_70 : nonce_t) : seq uint32 :=
  let uints_71 : seq uint32 :=
    seq_new_ (default) (usize 4) in 
  let uints_71 :=
    seq_upd uints_71 (usize 0) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (nonce_70) ((usize 0, usize 4)))) in 
  let uints_71 :=
    seq_upd uints_71 (usize 1) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (nonce_70) ((usize 4, usize 8)))) in 
  let uints_71 :=
    seq_upd uints_71 (usize 2) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (nonce_70) ((usize 8, usize 12)))) in 
  let uints_71 :=
    seq_upd uints_71 (usize 3) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (nonce_70) ((usize 12, usize 16)))) in 
  uints_71.

Definition key_to_u32s (key_72 : key_t) : seq uint32 :=
  let uints_73 : seq uint32 :=
    seq_new_ (default) (usize 8) in 
  let uints_73 :=
    seq_upd uints_73 (usize 0) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (key_72) ((usize 0, usize 4)))) in 
  let uints_73 :=
    seq_upd uints_73 (usize 1) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (key_72) ((usize 4, usize 8)))) in 
  let uints_73 :=
    seq_upd uints_73 (usize 2) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (key_72) ((usize 8, usize 12)))) in 
  let uints_73 :=
    seq_upd uints_73 (usize 3) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (key_72) ((usize 12, usize 16)))) in 
  let uints_73 :=
    seq_upd uints_73 (usize 4) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (key_72) ((usize 16, usize 20)))) in 
  let uints_73 :=
    seq_upd uints_73 (usize 5) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (key_72) ((usize 20, usize 24)))) in 
  let uints_73 :=
    seq_upd uints_73 (usize 6) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (key_72) ((usize 24, usize 28)))) in 
  let uints_73 :=
    seq_upd uints_73 (usize 7) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (key_72) ((usize 28, usize 32)))) in 
  uints_73.

Definition gimli_aead_encrypt
  (message_74 : byte_seq)
  (ad_75 : byte_seq)
  (nonce_76 : nonce_t)
  (key_77 : key_t)
  : (byte_seq × tag_t) :=
  let s_78 : state_t :=
    array_from_seq (12) (seq_concat (nonce_to_u32s (nonce_76)) (key_to_u32s (
          key_77))) in 
  let s_79 : state_t :=
    gimli (s_78) in 
  let s_80 : state_t :=
    process_ad (ad_75) (s_79) in 
  let '(s_81, ciphertext_82) :=
    process_msg (message_74) (s_80) in 
  let tag_83 : block_t :=
    squeeze_block (s_81) in 
  let tag_84 : tag_t :=
    array_from_seq (16) (tag_83) in 
  (ciphertext_82, tag_84).

Definition gimli_aead_decrypt
  (ciphertext_85 : byte_seq)
  (ad_86 : byte_seq)
  (tag_87 : tag_t)
  (nonce_88 : nonce_t)
  (key_89 : key_t)
  : byte_seq :=
  let s_90 : state_t :=
    array_from_seq (12) (seq_concat (nonce_to_u32s (nonce_88)) (key_to_u32s (
          key_89))) in 
  let s_91 : state_t :=
    gimli (s_90) in 
  let s_92 : state_t :=
    process_ad (ad_86) (s_91) in 
  let '(s_93, message_94) :=
    process_ct (ciphertext_85) (s_92) in 
  let my_tag_95 : block_t :=
    squeeze_block (s_93) in 
  let my_tag_96 : tag_t :=
    array_from_seq (16) (my_tag_95) in 
  let out_97 : seq uint8 :=
    seq_new_ (default) (usize 0) in 
  let '(out_97) :=
    if array_equal (my_tag_96) (tag_87):bool then (let out_97 :=
        message_94 in 
      (out_97)) else ((out_97)) in 
  out_97.

