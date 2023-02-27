(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.
Export Hacspec_Lib.

Definition state_t := nseq (uint32) (usize 12).

Definition state_idx_t :=
  nat_mod (usize 12).
Definition uint_size_in_state_idx_t(n : uint_size) : state_idx_t := int_in_nat_mod n.
Coercion uint_size_in_state_idx_t : uint_size >-> state_idx_t.

Definition swap
  (s_977 : state_t)
  (i_978 : state_idx_t)
  (j_979 : state_idx_t)
  
  : state_t :=
  let tmp_980 : uint32 :=
    array_index (s_977) (i_978) in 
  let s_977 :=
    array_upd s_977 (i_978) (array_index (s_977) (j_979)) in 
  let s_977 :=
    array_upd s_977 (j_979) (tmp_980) in 
  s_977.


Definition gimli_round (s_981 : state_t) (r_982 : int32)  : state_t :=
  let s_981 :=
    foldi (usize 0) (usize 4) (fun col_983 s_981 =>
      let x_984 : uint32 :=
        uint32_rotate_left (array_index (s_981) (col_983)) (usize 24) in 
      let y_985 : uint32 :=
        uint32_rotate_left (array_index (s_981) ((col_983) + (usize 4))) (
          usize 9) in 
      let z_986 : uint32 :=
        array_index (s_981) ((col_983) + (usize 8)) in 
      let s_981 :=
        array_upd s_981 ((col_983) + (usize 8)) (((x_984) .^ ((
                z_986) shift_left (usize 1))) .^ (((y_985) .& (
                z_986)) shift_left (usize 2))) in 
      let s_981 :=
        array_upd s_981 ((col_983) + (usize 4)) (((y_985) .^ (x_984)) .^ (((
                x_984) .| (z_986)) shift_left (usize 1))) in 
      let s_981 :=
        array_upd s_981 (col_983) (((z_986) .^ (y_985)) .^ (((x_984) .& (
                y_985)) shift_left (usize 3))) in 
      (s_981))
    s_981 in 
  let '(s_981) :=
    if ((r_982) .& (@repr WORDSIZE32 (3))) =.? (
      @repr WORDSIZE32 (0)):bool then (let s_981 :=
        swap (s_981) (usize 0) (usize 1) in 
      let s_981 :=
        swap (s_981) (usize 2) (usize 3) in 
      (s_981)) else ((s_981)) in 
  let '(s_981) :=
    if ((r_982) .& (@repr WORDSIZE32 (3))) =.? (
      @repr WORDSIZE32 (2)):bool then (let s_981 :=
        swap (s_981) (usize 0) (usize 2) in 
      let s_981 :=
        swap (s_981) (usize 1) (usize 3) in 
      (s_981)) else ((s_981)) in 
  let '(s_981) :=
    if ((r_982) .& (@repr WORDSIZE32 (3))) =.? (
      @repr WORDSIZE32 (0)):bool then (let s_981 :=
        array_upd s_981 (usize 0) ((array_index (s_981) (usize 0)) .^ ((secret (
                @repr WORDSIZE32 (2654435584)) : int32) .| (secret (
                r_982) : int32))) in 
      (s_981)) else ((s_981)) in 
  s_981.


Definition gimli (s_987 : state_t)  : state_t :=
  let s_987 :=
    foldi (usize 0) (usize 24) (fun rnd_988 s_987 =>
      let rnd_989 : int32 :=
        pub_u32 ((usize 24) - (rnd_988)) in 
      let s_987 :=
        gimli_round (s_987) (rnd_989) in 
      (s_987))
    s_987 in 
  s_987.


Definition block_t := nseq (uint8) (usize 16).

Definition digest_t := nseq (uint8) (usize 32).

Definition absorb_block
  (input_block_990 : block_t)
  (s_991 : state_t)
  
  : state_t :=
  let input_bytes_992 : seq uint32 :=
    array_to_le_uint32s (input_block_990) in 
  let s_991 :=
    array_upd s_991 (usize 0) ((array_index (s_991) (usize 0)) .^ (seq_index (
          input_bytes_992) (usize 0))) in 
  let s_991 :=
    array_upd s_991 (usize 1) ((array_index (s_991) (usize 1)) .^ (seq_index (
          input_bytes_992) (usize 1))) in 
  let s_991 :=
    array_upd s_991 (usize 2) ((array_index (s_991) (usize 2)) .^ (seq_index (
          input_bytes_992) (usize 2))) in 
  let s_991 :=
    array_upd s_991 (usize 3) ((array_index (s_991) (usize 3)) .^ (seq_index (
          input_bytes_992) (usize 3))) in 
  gimli (s_991).


Definition squeeze_block (s_993 : state_t)  : block_t :=
  let block_994 : block_t :=
    array_new_ (default : uint8) (16) in 
  let block_994 :=
    foldi (usize 0) (usize 4) (fun i_995 block_994 =>
      let s_i_996 : uint32 :=
        array_index (s_993) (i_995) in 
      let s_i_bytes_997 : seq uint8 :=
        uint32_to_le_bytes (s_i_996) in 
      let block_994 :=
        array_upd block_994 ((usize 4) * (i_995)) (seq_index (s_i_bytes_997) (
            usize 0)) in 
      let block_994 :=
        array_upd block_994 (((usize 4) * (i_995)) + (usize 1)) (seq_index (
            s_i_bytes_997) (usize 1)) in 
      let block_994 :=
        array_upd block_994 (((usize 4) * (i_995)) + (usize 2)) (seq_index (
            s_i_bytes_997) (usize 2)) in 
      let block_994 :=
        array_upd block_994 (((usize 4) * (i_995)) + (usize 3)) (seq_index (
            s_i_bytes_997) (usize 3)) in 
      (block_994))
    block_994 in 
  block_994.


Definition gimli_hash_state
  (input_998 : byte_seq)
  (s_999 : state_t)
  
  : state_t :=
  let rate_1000 : uint_size :=
    array_length  in 
  let chunks_1001 : uint_size :=
    seq_num_exact_chunks (input_998) (rate_1000) in 
  let s_999 :=
    foldi (usize 0) (chunks_1001) (fun i_1002 s_999 =>
      let input_block_1003 : seq uint8 :=
        seq_get_exact_chunk (input_998) (rate_1000) (i_1002) in 
      let full_block_1004 : block_t :=
        array_from_seq (16) (input_block_1003) in 
      let s_999 :=
        absorb_block (full_block_1004) (s_999) in 
      (s_999))
    s_999 in 
  let input_block_1005 : seq uint8 :=
    seq_get_remainder_chunk (input_998) (rate_1000) in 
  let input_block_padded_1006 : block_t :=
    array_new_ (default : uint8) (16) in 
  let input_block_padded_1007 : block_t :=
    array_update_start (input_block_padded_1006) (input_block_1005) in 
  let input_block_padded_1007 :=
    array_upd input_block_padded_1007 (seq_len (input_block_1005)) (secret (
        @repr WORDSIZE8 1) : int8) in 
  let s_999 :=
    array_upd s_999 (usize 11) ((array_index (s_999) (usize 11)) .^ (secret (
          @repr WORDSIZE32 (16777216)) : int32)) in 
  let s_999 :=
    absorb_block (input_block_padded_1007) (s_999) in 
  s_999.


Definition gimli_hash (input_bytes_1008 : byte_seq)  : digest_t :=
  let s_1009 : state_t :=
    array_new_ (default : uint32) (12) in 
  let s_1010 : state_t :=
    gimli_hash_state (input_bytes_1008) (s_1009) in 
  let output_1011 : digest_t :=
    array_new_ (default : uint8) (32) in 
  let output_1012 : digest_t :=
    array_update_start (output_1011) (array_to_seq (squeeze_block (s_1010))) in 
  let s_1013 : state_t :=
    gimli (s_1010) in 
  array_update (output_1012) (array_length ) (array_to_seq (squeeze_block (
      s_1013))).


Definition nonce_t := nseq (uint8) (usize 16).

Definition key_t := nseq (uint8) (usize 32).

Definition tag_t := nseq (uint8) (usize 16).

Definition process_ad (ad_1014 : byte_seq) (s_1015 : state_t)  : state_t :=
  gimli_hash_state (ad_1014) (s_1015).


Definition process_msg
  (message_1016 : byte_seq)
  (s_1017 : state_t)
  
  : (state_t '× byte_seq) :=
  let ciphertext_1018 : seq uint8 :=
    seq_new_ (default : uint8) (seq_len (message_1016)) in 
  let rate_1019 : uint_size :=
    array_length  in 
  let num_chunks_1020 : uint_size :=
    seq_num_exact_chunks (message_1016) (rate_1019) in 
  let '(s_1017, ciphertext_1018) :=
    foldi (usize 0) (num_chunks_1020) (fun i_1021 '(s_1017, ciphertext_1018) =>
      let key_block_1022 : block_t :=
        squeeze_block (s_1017) in 
      let msg_block_1023 : seq uint8 :=
        seq_get_exact_chunk (message_1016) (rate_1019) (i_1021) in 
      let msg_block_1024 : block_t :=
        array_from_seq (16) (msg_block_1023) in 
      let ciphertext_1018 :=
        seq_set_exact_chunk (ciphertext_1018) (rate_1019) (i_1021) (
          array_to_seq ((msg_block_1024) array_xor (key_block_1022))) in 
      let s_1017 :=
        absorb_block (msg_block_1024) (s_1017) in 
      (s_1017, ciphertext_1018))
    (s_1017, ciphertext_1018) in 
  let key_block_1025 : block_t :=
    squeeze_block (s_1017) in 
  let last_block_1026 : seq uint8 :=
    seq_get_remainder_chunk (message_1016) (rate_1019) in 
  let block_len_1027 : uint_size :=
    seq_len (last_block_1026) in 
  let msg_block_padded_1028 : block_t :=
    array_new_ (default : uint8) (16) in 
  let msg_block_padded_1029 : block_t :=
    array_update_start (msg_block_padded_1028) (last_block_1026) in 
  let ciphertext_1018 :=
    seq_set_chunk (ciphertext_1018) (rate_1019) (num_chunks_1020) (
      array_slice_range ((msg_block_padded_1029) array_xor (key_block_1025)) ((
          usize 0,
          block_len_1027
        ))) in 
  let msg_block_padded_1029 :=
    array_upd msg_block_padded_1029 (block_len_1027) ((array_index (
          msg_block_padded_1029) (block_len_1027)) .^ (secret (
          @repr WORDSIZE8 1) : int8)) in 
  let s_1017 :=
    array_upd s_1017 (usize 11) ((array_index (s_1017) (usize 11)) .^ (secret (
          @repr WORDSIZE32 (16777216)) : int32)) in 
  let s_1017 :=
    absorb_block (msg_block_padded_1029) (s_1017) in 
  (s_1017, ciphertext_1018).


Definition process_ct
  (ciphertext_1030 : byte_seq)
  (s_1031 : state_t)
  
  : (state_t '× byte_seq) :=
  let message_1032 : seq uint8 :=
    seq_new_ (default : uint8) (seq_len (ciphertext_1030)) in 
  let rate_1033 : uint_size :=
    array_length  in 
  let num_chunks_1034 : uint_size :=
    seq_num_exact_chunks (ciphertext_1030) (rate_1033) in 
  let '(s_1031, message_1032) :=
    foldi (usize 0) (num_chunks_1034) (fun i_1035 '(s_1031, message_1032) =>
      let key_block_1036 : block_t :=
        squeeze_block (s_1031) in 
      let ct_block_1037 : seq uint8 :=
        seq_get_exact_chunk (ciphertext_1030) (rate_1033) (i_1035) in 
      let ct_block_1038 : block_t :=
        array_from_seq (16) (ct_block_1037) in 
      let msg_block_1039 : block_t :=
        (ct_block_1038) array_xor (key_block_1036) in 
      let message_1032 :=
        seq_set_exact_chunk (message_1032) (rate_1033) (i_1035) (array_to_seq ((
            ct_block_1038) array_xor (key_block_1036))) in 
      let s_1031 :=
        absorb_block (msg_block_1039) (s_1031) in 
      (s_1031, message_1032))
    (s_1031, message_1032) in 
  let key_block_1040 : block_t :=
    squeeze_block (s_1031) in 
  let ct_final_1041 : seq uint8 :=
    seq_get_remainder_chunk (ciphertext_1030) (rate_1033) in 
  let block_len_1042 : uint_size :=
    seq_len (ct_final_1041) in 
  let ct_block_padded_1043 : block_t :=
    array_new_ (default : uint8) (16) in 
  let ct_block_padded_1044 : block_t :=
    array_update_start (ct_block_padded_1043) (ct_final_1041) in 
  let msg_block_1045 : block_t :=
    (ct_block_padded_1044) array_xor (key_block_1040) in 
  let message_1032 :=
    seq_set_chunk (message_1032) (rate_1033) (num_chunks_1034) (
      array_slice_range (msg_block_1045) ((usize 0, block_len_1042))) in 
  let msg_block_1046 : block_t :=
    array_from_slice_range (default : uint8) (16) (
      array_to_seq (msg_block_1045)) ((usize 0, block_len_1042)) in 
  let msg_block_1046 :=
    array_upd msg_block_1046 (block_len_1042) ((array_index (msg_block_1046) (
          block_len_1042)) .^ (secret (@repr WORDSIZE8 1) : int8)) in 
  let s_1031 :=
    array_upd s_1031 (usize 11) ((array_index (s_1031) (usize 11)) .^ (secret (
          @repr WORDSIZE32 (16777216)) : int32)) in 
  let s_1031 :=
    absorb_block (msg_block_1046) (s_1031) in 
  (s_1031, message_1032).


Definition nonce_to_u32s (nonce_1047 : nonce_t)  : seq uint32 :=
  let uints_1048 : seq uint32 :=
    seq_new_ (default : uint32) (usize 4) in 
  let uints_1048 :=
    seq_upd uints_1048 (usize 0) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (nonce_1047)) ((usize 0, usize 4
          )))) in 
  let uints_1048 :=
    seq_upd uints_1048 (usize 1) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (nonce_1047)) ((usize 4, usize 8
          )))) in 
  let uints_1048 :=
    seq_upd uints_1048 (usize 2) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (nonce_1047)) ((usize 8, usize 12
          )))) in 
  let uints_1048 :=
    seq_upd uints_1048 (usize 3) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (nonce_1047)) ((usize 12, usize 16
          )))) in 
  uints_1048.


Definition key_to_u32s (key_1049 : key_t)  : seq uint32 :=
  let uints_1050 : seq uint32 :=
    seq_new_ (default : uint32) (usize 8) in 
  let uints_1050 :=
    seq_upd uints_1050 (usize 0) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1049)) ((usize 0, usize 4
          )))) in 
  let uints_1050 :=
    seq_upd uints_1050 (usize 1) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1049)) ((usize 4, usize 8
          )))) in 
  let uints_1050 :=
    seq_upd uints_1050 (usize 2) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1049)) ((usize 8, usize 12
          )))) in 
  let uints_1050 :=
    seq_upd uints_1050 (usize 3) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1049)) ((usize 12, usize 16
          )))) in 
  let uints_1050 :=
    seq_upd uints_1050 (usize 4) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1049)) ((usize 16, usize 20
          )))) in 
  let uints_1050 :=
    seq_upd uints_1050 (usize 5) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1049)) ((usize 20, usize 24
          )))) in 
  let uints_1050 :=
    seq_upd uints_1050 (usize 6) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1049)) ((usize 24, usize 28
          )))) in 
  let uints_1050 :=
    seq_upd uints_1050 (usize 7) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1049)) ((usize 28, usize 32
          )))) in 
  uints_1050.


Definition gimli_aead_encrypt
  (message_1051 : byte_seq)
  (ad_1052 : byte_seq)
  (nonce_1053 : nonce_t)
  (key_1054 : key_t)
  
  : (byte_seq '× tag_t) :=
  let s_1055 : state_t :=
    array_from_seq (12) (seq_concat (nonce_to_u32s (nonce_1053)) (key_to_u32s (
          key_1054))) in 
  let s_1056 : state_t :=
    gimli (s_1055) in 
  let s_1057 : state_t :=
    process_ad (ad_1052) (s_1056) in 
  let '(s_1058, ciphertext_1059) :=
    process_msg (message_1051) (s_1057) in 
  let tag_1060 : block_t :=
    squeeze_block (s_1058) in 
  let tag_1061 : tag_t :=
    array_from_seq (16) (array_to_seq (tag_1060)) in 
  (ciphertext_1059, tag_1061).


Definition gimli_aead_decrypt
  (ciphertext_1062 : byte_seq)
  (ad_1063 : byte_seq)
  (tag_1064 : tag_t)
  (nonce_1065 : nonce_t)
  (key_1066 : key_t)
  
  : byte_seq :=
  let s_1067 : state_t :=
    array_from_seq (12) (seq_concat (nonce_to_u32s (nonce_1065)) (key_to_u32s (
          key_1066))) in 
  let s_1068 : state_t :=
    gimli (s_1067) in 
  let s_1069 : state_t :=
    process_ad (ad_1063) (s_1068) in 
  let '(s_1070, message_1071) :=
    process_ct (ciphertext_1062) (s_1069) in 
  let my_tag_1072 : block_t :=
    squeeze_block (s_1070) in 
  let my_tag_1073 : tag_t :=
    array_from_seq (16) (array_to_seq (my_tag_1072)) in 
  let out_1074 : seq uint8 :=
    seq_new_ (default : uint8) (usize 0) in 
  let '(out_1074) :=
    if array_equal (my_tag_1073) (tag_1064):bool then (let out_1074 :=
        message_1071 in 
      (out_1074)) else ((out_1074)) in 
  out_1074.


