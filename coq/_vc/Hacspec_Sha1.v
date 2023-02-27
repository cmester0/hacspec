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

Definition schedule_t := nseq (uint32) (usize 80).

Definition block_words_v : uint_size :=
  (usize 512) / (usize 32).

Definition hash_words_v : uint_size :=
  (usize 160) / (usize 32).

Definition block_t := nseq (uint32) (block_words_v).

Definition hash_t := nseq (uint32) (hash_words_v).

Definition block_bytes_v : uint_size :=
  (usize 512) / (usize 8).

Definition hash_bytes_v : uint_size :=
  (usize 160) / (usize 8).

Definition block_bytes_t := nseq (uint8) (block_bytes_v).

Definition sha1_digest_t := nseq (uint8) (hash_bytes_v).

Definition bitlength_bytes_v : uint_size :=
  (usize 64) / (usize 8).

Definition ch (x_1075 : uint32) (y_1076 : uint32) (z_1077 : uint32)  : uint32 :=
  ((x_1075) .& (y_1076)) .^ ((not (x_1075)) .& (z_1077)).


Definition parity
  (x_1078 : uint32)
  (y_1079 : uint32)
  (z_1080 : uint32)
  
  : uint32 :=
  ((x_1078) .^ (y_1079)) .^ (z_1080).


Definition maj
  (x_1081 : uint32)
  (y_1082 : uint32)
  (z_1083 : uint32)
  
  : uint32 :=
  (((x_1081) .& (y_1082)) .^ ((x_1081) .& (z_1083))) .^ ((y_1082) .& (z_1083)).


Definition hash_init_v : hash_t :=
  array_from_list uint32 (let l :=
      [
        secret (@repr WORDSIZE32 (1732584193)) : int32;
        secret (@repr WORDSIZE32 (4023233417)) : int32;
        secret (@repr WORDSIZE32 (2562383102)) : int32;
        secret (@repr WORDSIZE32 (271733878)) : int32;
        secret (@repr WORDSIZE32 (3285377520)) : int32
      ] in  l).

Definition compress
  (m_bytes_1084 : block_bytes_t)
  (h_1085 : hash_t)
  
  : hash_t :=
  let m_1086 : seq uint32 :=
    array_to_be_uint32s (m_bytes_1084) in 
  let w_1087 : schedule_t :=
    array_new_ (default : uint32) (80) in 
  let w_1087 :=
    foldi (usize 0) (usize 80) (fun t_1088 w_1087 =>
      let '(w_1087) :=
        if (t_1088) <.? (usize 16):bool then (let w_1087 :=
            array_upd w_1087 (t_1088) (seq_index (m_1086) (t_1088)) in 
          (w_1087)) else (let w_1087 :=
            array_upd w_1087 (t_1088) (uint32_rotate_left ((((array_index (
                        w_1087) ((t_1088) - (usize 3))) .^ (array_index (
                        w_1087) ((t_1088) - (usize 8)))) .^ (array_index (
                      w_1087) ((t_1088) - (usize 14)))) .^ (array_index (
                    w_1087) ((t_1088) - (usize 16)))) (usize 1)) in 
          (w_1087)) in 
      (w_1087))
    w_1087 in 
  let a_1089 : uint32 :=
    array_index (h_1085) (usize 0) in 
  let b_1090 : uint32 :=
    array_index (h_1085) (usize 1) in 
  let c_1091 : uint32 :=
    array_index (h_1085) (usize 2) in 
  let d_1092 : uint32 :=
    array_index (h_1085) (usize 3) in 
  let e_1093 : uint32 :=
    array_index (h_1085) (usize 4) in 
  let '(a_1089, b_1090, c_1091, d_1092, e_1093) :=
    foldi (usize 0) (usize 80) (fun t_1094 '(
        a_1089,
        b_1090,
        c_1091,
        d_1092,
        e_1093
      ) =>
      let t_1095 : uint32 :=
        uint32_zero  in 
      let '(t_1095) :=
        if ((usize 0) <=.? (t_1094)) && ((t_1094) <.? (usize 20)):bool then (
          let t_1095 :=
            ((((uint32_rotate_left (a_1089) (usize 5)) .+ (ch (b_1090) (
                      c_1091) (d_1092))) .+ (e_1093)) .+ (secret (
                  @repr WORDSIZE32 (1518500249)) : int32)) .+ (array_index (
                w_1087) (t_1094)) in 
          (t_1095)) else ((t_1095)) in 
      let '(t_1095) :=
        if ((usize 20) <=.? (t_1094)) && ((t_1094) <.? (usize 40)):bool then (
          let t_1095 :=
            ((((uint32_rotate_left (a_1089) (usize 5)) .+ (parity (b_1090) (
                      c_1091) (d_1092))) .+ (e_1093)) .+ (secret (
                  @repr WORDSIZE32 (1859775393)) : int32)) .+ (array_index (
                w_1087) (t_1094)) in 
          (t_1095)) else ((t_1095)) in 
      let '(t_1095) :=
        if ((usize 40) <=.? (t_1094)) && ((t_1094) <.? (usize 60)):bool then (
          let t_1095 :=
            ((((uint32_rotate_left (a_1089) (usize 5)) .+ (maj (b_1090) (
                      c_1091) (d_1092))) .+ (e_1093)) .+ (secret (
                  @repr WORDSIZE32 (2400959708)) : int32)) .+ (array_index (
                w_1087) (t_1094)) in 
          (t_1095)) else ((t_1095)) in 
      let '(t_1095) :=
        if ((usize 60) <=.? (t_1094)) && ((t_1094) <.? (usize 80)):bool then (
          let t_1095 :=
            ((((uint32_rotate_left (a_1089) (usize 5)) .+ (parity (b_1090) (
                      c_1091) (d_1092))) .+ (e_1093)) .+ (secret (
                  @repr WORDSIZE32 (3395469782)) : int32)) .+ (array_index (
                w_1087) (t_1094)) in 
          (t_1095)) else ((t_1095)) in 
      let e_1093 :=
        d_1092 in 
      let d_1092 :=
        c_1091 in 
      let c_1091 :=
        uint32_rotate_left (b_1090) (usize 30) in 
      let b_1090 :=
        a_1089 in 
      let a_1089 :=
        t_1095 in 
      (a_1089, b_1090, c_1091, d_1092, e_1093))
    (a_1089, b_1090, c_1091, d_1092, e_1093) in 
  let h_1085 :=
    array_upd h_1085 (usize 0) ((a_1089) .+ (array_index (h_1085) (
          usize 0))) in 
  let h_1085 :=
    array_upd h_1085 (usize 1) ((b_1090) .+ (array_index (h_1085) (
          usize 1))) in 
  let h_1085 :=
    array_upd h_1085 (usize 2) ((c_1091) .+ (array_index (h_1085) (
          usize 2))) in 
  let h_1085 :=
    array_upd h_1085 (usize 3) ((d_1092) .+ (array_index (h_1085) (
          usize 3))) in 
  let h_1085 :=
    array_upd h_1085 (usize 4) ((e_1093) .+ (array_index (h_1085) (
          usize 4))) in 
  h_1085.


Definition hash (msg_1096 : byte_seq)  : sha1_digest_t :=
  let h_1097 : hash_t :=
    hash_init_v in 
  let h_1097 :=
    foldi (usize 0) (seq_num_exact_chunks (msg_1096) (
          block_bytes_v)) (fun i_1098 h_1097 =>
      let raw_bytes_1099 : seq uint8 :=
        seq_get_exact_chunk (msg_1096) (block_bytes_v) (i_1098) in 
      let block_bytes_1100 : block_bytes_t :=
        array_from_seq (block_bytes_v) (raw_bytes_1099) in 
      let h_1097 :=
        compress (block_bytes_1100) (h_1097) in 
      (h_1097))
    h_1097 in 
  let raw_bytes_1101 : seq uint8 :=
    seq_get_remainder_chunk (msg_1096) (block_bytes_v) in 
  let block_bytes_1102 : block_bytes_t :=
    array_update_start (array_new_ (default : uint8) (block_bytes_v)) (
      raw_bytes_1101) in 
  let block_bytes_1102 :=
    array_upd block_bytes_1102 (seq_len (raw_bytes_1101)) (secret (
        @repr WORDSIZE8 128) : int8) in 
  let message_bitlength_1103 : uint64 :=
    secret (pub_u64 ((seq_len (msg_1096)) * (usize 8))) : int64 in 
  let '(h_1097, block_bytes_1102) :=
    if (seq_len (raw_bytes_1101)) <.? ((block_bytes_v) - (
        bitlength_bytes_v)):bool then (let block_bytes_1102 :=
        array_update (block_bytes_1102) ((block_bytes_v) - (
            bitlength_bytes_v)) (array_to_seq (uint64_to_be_bytes (
            message_bitlength_1103))) in 
      let h_1097 :=
        compress (block_bytes_1102) (h_1097) in 
      (h_1097, block_bytes_1102)) else (let h_1097 :=
        compress (block_bytes_1102) (h_1097) in 
      let pad_block_1104 : block_bytes_t :=
        array_new_ (default : uint8) (block_bytes_v) in 
      let pad_block_1104 :=
        array_update (pad_block_1104) ((block_bytes_v) - (bitlength_bytes_v)) (
          array_to_seq (uint64_to_be_bytes (message_bitlength_1103))) in 
      let h_1097 :=
        compress (pad_block_1104) (h_1097) in 
      (h_1097, block_bytes_1102)) in 
  array_from_seq (hash_bytes_v) (array_to_be_bytes (h_1097)).


Definition sha1 (msg_1105 : byte_seq)  : sha1_digest_t :=
  hash (msg_1105).


