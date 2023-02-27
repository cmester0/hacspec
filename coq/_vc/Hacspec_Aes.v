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

Definition blocksize_v : uint_size :=
  usize 16.

Definition ivsize_v : uint_size :=
  usize 12.

Definition key_length_v : uint_size :=
  usize 4.

Definition rounds_v : uint_size :=
  usize 10.

Definition key_schedule_length_v : uint_size :=
  usize 176.

Definition iterations_v : uint_size :=
  usize 40.

Definition invalid_key_expansion_index_v : int8 :=
  @repr WORDSIZE8 1.

Definition block_t := nseq (uint8) (blocksize_v).

Definition word_t := nseq (uint8) (key_length_v).

Definition round_key_t := nseq (uint8) (blocksize_v).

Definition aes_nonce_t := nseq (uint8) (ivsize_v).

Definition s_box_t := nseq (uint8) (usize 256).

Definition r_con_t := nseq (uint8) (usize 15).

Definition bytes144_t := nseq (uint8) (usize 144).

Definition bytes176_t := nseq (uint8) (key_schedule_length_v).

Definition key128_t := nseq (uint8) (blocksize_v).

Notation "'byte_seq_result_t'" := ((result byte_seq int8)) : hacspec_scope.

Notation "'block_result_t'" := ((result block_t int8)) : hacspec_scope.

Notation "'word_result_t'" := ((result word_t int8)) : hacspec_scope.

Definition sbox_v : s_box_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 99) : int8;
        secret (@repr WORDSIZE8 124) : int8;
        secret (@repr WORDSIZE8 119) : int8;
        secret (@repr WORDSIZE8 123) : int8;
        secret (@repr WORDSIZE8 242) : int8;
        secret (@repr WORDSIZE8 107) : int8;
        secret (@repr WORDSIZE8 111) : int8;
        secret (@repr WORDSIZE8 197) : int8;
        secret (@repr WORDSIZE8 48) : int8;
        secret (@repr WORDSIZE8 1) : int8;
        secret (@repr WORDSIZE8 103) : int8;
        secret (@repr WORDSIZE8 43) : int8;
        secret (@repr WORDSIZE8 254) : int8;
        secret (@repr WORDSIZE8 215) : int8;
        secret (@repr WORDSIZE8 171) : int8;
        secret (@repr WORDSIZE8 118) : int8;
        secret (@repr WORDSIZE8 202) : int8;
        secret (@repr WORDSIZE8 130) : int8;
        secret (@repr WORDSIZE8 201) : int8;
        secret (@repr WORDSIZE8 125) : int8;
        secret (@repr WORDSIZE8 250) : int8;
        secret (@repr WORDSIZE8 89) : int8;
        secret (@repr WORDSIZE8 71) : int8;
        secret (@repr WORDSIZE8 240) : int8;
        secret (@repr WORDSIZE8 173) : int8;
        secret (@repr WORDSIZE8 212) : int8;
        secret (@repr WORDSIZE8 162) : int8;
        secret (@repr WORDSIZE8 175) : int8;
        secret (@repr WORDSIZE8 156) : int8;
        secret (@repr WORDSIZE8 164) : int8;
        secret (@repr WORDSIZE8 114) : int8;
        secret (@repr WORDSIZE8 192) : int8;
        secret (@repr WORDSIZE8 183) : int8;
        secret (@repr WORDSIZE8 253) : int8;
        secret (@repr WORDSIZE8 147) : int8;
        secret (@repr WORDSIZE8 38) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 63) : int8;
        secret (@repr WORDSIZE8 247) : int8;
        secret (@repr WORDSIZE8 204) : int8;
        secret (@repr WORDSIZE8 52) : int8;
        secret (@repr WORDSIZE8 165) : int8;
        secret (@repr WORDSIZE8 229) : int8;
        secret (@repr WORDSIZE8 241) : int8;
        secret (@repr WORDSIZE8 113) : int8;
        secret (@repr WORDSIZE8 216) : int8;
        secret (@repr WORDSIZE8 49) : int8;
        secret (@repr WORDSIZE8 21) : int8;
        secret (@repr WORDSIZE8 4) : int8;
        secret (@repr WORDSIZE8 199) : int8;
        secret (@repr WORDSIZE8 35) : int8;
        secret (@repr WORDSIZE8 195) : int8;
        secret (@repr WORDSIZE8 24) : int8;
        secret (@repr WORDSIZE8 150) : int8;
        secret (@repr WORDSIZE8 5) : int8;
        secret (@repr WORDSIZE8 154) : int8;
        secret (@repr WORDSIZE8 7) : int8;
        secret (@repr WORDSIZE8 18) : int8;
        secret (@repr WORDSIZE8 128) : int8;
        secret (@repr WORDSIZE8 226) : int8;
        secret (@repr WORDSIZE8 235) : int8;
        secret (@repr WORDSIZE8 39) : int8;
        secret (@repr WORDSIZE8 178) : int8;
        secret (@repr WORDSIZE8 117) : int8;
        secret (@repr WORDSIZE8 9) : int8;
        secret (@repr WORDSIZE8 131) : int8;
        secret (@repr WORDSIZE8 44) : int8;
        secret (@repr WORDSIZE8 26) : int8;
        secret (@repr WORDSIZE8 27) : int8;
        secret (@repr WORDSIZE8 110) : int8;
        secret (@repr WORDSIZE8 90) : int8;
        secret (@repr WORDSIZE8 160) : int8;
        secret (@repr WORDSIZE8 82) : int8;
        secret (@repr WORDSIZE8 59) : int8;
        secret (@repr WORDSIZE8 214) : int8;
        secret (@repr WORDSIZE8 179) : int8;
        secret (@repr WORDSIZE8 41) : int8;
        secret (@repr WORDSIZE8 227) : int8;
        secret (@repr WORDSIZE8 47) : int8;
        secret (@repr WORDSIZE8 132) : int8;
        secret (@repr WORDSIZE8 83) : int8;
        secret (@repr WORDSIZE8 209) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 237) : int8;
        secret (@repr WORDSIZE8 32) : int8;
        secret (@repr WORDSIZE8 252) : int8;
        secret (@repr WORDSIZE8 177) : int8;
        secret (@repr WORDSIZE8 91) : int8;
        secret (@repr WORDSIZE8 106) : int8;
        secret (@repr WORDSIZE8 203) : int8;
        secret (@repr WORDSIZE8 190) : int8;
        secret (@repr WORDSIZE8 57) : int8;
        secret (@repr WORDSIZE8 74) : int8;
        secret (@repr WORDSIZE8 76) : int8;
        secret (@repr WORDSIZE8 88) : int8;
        secret (@repr WORDSIZE8 207) : int8;
        secret (@repr WORDSIZE8 208) : int8;
        secret (@repr WORDSIZE8 239) : int8;
        secret (@repr WORDSIZE8 170) : int8;
        secret (@repr WORDSIZE8 251) : int8;
        secret (@repr WORDSIZE8 67) : int8;
        secret (@repr WORDSIZE8 77) : int8;
        secret (@repr WORDSIZE8 51) : int8;
        secret (@repr WORDSIZE8 133) : int8;
        secret (@repr WORDSIZE8 69) : int8;
        secret (@repr WORDSIZE8 249) : int8;
        secret (@repr WORDSIZE8 2) : int8;
        secret (@repr WORDSIZE8 127) : int8;
        secret (@repr WORDSIZE8 80) : int8;
        secret (@repr WORDSIZE8 60) : int8;
        secret (@repr WORDSIZE8 159) : int8;
        secret (@repr WORDSIZE8 168) : int8;
        secret (@repr WORDSIZE8 81) : int8;
        secret (@repr WORDSIZE8 163) : int8;
        secret (@repr WORDSIZE8 64) : int8;
        secret (@repr WORDSIZE8 143) : int8;
        secret (@repr WORDSIZE8 146) : int8;
        secret (@repr WORDSIZE8 157) : int8;
        secret (@repr WORDSIZE8 56) : int8;
        secret (@repr WORDSIZE8 245) : int8;
        secret (@repr WORDSIZE8 188) : int8;
        secret (@repr WORDSIZE8 182) : int8;
        secret (@repr WORDSIZE8 218) : int8;
        secret (@repr WORDSIZE8 33) : int8;
        secret (@repr WORDSIZE8 16) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 243) : int8;
        secret (@repr WORDSIZE8 210) : int8;
        secret (@repr WORDSIZE8 205) : int8;
        secret (@repr WORDSIZE8 12) : int8;
        secret (@repr WORDSIZE8 19) : int8;
        secret (@repr WORDSIZE8 236) : int8;
        secret (@repr WORDSIZE8 95) : int8;
        secret (@repr WORDSIZE8 151) : int8;
        secret (@repr WORDSIZE8 68) : int8;
        secret (@repr WORDSIZE8 23) : int8;
        secret (@repr WORDSIZE8 196) : int8;
        secret (@repr WORDSIZE8 167) : int8;
        secret (@repr WORDSIZE8 126) : int8;
        secret (@repr WORDSIZE8 61) : int8;
        secret (@repr WORDSIZE8 100) : int8;
        secret (@repr WORDSIZE8 93) : int8;
        secret (@repr WORDSIZE8 25) : int8;
        secret (@repr WORDSIZE8 115) : int8;
        secret (@repr WORDSIZE8 96) : int8;
        secret (@repr WORDSIZE8 129) : int8;
        secret (@repr WORDSIZE8 79) : int8;
        secret (@repr WORDSIZE8 220) : int8;
        secret (@repr WORDSIZE8 34) : int8;
        secret (@repr WORDSIZE8 42) : int8;
        secret (@repr WORDSIZE8 144) : int8;
        secret (@repr WORDSIZE8 136) : int8;
        secret (@repr WORDSIZE8 70) : int8;
        secret (@repr WORDSIZE8 238) : int8;
        secret (@repr WORDSIZE8 184) : int8;
        secret (@repr WORDSIZE8 20) : int8;
        secret (@repr WORDSIZE8 222) : int8;
        secret (@repr WORDSIZE8 94) : int8;
        secret (@repr WORDSIZE8 11) : int8;
        secret (@repr WORDSIZE8 219) : int8;
        secret (@repr WORDSIZE8 224) : int8;
        secret (@repr WORDSIZE8 50) : int8;
        secret (@repr WORDSIZE8 58) : int8;
        secret (@repr WORDSIZE8 10) : int8;
        secret (@repr WORDSIZE8 73) : int8;
        secret (@repr WORDSIZE8 6) : int8;
        secret (@repr WORDSIZE8 36) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 194) : int8;
        secret (@repr WORDSIZE8 211) : int8;
        secret (@repr WORDSIZE8 172) : int8;
        secret (@repr WORDSIZE8 98) : int8;
        secret (@repr WORDSIZE8 145) : int8;
        secret (@repr WORDSIZE8 149) : int8;
        secret (@repr WORDSIZE8 228) : int8;
        secret (@repr WORDSIZE8 121) : int8;
        secret (@repr WORDSIZE8 231) : int8;
        secret (@repr WORDSIZE8 200) : int8;
        secret (@repr WORDSIZE8 55) : int8;
        secret (@repr WORDSIZE8 109) : int8;
        secret (@repr WORDSIZE8 141) : int8;
        secret (@repr WORDSIZE8 213) : int8;
        secret (@repr WORDSIZE8 78) : int8;
        secret (@repr WORDSIZE8 169) : int8;
        secret (@repr WORDSIZE8 108) : int8;
        secret (@repr WORDSIZE8 86) : int8;
        secret (@repr WORDSIZE8 244) : int8;
        secret (@repr WORDSIZE8 234) : int8;
        secret (@repr WORDSIZE8 101) : int8;
        secret (@repr WORDSIZE8 122) : int8;
        secret (@repr WORDSIZE8 174) : int8;
        secret (@repr WORDSIZE8 8) : int8;
        secret (@repr WORDSIZE8 186) : int8;
        secret (@repr WORDSIZE8 120) : int8;
        secret (@repr WORDSIZE8 37) : int8;
        secret (@repr WORDSIZE8 46) : int8;
        secret (@repr WORDSIZE8 28) : int8;
        secret (@repr WORDSIZE8 166) : int8;
        secret (@repr WORDSIZE8 180) : int8;
        secret (@repr WORDSIZE8 198) : int8;
        secret (@repr WORDSIZE8 232) : int8;
        secret (@repr WORDSIZE8 221) : int8;
        secret (@repr WORDSIZE8 116) : int8;
        secret (@repr WORDSIZE8 31) : int8;
        secret (@repr WORDSIZE8 75) : int8;
        secret (@repr WORDSIZE8 189) : int8;
        secret (@repr WORDSIZE8 139) : int8;
        secret (@repr WORDSIZE8 138) : int8;
        secret (@repr WORDSIZE8 112) : int8;
        secret (@repr WORDSIZE8 62) : int8;
        secret (@repr WORDSIZE8 181) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 72) : int8;
        secret (@repr WORDSIZE8 3) : int8;
        secret (@repr WORDSIZE8 246) : int8;
        secret (@repr WORDSIZE8 14) : int8;
        secret (@repr WORDSIZE8 97) : int8;
        secret (@repr WORDSIZE8 53) : int8;
        secret (@repr WORDSIZE8 87) : int8;
        secret (@repr WORDSIZE8 185) : int8;
        secret (@repr WORDSIZE8 134) : int8;
        secret (@repr WORDSIZE8 193) : int8;
        secret (@repr WORDSIZE8 29) : int8;
        secret (@repr WORDSIZE8 158) : int8;
        secret (@repr WORDSIZE8 225) : int8;
        secret (@repr WORDSIZE8 248) : int8;
        secret (@repr WORDSIZE8 152) : int8;
        secret (@repr WORDSIZE8 17) : int8;
        secret (@repr WORDSIZE8 105) : int8;
        secret (@repr WORDSIZE8 217) : int8;
        secret (@repr WORDSIZE8 142) : int8;
        secret (@repr WORDSIZE8 148) : int8;
        secret (@repr WORDSIZE8 155) : int8;
        secret (@repr WORDSIZE8 30) : int8;
        secret (@repr WORDSIZE8 135) : int8;
        secret (@repr WORDSIZE8 233) : int8;
        secret (@repr WORDSIZE8 206) : int8;
        secret (@repr WORDSIZE8 85) : int8;
        secret (@repr WORDSIZE8 40) : int8;
        secret (@repr WORDSIZE8 223) : int8;
        secret (@repr WORDSIZE8 140) : int8;
        secret (@repr WORDSIZE8 161) : int8;
        secret (@repr WORDSIZE8 137) : int8;
        secret (@repr WORDSIZE8 13) : int8;
        secret (@repr WORDSIZE8 191) : int8;
        secret (@repr WORDSIZE8 230) : int8;
        secret (@repr WORDSIZE8 66) : int8;
        secret (@repr WORDSIZE8 104) : int8;
        secret (@repr WORDSIZE8 65) : int8;
        secret (@repr WORDSIZE8 153) : int8;
        secret (@repr WORDSIZE8 45) : int8;
        secret (@repr WORDSIZE8 15) : int8;
        secret (@repr WORDSIZE8 176) : int8;
        secret (@repr WORDSIZE8 84) : int8;
        secret (@repr WORDSIZE8 187) : int8;
        secret (@repr WORDSIZE8 22) : int8
      ] in  l).

Definition rcon_v : r_con_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 141) : int8;
        secret (@repr WORDSIZE8 1) : int8;
        secret (@repr WORDSIZE8 2) : int8;
        secret (@repr WORDSIZE8 4) : int8;
        secret (@repr WORDSIZE8 8) : int8;
        secret (@repr WORDSIZE8 16) : int8;
        secret (@repr WORDSIZE8 32) : int8;
        secret (@repr WORDSIZE8 64) : int8;
        secret (@repr WORDSIZE8 128) : int8;
        secret (@repr WORDSIZE8 27) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 108) : int8;
        secret (@repr WORDSIZE8 216) : int8;
        secret (@repr WORDSIZE8 171) : int8;
        secret (@repr WORDSIZE8 77) : int8
      ] in  l).

Definition sub_bytes (state_0 : block_t)  : block_t :=
  let st_1 : block_t :=
    state_0 in 
  let st_1 :=
    foldi (usize 0) (blocksize_v) (fun i_2 st_1 =>
      let st_1 :=
        array_upd st_1 (i_2) (array_index (sbox_v) (uint8_declassify (
              array_index (state_0) (i_2)))) in 
      (st_1))
    st_1 in 
  st_1.


Definition shift_row
  (i_3 : uint_size)
  (shift_4 : uint_size)
  (state_5 : block_t)
  
  : block_t :=
  let out_6 : block_t :=
    state_5 in 
  let out_6 :=
    array_upd out_6 (i_3) (array_index (state_5) ((i_3) + ((usize 4) * ((
              shift_4) %% (usize 4))))) in 
  let out_6 :=
    array_upd out_6 ((i_3) + (usize 4)) (array_index (state_5) ((i_3) + ((
            usize 4) * (((shift_4) + (usize 1)) %% (usize 4))))) in 
  let out_6 :=
    array_upd out_6 ((i_3) + (usize 8)) (array_index (state_5) ((i_3) + ((
            usize 4) * (((shift_4) + (usize 2)) %% (usize 4))))) in 
  let out_6 :=
    array_upd out_6 ((i_3) + (usize 12)) (array_index (state_5) ((i_3) + ((
            usize 4) * (((shift_4) + (usize 3)) %% (usize 4))))) in 
  out_6.


Definition shift_rows (state_7 : block_t)  : block_t :=
  let state_8 : block_t :=
    shift_row (usize 1) (usize 1) (state_7) in 
  let state_9 : block_t :=
    shift_row (usize 2) (usize 2) (state_8) in 
  shift_row (usize 3) (usize 3) (state_9).


Definition xtime (x_10 : uint8)  : uint8 :=
  let x1_11 : uint8 :=
    (x_10) shift_left (usize 1) in 
  let x7_12 : uint8 :=
    (x_10) shift_right (usize 7) in 
  let x71_13 : uint8 :=
    (x7_12) .& (secret (@repr WORDSIZE8 1) : int8) in 
  let x711b_14 : uint8 :=
    (x71_13) .* (secret (@repr WORDSIZE8 27) : int8) in 
  (x1_11) .^ (x711b_14).


Definition mix_column (c_15 : uint_size) (state_16 : block_t)  : block_t :=
  let i0_17 : uint_size :=
    (usize 4) * (c_15) in 
  let s0_18 : uint8 :=
    array_index (state_16) (i0_17) in 
  let s1_19 : uint8 :=
    array_index (state_16) ((i0_17) + (usize 1)) in 
  let s2_20 : uint8 :=
    array_index (state_16) ((i0_17) + (usize 2)) in 
  let s3_21 : uint8 :=
    array_index (state_16) ((i0_17) + (usize 3)) in 
  let st_22 : block_t :=
    state_16 in 
  let tmp_23 : uint8 :=
    (((s0_18) .^ (s1_19)) .^ (s2_20)) .^ (s3_21) in 
  let st_22 :=
    array_upd st_22 (i0_17) (((s0_18) .^ (tmp_23)) .^ (xtime ((s0_18) .^ (
            s1_19)))) in 
  let st_22 :=
    array_upd st_22 ((i0_17) + (usize 1)) (((s1_19) .^ (tmp_23)) .^ (xtime ((
            s1_19) .^ (s2_20)))) in 
  let st_22 :=
    array_upd st_22 ((i0_17) + (usize 2)) (((s2_20) .^ (tmp_23)) .^ (xtime ((
            s2_20) .^ (s3_21)))) in 
  let st_22 :=
    array_upd st_22 ((i0_17) + (usize 3)) (((s3_21) .^ (tmp_23)) .^ (xtime ((
            s3_21) .^ (s0_18)))) in 
  st_22.


Definition mix_columns (state_24 : block_t)  : block_t :=
  let state_25 : block_t :=
    mix_column (usize 0) (state_24) in 
  let state_26 : block_t :=
    mix_column (usize 1) (state_25) in 
  let state_27 : block_t :=
    mix_column (usize 2) (state_26) in 
  mix_column (usize 3) (state_27).


Definition add_round_key
  (state_28 : block_t)
  (key_29 : round_key_t)
  
  : block_t :=
  let out_30 : block_t :=
    state_28 in 
  let out_30 :=
    foldi (usize 0) (blocksize_v) (fun i_31 out_30 =>
      let out_30 :=
        array_upd out_30 (i_31) ((array_index (out_30) (i_31)) .^ (array_index (
              key_29) (i_31))) in 
      (out_30))
    out_30 in 
  out_30.


Definition aes_enc
  (state_32 : block_t)
  (round_key_33 : round_key_t)
  
  : block_t :=
  let state_34 : block_t :=
    sub_bytes (state_32) in 
  let state_35 : block_t :=
    shift_rows (state_34) in 
  let state_36 : block_t :=
    mix_columns (state_35) in 
  add_round_key (state_36) (round_key_33).


Definition aes_enc_last
  (state_37 : block_t)
  (round_key_38 : round_key_t)
  
  : block_t :=
  let state_39 : block_t :=
    sub_bytes (state_37) in 
  let state_40 : block_t :=
    shift_rows (state_39) in 
  add_round_key (state_40) (round_key_38).


Definition rounds_aes (state_41 : block_t) (key_42 : byte_seq)  : block_t :=
  let out_43 : block_t :=
    state_41 in 
  let out_43 :=
    foldi (usize 0) (seq_num_chunks (key_42) (blocksize_v)) (fun i_44 out_43 =>
      let '(_, key_block_45) :=
        seq_get_chunk (key_42) (blocksize_v) (i_44) in 
      let out_43 :=
        aes_enc (out_43) (array_from_seq (blocksize_v) (key_block_45)) in 
      (out_43))
    out_43 in 
  out_43.


Definition block_cipher_aes
  (input_46 : block_t)
  (key_47 : byte_seq)
  (nr_48 : uint_size)
  
  : block_t :=
  let k0_49 : round_key_t :=
    array_from_slice_range (default : uint8) (blocksize_v) (key_47) ((
        usize 0,
        usize 16
      )) in 
  let k_50 : seq uint8 :=
    seq_from_slice_range (key_47) ((usize 16, (nr_48) * (usize 16))) in 
  let kn_51 : round_key_t :=
    array_from_slice (default : uint8) (blocksize_v) (key_47) ((nr_48) * (
        usize 16)) (usize 16) in 
  let state_52 : block_t :=
    add_round_key (input_46) (k0_49) in 
  let state_53 : block_t :=
    rounds_aes (state_52) (k_50) in 
  aes_enc_last (state_53) (kn_51).


Definition rotate_word (w_54 : word_t)  : word_t :=
  array_from_list uint8 (let l :=
      [
        array_index (w_54) (usize 1);
        array_index (w_54) (usize 2);
        array_index (w_54) (usize 3);
        array_index (w_54) (usize 0)
      ] in  l).


Definition slice_word (w_55 : word_t)  : word_t :=
  array_from_list uint8 (let l :=
      [
        array_index (sbox_v) (declassify_usize_from_uint8 (array_index (w_55) (
              usize 0)));
        array_index (sbox_v) (declassify_usize_from_uint8 (array_index (w_55) (
              usize 1)));
        array_index (sbox_v) (declassify_usize_from_uint8 (array_index (w_55) (
              usize 2)));
        array_index (sbox_v) (declassify_usize_from_uint8 (array_index (w_55) (
              usize 3)))
      ] in  l).


Definition aes_keygen_assist (w_56 : word_t) (rcon_57 : uint8)  : word_t :=
  let k_58 : word_t :=
    rotate_word (w_56) in 
  let k_58 :=
    slice_word (k_58) in 
  let k_58 :=
    array_upd k_58 (usize 0) ((array_index (k_58) (usize 0)) .^ (rcon_57)) in 
  k_58.


Definition key_expansion_word
  (w0_59 : word_t)
  (w1_60 : word_t)
  (i_61 : uint_size)
  (nk_62 : uint_size)
  (nr_63 : uint_size)
  
  : word_result_t :=
  let k_64 : word_t :=
    w1_60 in 
  let result_65 : (result word_t int8) :=
    @Err word_t int8 (invalid_key_expansion_index_v) in 
  let '(k_64, result_65) :=
    if (i_61) <.? ((usize 4) * ((nr_63) + (usize 1))):bool then (let '(k_64) :=
        if ((i_61) %% (nk_62)) =.? (usize 0):bool then (let k_64 :=
            aes_keygen_assist (k_64) (array_index (rcon_v) ((i_61) / (
                  nk_62))) in 
          (k_64)) else (let '(k_64) :=
            if ((nk_62) >.? (usize 6)) && (((i_61) %% (nk_62)) =.? (
                usize 4)):bool then (let k_64 :=
                slice_word (k_64) in 
              (k_64)) else ((k_64)) in 
          (k_64)) in 
      let k_64 :=
        foldi (usize 0) (usize 4) (fun i_66 k_64 =>
          let k_64 :=
            array_upd k_64 (i_66) ((array_index (k_64) (i_66)) .^ (array_index (
                  w0_59) (i_66))) in 
          (k_64))
        k_64 in 
      let result_65 :=
        @Ok word_t int8 (k_64) in 
      (k_64, result_65)) else ((k_64, result_65)) in 
  result_65.


Definition key_expansion_aes
  (key_67 : byte_seq)
  (nk_68 : uint_size)
  (nr_69 : uint_size)
  (key_schedule_length_70 : uint_size)
  (key_length_71 : uint_size)
  (iterations_72 : uint_size)
  
  : byte_seq_result_t :=
  let key_ex_73 : seq uint8 :=
    seq_new_ (default : uint8) (key_schedule_length_70) in 
  let key_ex_73 :=
    seq_update_start (key_ex_73) (key_67) in 
  let word_size_74 : uint_size :=
    key_length_71 in 
  bind (foldibnd (usize 0) to (
      iterations_72) for key_ex_73 >> (fun j_75 key_ex_73 =>
    let i_76 : uint_size :=
      (j_75) + (word_size_74) in 
    bind (key_expansion_word (array_from_slice (default : uint8) (
          key_length_v) (key_ex_73) ((usize 4) * ((i_76) - (word_size_74))) (
          usize 4)) (array_from_slice (default : uint8) (key_length_v) (
          key_ex_73) (((usize 4) * (i_76)) - (usize 4)) (usize 4)) (i_76) (
        nk_68) (nr_69)) (fun word_77 => let key_ex_73 :=
        seq_update (key_ex_73) ((usize 4) * (i_76)) (array_to_seq (word_77)) in 
      @Ok (seq uint8) int8 ((key_ex_73))))) (fun key_ex_73 =>
    @Ok byte_seq int8 (key_ex_73)).


Definition aes_encrypt_block
  (k_78 : byte_seq)
  (input_79 : block_t)
  (nk_80 : uint_size)
  (nr_81 : uint_size)
  (key_schedule_length_82 : uint_size)
  (key_length_83 : uint_size)
  (iterations_84 : uint_size)
  
  : block_result_t :=
  bind (key_expansion_aes (k_78) (nk_80) (nr_81) (key_schedule_length_82) (
      key_length_83) (iterations_84)) (fun key_ex_85 => @Ok block_t int8 (
      block_cipher_aes (input_79) (key_ex_85) (nr_81))).


Definition aes128_encrypt_block
  (k_86 : key128_t)
  (input_87 : block_t)
  
  : block_t :=
  result_unwrap (aes_encrypt_block (seq_from_seq (array_to_seq (k_86))) (
      input_87) (key_length_v) (rounds_v) (key_schedule_length_v) (
      key_length_v) (iterations_v)).


Definition aes_ctr_key_block
  (k_88 : byte_seq)
  (n_89 : aes_nonce_t)
  (c_90 : uint32)
  (nk_91 : uint_size)
  (nr_92 : uint_size)
  (key_schedule_length_93 : uint_size)
  (key_length_94 : uint_size)
  (iterations_95 : uint_size)
  
  : block_result_t :=
  let input_96 : block_t :=
    array_new_ (default : uint8) (blocksize_v) in 
  let input_96 :=
    array_update (input_96) (usize 0) (array_to_seq (n_89)) in 
  let input_96 :=
    array_update (input_96) (usize 12) (array_to_seq (uint32_to_be_bytes (
        c_90))) in 
  aes_encrypt_block (k_88) (input_96) (nk_91) (nr_92) (key_schedule_length_93) (
    key_length_94) (iterations_95).


Definition xor_block (block_97 : block_t) (key_block_98 : block_t)  : block_t :=
  let out_99 : block_t :=
    block_97 in 
  let out_99 :=
    foldi (usize 0) (blocksize_v) (fun i_100 out_99 =>
      let out_99 :=
        array_upd out_99 (i_100) ((array_index (out_99) (i_100)) .^ (
            array_index (key_block_98) (i_100))) in 
      (out_99))
    out_99 in 
  out_99.


Definition aes_counter_mode
  (key_101 : byte_seq)
  (nonce_102 : aes_nonce_t)
  (counter_103 : uint32)
  (msg_104 : byte_seq)
  (nk_105 : uint_size)
  (nr_106 : uint_size)
  (key_schedule_length_107 : uint_size)
  (key_length_108 : uint_size)
  (iterations_109 : uint_size)
  
  : byte_seq_result_t :=
  let ctr_110 : uint32 :=
    counter_103 in 
  let blocks_out_111 : seq uint8 :=
    seq_new_ (default : uint8) (seq_len (msg_104)) in 
  let n_blocks_112 : uint_size :=
    seq_num_exact_chunks (msg_104) (blocksize_v) in 
  bind (foldibnd (usize 0) to (n_blocks_112) for (ctr_110, blocks_out_111
    ) >> (fun i_113 '(ctr_110, blocks_out_111) =>
    let msg_block_114 : seq uint8 :=
      seq_get_exact_chunk (msg_104) (blocksize_v) (i_113) in 
    bind (aes_ctr_key_block (key_101) (nonce_102) (ctr_110) (nk_105) (nr_106) (
        key_schedule_length_107) (key_length_108) (iterations_109)) (
      fun key_block_115 => let blocks_out_111 :=
        seq_set_chunk (blocks_out_111) (blocksize_v) (i_113) (
          array_to_seq (xor_block (array_from_seq (blocksize_v) (
              msg_block_114)) (key_block_115))) in 
      let ctr_110 :=
        (ctr_110) .+ (secret (@repr WORDSIZE32 (1)) : int32) in 
      @Ok (uint32 '× seq uint8) int8 ((ctr_110, blocks_out_111))))) (fun '(
      ctr_110,
      blocks_out_111
    ) => let last_block_116 : seq uint8 :=
      seq_get_remainder_chunk (msg_104) (blocksize_v) in 
    let last_block_len_117 : uint_size :=
      seq_len (last_block_116) in 
    ifbnd (last_block_len_117) !=.? (usize 0) : bool
    thenbnd (let last_block_118 : block_t :=
        array_update_start (array_new_ (default : uint8) (blocksize_v)) (
          last_block_116) in 
      bind (aes_ctr_key_block (key_101) (nonce_102) (ctr_110) (nk_105) (
          nr_106) (key_schedule_length_107) (key_length_108) (iterations_109)) (
        fun key_block_119 => let blocks_out_111 :=
          seq_set_chunk (blocks_out_111) (blocksize_v) (n_blocks_112) (
            array_slice_range (xor_block (last_block_118) (key_block_119)) ((
                usize 0,
                last_block_len_117
              ))) in 
        @Ok (seq uint8) int8 ((blocks_out_111))))
    else ((blocks_out_111)) >> (fun '(blocks_out_111) =>
    @Ok byte_seq int8 (blocks_out_111))).


Definition aes128_encrypt
  (key_120 : key128_t)
  (nonce_121 : aes_nonce_t)
  (counter_122 : uint32)
  (msg_123 : byte_seq)
  
  : byte_seq :=
  result_unwrap (aes_counter_mode (seq_from_seq (array_to_seq (key_120))) (
      nonce_121) (counter_122) (msg_123) (key_length_v) (rounds_v) (
      key_schedule_length_v) (key_length_v) (iterations_v)).


Definition aes128_decrypt
  (key_124 : key128_t)
  (nonce_125 : aes_nonce_t)
  (counter_126 : uint32)
  (ctxt_127 : byte_seq)
  
  : byte_seq :=
  result_unwrap (aes_counter_mode (seq_from_seq (array_to_seq (key_124))) (
      nonce_125) (counter_126) (ctxt_127) (key_length_v) (rounds_v) (
      key_schedule_length_v) (key_length_v) (iterations_v)).


