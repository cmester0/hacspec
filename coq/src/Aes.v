(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Definition blocksize : uint_size :=
  usize 16.

Definition ivsize : uint_size :=
  usize 12.

Definition key_length : uint_size :=
  usize 4.

Definition rounds : uint_size :=
  usize 10.

Definition key_schedule_length : uint_size :=
  usize 176.

Definition iterations : uint_size :=
  usize 40.

Definition invalid_key_expansion_index : int8 :=
  @repr WORDSIZE8 1.

Definition block := nseq (uint8) (blocksize).

Definition word := nseq (uint8) (key_length).

Definition round_key := nseq (uint8) (blocksize).

Definition aes_nonce := nseq (uint8) (ivsize).

Definition s_box := nseq (uint8) (usize 256).

Definition r_con := nseq (uint8) (usize 15).

Definition bytes144 := nseq (uint8) (usize 144).

Definition bytes176 := nseq (uint8) (key_schedule_length).

Definition key128 := nseq (uint8) (blocksize).

Notation "'byte_seq_result'" := ((result byte_seq int8)) : hacspec_scope.

Notation "'block_result'" := ((result block int8)) : hacspec_scope.

Notation "'word_result'" := ((result word int8)) : hacspec_scope.

Definition sbox : s_box :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 99);
        secret (@repr WORDSIZE8 124);
        secret (@repr WORDSIZE8 119);
        secret (@repr WORDSIZE8 123);
        secret (@repr WORDSIZE8 242);
        secret (@repr WORDSIZE8 107);
        secret (@repr WORDSIZE8 111);
        secret (@repr WORDSIZE8 197);
        secret (@repr WORDSIZE8 48);
        secret (@repr WORDSIZE8 1);
        secret (@repr WORDSIZE8 103);
        secret (@repr WORDSIZE8 43);
        secret (@repr WORDSIZE8 254);
        secret (@repr WORDSIZE8 215);
        secret (@repr WORDSIZE8 171);
        secret (@repr WORDSIZE8 118);
        secret (@repr WORDSIZE8 202);
        secret (@repr WORDSIZE8 130);
        secret (@repr WORDSIZE8 201);
        secret (@repr WORDSIZE8 125);
        secret (@repr WORDSIZE8 250);
        secret (@repr WORDSIZE8 89);
        secret (@repr WORDSIZE8 71);
        secret (@repr WORDSIZE8 240);
        secret (@repr WORDSIZE8 173);
        secret (@repr WORDSIZE8 212);
        secret (@repr WORDSIZE8 162);
        secret (@repr WORDSIZE8 175);
        secret (@repr WORDSIZE8 156);
        secret (@repr WORDSIZE8 164);
        secret (@repr WORDSIZE8 114);
        secret (@repr WORDSIZE8 192);
        secret (@repr WORDSIZE8 183);
        secret (@repr WORDSIZE8 253);
        secret (@repr WORDSIZE8 147);
        secret (@repr WORDSIZE8 38);
        secret (@repr WORDSIZE8 54);
        secret (@repr WORDSIZE8 63);
        secret (@repr WORDSIZE8 247);
        secret (@repr WORDSIZE8 204);
        secret (@repr WORDSIZE8 52);
        secret (@repr WORDSIZE8 165);
        secret (@repr WORDSIZE8 229);
        secret (@repr WORDSIZE8 241);
        secret (@repr WORDSIZE8 113);
        secret (@repr WORDSIZE8 216);
        secret (@repr WORDSIZE8 49);
        secret (@repr WORDSIZE8 21);
        secret (@repr WORDSIZE8 4);
        secret (@repr WORDSIZE8 199);
        secret (@repr WORDSIZE8 35);
        secret (@repr WORDSIZE8 195);
        secret (@repr WORDSIZE8 24);
        secret (@repr WORDSIZE8 150);
        secret (@repr WORDSIZE8 5);
        secret (@repr WORDSIZE8 154);
        secret (@repr WORDSIZE8 7);
        secret (@repr WORDSIZE8 18);
        secret (@repr WORDSIZE8 128);
        secret (@repr WORDSIZE8 226);
        secret (@repr WORDSIZE8 235);
        secret (@repr WORDSIZE8 39);
        secret (@repr WORDSIZE8 178);
        secret (@repr WORDSIZE8 117);
        secret (@repr WORDSIZE8 9);
        secret (@repr WORDSIZE8 131);
        secret (@repr WORDSIZE8 44);
        secret (@repr WORDSIZE8 26);
        secret (@repr WORDSIZE8 27);
        secret (@repr WORDSIZE8 110);
        secret (@repr WORDSIZE8 90);
        secret (@repr WORDSIZE8 160);
        secret (@repr WORDSIZE8 82);
        secret (@repr WORDSIZE8 59);
        secret (@repr WORDSIZE8 214);
        secret (@repr WORDSIZE8 179);
        secret (@repr WORDSIZE8 41);
        secret (@repr WORDSIZE8 227);
        secret (@repr WORDSIZE8 47);
        secret (@repr WORDSIZE8 132);
        secret (@repr WORDSIZE8 83);
        secret (@repr WORDSIZE8 209);
        secret (@repr WORDSIZE8 0);
        secret (@repr WORDSIZE8 237);
        secret (@repr WORDSIZE8 32);
        secret (@repr WORDSIZE8 252);
        secret (@repr WORDSIZE8 177);
        secret (@repr WORDSIZE8 91);
        secret (@repr WORDSIZE8 106);
        secret (@repr WORDSIZE8 203);
        secret (@repr WORDSIZE8 190);
        secret (@repr WORDSIZE8 57);
        secret (@repr WORDSIZE8 74);
        secret (@repr WORDSIZE8 76);
        secret (@repr WORDSIZE8 88);
        secret (@repr WORDSIZE8 207);
        secret (@repr WORDSIZE8 208);
        secret (@repr WORDSIZE8 239);
        secret (@repr WORDSIZE8 170);
        secret (@repr WORDSIZE8 251);
        secret (@repr WORDSIZE8 67);
        secret (@repr WORDSIZE8 77);
        secret (@repr WORDSIZE8 51);
        secret (@repr WORDSIZE8 133);
        secret (@repr WORDSIZE8 69);
        secret (@repr WORDSIZE8 249);
        secret (@repr WORDSIZE8 2);
        secret (@repr WORDSIZE8 127);
        secret (@repr WORDSIZE8 80);
        secret (@repr WORDSIZE8 60);
        secret (@repr WORDSIZE8 159);
        secret (@repr WORDSIZE8 168);
        secret (@repr WORDSIZE8 81);
        secret (@repr WORDSIZE8 163);
        secret (@repr WORDSIZE8 64);
        secret (@repr WORDSIZE8 143);
        secret (@repr WORDSIZE8 146);
        secret (@repr WORDSIZE8 157);
        secret (@repr WORDSIZE8 56);
        secret (@repr WORDSIZE8 245);
        secret (@repr WORDSIZE8 188);
        secret (@repr WORDSIZE8 182);
        secret (@repr WORDSIZE8 218);
        secret (@repr WORDSIZE8 33);
        secret (@repr WORDSIZE8 16);
        secret (@repr WORDSIZE8 255);
        secret (@repr WORDSIZE8 243);
        secret (@repr WORDSIZE8 210);
        secret (@repr WORDSIZE8 205);
        secret (@repr WORDSIZE8 12);
        secret (@repr WORDSIZE8 19);
        secret (@repr WORDSIZE8 236);
        secret (@repr WORDSIZE8 95);
        secret (@repr WORDSIZE8 151);
        secret (@repr WORDSIZE8 68);
        secret (@repr WORDSIZE8 23);
        secret (@repr WORDSIZE8 196);
        secret (@repr WORDSIZE8 167);
        secret (@repr WORDSIZE8 126);
        secret (@repr WORDSIZE8 61);
        secret (@repr WORDSIZE8 100);
        secret (@repr WORDSIZE8 93);
        secret (@repr WORDSIZE8 25);
        secret (@repr WORDSIZE8 115);
        secret (@repr WORDSIZE8 96);
        secret (@repr WORDSIZE8 129);
        secret (@repr WORDSIZE8 79);
        secret (@repr WORDSIZE8 220);
        secret (@repr WORDSIZE8 34);
        secret (@repr WORDSIZE8 42);
        secret (@repr WORDSIZE8 144);
        secret (@repr WORDSIZE8 136);
        secret (@repr WORDSIZE8 70);
        secret (@repr WORDSIZE8 238);
        secret (@repr WORDSIZE8 184);
        secret (@repr WORDSIZE8 20);
        secret (@repr WORDSIZE8 222);
        secret (@repr WORDSIZE8 94);
        secret (@repr WORDSIZE8 11);
        secret (@repr WORDSIZE8 219);
        secret (@repr WORDSIZE8 224);
        secret (@repr WORDSIZE8 50);
        secret (@repr WORDSIZE8 58);
        secret (@repr WORDSIZE8 10);
        secret (@repr WORDSIZE8 73);
        secret (@repr WORDSIZE8 6);
        secret (@repr WORDSIZE8 36);
        secret (@repr WORDSIZE8 92);
        secret (@repr WORDSIZE8 194);
        secret (@repr WORDSIZE8 211);
        secret (@repr WORDSIZE8 172);
        secret (@repr WORDSIZE8 98);
        secret (@repr WORDSIZE8 145);
        secret (@repr WORDSIZE8 149);
        secret (@repr WORDSIZE8 228);
        secret (@repr WORDSIZE8 121);
        secret (@repr WORDSIZE8 231);
        secret (@repr WORDSIZE8 200);
        secret (@repr WORDSIZE8 55);
        secret (@repr WORDSIZE8 109);
        secret (@repr WORDSIZE8 141);
        secret (@repr WORDSIZE8 213);
        secret (@repr WORDSIZE8 78);
        secret (@repr WORDSIZE8 169);
        secret (@repr WORDSIZE8 108);
        secret (@repr WORDSIZE8 86);
        secret (@repr WORDSIZE8 244);
        secret (@repr WORDSIZE8 234);
        secret (@repr WORDSIZE8 101);
        secret (@repr WORDSIZE8 122);
        secret (@repr WORDSIZE8 174);
        secret (@repr WORDSIZE8 8);
        secret (@repr WORDSIZE8 186);
        secret (@repr WORDSIZE8 120);
        secret (@repr WORDSIZE8 37);
        secret (@repr WORDSIZE8 46);
        secret (@repr WORDSIZE8 28);
        secret (@repr WORDSIZE8 166);
        secret (@repr WORDSIZE8 180);
        secret (@repr WORDSIZE8 198);
        secret (@repr WORDSIZE8 232);
        secret (@repr WORDSIZE8 221);
        secret (@repr WORDSIZE8 116);
        secret (@repr WORDSIZE8 31);
        secret (@repr WORDSIZE8 75);
        secret (@repr WORDSIZE8 189);
        secret (@repr WORDSIZE8 139);
        secret (@repr WORDSIZE8 138);
        secret (@repr WORDSIZE8 112);
        secret (@repr WORDSIZE8 62);
        secret (@repr WORDSIZE8 181);
        secret (@repr WORDSIZE8 102);
        secret (@repr WORDSIZE8 72);
        secret (@repr WORDSIZE8 3);
        secret (@repr WORDSIZE8 246);
        secret (@repr WORDSIZE8 14);
        secret (@repr WORDSIZE8 97);
        secret (@repr WORDSIZE8 53);
        secret (@repr WORDSIZE8 87);
        secret (@repr WORDSIZE8 185);
        secret (@repr WORDSIZE8 134);
        secret (@repr WORDSIZE8 193);
        secret (@repr WORDSIZE8 29);
        secret (@repr WORDSIZE8 158);
        secret (@repr WORDSIZE8 225);
        secret (@repr WORDSIZE8 248);
        secret (@repr WORDSIZE8 152);
        secret (@repr WORDSIZE8 17);
        secret (@repr WORDSIZE8 105);
        secret (@repr WORDSIZE8 217);
        secret (@repr WORDSIZE8 142);
        secret (@repr WORDSIZE8 148);
        secret (@repr WORDSIZE8 155);
        secret (@repr WORDSIZE8 30);
        secret (@repr WORDSIZE8 135);
        secret (@repr WORDSIZE8 233);
        secret (@repr WORDSIZE8 206);
        secret (@repr WORDSIZE8 85);
        secret (@repr WORDSIZE8 40);
        secret (@repr WORDSIZE8 223);
        secret (@repr WORDSIZE8 140);
        secret (@repr WORDSIZE8 161);
        secret (@repr WORDSIZE8 137);
        secret (@repr WORDSIZE8 13);
        secret (@repr WORDSIZE8 191);
        secret (@repr WORDSIZE8 230);
        secret (@repr WORDSIZE8 66);
        secret (@repr WORDSIZE8 104);
        secret (@repr WORDSIZE8 65);
        secret (@repr WORDSIZE8 153);
        secret (@repr WORDSIZE8 45);
        secret (@repr WORDSIZE8 15);
        secret (@repr WORDSIZE8 176);
        secret (@repr WORDSIZE8 84);
        secret (@repr WORDSIZE8 187);
        secret (@repr WORDSIZE8 22)
      ] in  l).

Definition rcon : r_con :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 141);
        secret (@repr WORDSIZE8 1);
        secret (@repr WORDSIZE8 2);
        secret (@repr WORDSIZE8 4);
        secret (@repr WORDSIZE8 8);
        secret (@repr WORDSIZE8 16);
        secret (@repr WORDSIZE8 32);
        secret (@repr WORDSIZE8 64);
        secret (@repr WORDSIZE8 128);
        secret (@repr WORDSIZE8 27);
        secret (@repr WORDSIZE8 54);
        secret (@repr WORDSIZE8 108);
        secret (@repr WORDSIZE8 216);
        secret (@repr WORDSIZE8 171);
        secret (@repr WORDSIZE8 77)
      ] in  l).

Definition sub_bytes (state_0 : block) : block :=
  let st_1 : block :=
    state_0 in 
  let st_1 :=
    foldi (usize 0) (blocksize) (fun i_2 st_1 =>
      let st_1 :=
        array_upd st_1 (i_2) (array_index (sbox) (uint8_declassify (
              array_index (state_0) (i_2)))) in 
      (st_1))
    st_1 in 
  st_1.

Definition shift_row
  (i_3 : uint_size)
  (shift_4 : uint_size)
  (state_5 : block)
  : block :=
  let out_6 : block :=
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

Definition shift_rows (state_7 : block) : block :=
  let state_8 : block :=
    shift_row (usize 1) (usize 1) (state_7) in 
  let state_9 : block :=
    shift_row (usize 2) (usize 2) (state_8) in 
  shift_row (usize 3) (usize 3) (state_9).

Definition xtime (x_10 : uint8) : uint8 :=
  let x1_11 : uint8 :=
    (x_10) shift_left (usize 1) in 
  let x7_12 : uint8 :=
    (x_10) shift_right (usize 7) in 
  let x71_13 : uint8 :=
    (x7_12) .& (secret (@repr WORDSIZE8 1)) in 
  let x711b_14 : uint8 :=
    (x71_13) .* (secret (@repr WORDSIZE8 27)) in 
  (x1_11) .^ (x711b_14).

Definition mix_column (c_15 : uint_size) (state_16 : block) : block :=
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
  let st_22 : block :=
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

Definition mix_columns (state_24 : block) : block :=
  let state_25 : block :=
    mix_column (usize 0) (state_24) in 
  let state_26 : block :=
    mix_column (usize 1) (state_25) in 
  let state_27 : block :=
    mix_column (usize 2) (state_26) in 
  mix_column (usize 3) (state_27).

Definition add_round_key (state_28 : block) (key_29 : round_key) : block :=
  let out_30 : block :=
    state_28 in 
  let out_30 :=
    foldi (usize 0) (blocksize) (fun i_31 out_30 =>
      let out_30 :=
        array_upd out_30 (i_31) ((array_index (out_30) (i_31)) .^ (array_index (
              key_29) (i_31))) in 
      (out_30))
    out_30 in 
  out_30.

Definition aes_enc (state_32 : block) (round_key_33 : round_key) : block :=
  let state_34 : block :=
    sub_bytes (state_32) in 
  let state_35 : block :=
    shift_rows (state_34) in 
  let state_36 : block :=
    mix_columns (state_35) in 
  add_round_key (state_36) (round_key_33).

Definition aes_enc_last (state_37 : block) (round_key_38 : round_key) : block :=
  let state_39 : block :=
    sub_bytes (state_37) in 
  let state_40 : block :=
    shift_rows (state_39) in 
  add_round_key (state_40) (round_key_38).

Definition rounds_aes (state_41 : block) (key_42 : byte_seq) : block :=
  let out_43 : block :=
    state_41 in 
  let out_43 :=
    foldi (usize 0) (seq_num_chunks (key_42) (blocksize)) (fun i_44 out_43 =>
      let '(_, key_block_45) :=
        seq_get_chunk (key_42) (blocksize) (i_44) in 
      let out_43 :=
        aes_enc (out_43) (array_from_seq (blocksize) (key_block_45)) in 
      (out_43))
    out_43 in 
  out_43.

Definition block_cipher_aes
  (input_46 : block)
  (key_47 : byte_seq)
  (nr_48 : uint_size)
  : block :=
  let k0_49 : round_key :=
    array_from_slice_range (secret (@repr WORDSIZE8 0)) (blocksize) (key_47) ((
        usize 0,
        usize 16
      )) in 
  let k_50 : seq uint8 :=
    seq_from_slice_range (key_47) ((usize 16, (nr_48) * (usize 16))) in 
  let kn_51 : round_key :=
    array_from_slice (secret (@repr WORDSIZE8 0)) (blocksize) (key_47) ((
        nr_48) * (usize 16)) (usize 16) in 
  let state_52 : block :=
    add_round_key (input_46) (k0_49) in 
  let state_53 : block :=
    rounds_aes (state_52) (k_50) in 
  aes_enc_last (state_53) (kn_51).

Definition rotate_word (w_54 : word) : word :=
  array_from_list uint8 (let l :=
      [
        array_index (w_54) (usize 1);
        array_index (w_54) (usize 2);
        array_index (w_54) (usize 3);
        array_index (w_54) (usize 0)
      ] in  l).

Definition slice_word (w_55 : word) : word :=
  array_from_list uint8 (let l :=
      [
        array_index (sbox) (declassify_usize_from_uint8 (array_index (w_55) (
              usize 0)));
        array_index (sbox) (declassify_usize_from_uint8 (array_index (w_55) (
              usize 1)));
        array_index (sbox) (declassify_usize_from_uint8 (array_index (w_55) (
              usize 2)));
        array_index (sbox) (declassify_usize_from_uint8 (array_index (w_55) (
              usize 3)))
      ] in  l).

Definition aes_keygen_assist (w_56 : word) (rcon_57 : uint8) : word :=
  let k_58 : word :=
    rotate_word (w_56) in 
  let k_58 :=
    slice_word (k_58) in 
  let k_58 :=
    array_upd k_58 (usize 0) ((array_index (k_58) (usize 0)) .^ (rcon_57)) in 
  k_58.

Definition key_expansion_word
  (w0_59 : word)
  (w1_60 : word)
  (i_61 : uint_size)
  (nk_62 : uint_size)
  (nr_63 : uint_size)
  : word_result :=
  let k_64 : word :=
    w1_60 in 
  let result_65 : (result word int8) :=
    @Err word int8 (invalid_key_expansion_index) in 
  let '(k_64, result_65) :=
    if (i_61) <.? ((usize 4) * ((nr_63) + (usize 1))):bool then (let '(k_64) :=
        if ((i_61) %% (nk_62)) =.? (usize 0):bool then (let k_64 :=
            aes_keygen_assist (k_64) (array_index (rcon) ((i_61) / (nk_62))) in 
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
        @Ok word int8 (k_64) in 
      (k_64, result_65)) else ((k_64, result_65)) in 
  result_65.

Definition key_expansion_aes
  (key_67 : byte_seq)
  (nk_68 : uint_size)
  (nr_69 : uint_size)
  (key_schedule_length_70 : uint_size)
  (key_length_71 : uint_size)
  (iterations_72 : uint_size)
  : byte_seq_result :=
  let key_ex_73 : seq uint8 :=
    seq_new_ (secret (@repr WORDSIZE8 0)) (key_schedule_length_70) in 
  let key_ex_73 :=
    seq_update_start (key_ex_73) (key_67) in 
  let word_size_74 : uint_size :=
    key_length_71 in 
  result_bind (foldibnd (usize 0) to (
      iterations_72) for key_ex_73>> (fun j_75 key_ex_73 =>
    let i_76 : uint_size :=
      (j_75) + (word_size_74) in 
    result_bind (key_expansion_word (array_from_slice (secret (
            @repr WORDSIZE8 0)) (key_length) (key_ex_73) ((usize 4) * ((
              i_76) - (word_size_74))) (usize 4)) (array_from_slice (secret (
            @repr WORDSIZE8 0)) (key_length) (key_ex_73) (((usize 4) * (
              i_76)) - (usize 4)) (usize 4)) (i_76) (nk_68) (nr_69)) (
      fun word_77 => let key_ex_73 :=
        seq_update (key_ex_73) ((usize 4) * (i_76)) (word_77) in 
      Ok ((key_ex_73))))) (fun key_ex_73 => @Ok byte_seq int8 (key_ex_73)).

Definition aes_encrypt_block
  (k_78 : byte_seq)
  (input_79 : block)
  (nk_80 : uint_size)
  (nr_81 : uint_size)
  (key_schedule_length_82 : uint_size)
  (key_length_83 : uint_size)
  (iterations_84 : uint_size)
  : block_result :=
  result_bind (key_expansion_aes (k_78) (nk_80) (nr_81) (
      key_schedule_length_82) (key_length_83) (iterations_84)) (fun key_ex_85 =>
    @Ok block int8 (block_cipher_aes (input_79) (key_ex_85) (nr_81))).
  
Definition aes128_encrypt_block (k_86 : key128) (input_87 : block) : `{match (aes_encrypt_block (seq_from_seq (k_86)) (input_87) (
      key_length) (rounds) (key_schedule_length) (key_length) (iterations)) with Ok _ => True | _ => False end} -> block :=
  (@result_unwrap _ _ (aes_encrypt_block (seq_from_seq (k_86)) (input_87) (
      key_length) (rounds) (key_schedule_length) (key_length) (iterations))).

Definition aes_ctr_key_block
  (k_88 : byte_seq)
  (n_89 : aes_nonce)
  (c_90 : uint32)
  (nk_91 : uint_size)
  (nr_92 : uint_size)
  (key_schedule_length_93 : uint_size)
  (key_length_94 : uint_size)
  (iterations_95 : uint_size)
  : block_result :=
  let input_96 : block :=
    array_new_ (secret (@repr WORDSIZE8 0)) (blocksize) in 
  let input_96 :=
    array_update (input_96) (usize 0) (n_89) in 
  let input_96 :=
    array_update (input_96) (usize 12) (uint32_to_be_bytes (c_90)) in 
  aes_encrypt_block (k_88) (input_96) (nk_91) (nr_92) (key_schedule_length_93) (
    key_length_94) (iterations_95).

Definition xor_block (block_97 : block) (key_block_98 : block) : block :=
  let out_99 : block :=
    block_97 in 
  let out_99 :=
    foldi (usize 0) (blocksize) (fun i_100 out_99 =>
      let out_99 :=
        array_upd out_99 (i_100) ((array_index (out_99) (i_100)) .^ (
            array_index (key_block_98) (i_100))) in 
      (out_99))
    out_99 in 
  out_99.

Definition aes_counter_mode
  (key_101 : byte_seq)
  (nonce_102 : aes_nonce)
  (counter_103 : uint32)
  (msg_104 : byte_seq)
  (nk_105 : uint_size)
  (nr_106 : uint_size)
  (key_schedule_length_107 : uint_size)
  (key_length_108 : uint_size)
  (iterations_109 : uint_size)
  : byte_seq_result :=
  let ctr_110 : uint32 :=
    counter_103 in 
  let blocks_out_111 : seq uint8 :=
    seq_new_ (secret (@repr WORDSIZE8 0)) (seq_len (msg_104)) in 
  let n_blocks_112 : uint_size :=
    seq_num_exact_chunks (msg_104) (blocksize) in 
  result_bind (foldibnd (usize 0) to (n_blocks_112) for (ctr_110, blocks_out_111
    )>> (fun i_113 '(ctr_110, blocks_out_111) =>
    let msg_block_114 : seq uint8 :=
      seq_get_exact_chunk (msg_104) (blocksize) (i_113) in 
    result_bind (aes_ctr_key_block (key_101) (nonce_102) (ctr_110) (nk_105) (
        nr_106) (key_schedule_length_107) (key_length_108) (iterations_109)) (
      fun key_block_115 => let blocks_out_111 :=
        seq_set_chunk (blocks_out_111) (blocksize) (i_113) (xor_block (
            array_from_seq (blocksize) (msg_block_114)) (key_block_115)) in 
      let ctr_110 :=
        (ctr_110) .+ (secret (@repr WORDSIZE32 1)) in 
      Ok ((ctr_110, blocks_out_111))))) (fun '(ctr_110, blocks_out_111) =>
    let last_block_116 : seq uint8 :=
      seq_get_remainder_chunk (msg_104) (blocksize) in 
    let last_block_len_117 : uint_size :=
      seq_len (last_block_116) in 
    ifbnd (last_block_len_117) !=.? (usize 0) : bool
    thenbnd (let last_block_118 : block :=
        array_update_start (array_new_ (secret (@repr WORDSIZE8 0)) (
            blocksize)) (last_block_116) in 
      result_bind (aes_ctr_key_block (key_101) (nonce_102) (ctr_110) (nk_105) (
          nr_106) (key_schedule_length_107) (key_length_108) (iterations_109)) (
        fun key_block_119 => let blocks_out_111 :=
          seq_set_chunk (blocks_out_111) (blocksize) (n_blocks_112) (
            array_slice_range (xor_block (last_block_118) (key_block_119)) ((
                usize 0,
                last_block_len_117
              ))) in 
        Ok ((blocks_out_111))))
    else ((blocks_out_111)) >> (fun '(blocks_out_111) =>
    @Ok byte_seq int8 (blocks_out_111))).

Definition aes128_encrypt
  (key_120 : key128)
  (nonce_121 : aes_nonce)
  (counter_122 : uint32)
  (msg_123 : byte_seq)
  : byte_seq :=
  result_unwrap (aes_counter_mode (seq_from_seq (key_120)) (nonce_121) (
      counter_122) (msg_123) (key_length) (rounds) (key_schedule_length) (
      key_length) (iterations)).

Definition aes128_decrypt
  (key_124 : key128)
  (nonce_125 : aes_nonce)
  (counter_126 : uint32)
  (ctxt_127 : byte_seq)
  : byte_seq :=
  result_unwrap (aes_counter_mode (seq_from_seq (key_124)) (nonce_125) (
      counter_126) (ctxt_127) (key_length) (rounds) (key_schedule_length) (
      key_length) (iterations)).

