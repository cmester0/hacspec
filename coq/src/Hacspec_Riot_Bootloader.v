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

Definition riotboot_magic_v : int32 :=
  @repr WORDSIZE32 (1414482258).

Notation "'fletcher_t'" := ((int32 '× int32)) : hacspec_scope.

Definition new_fletcher   : fletcher_t :=
  (@repr WORDSIZE32 (65535), @repr WORDSIZE32 (65535)).


Definition max_chunk_size   : uint_size :=
  usize 360.


Definition reduce_u32 (x_1143 : int32)  : int32 :=
  ((x_1143) .& (@repr WORDSIZE32 (65535))) .+ ((x_1143) shift_right (
      @repr WORDSIZE32 (16))).


Definition combine (lower_1144 : int32) (upper_1145 : int32)  : int32 :=
  (lower_1144) .| ((upper_1145) shift_left (@repr WORDSIZE32 (16))).


Definition update_fletcher
  (f_1146 : fletcher_t)
  (data_1147 : seq int16)
  
  : fletcher_t :=
  let max_chunk_size_1148 : uint_size :=
    max_chunk_size  in 
  let '(a_1149, b_1150) :=
    f_1146 in 
  let '(a_1149, b_1150) :=
    foldi (usize 0) (seq_num_chunks (data_1147) (
          max_chunk_size_1148)) (fun i_1151 '(a_1149, b_1150) =>
      let '(chunk_len_1152, chunk_1153) :=
        seq_get_chunk (data_1147) (max_chunk_size_1148) (i_1151) in 
      let intermediate_a_1154 : int32 :=
        a_1149 in 
      let intermediate_b_1155 : int32 :=
        b_1150 in 
      let '(intermediate_a_1154, intermediate_b_1155) :=
        foldi (usize 0) (chunk_len_1152) (fun j_1156 '(
            intermediate_a_1154,
            intermediate_b_1155
          ) =>
          let intermediate_a_1154 :=
            (intermediate_a_1154) .+ (@cast _ uint32 _ (seq_index (chunk_1153) (
                  j_1156))) in 
          let intermediate_b_1155 :=
            (intermediate_b_1155) .+ (intermediate_a_1154) in 
          (intermediate_a_1154, intermediate_b_1155))
        (intermediate_a_1154, intermediate_b_1155) in 
      let a_1149 :=
        reduce_u32 (intermediate_a_1154) in 
      let b_1150 :=
        reduce_u32 (intermediate_b_1155) in 
      (a_1149, b_1150))
    (a_1149, b_1150) in 
  let a_1149 :=
    reduce_u32 (a_1149) in 
  let b_1150 :=
    reduce_u32 (b_1150) in 
  (a_1149, b_1150).


Definition value (x_1157 : fletcher_t)  : int32 :=
  let '(a_1158, b_1159) :=
    x_1157 in 
  combine (a_1158) (b_1159).


Notation "'header_t'" := ((int32 '× int32 '× int32 '× int32
)) : hacspec_scope.

Definition header_as_u16_slice (h_1160 : header_t)  : seq int16 :=
  let '(magic_1161, seq_number_1162, start_addr_1163, _) :=
    h_1160 in 
  let magic_1164 : u32_word_t :=
    u32_to_be_bytes (magic_1161) in 
  let seq_number_1165 : u32_word_t :=
    u32_to_be_bytes (seq_number_1162) in 
  let start_addr_1166 : u32_word_t :=
    u32_to_be_bytes (start_addr_1163) in 
  let u8_seq_1167 : seq int8 :=
    seq_new_ (default : int8) (usize 12) in 
  let u8_seq_1168 : seq int8 :=
    seq_update_slice (u8_seq_1167) (usize 0) (array_to_seq (magic_1164)) (
      usize 0) (usize 4) in 
  let u8_seq_1169 : seq int8 :=
    seq_update_slice (u8_seq_1168) (usize 4) (array_to_seq (seq_number_1165)) (
      usize 0) (usize 4) in 
  let u8_seq_1170 : seq int8 :=
    seq_update_slice (u8_seq_1169) (usize 8) (array_to_seq (start_addr_1166)) (
      usize 0) (usize 4) in 
  let u16_seq_1171 : seq int16 :=
    seq_new_ (default : int16) (usize 6) in 
  let u16_seq_1171 :=
    foldi (usize 0) (usize 3) (fun i_1172 u16_seq_1171 =>
      let u16_word_1173 : u16_word_t :=
        array_from_seq (2) (seq_slice (u8_seq_1170) ((i_1172) * (usize 4)) (
            usize 2)) in 
      let u16_value_1174 : int16 :=
        u16_from_be_bytes (u16_word_1173) in 
      let u16_seq_1171 :=
        seq_upd u16_seq_1171 (((usize 2) * (i_1172)) + (usize 1)) (
          u16_value_1174) in 
      let u16_word_1175 : u16_word_t :=
        array_from_seq (2) (seq_slice (u8_seq_1170) (((i_1172) * (usize 4)) + (
              usize 2)) (usize 2)) in 
      let u16_value_1176 : int16 :=
        u16_from_be_bytes (u16_word_1175) in 
      let u16_seq_1171 :=
        seq_upd u16_seq_1171 ((usize 2) * (i_1172)) (u16_value_1176) in 
      (u16_seq_1171))
    u16_seq_1171 in 
  u16_seq_1171.


Definition is_valid_header (h_1177 : header_t)  : bool :=
  let '(magic_number_1178, seq_number_1179, start_addr_1180, checksum_1181) :=
    h_1177 in 
  let slice_1182 : seq int16 :=
    header_as_u16_slice ((
        magic_number_1178,
        seq_number_1179,
        start_addr_1180,
        checksum_1181
      )) in 
  let result_1183 : bool :=
    false in 
  let '(result_1183) :=
    if (magic_number_1178) =.? (riotboot_magic_v):bool then (
      let fletcher_1184 : (int32 '× int32) :=
        new_fletcher  in 
      let fletcher_1185 : (int32 '× int32) :=
        update_fletcher (fletcher_1184) (slice_1182) in 
      let sum_1186 : int32 :=
        value (fletcher_1185) in 
      let result_1183 :=
        (sum_1186) =.? (checksum_1181) in 
      (result_1183)) else ((result_1183)) in 
  result_1183.


Definition choose_image (images_1187 : seq header_t)  : (bool '× int32) :=
  let image_1188 : int32 :=
    @repr WORDSIZE32 (0) in 
  let image_found_1189 : bool :=
    false in 
  let '(image_1188, image_found_1189) :=
    foldi (usize 0) (seq_len (images_1187)) (fun i_1190 '(
        image_1188,
        image_found_1189
      ) =>
      let header_1191 : (int32 '× int32 '× int32 '× int32) :=
        seq_index (images_1187) (i_1190) in 
      let '(magic_number_1192, seq_number_1193, start_addr_1194, checksum_1195
        ) :=
        header_1191 in 
      let '(image_1188, image_found_1189) :=
        if is_valid_header ((
            magic_number_1192,
            seq_number_1193,
            start_addr_1194,
            checksum_1195
          )):bool then (let change_image_1196 : bool :=
            negb ((image_found_1189) && ((seq_number_1193) <=.? (
                  image_1188))) in 
          let '(image_1188, image_found_1189) :=
            if change_image_1196:bool then (let image_1188 :=
                start_addr_1194 in 
              let image_found_1189 :=
                true in 
              (image_1188, image_found_1189)) else ((
                image_1188,
                image_found_1189
              )) in 
          (image_1188, image_found_1189)) else ((image_1188, image_found_1189
          )) in 
      (image_1188, image_found_1189))
    (image_1188, image_found_1189) in 
  (image_found_1189, image_1188).


