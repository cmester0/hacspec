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

Definition gf128_block_t := nseq (uint8) (blocksize_v).

Definition gf128_key_t := nseq (uint8) (blocksize_v).

Definition gf128_tag_t := nseq (uint8) (blocksize_v).

Notation "'element_t'" := (uint128) : hacspec_scope.

Definition irred_v : element_t :=
  secret (@repr WORDSIZE128 299076299051606071403356588563077529600) : int128.

Definition fadd (x_167 : element_t) (y_168 : element_t)  : element_t :=
  (x_167) .^ (y_168).


Definition fmul (x_169 : element_t) (y_170 : element_t)  : element_t :=
  let res_171 : element_t :=
    secret (@repr WORDSIZE128 0) : int128 in 
  let sh_172 : uint128 :=
    x_169 in 
  let '(res_171, sh_172) :=
    foldi (usize 0) (usize 128) (fun i_173 '(res_171, sh_172) =>
      let '(res_171) :=
        if (uint128_declassify ((y_170) .& ((secret (
                  @repr WORDSIZE128 1) : int128) shift_left ((usize 127) - (
                  i_173))))) !=.? (uint128_declassify (secret (
              @repr WORDSIZE128 0) : int128)):bool then (let res_171 :=
            (res_171) .^ (sh_172) in 
          (res_171)) else ((res_171)) in 
      let '(sh_172) :=
        if (uint128_declassify ((sh_172) .& (secret (
                @repr WORDSIZE128 1) : int128))) !=.? (uint128_declassify (
            secret (@repr WORDSIZE128 0) : int128)):bool then (let sh_172 :=
            ((sh_172) shift_right (usize 1)) .^ (irred_v) in 
          (sh_172)) else (let sh_172 :=
            (sh_172) shift_right (usize 1) in 
          (sh_172)) in 
      (res_171, sh_172))
    (res_171, sh_172) in 
  res_171.


Definition encode (block_174 : gf128_block_t)  : element_t :=
  uint128_from_be_bytes (array_from_seq (16) (array_to_seq (block_174))).


Definition decode (e_175 : element_t)  : gf128_block_t :=
  array_from_seq (blocksize_v) (array_to_seq (uint128_to_be_bytes (e_175))).


Definition update
  (r_176 : element_t)
  (block_177 : gf128_block_t)
  (acc_178 : element_t)
  
  : element_t :=
  fmul (fadd (encode (block_177)) (acc_178)) (r_176).


Definition poly (msg_179 : byte_seq) (r_180 : element_t)  : element_t :=
  let l_181 : uint_size :=
    seq_len (msg_179) in 
  let n_blocks_182 : uint_size :=
    (l_181) / (blocksize_v) in 
  let rem_183 : uint_size :=
    (l_181) %% (blocksize_v) in 
  let acc_184 : uint128 :=
    secret (@repr WORDSIZE128 0) : int128 in 
  let acc_184 :=
    foldi (usize 0) (n_blocks_182) (fun i_185 acc_184 =>
      let k_186 : uint_size :=
        (i_185) * (blocksize_v) in 
      let block_187 : gf128_block_t :=
        array_new_ (default : uint8) (blocksize_v) in 
      let block_187 :=
        array_update_start (block_187) (seq_slice_range (msg_179) ((
              k_186,
              (k_186) + (blocksize_v)
            ))) in 
      let acc_184 :=
        update (r_180) (block_187) (acc_184) in 
      (acc_184))
    acc_184 in 
  let '(acc_184) :=
    if (rem_183) !=.? (usize 0):bool then (let k_188 : uint_size :=
        (n_blocks_182) * (blocksize_v) in 
      let last_block_189 : gf128_block_t :=
        array_new_ (default : uint8) (blocksize_v) in 
      let last_block_189 :=
        array_update_slice (last_block_189) (usize 0) (msg_179) (k_188) (
          rem_183) in 
      let acc_184 :=
        update (r_180) (last_block_189) (acc_184) in 
      (acc_184)) else ((acc_184)) in 
  acc_184.


Definition gmac (text_190 : byte_seq) (k_191 : gf128_key_t)  : gf128_tag_t :=
  let s_192 : gf128_block_t :=
    array_new_ (default : uint8) (blocksize_v) in 
  let r_193 : uint128 :=
    encode (array_from_seq (blocksize_v) (array_to_seq (k_191))) in 
  let a_194 : uint128 :=
    poly (text_190) (r_193) in 
  array_from_seq (blocksize_v) (array_to_seq (decode (fadd (a_194) (encode (
          s_192))))).


