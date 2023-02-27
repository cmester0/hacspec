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

Definition poly_key_t := nseq (uint8) (usize 32).

Definition blocksize_v : uint_size :=
  usize 16.

Definition poly_block_t := nseq (uint8) (usize 16).

Definition poly1305_tag_t := nseq (uint8) (usize 16).

Notation "'sub_block_t'" := (byte_seq) : hacspec_scope.

Notation "'block_index_t'" := (uint_size) : hacspec_scope.

Definition field_canvas_t := nseq (int8) (17).
Definition field_element_t := nat_mod 0x03fffffffffffffffffffffffffffffffb.

Notation "'poly_state_t'" := ((
  field_element_t '×
  field_element_t '×
  poly_key_t
)) : hacspec_scope.

Definition poly1305_encode_r (b_285 : poly_block_t)  : field_element_t :=
  let n_286 : uint128 :=
    uint128_from_le_bytes (array_from_seq (16) (array_to_seq (b_285))) in 
  let n_286 :=
    (n_286) .& (secret (
        @repr WORDSIZE128 21267647620597763993911028882763415551) : int128) in 
  nat_mod_from_secret_literal (n_286).


Definition poly1305_encode_block (b_287 : poly_block_t)  : field_element_t :=
  let n_288 : uint128 :=
    uint128_from_le_bytes (array_from_seq (16) (array_to_seq (b_287))) in 
  let f_289 : field_element_t :=
    nat_mod_from_secret_literal (n_288) in 
  (f_289) +% (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (
      usize 128) : field_element_t).


Definition poly1305_encode_last
  (pad_len_290 : block_index_t)
  (b_291 : sub_block_t)
  
  : field_element_t :=
  let n_292 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default : uint8) (16) (b_291) (
        usize 0) (seq_len (b_291))) in 
  let f_293 : field_element_t :=
    nat_mod_from_secret_literal (n_292) in 
  (f_293) +% (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) * (
        pad_len_290)) : field_element_t).


Definition poly1305_init (k_294 : poly_key_t)  : poly_state_t :=
  let r_295 : field_element_t :=
    poly1305_encode_r (array_from_slice (default : uint8) (16) (
        array_to_seq (k_294)) (usize 0) (usize 16)) in 
  (nat_mod_zero , r_295, k_294).


Definition poly1305_update_block
  (b_296 : poly_block_t)
  (st_297 : poly_state_t)
  
  : poly_state_t :=
  let '(acc_298, r_299, k_300) :=
    st_297 in 
  (((poly1305_encode_block (b_296)) +% (acc_298)) *% (r_299), r_299, k_300).


Definition poly1305_update_blocks
  (m_301 : byte_seq)
  (st_302 : poly_state_t)
  
  : poly_state_t :=
  let st_303 : (field_element_t '× field_element_t '× poly_key_t) :=
    st_302 in 
  let n_blocks_304 : uint_size :=
    (seq_len (m_301)) / (blocksize_v) in 
  let st_303 :=
    foldi (usize 0) (n_blocks_304) (fun i_305 st_303 =>
      let block_306 : poly_block_t :=
        array_from_seq (16) (seq_get_exact_chunk (m_301) (blocksize_v) (
            i_305)) in 
      let st_303 :=
        poly1305_update_block (block_306) (st_303) in 
      (st_303))
    st_303 in 
  st_303.


Definition poly1305_update_last
  (pad_len_307 : uint_size)
  (b_308 : sub_block_t)
  (st_309 : poly_state_t)
  
  : poly_state_t :=
  let st_310 : (field_element_t '× field_element_t '× poly_key_t) :=
    st_309 in 
  let '(st_310) :=
    if (seq_len (b_308)) !=.? (usize 0):bool then (let '(acc_311, r_312, k_313
        ) :=
        st_310 in 
      let st_310 :=
        (
          ((poly1305_encode_last (pad_len_307) (b_308)) +% (acc_311)) *% (
            r_312),
          r_312,
          k_313
        ) in 
      (st_310)) else ((st_310)) in 
  st_310.


Definition poly1305_update
  (m_314 : byte_seq)
  (st_315 : poly_state_t)
  
  : poly_state_t :=
  let st_316 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_update_blocks (m_314) (st_315) in 
  let last_317 : seq uint8 :=
    seq_get_remainder_chunk (m_314) (blocksize_v) in 
  poly1305_update_last (seq_len (last_317)) (last_317) (st_316).


Definition poly1305_finish (st_318 : poly_state_t)  : poly1305_tag_t :=
  let '(acc_319, _, k_320) :=
    st_318 in 
  let n_321 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default : uint8) (16) (
        array_to_seq (k_320)) (usize 16) (usize 16)) in 
  let aby_322 : seq uint8 :=
    nat_mod_to_byte_seq_le (acc_319) in 
  let a_323 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default : uint8) (16) (aby_322) (
        usize 0) (usize 16)) in 
  array_from_seq (16) (array_to_seq (uint128_to_le_bytes ((a_323) .+ (n_321)))).


Definition poly1305
  (m_324 : byte_seq)
  (key_325 : poly_key_t)
  
  : poly1305_tag_t :=
  let st_326 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_init (key_325) in 
  let st_326 :=
    poly1305_update (m_324) (st_326) in 
  poly1305_finish (st_326).


