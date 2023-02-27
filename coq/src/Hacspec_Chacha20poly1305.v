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

Require Import Hacspec_Chacha20.
Export Hacspec_Chacha20.

Require Import Hacspec_Poly1305.
Export Hacspec_Poly1305.

Inductive error_t :=
| InvalidTag : error_t.

Notation "'cha_cha_poly_key_t'" := (cha_cha_key_t) : hacspec_scope.

Notation "'cha_cha_poly_iv_t'" := (cha_cha_iv_t) : hacspec_scope.

Notation "'byte_seq_result_t'" := ((result byte_seq error_t)) : hacspec_scope.

Definition init
  (key_258 : cha_cha_poly_key_t)
  (iv_259 : cha_cha_poly_iv_t)
  
  : poly_state_t :=
  let key_block0_260 : block_t :=
    chacha20_key_block0 (key_258) (iv_259) in 
  let poly_key_261 : poly_key_t :=
    array_from_slice (default : uint8) (32) (array_to_seq (key_block0_260)) (
      usize 0) (usize 32) in 
  poly1305_init (poly_key_261).


Definition poly1305_update_padded
  (m_262 : byte_seq)
  (st_263 : poly_state_t)
  
  : poly_state_t :=
  let st_264 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_update_blocks (m_262) (st_263) in 
  let last_265 : seq uint8 :=
    seq_get_remainder_chunk (m_262) (usize 16) in 
  poly1305_update_last (usize 16) (last_265) (st_264).


Definition finish
  (aad_len_266 : uint_size)
  (cipher_len_267 : uint_size)
  (st_268 : poly_state_t)
  
  : poly1305_tag_t :=
  let last_block_269 : poly_block_t :=
    array_new_ (default : uint8) (16) in 
  let last_block_269 :=
    array_update (last_block_269) (usize 0) (array_to_seq (uint64_to_le_bytes (
        secret (pub_u64 (aad_len_266)) : int64))) in 
  let last_block_269 :=
    array_update (last_block_269) (usize 8) (array_to_seq (uint64_to_le_bytes (
        secret (pub_u64 (cipher_len_267)) : int64))) in 
  let st_270 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_update_block (last_block_269) (st_268) in 
  poly1305_finish (st_270).


Definition chacha20_poly1305_encrypt
  (key_271 : cha_cha_poly_key_t)
  (iv_272 : cha_cha_poly_iv_t)
  (aad_273 : byte_seq)
  (msg_274 : byte_seq)
  
  : (byte_seq '× poly1305_tag_t) :=
  let cipher_text_275 : seq uint8 :=
    chacha20 (key_271) (iv_272) (@repr WORDSIZE32 (1)) (msg_274) in 
  let poly_st_276 : (field_element_t '× field_element_t '× poly_key_t) :=
    init (key_271) (iv_272) in 
  let poly_st_276 :=
    poly1305_update_padded (aad_273) (poly_st_276) in 
  let poly_st_276 :=
    poly1305_update_padded (cipher_text_275) (poly_st_276) in 
  let tag_277 : poly1305_tag_t :=
    finish (seq_len (aad_273)) (seq_len (cipher_text_275)) (poly_st_276) in 
  (cipher_text_275, tag_277).


Definition chacha20_poly1305_decrypt
  (key_278 : cha_cha_poly_key_t)
  (iv_279 : cha_cha_poly_iv_t)
  (aad_280 : byte_seq)
  (cipher_text_281 : byte_seq)
  (tag_282 : poly1305_tag_t)
  
  : byte_seq_result_t :=
  let poly_st_283 : (field_element_t '× field_element_t '× poly_key_t) :=
    init (key_278) (iv_279) in 
  let poly_st_283 :=
    poly1305_update_padded (aad_280) (poly_st_283) in 
  let poly_st_283 :=
    poly1305_update_padded (cipher_text_281) (poly_st_283) in 
  let my_tag_284 : poly1305_tag_t :=
    finish (seq_len (aad_280)) (seq_len (cipher_text_281)) (poly_st_283) in 
  (if (array_declassify_eq (my_tag_284) (tag_282)):bool then (
      @Ok byte_seq error_t (chacha20 (key_278) (iv_279) (@repr WORDSIZE32 (1)) (
          cipher_text_281))) else (@Err byte_seq error_t (InvalidTag))).


