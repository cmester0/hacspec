(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp.word Require Import ssrZ word.
From Jasmin Require Import word.

From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.

Require Import ChoiceEquality.
Require Import LocationUtility.
Require Import Hacspec_Lib_Comparable.
Require Import Hacspec_Lib_Pre.
Require Import Hacspec_Lib.

Open Scope hacspec_scope.
Import choice.Choice.Exports.

Obligation Tactic := try timeout 8 solve_ssprove_obligations.


Require Import Hacspec_Chacha20.

Require Import Hacspec_Poly1305.

Definition error_t : ChoiceEquality :=
  unit_ChoiceEquality.
Definition InvalidTag : error_t :=
   tt.

Notation "'cha_cha_poly_key_t'" := (cha_cha_key_t) : hacspec_scope.

Notation "'cha_cha_poly_iv_t'" := (cha_cha_iv_t) : hacspec_scope.

Notation "'byte_seq_result_t'" := ((result error_t byte_seq)) : hacspec_scope.


Notation "'init_inp'" :=(
  cha_cha_poly_key_t × cha_cha_poly_iv_t : choice_type) (in custom pack_type at level 2).
Notation "'init_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition INIT : nat :=
  336.
Program Definition init (key_332 : cha_cha_poly_key_t) (
    iv_333 : cha_cha_poly_iv_t)
  : both (fset.fset0) [interface] (poly_state_t) :=
  ((letb key_block0_334 : block_t :=
        chacha20_key_block0 (lift_to_both0 key_332) (lift_to_both0 iv_333) in
      letb poly_key_335 : poly_key_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 key_block0_334)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (poly1305_init (
          lift_to_both0 poly_key_335))
      ) : both (fset.fset0) [interface] (poly_state_t)).
Fail Next Obligation.


Notation "'poly1305_update_padded_inp'" :=(
  byte_seq × poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_padded_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_UPDATE_PADDED : nat :=
  341.
Program Definition poly1305_update_padded (m_337 : byte_seq) (
    st_338 : poly_state_t)
  : both (fset.fset0) [interface] (poly_state_t) :=
  ((letb st_339 : (field_element_t '× field_element_t '× poly_key_t) :=
        poly1305_update_blocks (lift_to_both0 m_337) (lift_to_both0 st_338) in
      letb last_340 : seq uint8 :=
        seq_get_remainder_chunk (lift_to_both0 m_337) (lift_to_both0 (
            usize 16)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (poly1305_update_last (
          lift_to_both0 (usize 16)) (lift_to_both0 last_340) (
          lift_to_both0 st_339))
      ) : both (fset.fset0) [interface] (poly_state_t)).
Fail Next Obligation.

Definition last_block_342_loc : ChoiceEqualityLocation :=
  (poly_block_t ; 343%nat).
Notation "'finish_inp'" :=(
  uint_size × uint_size × poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'finish_out'" :=(
  poly1305_tag_t : choice_type) (in custom pack_type at level 2).
Definition FINISH : nat :=
  348.
Program Definition finish (aad_len_344 : uint_size) (
    cipher_len_345 : uint_size) (st_346 : poly_state_t)
  : both (CEfset ([last_block_342_loc])) [interface] (poly1305_tag_t) :=
  ((letbm last_block_342 : poly_block_t loc( last_block_342_loc ) :=
        array_new_ (default : uint8) (16) in
      letbm last_block_342 loc( last_block_342_loc ) :=
        array_update (lift_to_both0 last_block_342) (lift_to_both0 (usize 0)) (
          array_to_seq (uint64_to_le_bytes (secret (pub_u64 (is_pure (
                  lift_to_both0 aad_len_344)))))) in
      letbm last_block_342 loc( last_block_342_loc ) :=
        array_update (lift_to_both0 last_block_342) (lift_to_both0 (usize 8)) (
          array_to_seq (uint64_to_le_bytes (secret (pub_u64 (is_pure (
                  lift_to_both0 cipher_len_345)))))) in
      letb st_347 : (field_element_t '× field_element_t '× poly_key_t) :=
        poly1305_update_block (lift_to_both0 last_block_342) (
          lift_to_both0 st_346) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (poly1305_finish (
          lift_to_both0 st_347))
      ) : both (CEfset ([last_block_342_loc])) [interface] (poly1305_tag_t)).
Fail Next Obligation.

Definition poly_st_349_loc : ChoiceEqualityLocation :=
  ((field_element_t '× field_element_t '× poly_key_t) ; 350%nat).
Notation "'chacha20_poly1305_encrypt_inp'" :=(
  cha_cha_poly_key_t × cha_cha_poly_iv_t × byte_seq × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_poly1305_encrypt_out'" :=((byte_seq '× poly1305_tag_t
  ) : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_POLY1305_ENCRYPT : nat :=
  357.
Program Definition chacha20_poly1305_encrypt (key_351 : cha_cha_poly_key_t) (
    iv_352 : cha_cha_poly_iv_t) (aad_355 : byte_seq) (msg_353 : byte_seq)
  : both (CEfset ([last_block_342_loc ; poly_st_349_loc])) [interface] ((
      byte_seq '×
      poly1305_tag_t
    )) :=
  ((letb cipher_text_354 : seq uint8 :=
        chacha20 (lift_to_both0 key_351) (lift_to_both0 iv_352) (lift_to_both0 (
            @repr U32 1)) (lift_to_both0 msg_353) in
      letbm poly_st_349 : (field_element_t '× field_element_t '× poly_key_t
        ) loc( poly_st_349_loc ) :=
        init (lift_to_both0 key_351) (lift_to_both0 iv_352) in
      letbm poly_st_349 loc( poly_st_349_loc ) :=
        poly1305_update_padded (lift_to_both0 aad_355) (
          lift_to_both0 poly_st_349) in
      letbm poly_st_349 loc( poly_st_349_loc ) :=
        poly1305_update_padded (lift_to_both0 cipher_text_354) (
          lift_to_both0 poly_st_349) in
      letb tag_356 : poly1305_tag_t :=
        finish (seq_len (lift_to_both0 aad_355)) (seq_len (
            lift_to_both0 cipher_text_354)) (lift_to_both0 poly_st_349) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 cipher_text_354,
          lift_to_both0 tag_356
        ))
      ) : both (CEfset ([last_block_342_loc ; poly_st_349_loc])) [interface] ((
        byte_seq '×
        poly1305_tag_t
      ))).
Fail Next Obligation.

Definition poly_st_358_loc : ChoiceEqualityLocation :=
  ((field_element_t '× field_element_t '× poly_key_t) ; 359%nat).
Notation "'chacha20_poly1305_decrypt_inp'" :=(
  cha_cha_poly_key_t × cha_cha_poly_iv_t × byte_seq × byte_seq × poly1305_tag_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_poly1305_decrypt_out'" :=(
  byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_POLY1305_DECRYPT : nat :=
  366.
Program Definition chacha20_poly1305_decrypt (key_360 : cha_cha_poly_key_t) (
    iv_361 : cha_cha_poly_iv_t) (aad_362 : byte_seq) (
    cipher_text_363 : byte_seq) (tag_365 : poly1305_tag_t)
  : both (CEfset ([last_block_342_loc ; poly_st_358_loc])) [interface] (
    byte_seq_result_t) :=
  ((letbm poly_st_358 : (field_element_t '× field_element_t '× poly_key_t
        ) loc( poly_st_358_loc ) :=
        init (lift_to_both0 key_360) (lift_to_both0 iv_361) in
      letbm poly_st_358 loc( poly_st_358_loc ) :=
        poly1305_update_padded (lift_to_both0 aad_362) (
          lift_to_both0 poly_st_358) in
      letbm poly_st_358 loc( poly_st_358_loc ) :=
        poly1305_update_padded (lift_to_both0 cipher_text_363) (
          lift_to_both0 poly_st_358) in
      letb my_tag_364 : poly1305_tag_t :=
        finish (seq_len (lift_to_both0 aad_362)) (seq_len (
            lift_to_both0 cipher_text_363)) (lift_to_both0 poly_st_358) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (array_declassify_eq (
            lift_to_both0 my_tag_364) (lift_to_both0 tag_365))
        then @Ok byte_seq error_t (chacha20 (lift_to_both0 key_360) (
            lift_to_both0 iv_361) (lift_to_both0 (@repr U32 1)) (
            lift_to_both0 cipher_text_363))
        else @Err byte_seq error_t (InvalidTag))
      ) : both (CEfset ([last_block_342_loc ; poly_st_358_loc])) [interface] (
      byte_seq_result_t)).
Fail Next Obligation.

