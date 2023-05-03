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


Definition poly_key_t := nseq (uint8) (usize 32).

Definition blocksize_v : uint_size :=
  usize 16.

Definition poly_block_t := nseq (uint8) (usize 16).

Definition poly1305_tag_t := nseq (uint8) (usize 16).

Notation "'sub_block_t'" := (byte_seq) : hacspec_scope.

Notation "'block_index_t'" := (uint_size) : hacspec_scope.

Definition field_canvas_t := nseq (int8) (usize 17).
Definition field_element_t := nat_mod 0x03fffffffffffffffffffffffffffffffb.

Notation "'poly_state_t'" := ((field_element_t × field_element_t × poly_key_t
)) : hacspec_scope.

Definition n_367_loc : ChoiceEqualityLocation :=
  (uint128 ; 368%nat).
Notation "'poly1305_encode_r_inp'" :=(
  poly_block_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_encode_r_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_ENCODE_R : nat :=
  370.
Program Definition poly1305_encode_r (b_369 : poly_block_t)
  : both (CEfset ([n_367_loc])) [interface] (field_element_t) :=
  ((letbm n_367 : uint128 loc( n_367_loc ) :=
        uint128_from_le_bytes (array_from_seq (16) (
            array_to_seq (lift_to_both0 b_369))) in
      letbm n_367 loc( n_367_loc ) :=
        (lift_to_both0 n_367) .& (secret (lift_to_both0 (
              @repr U128 21267647620597763993911028882763415551))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        nat_mod_from_secret_literal (lift_to_both0 n_367))
      ) : both (CEfset ([n_367_loc])) [interface] (field_element_t)).
Fail Next Obligation.


Notation "'poly1305_encode_block_inp'" :=(
  poly_block_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_encode_block_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_ENCODE_BLOCK : nat :=
  374.
Program Definition poly1305_encode_block (b_371 : poly_block_t)
  : both (fset.fset0) [interface] (field_element_t) :=
  ((letb n_372 : uint128 :=
        uint128_from_le_bytes (array_from_seq (16) (
            array_to_seq (lift_to_both0 b_371))) in
      letb f_373 : field_element_t :=
        nat_mod_from_secret_literal (lift_to_both0 n_372) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 f_373) +% (nat_mod_pow2 (
            0x03fffffffffffffffffffffffffffffffb) (lift_to_both0 (usize 128))))
      ) : both (fset.fset0) [interface] (field_element_t)).
Fail Next Obligation.


Notation "'poly1305_encode_last_inp'" :=(
  block_index_t × sub_block_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_encode_last_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_ENCODE_LAST : nat :=
  379.
Program Definition poly1305_encode_last (pad_len_378 : block_index_t) (
    b_375 : sub_block_t)
  : both (fset.fset0) [interface] (field_element_t) :=
  ((letb n_376 : uint128 :=
        uint128_from_le_bytes (array_from_slice (default : uint8) (16) (
            lift_to_both0 b_375) (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 b_375))) in
      letb f_377 : field_element_t :=
        nat_mod_from_secret_literal (lift_to_both0 n_376) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 f_377) +% (nat_mod_pow2 (
            0x03fffffffffffffffffffffffffffffffb) ((lift_to_both0 (
                usize 8)) .* (lift_to_both0 pad_len_378))))
      ) : both (fset.fset0) [interface] (field_element_t)).
Fail Next Obligation.


Notation "'poly1305_init_inp'" :=(
  poly_key_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_init_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_INIT : nat :=
  382.
Program Definition poly1305_init (k_380 : poly_key_t)
  : both (CEfset ([n_367_loc])) [interface] (poly_state_t) :=
  ((letb r_381 : field_element_t :=
        poly1305_encode_r (array_from_slice (default : uint8) (16) (
            array_to_seq (lift_to_both0 k_380)) (lift_to_both0 (usize 0)) (
            lift_to_both0 (usize 16))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          nat_mod_zero ,
          lift_to_both0 r_381,
          lift_to_both0 k_380
        ))
      ) : both (CEfset ([n_367_loc])) [interface] (poly_state_t)).
Fail Next Obligation.


Notation "'poly1305_update_block_inp'" :=(
  poly_block_t × poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_block_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_UPDATE_BLOCK : nat :=
  388.
Program Definition poly1305_update_block (b_387 : poly_block_t) (
    st_383 : poly_state_t)
  : both (fset.fset0) [interface] (poly_state_t) :=
  ((letb '(acc_384, r_385, k_386) : (
          field_element_t '×
          field_element_t '×
          poly_key_t
        ) :=
        lift_to_both0 st_383 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          ((poly1305_encode_block (lift_to_both0 b_387)) +% (
              lift_to_both0 acc_384)) *% (lift_to_both0 r_385),
          lift_to_both0 r_385,
          lift_to_both0 k_386
        ))
      ) : both (fset.fset0) [interface] (poly_state_t)).
Fail Next Obligation.

Definition st_389_loc : ChoiceEqualityLocation :=
  ((field_element_t '× field_element_t '× poly_key_t) ; 390%nat).
Notation "'poly1305_update_blocks_inp'" :=(
  byte_seq × poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_blocks_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_UPDATE_BLOCKS : nat :=
  396.
Program Definition poly1305_update_blocks (m_392 : byte_seq) (
    st_391 : poly_state_t)
  : both (CEfset ([st_389_loc])) [interface] (poly_state_t) :=
  ((letbm st_389 : (field_element_t '× field_element_t '× poly_key_t
        ) loc( st_389_loc ) :=
        lift_to_both0 st_391 in
      letb n_blocks_393 : uint_size :=
        (seq_len (lift_to_both0 m_392)) ./ (lift_to_both0 blocksize_v) in
      letb st_389 :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 n_blocks_393) st_389 (L := (CEfset ([st_389_loc]))) (
            I := [interface]) (fun i_394 st_389 =>
            letb block_395 : poly_block_t :=
              array_from_seq (16) (seq_get_exact_chunk (lift_to_both0 m_392) (
                  lift_to_both0 blocksize_v) (lift_to_both0 i_394)) in
            letbm st_389 loc( st_389_loc ) :=
              poly1305_update_block (lift_to_both0 block_395) (
                lift_to_both0 st_389) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 st_389)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 st_389)
      ) : both (CEfset ([st_389_loc])) [interface] (poly_state_t)).
Fail Next Obligation.

Definition st_397_loc : ChoiceEqualityLocation :=
  ((field_element_t '× field_element_t '× poly_key_t) ; 398%nat).
Notation "'poly1305_update_last_inp'" :=(
  uint_size × sub_block_t × poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_last_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_UPDATE_LAST : nat :=
  405.
Program Definition poly1305_update_last (pad_len_404 : uint_size) (
    b_400 : sub_block_t) (st_399 : poly_state_t)
  : both (CEfset ([st_397_loc])) [interface] (poly_state_t) :=
  ((letbm st_397 : (field_element_t '× field_element_t '× poly_key_t
        ) loc( st_397_loc ) :=
        lift_to_both0 st_399 in
      letb '(st_397) :=
        if (seq_len (lift_to_both0 b_400)) !=.? (lift_to_both0 (
            usize 0)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([st_397_loc])) (L2 := CEfset (
            [st_397_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letb '(
              acc_401,
              r_402,
              k_403
            ) : (field_element_t '× field_element_t '× poly_key_t) :=
            lift_to_both0 st_397 in
          letbm st_397 loc( st_397_loc ) :=
            prod_b(
              ((poly1305_encode_last (lift_to_both0 pad_len_404) (
                    lift_to_both0 b_400)) +% (lift_to_both0 acc_401)) *% (
                lift_to_both0 r_402),
              lift_to_both0 r_402,
              lift_to_both0 k_403
            ) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 st_397)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 st_397)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 st_397)
      ) : both (CEfset ([st_397_loc])) [interface] (poly_state_t)).
Fail Next Obligation.


Notation "'poly1305_update_inp'" :=(
  byte_seq × poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_update_out'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_UPDATE : nat :=
  410.
Program Definition poly1305_update (m_406 : byte_seq) (st_407 : poly_state_t)
  : both (CEfset ([st_389_loc ; st_397_loc])) [interface] (poly_state_t) :=
  ((letb st_408 : (field_element_t '× field_element_t '× poly_key_t) :=
        poly1305_update_blocks (lift_to_both0 m_406) (lift_to_both0 st_407) in
      letb last_409 : seq uint8 :=
        seq_get_remainder_chunk (lift_to_both0 m_406) (
          lift_to_both0 blocksize_v) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (poly1305_update_last (
          seq_len (lift_to_both0 last_409)) (lift_to_both0 last_409) (
          lift_to_both0 st_408))
      ) : both (CEfset ([st_389_loc ; st_397_loc])) [interface] (poly_state_t)).
Fail Next Obligation.


Notation "'poly1305_finish_inp'" :=(
  poly_state_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_finish_out'" :=(
  poly1305_tag_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305_FINISH : nat :=
  417.
Program Definition poly1305_finish (st_411 : poly_state_t)
  : both (fset.fset0) [interface] (poly1305_tag_t) :=
  ((letb '(acc_412, _, k_413) : (
          field_element_t '×
          field_element_t '×
          poly_key_t
        ) :=
        lift_to_both0 st_411 in
      letb n_414 : uint128 :=
        uint128_from_le_bytes (array_from_slice (default : uint8) (16) (
            array_to_seq (lift_to_both0 k_413)) (lift_to_both0 (usize 16)) (
            lift_to_both0 (usize 16))) in
      letb aby_415 : seq uint8 :=
        nat_mod_to_byte_seq_le (lift_to_both0 acc_412) in
      letb a_416 : uint128 :=
        uint128_from_le_bytes (array_from_slice (default : uint8) (16) (
            lift_to_both0 aby_415) (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 16))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (16) (
          array_to_seq (uint128_to_le_bytes ((lift_to_both0 a_416) .+ (
              lift_to_both0 n_414)))))
      ) : both (fset.fset0) [interface] (poly1305_tag_t)).
Fail Next Obligation.

Definition st_418_loc : ChoiceEqualityLocation :=
  ((field_element_t '× field_element_t '× poly_key_t) ; 419%nat).
Notation "'poly1305_inp'" :=(
  byte_seq × poly_key_t : choice_type) (in custom pack_type at level 2).
Notation "'poly1305_out'" :=(
  poly1305_tag_t : choice_type) (in custom pack_type at level 2).
Definition POLY1305 : nat :=
  422.
Program Definition poly1305 (m_421 : byte_seq) (key_420 : poly_key_t)
  : both (CEfset (
      [n_367_loc ; st_389_loc ; st_397_loc ; st_418_loc])) [interface] (
    poly1305_tag_t) :=
  ((letbm st_418 : (field_element_t '× field_element_t '× poly_key_t
        ) loc( st_418_loc ) :=
        poly1305_init (lift_to_both0 key_420) in
      letbm st_418 loc( st_418_loc ) :=
        poly1305_update (lift_to_both0 m_421) (lift_to_both0 st_418) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (poly1305_finish (
          lift_to_both0 st_418))
      ) : both (CEfset (
        [n_367_loc ; st_389_loc ; st_397_loc ; st_418_loc])) [interface] (
      poly1305_tag_t)).
Fail Next Obligation.

