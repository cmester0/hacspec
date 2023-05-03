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


Notation "'ristretto_point_t'" := ((
  field_element_t ×
  field_element_t ×
  field_element_t ×
  field_element_t
)) : hacspec_scope.

Notation "'decode_result_t'" := ((
  result int8 ristretto_point_t)) : hacspec_scope.

Definition ristretto_point_encoded_t := nseq (uint8) (usize 32).

Definition byte_string_t := nseq (uint8) (usize 64).

Definition field_canvas_t := nseq (int8) (usize 32).
Definition field_element_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition scalar_canvas_t := nseq (int8) (usize 32).
Definition scalar_t :=
  nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed.

Definition decoding_error_v : int8 :=
  @repr U8 20.


Notation "'p_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'p_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition P : nat :=
  752.
Program Definition p  : both (fset.fset0) [interface] (field_element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_from_byte_seq_be (
          [
            secret (lift_to_both0 (@repr U8 127));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 237))
          ]))
      ) : both (fset.fset0) [interface] (field_element_t)).
Fail Next Obligation.


Notation "'d_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'d_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition D : nat :=
  753.
Program Definition d  : both (fset.fset0) [interface] (field_element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_from_byte_seq_be (
          [
            secret (lift_to_both0 (@repr U8 82));
            secret (lift_to_both0 (@repr U8 3));
            secret (lift_to_both0 (@repr U8 108));
            secret (lift_to_both0 (@repr U8 238));
            secret (lift_to_both0 (@repr U8 43));
            secret (lift_to_both0 (@repr U8 111));
            secret (lift_to_both0 (@repr U8 254));
            secret (lift_to_both0 (@repr U8 115));
            secret (lift_to_both0 (@repr U8 140));
            secret (lift_to_both0 (@repr U8 199));
            secret (lift_to_both0 (@repr U8 64));
            secret (lift_to_both0 (@repr U8 121));
            secret (lift_to_both0 (@repr U8 119));
            secret (lift_to_both0 (@repr U8 121));
            secret (lift_to_both0 (@repr U8 232));
            secret (lift_to_both0 (@repr U8 152));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 112));
            secret (lift_to_both0 (@repr U8 10));
            secret (lift_to_both0 (@repr U8 77));
            secret (lift_to_both0 (@repr U8 65));
            secret (lift_to_both0 (@repr U8 65));
            secret (lift_to_both0 (@repr U8 216));
            secret (lift_to_both0 (@repr U8 171));
            secret (lift_to_both0 (@repr U8 117));
            secret (lift_to_both0 (@repr U8 235));
            secret (lift_to_both0 (@repr U8 77));
            secret (lift_to_both0 (@repr U8 202));
            secret (lift_to_both0 (@repr U8 19));
            secret (lift_to_both0 (@repr U8 89));
            secret (lift_to_both0 (@repr U8 120));
            secret (lift_to_both0 (@repr U8 163))
          ]))
      ) : both (fset.fset0) [interface] (field_element_t)).
Fail Next Obligation.


Notation "'sqrt_m1_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_m1_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition SQRT_M1 : nat :=
  754.
Program Definition sqrt_m1  : both (fset.fset0) [interface] (field_element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_from_byte_seq_be (
          [
            secret (lift_to_both0 (@repr U8 43));
            secret (lift_to_both0 (@repr U8 131));
            secret (lift_to_both0 (@repr U8 36));
            secret (lift_to_both0 (@repr U8 128));
            secret (lift_to_both0 (@repr U8 79));
            secret (lift_to_both0 (@repr U8 193));
            secret (lift_to_both0 (@repr U8 223));
            secret (lift_to_both0 (@repr U8 11));
            secret (lift_to_both0 (@repr U8 43));
            secret (lift_to_both0 (@repr U8 77));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 153));
            secret (lift_to_both0 (@repr U8 61));
            secret (lift_to_both0 (@repr U8 251));
            secret (lift_to_both0 (@repr U8 215));
            secret (lift_to_both0 (@repr U8 167));
            secret (lift_to_both0 (@repr U8 47));
            secret (lift_to_both0 (@repr U8 67));
            secret (lift_to_both0 (@repr U8 24));
            secret (lift_to_both0 (@repr U8 6));
            secret (lift_to_both0 (@repr U8 173));
            secret (lift_to_both0 (@repr U8 47));
            secret (lift_to_both0 (@repr U8 228));
            secret (lift_to_both0 (@repr U8 120));
            secret (lift_to_both0 (@repr U8 196));
            secret (lift_to_both0 (@repr U8 238));
            secret (lift_to_both0 (@repr U8 27));
            secret (lift_to_both0 (@repr U8 39));
            secret (lift_to_both0 (@repr U8 74));
            secret (lift_to_both0 (@repr U8 14));
            secret (lift_to_both0 (@repr U8 160));
            secret (lift_to_both0 (@repr U8 176))
          ]))
      ) : both (fset.fset0) [interface] (field_element_t)).
Fail Next Obligation.


Notation "'invsqrt_a_minus_d_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'invsqrt_a_minus_d_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition INVSQRT_A_MINUS_D : nat :=
  755.
Program Definition invsqrt_a_minus_d 
  : both (fset.fset0) [interface] (field_element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_from_byte_seq_be (
          [
            secret (lift_to_both0 (@repr U8 120));
            secret (lift_to_both0 (@repr U8 108));
            secret (lift_to_both0 (@repr U8 137));
            secret (lift_to_both0 (@repr U8 5));
            secret (lift_to_both0 (@repr U8 207));
            secret (lift_to_both0 (@repr U8 175));
            secret (lift_to_both0 (@repr U8 252));
            secret (lift_to_both0 (@repr U8 162));
            secret (lift_to_both0 (@repr U8 22));
            secret (lift_to_both0 (@repr U8 194));
            secret (lift_to_both0 (@repr U8 123));
            secret (lift_to_both0 (@repr U8 145));
            secret (lift_to_both0 (@repr U8 254));
            secret (lift_to_both0 (@repr U8 1));
            secret (lift_to_both0 (@repr U8 216));
            secret (lift_to_both0 (@repr U8 64));
            secret (lift_to_both0 (@repr U8 157));
            secret (lift_to_both0 (@repr U8 47));
            secret (lift_to_both0 (@repr U8 22));
            secret (lift_to_both0 (@repr U8 23));
            secret (lift_to_both0 (@repr U8 90));
            secret (lift_to_both0 (@repr U8 65));
            secret (lift_to_both0 (@repr U8 114));
            secret (lift_to_both0 (@repr U8 190));
            secret (lift_to_both0 (@repr U8 153));
            secret (lift_to_both0 (@repr U8 200));
            secret (lift_to_both0 (@repr U8 253));
            secret (lift_to_both0 (@repr U8 170));
            secret (lift_to_both0 (@repr U8 128));
            secret (lift_to_both0 (@repr U8 93));
            secret (lift_to_both0 (@repr U8 64));
            secret (lift_to_both0 (@repr U8 234))
          ]))
      ) : both (fset.fset0) [interface] (field_element_t)).
Fail Next Obligation.


Notation "'sqrt_ad_minus_one_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_ad_minus_one_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition SQRT_AD_MINUS_ONE : nat :=
  756.
Program Definition sqrt_ad_minus_one 
  : both (fset.fset0) [interface] (field_element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_from_byte_seq_be (
          [
            secret (lift_to_both0 (@repr U8 55));
            secret (lift_to_both0 (@repr U8 105));
            secret (lift_to_both0 (@repr U8 49));
            secret (lift_to_both0 (@repr U8 191));
            secret (lift_to_both0 (@repr U8 43));
            secret (lift_to_both0 (@repr U8 131));
            secret (lift_to_both0 (@repr U8 72));
            secret (lift_to_both0 (@repr U8 172));
            secret (lift_to_both0 (@repr U8 15));
            secret (lift_to_both0 (@repr U8 60));
            secret (lift_to_both0 (@repr U8 252));
            secret (lift_to_both0 (@repr U8 201));
            secret (lift_to_both0 (@repr U8 49));
            secret (lift_to_both0 (@repr U8 245));
            secret (lift_to_both0 (@repr U8 209));
            secret (lift_to_both0 (@repr U8 253));
            secret (lift_to_both0 (@repr U8 175));
            secret (lift_to_both0 (@repr U8 157));
            secret (lift_to_both0 (@repr U8 142));
            secret (lift_to_both0 (@repr U8 12));
            secret (lift_to_both0 (@repr U8 27));
            secret (lift_to_both0 (@repr U8 120));
            secret (lift_to_both0 (@repr U8 84));
            secret (lift_to_both0 (@repr U8 189));
            secret (lift_to_both0 (@repr U8 126));
            secret (lift_to_both0 (@repr U8 151));
            secret (lift_to_both0 (@repr U8 246));
            secret (lift_to_both0 (@repr U8 160));
            secret (lift_to_both0 (@repr U8 73));
            secret (lift_to_both0 (@repr U8 123));
            secret (lift_to_both0 (@repr U8 46));
            secret (lift_to_both0 (@repr U8 27))
          ]))
      ) : both (fset.fset0) [interface] (field_element_t)).
Fail Next Obligation.


Notation "'one_minus_d_sq_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'one_minus_d_sq_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition ONE_MINUS_D_SQ : nat :=
  757.
Program Definition one_minus_d_sq 
  : both (fset.fset0) [interface] (field_element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_from_byte_seq_be (
          [
            secret (lift_to_both0 (@repr U8 2));
            secret (lift_to_both0 (@repr U8 144));
            secret (lift_to_both0 (@repr U8 114));
            secret (lift_to_both0 (@repr U8 168));
            secret (lift_to_both0 (@repr U8 178));
            secret (lift_to_both0 (@repr U8 179));
            secret (lift_to_both0 (@repr U8 224));
            secret (lift_to_both0 (@repr U8 215));
            secret (lift_to_both0 (@repr U8 153));
            secret (lift_to_both0 (@repr U8 148));
            secret (lift_to_both0 (@repr U8 171));
            secret (lift_to_both0 (@repr U8 221));
            secret (lift_to_both0 (@repr U8 190));
            secret (lift_to_both0 (@repr U8 112));
            secret (lift_to_both0 (@repr U8 223));
            secret (lift_to_both0 (@repr U8 228));
            secret (lift_to_both0 (@repr U8 44));
            secret (lift_to_both0 (@repr U8 129));
            secret (lift_to_both0 (@repr U8 161));
            secret (lift_to_both0 (@repr U8 56));
            secret (lift_to_both0 (@repr U8 205));
            secret (lift_to_both0 (@repr U8 94));
            secret (lift_to_both0 (@repr U8 53));
            secret (lift_to_both0 (@repr U8 15));
            secret (lift_to_both0 (@repr U8 226));
            secret (lift_to_both0 (@repr U8 124));
            secret (lift_to_both0 (@repr U8 9));
            secret (lift_to_both0 (@repr U8 193));
            secret (lift_to_both0 (@repr U8 148));
            secret (lift_to_both0 (@repr U8 95));
            secret (lift_to_both0 (@repr U8 193));
            secret (lift_to_both0 (@repr U8 118))
          ]))
      ) : both (fset.fset0) [interface] (field_element_t)).
Fail Next Obligation.


Notation "'d_minus_one_sq_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'d_minus_one_sq_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition D_MINUS_ONE_SQ : nat :=
  758.
Program Definition d_minus_one_sq 
  : both (fset.fset0) [interface] (field_element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_from_byte_seq_be (
          [
            secret (lift_to_both0 (@repr U8 89));
            secret (lift_to_both0 (@repr U8 104));
            secret (lift_to_both0 (@repr U8 179));
            secret (lift_to_both0 (@repr U8 122));
            secret (lift_to_both0 (@repr U8 246));
            secret (lift_to_both0 (@repr U8 108));
            secret (lift_to_both0 (@repr U8 34));
            secret (lift_to_both0 (@repr U8 65));
            secret (lift_to_both0 (@repr U8 76));
            secret (lift_to_both0 (@repr U8 220));
            secret (lift_to_both0 (@repr U8 211));
            secret (lift_to_both0 (@repr U8 47));
            secret (lift_to_both0 (@repr U8 82));
            secret (lift_to_both0 (@repr U8 155));
            secret (lift_to_both0 (@repr U8 78));
            secret (lift_to_both0 (@repr U8 235));
            secret (lift_to_both0 (@repr U8 210));
            secret (lift_to_both0 (@repr U8 158));
            secret (lift_to_both0 (@repr U8 74));
            secret (lift_to_both0 (@repr U8 44));
            secret (lift_to_both0 (@repr U8 176));
            secret (lift_to_both0 (@repr U8 30));
            secret (lift_to_both0 (@repr U8 25));
            secret (lift_to_both0 (@repr U8 153));
            secret (lift_to_both0 (@repr U8 49));
            secret (lift_to_both0 (@repr U8 173));
            secret (lift_to_both0 (@repr U8 90));
            secret (lift_to_both0 (@repr U8 170));
            secret (lift_to_both0 (@repr U8 68));
            secret (lift_to_both0 (@repr U8 237));
            secret (lift_to_both0 (@repr U8 77));
            secret (lift_to_both0 (@repr U8 32))
          ]))
      ) : both (fset.fset0) [interface] (field_element_t)).
Fail Next Obligation.


Notation "'base_point_encoded_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'base_point_encoded_out'" :=(
  ristretto_point_encoded_t : choice_type) (in custom pack_type at level 2).
Definition BASE_POINT_ENCODED : nat :=
  759.
Program Definition base_point_encoded 
  : both (fset.fset0) [interface] (ristretto_point_encoded_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (32) ([
            secret (lift_to_both0 (@repr U8 226));
            secret (lift_to_both0 (@repr U8 242));
            secret (lift_to_both0 (@repr U8 174));
            secret (lift_to_both0 (@repr U8 10));
            secret (lift_to_both0 (@repr U8 106));
            secret (lift_to_both0 (@repr U8 188));
            secret (lift_to_both0 (@repr U8 78));
            secret (lift_to_both0 (@repr U8 113));
            secret (lift_to_both0 (@repr U8 168));
            secret (lift_to_both0 (@repr U8 132));
            secret (lift_to_both0 (@repr U8 169));
            secret (lift_to_both0 (@repr U8 97));
            secret (lift_to_both0 (@repr U8 197));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 81));
            secret (lift_to_both0 (@repr U8 95));
            secret (lift_to_both0 (@repr U8 88));
            secret (lift_to_both0 (@repr U8 227));
            secret (lift_to_both0 (@repr U8 11));
            secret (lift_to_both0 (@repr U8 106));
            secret (lift_to_both0 (@repr U8 165));
            secret (lift_to_both0 (@repr U8 130));
            secret (lift_to_both0 (@repr U8 221));
            secret (lift_to_both0 (@repr U8 141));
            secret (lift_to_both0 (@repr U8 182));
            secret (lift_to_both0 (@repr U8 166));
            secret (lift_to_both0 (@repr U8 89));
            secret (lift_to_both0 (@repr U8 69));
            secret (lift_to_both0 (@repr U8 224));
            secret (lift_to_both0 (@repr U8 141));
            secret (lift_to_both0 (@repr U8 45));
            secret (lift_to_both0 (@repr U8 118))
          ]))
      ) : both (fset.fset0) [interface] (ristretto_point_encoded_t)).
Fail Next Obligation.


Notation "'base_point_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'base_point_out'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Definition BASE_POINT : nat :=
  760.
Program Definition base_point 
  : both (fset.fset0) [interface] (ristretto_point_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (result_unwrap (decode (
            base_point_encoded )))
      ) : both (fset.fset0) [interface] (ristretto_point_t)).
Fail Next Obligation.


Notation "'identity_point_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'identity_point_out'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Definition IDENTITY_POINT : nat :=
  761.
Program Definition identity_point 
  : both (fset.fset0) [interface] (ristretto_point_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          fe (lift_to_both0 (usize 0)),
          fe (lift_to_both0 (usize 1)),
          fe (lift_to_both0 (usize 1)),
          fe (lift_to_both0 (usize 0))
        ))
      ) : both (fset.fset0) [interface] (ristretto_point_t)).
Fail Next Obligation.


Notation "'fe_inp'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'fe_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition FE : nat :=
  763.
Program Definition fe (x_762 : uint_size)
  : both (fset.fset0) [interface] (field_element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_from_literal (
          0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
          pub_u128 (is_pure (lift_to_both0 x_762))))
      ) : both (fset.fset0) [interface] (field_element_t)).
Fail Next Obligation.

Definition res_764_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 765%nat).
Notation "'geq_p_inp'" :=(
  seq uint8 : choice_type) (in custom pack_type at level 2).
Notation "'geq_p_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition GEQ_P : nat :=
  771.
Program Definition geq_p (x_768 : seq uint8)
  : both (CEfset ([res_764_loc])) [interface] (bool_ChoiceEquality) :=
  ((letb p_seq_766 : seq uint8 :=
        [
          secret (lift_to_both0 (@repr U8 237));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 255));
          secret (lift_to_both0 (@repr U8 127))
        ] in
      letbm res_764 : bool_ChoiceEquality loc( res_764_loc ) :=
        lift_to_both0 ((true : bool_ChoiceEquality)) in
      letb res_764 :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 p_seq_766)) res_764 (L := (CEfset (
                [res_764_loc]))) (I := [interface]) (fun index_767 res_764 =>
            letb x_index_769 : int8 :=
              uint8_declassify (seq_index (x_768) (lift_to_both0 index_767)) in
            letb p_index_770 : int8 :=
              uint8_declassify (seq_index (p_seq_766) (
                  lift_to_both0 index_767)) in
            letb '(res_764) :=
              if (lift_to_both0 x_index_769) !=.? (
                lift_to_both0 p_index_770) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([res_764_loc])) (L2 := CEfset (
                  [res_764_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm res_764 loc( res_764_loc ) :=
                  (lift_to_both0 x_index_769) >.? (lift_to_both0 p_index_770) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 res_764)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 res_764)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 res_764)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 res_764)
      ) : both (CEfset ([res_764_loc])) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'is_negative_inp'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'is_negative_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition IS_NEGATIVE : nat :=
  773.
Program Definition is_negative (e_772 : field_element_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 e_772) rem (fe (lift_to_both0 (usize 2)))) =.? (fe (
            lift_to_both0 (usize 1))))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'eq_inp'" :=(
  field_element_t × field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'eq_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition EQ : nat :=
  776.
Program Definition eq (u_774 : field_element_t) (v_775 : field_element_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 u_774) =.? (lift_to_both0 v_775))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'select_inp'" :=(
  field_element_t × bool_ChoiceEquality × field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'select_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition SELECT : nat :=
  780.
Program Definition select (u_778 : field_element_t) (
    cond_777 : bool_ChoiceEquality) (v_779 : field_element_t)
  : both (fset.fset0) [interface] (field_element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (lift_to_both0 cond_777)
        then lift_to_both0 u_778
        else lift_to_both0 v_779)
      ) : both (fset.fset0) [interface] (field_element_t)).
Fail Next Obligation.


Notation "'neg_fe_inp'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'neg_fe_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition NEG_FE : nat :=
  782.
Program Definition neg_fe (u_781 : field_element_t)
  : both (fset.fset0) [interface] (field_element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((fe (lift_to_both0 (
              usize 0))) -% (lift_to_both0 u_781))
      ) : both (fset.fset0) [interface] (field_element_t)).
Fail Next Obligation.


Notation "'abs_inp'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'abs_out'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Definition ABS : nat :=
  784.
Program Definition abs (u_783 : field_element_t)
  : both (fset.fset0) [interface] (field_element_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (select (neg_fe (
            lift_to_both0 u_783)) (is_negative (lift_to_both0 u_783)) (
          lift_to_both0 u_783))
      ) : both (fset.fset0) [interface] (field_element_t)).
Fail Next Obligation.

Definition r_785_loc : ChoiceEqualityLocation :=
  (field_element_t ; 786%nat).
Notation "'sqrt_ratio_m1_inp'" :=(
  field_element_t × field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_ratio_m1_out'" :=((bool_ChoiceEquality '× field_element_t
  ) : choice_type) (in custom pack_type at level 2).
Definition SQRT_RATIO_M1 : nat :=
  797.
Program Definition sqrt_ratio_m1 (u_790 : field_element_t) (
    v_787 : field_element_t)
  : both (CEfset ([r_785_loc])) [interface] ((
      bool_ChoiceEquality '×
      field_element_t
    )) :=
  ((letb v3_788 : field_element_t :=
        (nat_mod_pow (lift_to_both0 v_787) (lift_to_both0 (@repr U128 2))) *% (
          lift_to_both0 v_787) in
      letb v7_789 : field_element_t :=
        (nat_mod_pow (lift_to_both0 v3_788) (lift_to_both0 (@repr U128 2))) *% (
          lift_to_both0 v_787) in
      letbm r_785 : field_element_t loc( r_785_loc ) :=
        ((lift_to_both0 u_790) *% (lift_to_both0 v3_788)) *% (
          nat_mod_pow_felem ((lift_to_both0 u_790) *% (lift_to_both0 v7_789)) ((
              (p ) -% (fe (lift_to_both0 (usize 5)))) /% (fe (lift_to_both0 (
                  usize 8))))) in
      letb check_791 : field_element_t :=
        (lift_to_both0 v_787) *% (nat_mod_pow (lift_to_both0 r_785) (
            lift_to_both0 (@repr U128 2))) in
      letb correct_sign_sqrt_792 : bool_ChoiceEquality :=
        eq (lift_to_both0 check_791) (lift_to_both0 u_790) in
      letb flipped_sign_sqrt_793 : bool_ChoiceEquality :=
        eq (lift_to_both0 check_791) (neg_fe (lift_to_both0 u_790)) in
      letb flipped_sign_sqrt_i_794 : bool_ChoiceEquality :=
        eq (lift_to_both0 check_791) ((neg_fe (lift_to_both0 u_790)) *% (
            sqrt_m1 )) in
      letb r_prime_795 : field_element_t :=
        (sqrt_m1 ) *% (lift_to_both0 r_785) in
      letbm r_785 loc( r_785_loc ) :=
        select (lift_to_both0 r_prime_795) ((
            lift_to_both0 flipped_sign_sqrt_793) || (
            lift_to_both0 flipped_sign_sqrt_i_794)) (lift_to_both0 r_785) in
      letbm r_785 loc( r_785_loc ) := abs (lift_to_both0 r_785) in
      letb was_square_796 : bool_ChoiceEquality :=
        (lift_to_both0 correct_sign_sqrt_792) || (
          lift_to_both0 flipped_sign_sqrt_793) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 was_square_796,
          lift_to_both0 r_785
        ))
      ) : both (CEfset ([r_785_loc])) [interface] ((
        bool_ChoiceEquality '×
        field_element_t
      ))).
Fail Next Obligation.

Definition s_798_loc : ChoiceEqualityLocation :=
  (field_element_t ; 799%nat).
Notation "'map_inp'" :=(
  field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'map_out'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Definition MAP : nat :=
  814.
Program Definition map (t_802 : field_element_t)
  : both (CEfset ([r_785_loc ; s_798_loc])) [interface] (ristretto_point_t) :=
  ((letb one_800 : field_element_t := fe (lift_to_both0 (usize 1)) in
      letb minus_one_801 : field_element_t := neg_fe (lift_to_both0 one_800) in
      letb r_803 : field_element_t :=
        (sqrt_m1 ) *% (nat_mod_pow (lift_to_both0 t_802) (lift_to_both0 (
              @repr U128 2))) in
      letb u_804 : field_element_t :=
        ((lift_to_both0 r_803) +% (lift_to_both0 one_800)) *% (
          one_minus_d_sq ) in
      letb v_805 : field_element_t :=
        ((lift_to_both0 minus_one_801) -% ((lift_to_both0 r_803) *% (d ))) *% ((
            lift_to_both0 r_803) +% (d )) in
      letb '(was_square_806, s_798) : (bool_ChoiceEquality '× field_element_t
        ) :=
        sqrt_ratio_m1 (lift_to_both0 u_804) (lift_to_both0 v_805) in
      letb s_prime_807 : field_element_t :=
        neg_fe (abs ((lift_to_both0 s_798) *% (lift_to_both0 t_802))) in
      letbm s_798 loc( s_798_loc ) :=
        select (lift_to_both0 s_798) (lift_to_both0 was_square_806) (
          lift_to_both0 s_prime_807) in
      letb c_808 : field_element_t :=
        select (lift_to_both0 minus_one_801) (lift_to_both0 was_square_806) (
          lift_to_both0 r_803) in
      letb n_809 : field_element_t :=
        (((lift_to_both0 c_808) *% ((lift_to_both0 r_803) -% (
                lift_to_both0 one_800))) *% (d_minus_one_sq )) -% (
          lift_to_both0 v_805) in
      letb w0_810 : field_element_t :=
        ((fe (lift_to_both0 (usize 2))) *% (lift_to_both0 s_798)) *% (
          lift_to_both0 v_805) in
      letb w1_811 : field_element_t :=
        (lift_to_both0 n_809) *% (sqrt_ad_minus_one ) in
      letb w2_812 : field_element_t :=
        (lift_to_both0 one_800) -% (nat_mod_pow (lift_to_both0 s_798) (
            lift_to_both0 (@repr U128 2))) in
      letb w3_813 : field_element_t :=
        (lift_to_both0 one_800) +% (nat_mod_pow (lift_to_both0 s_798) (
            lift_to_both0 (@repr U128 2))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          (lift_to_both0 w0_810) *% (lift_to_both0 w3_813),
          (lift_to_both0 w2_812) *% (lift_to_both0 w1_811),
          (lift_to_both0 w1_811) *% (lift_to_both0 w3_813),
          (lift_to_both0 w0_810) *% (lift_to_both0 w2_812)
        ))
      ) : both (CEfset ([r_785_loc ; s_798_loc])) [interface] (
      ristretto_point_t)).
Fail Next Obligation.

Definition r1_bytes_816_loc : ChoiceEqualityLocation :=
  (seq int8 ; 817%nat).
Definition r0_bytes_815_loc : ChoiceEqualityLocation :=
  (seq int8 ; 818%nat).
Notation "'one_way_map_inp'" :=(
  byte_string_t : choice_type) (in custom pack_type at level 2).
Notation "'one_way_map_out'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Definition ONE_WAY_MAP : nat :=
  826.
Program Definition one_way_map (b_819 : byte_string_t)
  : both (CEfset (
      [r_785_loc ; s_798_loc ; r0_bytes_815_loc ; r1_bytes_816_loc])) [interface] (
    ristretto_point_t) :=
  ((letb r0_bytes_820 : seq uint8 :=
        array_slice (lift_to_both0 b_819) (lift_to_both0 (usize 0)) (
          lift_to_both0 (usize 32)) in
      letb r1_bytes_821 : seq uint8 :=
        array_slice (lift_to_both0 b_819) (lift_to_both0 (usize 32)) (
          lift_to_both0 (usize 32)) in
      letbm r0_bytes_815 : seq int8 loc( r0_bytes_815_loc ) :=
        seq_declassify (lift_to_both0 r0_bytes_820) in
      letbm r1_bytes_816 : seq int8 loc( r1_bytes_816_loc ) :=
        seq_declassify (lift_to_both0 r1_bytes_821) in
      letb r0_bytes_815 : seq int8 :=
        seq_upd r0_bytes_815 (lift_to_both0 (usize 31)) (is_pure ((seq_index (
                r0_bytes_815) (lift_to_both0 (usize 31))) .% (lift_to_both0 (
                @repr U8 128)))) in
      letb r1_bytes_816 : seq int8 :=
        seq_upd r1_bytes_816 (lift_to_both0 (usize 31)) (is_pure ((seq_index (
                r1_bytes_816) (lift_to_both0 (usize 31))) .% (lift_to_both0 (
                @repr U8 128)))) in
      letb r0_822 : field_element_t :=
        nat_mod_from_public_byte_seq_le (lift_to_both0 r0_bytes_815) in
      letb r1_823 : field_element_t :=
        nat_mod_from_public_byte_seq_le (lift_to_both0 r1_bytes_816) in
      letb p1_824 : (
          field_element_t '×
          field_element_t '×
          field_element_t '×
          field_element_t
        ) :=
        map (lift_to_both0 r0_822) in
      letb p2_825 : (
          field_element_t '×
          field_element_t '×
          field_element_t '×
          field_element_t
        ) :=
        map (lift_to_both0 r1_823) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (add (
          lift_to_both0 p1_824) (lift_to_both0 p2_825))
      ) : both (CEfset (
        [r_785_loc ; s_798_loc ; r0_bytes_815_loc ; r1_bytes_816_loc])) [interface] (
      ristretto_point_t)).
Fail Next Obligation.

Definition y_827_loc : ChoiceEqualityLocation :=
  (field_element_t ; 828%nat).
Notation "'encode_inp'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_out'" :=(
  ristretto_point_encoded_t : choice_type) (in custom pack_type at level 2).
Definition ENCODE : nat :=
  848.
Program Definition encode (u_829 : ristretto_point_t)
  : both (CEfset ([r_785_loc ; y_827_loc])) [interface] (
    ristretto_point_encoded_t) :=
  ((letb '(x0_830, y0_831, z0_832, t0_833) : (
          field_element_t '×
          field_element_t '×
          field_element_t '×
          field_element_t
        ) :=
        lift_to_both0 u_829 in
      letb u1_834 : field_element_t :=
        ((lift_to_both0 z0_832) +% (lift_to_both0 y0_831)) *% ((
            lift_to_both0 z0_832) -% (lift_to_both0 y0_831)) in
      letb u2_835 : field_element_t :=
        (lift_to_both0 x0_830) *% (lift_to_both0 y0_831) in
      letb '(_, invsqrt_836) : (bool_ChoiceEquality '× field_element_t) :=
        sqrt_ratio_m1 (fe (lift_to_both0 (usize 1))) ((
            lift_to_both0 u1_834) *% (nat_mod_pow (lift_to_both0 u2_835) (
              lift_to_both0 (@repr U128 2)))) in
      letb den1_837 : field_element_t :=
        (lift_to_both0 invsqrt_836) *% (lift_to_both0 u1_834) in
      letb den2_838 : field_element_t :=
        (lift_to_both0 invsqrt_836) *% (lift_to_both0 u2_835) in
      letb z_inv_839 : field_element_t :=
        ((lift_to_both0 den1_837) *% (lift_to_both0 den2_838)) *% (
          lift_to_both0 t0_833) in
      letb ix0_840 : field_element_t := (lift_to_both0 x0_830) *% (sqrt_m1 ) in
      letb iy0_841 : field_element_t := (lift_to_both0 y0_831) *% (sqrt_m1 ) in
      letb enchanted_denominator_842 : field_element_t :=
        (lift_to_both0 den1_837) *% (invsqrt_a_minus_d ) in
      letb rotate_843 : bool_ChoiceEquality :=
        is_negative ((lift_to_both0 t0_833) *% (lift_to_both0 z_inv_839)) in
      letb x_844 : field_element_t :=
        select (lift_to_both0 iy0_841) (lift_to_both0 rotate_843) (
          lift_to_both0 x0_830) in
      letbm y_827 : field_element_t loc( y_827_loc ) :=
        select (lift_to_both0 ix0_840) (lift_to_both0 rotate_843) (
          lift_to_both0 y0_831) in
      letb z_845 : field_element_t := lift_to_both0 z0_832 in
      letb den_inv_846 : field_element_t :=
        select (lift_to_both0 enchanted_denominator_842) (
          lift_to_both0 rotate_843) (lift_to_both0 den2_838) in
      letbm y_827 loc( y_827_loc ) :=
        select (neg_fe (lift_to_both0 y_827)) (is_negative ((
              lift_to_both0 x_844) *% (lift_to_both0 z_inv_839))) (
          lift_to_both0 y_827) in
      letb s_847 : field_element_t :=
        abs ((lift_to_both0 den_inv_846) *% ((lift_to_both0 z_845) -% (
              lift_to_both0 y_827))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_update_start (
          array_new_ (default : uint8) (32)) (nat_mod_to_byte_seq_le (
            lift_to_both0 s_847)))
      ) : both (CEfset ([r_785_loc ; y_827_loc])) [interface] (
      ristretto_point_encoded_t)).
Fail Next Obligation.

Definition ret_849_loc : ChoiceEqualityLocation :=
  ((result (int8) (ristretto_point_t)) ; 850%nat).
Notation "'decode_inp'" :=(
  ristretto_point_encoded_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_out'" :=(
  decode_result_t : choice_type) (in custom pack_type at level 2).
Definition DECODE : nat :=
  866.
Program Definition decode (u_851 : ristretto_point_encoded_t)
  : both (CEfset ([res_764_loc ; r_785_loc ; ret_849_loc])) [interface] (
    decode_result_t) :=
  ((letbm ret_849 : (result (int8) (ristretto_point_t)) loc( ret_849_loc ) :=
        @Err ristretto_point_t int8 (lift_to_both0 decoding_error_v) in
      letb s_852 : field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 u_851)) in
      letb '(ret_849) :=
        if (negb (geq_p (array_to_le_bytes (lift_to_both0 u_851)))) && (negb (
            is_negative (lift_to_both0 s_852))) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [res_764_loc ; r_785_loc ; ret_849_loc])) (L2 := CEfset (
            [res_764_loc ; r_785_loc ; ret_849_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb one_853 : field_element_t := fe (lift_to_both0 (usize 1)) in
          letb ss_854 : field_element_t :=
            nat_mod_pow (lift_to_both0 s_852) (lift_to_both0 (@repr U128 2)) in
          letb u1_855 : field_element_t :=
            (lift_to_both0 one_853) -% (lift_to_both0 ss_854) in
          letb u2_856 : field_element_t :=
            (lift_to_both0 one_853) +% (lift_to_both0 ss_854) in
          letb u2_sqr_857 : field_element_t :=
            nat_mod_pow (lift_to_both0 u2_856) (lift_to_both0 (@repr U128 2)) in
          letb v_858 : field_element_t :=
            (neg_fe ((d ) *% (nat_mod_pow (lift_to_both0 u1_855) (
                    lift_to_both0 (@repr U128 2))))) -% (
              lift_to_both0 u2_sqr_857) in
          letb '(was_square_859, invsqrt_860) : (
              bool_ChoiceEquality '×
              field_element_t
            ) :=
            sqrt_ratio_m1 (lift_to_both0 one_853) ((lift_to_both0 v_858) *% (
                lift_to_both0 u2_sqr_857)) in
          letb den_x_861 : field_element_t :=
            (lift_to_both0 invsqrt_860) *% (lift_to_both0 u2_856) in
          letb den_y_862 : field_element_t :=
            ((lift_to_both0 invsqrt_860) *% (lift_to_both0 den_x_861)) *% (
              lift_to_both0 v_858) in
          letb x_863 : field_element_t :=
            abs (((lift_to_both0 s_852) +% (lift_to_both0 s_852)) *% (
                lift_to_both0 den_x_861)) in
          letb y_864 : field_element_t :=
            (lift_to_both0 u1_855) *% (lift_to_both0 den_y_862) in
          letb t_865 : field_element_t :=
            (lift_to_both0 x_863) *% (lift_to_both0 y_864) in
          letb '(ret_849) :=
            if negb (((negb (lift_to_both0 was_square_859)) || (is_negative (
                    lift_to_both0 t_865))) || ((lift_to_both0 y_864) =.? (fe (
                    lift_to_both0 (usize 0))))) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset (
                [res_764_loc ; r_785_loc ; ret_849_loc])) (L2 := CEfset (
                [res_764_loc ; r_785_loc ; ret_849_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letbm ret_849 loc( ret_849_loc ) :=
                @Ok ristretto_point_t int8 (prod_b(
                    lift_to_both0 x_863,
                    lift_to_both0 y_864,
                    lift_to_both0 one_853,
                    lift_to_both0 t_865
                  )) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 ret_849)
              )
            else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 ret_849)
             in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 ret_849)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 ret_849)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 ret_849)
      ) : both (CEfset ([res_764_loc ; r_785_loc ; ret_849_loc])) [interface] (
      decode_result_t)).
Fail Next Obligation.


Notation "'equals_inp'" :=(
  ristretto_point_t × ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'equals_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition EQUALS : nat :=
  873.
Program Definition equals (u_867 : ristretto_point_t) (
    v_870 : ristretto_point_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb '(x1_868, y1_869, _, _) : (
          field_element_t '×
          field_element_t '×
          field_element_t '×
          field_element_t
        ) :=
        lift_to_both0 u_867 in
      letb '(x2_871, y2_872, _, _) : (
          field_element_t '×
          field_element_t '×
          field_element_t '×
          field_element_t
        ) :=
        lift_to_both0 v_870 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((((
              lift_to_both0 x1_868) *% (lift_to_both0 y2_872)) =.? ((
              lift_to_both0 x2_871) *% (lift_to_both0 y1_869))) || (((
              lift_to_both0 y1_869) *% (lift_to_both0 y2_872)) =.? ((
              lift_to_both0 x1_868) *% (lift_to_both0 x2_871))))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'add_inp'" :=(
  ristretto_point_t × ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'add_out'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Definition ADD : nat :=
  896.
Program Definition add (u_874 : ristretto_point_t) (v_879 : ristretto_point_t)
  : both (fset.fset0) [interface] (ristretto_point_t) :=
  ((letb '(x1_875, y1_876, z1_877, t1_878) : (
          field_element_t '×
          field_element_t '×
          field_element_t '×
          field_element_t
        ) :=
        lift_to_both0 u_874 in
      letb '(x2_880, y2_881, z2_882, t2_883) : (
          field_element_t '×
          field_element_t '×
          field_element_t '×
          field_element_t
        ) :=
        lift_to_both0 v_879 in
      letb a_884 : field_element_t :=
        ((lift_to_both0 y1_876) -% (lift_to_both0 x1_875)) *% ((
            lift_to_both0 y2_881) +% (lift_to_both0 x2_880)) in
      letb b_885 : field_element_t :=
        ((lift_to_both0 y1_876) +% (lift_to_both0 x1_875)) *% ((
            lift_to_both0 y2_881) -% (lift_to_both0 x2_880)) in
      letb c_886 : field_element_t :=
        ((fe (lift_to_both0 (usize 2))) *% (lift_to_both0 z1_877)) *% (
          lift_to_both0 t2_883) in
      letb d_887 : field_element_t :=
        ((fe (lift_to_both0 (usize 2))) *% (lift_to_both0 t1_878)) *% (
          lift_to_both0 z2_882) in
      letb e_888 : field_element_t :=
        (lift_to_both0 d_887) +% (lift_to_both0 c_886) in
      letb f_889 : field_element_t :=
        (lift_to_both0 b_885) -% (lift_to_both0 a_884) in
      letb g_890 : field_element_t :=
        (lift_to_both0 b_885) +% (lift_to_both0 a_884) in
      letb h_891 : field_element_t :=
        (lift_to_both0 d_887) -% (lift_to_both0 c_886) in
      letb x3_892 : field_element_t :=
        (lift_to_both0 e_888) *% (lift_to_both0 f_889) in
      letb y3_893 : field_element_t :=
        (lift_to_both0 g_890) *% (lift_to_both0 h_891) in
      letb t3_894 : field_element_t :=
        (lift_to_both0 e_888) *% (lift_to_both0 h_891) in
      letb z3_895 : field_element_t :=
        (lift_to_both0 f_889) *% (lift_to_both0 g_890) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x3_892,
          lift_to_both0 y3_893,
          lift_to_both0 z3_895,
          lift_to_both0 t3_894
        ))
      ) : both (fset.fset0) [interface] (ristretto_point_t)).
Fail Next Obligation.


Notation "'neg_inp'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'neg_out'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Definition NEG : nat :=
  902.
Program Definition neg (u_897 : ristretto_point_t)
  : both (fset.fset0) [interface] (ristretto_point_t) :=
  ((letb '(x1_898, y1_899, z1_900, t1_901) : (
          field_element_t '×
          field_element_t '×
          field_element_t '×
          field_element_t
        ) :=
        lift_to_both0 u_897 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          neg_fe (lift_to_both0 x1_898),
          lift_to_both0 y1_899,
          neg_fe (lift_to_both0 z1_900),
          lift_to_both0 t1_901
        ))
      ) : both (fset.fset0) [interface] (ristretto_point_t)).
Fail Next Obligation.


Notation "'sub_inp'" :=(
  ristretto_point_t × ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'sub_out'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Definition SUB : nat :=
  905.
Program Definition sub (u_903 : ristretto_point_t) (v_904 : ristretto_point_t)
  : both (fset.fset0) [interface] (ristretto_point_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (add (
          lift_to_both0 u_903) (neg (lift_to_both0 v_904)))
      ) : both (fset.fset0) [interface] (ristretto_point_t)).
Fail Next Obligation.


Notation "'double_inp'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'double_out'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Definition DOUBLE : nat :=
  921.
Program Definition double (u_906 : ristretto_point_t)
  : both (fset.fset0) [interface] (ristretto_point_t) :=
  ((letb '(x1_907, y1_908, z1_909, _) : (
          field_element_t '×
          field_element_t '×
          field_element_t '×
          field_element_t
        ) :=
        lift_to_both0 u_906 in
      letb a_910 : field_element_t :=
        nat_mod_pow (lift_to_both0 x1_907) (lift_to_both0 (@repr U128 2)) in
      letb b_911 : field_element_t :=
        nat_mod_pow (lift_to_both0 y1_908) (lift_to_both0 (@repr U128 2)) in
      letb c_912 : field_element_t :=
        (fe (lift_to_both0 (usize 2))) *% (nat_mod_pow (lift_to_both0 z1_909) (
            lift_to_both0 (@repr U128 2))) in
      letb h_913 : field_element_t :=
        (lift_to_both0 a_910) +% (lift_to_both0 b_911) in
      letb e_914 : field_element_t :=
        (lift_to_both0 h_913) -% (nat_mod_pow ((lift_to_both0 x1_907) +% (
              lift_to_both0 y1_908)) (lift_to_both0 (@repr U128 2))) in
      letb g_915 : field_element_t :=
        (lift_to_both0 a_910) -% (lift_to_both0 b_911) in
      letb f_916 : field_element_t :=
        (lift_to_both0 c_912) +% (lift_to_both0 g_915) in
      letb x2_917 : field_element_t :=
        (lift_to_both0 e_914) *% (lift_to_both0 f_916) in
      letb y2_918 : field_element_t :=
        (lift_to_both0 g_915) *% (lift_to_both0 h_913) in
      letb t2_919 : field_element_t :=
        (lift_to_both0 e_914) *% (lift_to_both0 h_913) in
      letb z2_920 : field_element_t :=
        (lift_to_both0 f_916) *% (lift_to_both0 g_915) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x2_917,
          lift_to_both0 y2_918,
          lift_to_both0 z2_920,
          lift_to_both0 t2_919
        ))
      ) : both (fset.fset0) [interface] (ristretto_point_t)).
Fail Next Obligation.

Definition temp_923_loc : ChoiceEqualityLocation :=
  ((field_element_t '× field_element_t '× field_element_t '× field_element_t
    ) ; 924%nat).
Definition res_922_loc : ChoiceEqualityLocation :=
  ((field_element_t '× field_element_t '× field_element_t '× field_element_t
    ) ; 925%nat).
Notation "'mul_inp'" :=(
  scalar_t × ristretto_point_t : choice_type) (in custom pack_type at level 2).
Notation "'mul_out'" :=(
  ristretto_point_t : choice_type) (in custom pack_type at level 2).
Definition MUL : nat :=
  929.
Program Definition mul (k_928 : scalar_t) (p_926 : ristretto_point_t)
  : both (CEfset ([res_922_loc ; temp_923_loc])) [interface] (
    ristretto_point_t) :=
  ((letbm res_922 : (
          field_element_t '×
          field_element_t '×
          field_element_t '×
          field_element_t
        ) loc( res_922_loc ) :=
        identity_point  in
      letbm temp_923 : (
          field_element_t '×
          field_element_t '×
          field_element_t '×
          field_element_t
        ) loc( temp_923_loc ) :=
        lift_to_both0 p_926 in
      letb '(res_922, temp_923) :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 256)) prod_ce(res_922, temp_923) (L := (CEfset (
                [res_922_loc ; temp_923_loc]))) (I := [interface]) (fun i_927 '(
              res_922,
              temp_923
            ) =>
            letb '(res_922) :=
              if (nat_mod_get_bit (lift_to_both0 k_928) (
                  lift_to_both0 i_927)) =.? (nat_mod_from_literal (
                  0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed) (
                  lift_to_both0 (@repr U128 1))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([res_922_loc ; temp_923_loc])) (
                L2 := CEfset ([res_922_loc ; temp_923_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm res_922 loc( res_922_loc ) :=
                  add (lift_to_both0 res_922) (lift_to_both0 temp_923) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 res_922)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 res_922)
               in
            letbm temp_923 loc( temp_923_loc ) :=
              double (lift_to_both0 temp_923) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 res_922,
                lift_to_both0 temp_923
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 res_922)
      ) : both (CEfset ([res_922_loc ; temp_923_loc])) [interface] (
      ristretto_point_t)).
Fail Next Obligation.

