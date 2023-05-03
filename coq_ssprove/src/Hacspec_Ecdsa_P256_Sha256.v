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


Require Import Hacspec_P256.

Require Import Hacspec_Sha256.

Definition error_t : ChoiceEquality :=
  unit_ChoiceEquality '+ unit_ChoiceEquality.
Definition InvalidScalar : error_t :=
  inl tt.
Definition InvalidSignature : error_t :=
  inr tt.

Notation "'p256_public_key_t'" := (affine_t) : hacspec_scope.

Notation "'p256_secret_key_t'" := (p256_scalar_t) : hacspec_scope.

Notation "'p256_signature_t'" := ((p256_scalar_t × p256_scalar_t
)) : hacspec_scope.

Notation "'p256_signature_result_t'" := ((
  result error_t p256_signature_t)) : hacspec_scope.

Notation "'p256_verify_result_t'" := ((result error_t unit)) : hacspec_scope.

Notation "'check_result_t'" := ((result error_t unit)) : hacspec_scope.

Notation "'arithmetic_result_t'" := ((result error_t affine_t)) : hacspec_scope.


Notation "'check_scalar_zero_inp'" :=(
  p256_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'check_scalar_zero_out'" :=(
  check_result_t : choice_type) (in custom pack_type at level 2).
Definition CHECK_SCALAR_ZERO : nat :=
  487.
Program Definition check_scalar_zero (r_486 : p256_scalar_t)
  : both (fset.fset0) [interface] (check_result_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (nat_mod_equal (lift_to_both0 r_486) (
            nat_mod_zero ))
        then @Err unit_ChoiceEquality error_t (InvalidScalar)
        else @Ok unit_ChoiceEquality error_t (tt))
      ) : both (fset.fset0) [interface] (check_result_t)).
Fail Next Obligation.


Notation "'ecdsa_point_mul_base_inp'" :=(
  p256_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdsa_point_mul_base_out'" :=(
  arithmetic_result_t : choice_type) (in custom pack_type at level 2).
Definition ECDSA_POINT_MUL_BASE : nat :=
  488.
Program Definition ecdsa_point_mul_base (x_489 : p256_scalar_t)
  : both (fset.fset0) [interface] (arithmetic_result_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] (arithmetic_result_t)).
Fail Next Obligation.


Notation "'ecdsa_point_mul_inp'" :=(
  p256_scalar_t × affine_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdsa_point_mul_out'" :=(
  arithmetic_result_t : choice_type) (in custom pack_type at level 2).
Definition ECDSA_POINT_MUL : nat :=
  490.
Program Definition ecdsa_point_mul (k_491 : p256_scalar_t) (p_492 : affine_t)
  : both (fset.fset0) [interface] (arithmetic_result_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] (arithmetic_result_t)).
Fail Next Obligation.


Notation "'ecdsa_point_add_inp'" :=(
  affine_t × affine_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdsa_point_add_out'" :=(
  arithmetic_result_t : choice_type) (in custom pack_type at level 2).
Definition ECDSA_POINT_ADD : nat :=
  493.
Program Definition ecdsa_point_add (p_494 : affine_t) (q_495 : affine_t)
  : both (fset.fset0) [interface] (arithmetic_result_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (TODO match) ) : both (
      fset.fset0) [interface] (arithmetic_result_t)).
Fail Next Obligation.


Notation "'sign_inp'" :=(
  byte_seq × p256_secret_key_t × p256_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'sign_out'" :=(
  p256_signature_result_t : choice_type) (in custom pack_type at level 2).
Definition SIGN : nat :=
  508.
Program Definition sign (payload_500 : byte_seq) (sk_503 : p256_secret_key_t) (
    nonce_496 : p256_scalar_t)
  : both (fset.fset0) [interface] (p256_signature_result_t) :=
  ((letbnd(_) _ : unit_ChoiceEquality :=
        check_scalar_zero (lift_to_both0 nonce_496) in
      letbnd(_) '(k_x_497, k_y_498) : affine_t :=
        ecdsa_point_mul_base (lift_to_both0 nonce_496) in
      letb r_499 : p256_scalar_t :=
        nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
            lift_to_both0 k_x_497)) in
      letbnd(_) _ : unit_ChoiceEquality :=
        check_scalar_zero (lift_to_both0 r_499) in
      letb payload_hash_501 : sha256_digest_t :=
        hash (lift_to_both0 payload_500) in
      letb payload_hash_502 : p256_scalar_t :=
        nat_mod_from_byte_seq_be (
          array_to_seq (lift_to_both0 payload_hash_501)) in
      letb rsk_504 : p256_scalar_t :=
        (lift_to_both0 r_499) *% (lift_to_both0 sk_503) in
      letb hash_rsk_505 : p256_scalar_t :=
        (lift_to_both0 payload_hash_502) +% (lift_to_both0 rsk_504) in
      letb nonce_inv_506 : p256_scalar_t :=
        nat_mod_inv (lift_to_both0 nonce_496) in
      letb s_507 : p256_scalar_t :=
        (lift_to_both0 nonce_inv_506) *% (lift_to_both0 hash_rsk_505) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok p256_signature_t error_t (prod_b(
            lift_to_both0 r_499,
            lift_to_both0 s_507
          )))
      ) : both (fset.fset0) [interface] (p256_signature_result_t)).
Fail Next Obligation.


Notation "'ecdsa_p256_sha256_sign_inp'" :=(
  byte_seq × p256_secret_key_t × p256_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdsa_p256_sha256_sign_out'" :=(
  p256_signature_result_t : choice_type) (in custom pack_type at level 2).
Definition ECDSA_P256_SHA256_SIGN : nat :=
  512.
Program Definition ecdsa_p256_sha256_sign (payload_509 : byte_seq) (
    sk_510 : p256_secret_key_t) (nonce_511 : p256_scalar_t)
  : both (fset.fset0) [interface] (p256_signature_result_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (sign (
          lift_to_both0 payload_509) (lift_to_both0 sk_510) (
          lift_to_both0 nonce_511))
      ) : both (fset.fset0) [interface] (p256_signature_result_t)).
Fail Next Obligation.


Notation "'verify_inp'" :=(
  byte_seq × p256_public_key_t × p256_signature_t : choice_type) (in custom pack_type at level 2).
Notation "'verify_out'" :=(
  p256_verify_result_t : choice_type) (in custom pack_type at level 2).
Definition VERIFY : nat :=
  528.
Program Definition verify (payload_516 : byte_seq) (
    pk_523 : p256_public_key_t) (signature_513 : p256_signature_t)
  : both (fset.fset0) [interface] (p256_verify_result_t) :=
  ((letb '(r_514, s_515) : (p256_scalar_t '× p256_scalar_t) :=
        lift_to_both0 signature_513 in
      letb payload_hash_517 : sha256_digest_t :=
        hash (lift_to_both0 payload_516) in
      letb payload_hash_518 : p256_scalar_t :=
        nat_mod_from_byte_seq_be (
          array_to_seq (lift_to_both0 payload_hash_517)) in
      letb s_inv_519 : p256_scalar_t := nat_mod_inv (lift_to_both0 s_515) in
      letb u1_520 : p256_scalar_t :=
        (lift_to_both0 payload_hash_518) *% (lift_to_both0 s_inv_519) in
      letbnd(_) u1_521 : affine_t :=
        ecdsa_point_mul_base (lift_to_both0 u1_520) in
      letb u2_522 : p256_scalar_t :=
        (lift_to_both0 r_514) *% (lift_to_both0 s_inv_519) in
      letbnd(_) u2_524 : affine_t :=
        ecdsa_point_mul (lift_to_both0 u2_522) (lift_to_both0 pk_523) in
      letbnd(_) '(x_525, y_526) : affine_t :=
        ecdsa_point_add (lift_to_both0 u1_521) (lift_to_both0 u2_524) in
      letb x_527 : p256_scalar_t :=
        nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
            lift_to_both0 x_525)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 x_527) =.? (
            lift_to_both0 r_514))
        then @Ok unit_ChoiceEquality error_t (tt)
        else @Err unit_ChoiceEquality error_t (InvalidSignature))
      ) : both (fset.fset0) [interface] (p256_verify_result_t)).
Fail Next Obligation.


Notation "'ecdsa_p256_sha256_verify_inp'" :=(
  byte_seq × p256_public_key_t × p256_signature_t : choice_type) (in custom pack_type at level 2).
Notation "'ecdsa_p256_sha256_verify_out'" :=(
  p256_verify_result_t : choice_type) (in custom pack_type at level 2).
Definition ECDSA_P256_SHA256_VERIFY : nat :=
  532.
Program Definition ecdsa_p256_sha256_verify (payload_529 : byte_seq) (
    pk_530 : p256_public_key_t) (signature_531 : p256_signature_t)
  : both (fset.fset0) [interface] (p256_verify_result_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (verify (
          lift_to_both0 payload_529) (lift_to_both0 pk_530) (
          lift_to_both0 signature_531))
      ) : both (fset.fset0) [interface] (p256_verify_result_t)).
Fail Next Obligation.

