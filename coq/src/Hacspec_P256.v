(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Inductive error_t :=
| InvalidAddition : error_t.

Definition field_canvas_t := nseq (int8) (32).
Definition p256_field_element_t :=
  nat_mod 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff.

Definition scalar_canvas_t := nseq (int8) (32).
Definition p256_scalar_t :=
  nat_mod 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551.

Notation "'affine_t'" := ((p256_field_element_t × p256_field_element_t
)) : hacspec_scope.

Notation "'affine_result_t'" := ((result affine_t error_t)) : hacspec_scope.

Notation "'p256_jacobian_t'" := ((
  p256_field_element_t ×
  p256_field_element_t ×
  p256_field_element_t
)) : hacspec_scope.

Notation "'jacobian_result_t'" := ((
  result p256_jacobian_t error_t)) : hacspec_scope.

Definition element_t := nseq (uint8) (usize 32).

Definition jacobian_to_affine (p_0 : p256_jacobian_t) : affine_t :=
  let '(x_1, y_2, z_3) :=
    p_0 in 
  let z2_4 : p256_field_element_t :=
    nat_mod_exp (z_3) (@repr WORDSIZE32 2) in 
  let z2i_5 : p256_field_element_t :=
    nat_mod_inv (z2_4) in 
  let z3_6 : p256_field_element_t :=
    (z_3) *% (z2_4) in 
  let z3i_7 : p256_field_element_t :=
    nat_mod_inv (z3_6) in 
  let x_8 : p256_field_element_t :=
    (x_1) *% (z2i_5) in 
  let y_9 : p256_field_element_t :=
    (y_2) *% (z3i_7) in 
  (x_1, y_2).

Definition affine_to_jacobian (p_10 : affine_t) : p256_jacobian_t :=
  let '(x_11, y_12) :=
    p_10 in 
  (
    x_11,
    y_12,
    nat_mod_from_literal (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
      @repr WORDSIZE64 1) : p256_field_element_t
  ).

Definition point_double (p_13 : p256_jacobian_t) : p256_jacobian_t :=
  let '(x1_14, y1_15, z1_16) :=
    p_13 in 
  let delta_17 : p256_field_element_t :=
    nat_mod_exp (z1_16) (@repr WORDSIZE32 2) in 
  let gamma_18 : p256_field_element_t :=
    nat_mod_exp (y1_15) (@repr WORDSIZE32 2) in 
  let beta_19 : p256_field_element_t :=
    (x1_14) *% (gamma_18) in 
  let alpha_1_20 : p256_field_element_t :=
    (x1_14) -% (delta_17) in 
  let alpha_2_21 : p256_field_element_t :=
    (x1_14) +% (delta_17) in 
  let alpha_22 : p256_field_element_t :=
    (nat_mod_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        @repr WORDSIZE64 3) : p256_field_element_t) *% ((alpha_1_20) *% (
        alpha_2_21)) in 
  let x3_23 : p256_field_element_t :=
    (nat_mod_exp (alpha_22) (@repr WORDSIZE32 2)) -% ((nat_mod_from_literal (
          0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
          @repr WORDSIZE64 8) : p256_field_element_t) *% (beta_19)) in 
  let z3_24 : p256_field_element_t :=
    nat_mod_exp ((y1_15) +% (z1_16)) (@repr WORDSIZE32 2) in 
  let z3_25 : p256_field_element_t :=
    (z3_24) -% ((gamma_18) +% (delta_17)) in 
  let y3_1_26 : p256_field_element_t :=
    ((nat_mod_from_literal (
          0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
          @repr WORDSIZE64 4) : p256_field_element_t) *% (beta_19)) -% (
      x3_23) in 
  let y3_2_27 : p256_field_element_t :=
    (nat_mod_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        @repr WORDSIZE64 8) : p256_field_element_t) *% ((gamma_18) *% (
        gamma_18)) in 
  let y3_28 : p256_field_element_t :=
    ((alpha_22) *% (y3_1_26)) -% (y3_2_27) in 
  (x3_23, y3_28, z3_25).

Definition is_point_at_infinity (p_29 : p256_jacobian_t) : bool :=
  let '(x_30, y_31, z_32) :=
    p_29 in 
  nat_mod_equal (z_32) (nat_mod_from_literal (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
      @repr WORDSIZE64 0) : p256_field_element_t).

Definition s1_equal_s2
  (s1_33 : p256_field_element_t)
  (s2_34 : p256_field_element_t)
  : jacobian_result_t :=
  (if (nat_mod_equal (s1_33) (s2_34)):bool then (@Err p256_jacobian_t error_t (
        InvalidAddition)) else (@Ok p256_jacobian_t error_t ((
          nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr WORDSIZE64 0) : p256_field_element_t,
          nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr WORDSIZE64 1) : p256_field_element_t,
          nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr WORDSIZE64 0) : p256_field_element_t
        )))).

