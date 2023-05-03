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


Definition r_3311_loc : ChoiceEqualityLocation :=
  (int64 ; 3312%nat).
Definition x_3309_loc : ChoiceEqualityLocation :=
  (int64 ; 3313%nat).
Definition y_3310_loc : ChoiceEqualityLocation :=
  (int64 ; 3314%nat).
Notation "'xor_inp'" :=(
  int64 × int64 : choice_type) (in custom pack_type at level 2).
Notation "'xor_out'" :=(int64 : choice_type) (in custom pack_type at level 2).
Definition XOR : nat :=
  3317.
Program Definition xor (x_inp_3315 : int64) (y_inp_3316 : int64)
  : both (CEfset ([x_3309_loc ; y_3310_loc ; r_3311_loc])) [interface] (
    int64) :=
  ((letbm x_3309 : int64 loc( x_3309_loc ) := lift_to_both0 x_inp_3315 in
      letbm y_3310 : int64 loc( y_3310_loc ) := lift_to_both0 y_inp_3316 in
      letbm r_3311 : int64 loc( r_3311_loc ) :=
        (lift_to_both0 x_3309) .^ (lift_to_both0 y_3310) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 r_3311)
      ) : both (CEfset ([x_3309_loc ; y_3310_loc ; r_3311_loc])) [interface] (
      int64)).
Fail Next Obligation.

