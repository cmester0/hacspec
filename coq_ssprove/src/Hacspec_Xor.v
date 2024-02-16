(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp Require Import ssrZ word.
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


Definition r_3311_loc : Location :=
  (int64 ; 3312%nat).
Definition x_3309_loc : Location :=
  (int64 ; 3313%nat).
Definition y_3310_loc : Location :=
  (int64 ; 3314%nat).
Notation "'xor_inp'" :=(
  int64 × int64 : choice_type) (in custom pack_type at level 2).
Notation "'xor_out'" :=(int64 : choice_type) (in custom pack_type at level 2).
Definition XOR : nat :=
  3317.
Equations xor (x_inp_3315 : int64) (y_inp_3316 : int64)
  : both (fset ([x_3309_loc ; y_3310_loc ; r_3311_loc])) [interface] (
        int64) :=
  xor x_inp_3315 y_inp_3316 :=
  ((letb x_3309  loc( x_3309_loc ) := ret_both x_inp_3315 in
      letb y_3310 loc( y_3310_loc ) := ret_both y_inp_3316 in
      letb r_3311 loc( r_3311_loc ) :=
        ( x_3309) .^ ( y_3310) in
       solve_lift (r_3311)
      ) : both (fset ([x_3309_loc ; y_3310_loc ; r_3311_loc])) [interface] (
      int64)).
Fail Next Obligation.

Check (fun x y => is_state (both_prog (xor x y))).
