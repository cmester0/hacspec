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

Definition sum_first_n (n_0 : uint_size)  : uint_size :=
  let sum_1 : uint_size :=
    usize 0 in 
  let sum_1 :=
    foldi (usize 0) (n_0) (fun i_2 sum_1 =>
      let sum_1 :=
        (sum_1) + (i_2) in 
      (sum_1))
    sum_1 in 
  sum_1.


Theorem ensures_sum_first_n : forall result_3 (n_0 : uint_size),
 @sum_first_n n_0 = result_3 ->
 result_3 = ((n_0) * ((n_0) - (usize 1))) / (usize 2).
 Proof. Admitted.

