(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition fp_canvas_t := nseq (int8) (48).
Definition fp_t :=
  nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

Definition scalar_canvas_t := nseq (int8) (32).
Definition scalar_t :=
  nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000.

Notation "'g1_t'" := ((fp_t × fp_t × bool)) : hacspec_scope.

Notation "'fp2_t'" := ((fp_t × fp_t)) : hacspec_scope.

Notation "'g2_t'" := ((fp2_t × fp2_t × bool)) : hacspec_scope.

Notation "'fp6_t'" := ((fp2_t × fp2_t × fp2_t)) : hacspec_scope.

Notation "'fp12_t'" := ((fp6_t × fp6_t)) : hacspec_scope.

Definition fp_return_zero  : fp_t :=
  nat_mod_zero .

Theorem ensures_fp_return_zero : forall result_0 ,
 @fp_return_zero  = result_0 ->
 ((nat_mod_model (result_0)) =.? (usize 0)) = true.
Proof.
  intros.
  subst.
  reflexivity.
Qed.

Definition fp2fromfp (n_1 : fp_t) : fp2_t :=
  (n_1, nat_mod_zero ).

Definition fp2zero  : fp2_t :=
  fp2fromfp (nat_mod_zero ).

Definition fp2neg (n_2 : fp2_t) : fp2_t :=
  let '(n1_3, n2_4) :=
    n_2 in 
  ((nat_mod_zero ) -% (n1_3), (nat_mod_zero ) -% (n2_4)).

