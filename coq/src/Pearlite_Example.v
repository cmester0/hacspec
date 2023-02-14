(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
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
Proof.
  intros. subst.

  rewrite !nat_N_Z.
  setoid_rewrite Z2Nat.id ; try easy.

  Set Printing Coercions.

  replace (unsigned (usize 1)) with 1 by reflexivity.
  replace (unsigned (usize 2)) with 2 by reflexivity.

  induction_uint_size_as_nat n_0.
  - reflexivity.
  - rewrite H1.
    rewrite Z.sub_succ_l.

    rewrite <- Zmult_succ_l_reverse.
    rewrite <- Zmult_succ_r_reverse.

    rewrite <- Zplus_assoc.
    replace (Z.of_nat H + Z.succ (Z.of_nat H - 1))%Z with (Z.of_nat H * 2)%Z.
    rewrite Z_div_plus.

    unfold sum_first_n in H2 |- *.
    unfold foldi in H2 |- *.
    rewrite H1.
    rewrite Z.sub_0_r in H2 |- *.

    rewrite <- Zpos_P_of_succ_nat.

    destruct H ; [ reflexivity | ].
    rewrite Nat2Z.inj_succ in H2.
    rewrite unsigned_repr_alt in H2.
    rewrite <- Zpos_P_of_succ_nat in H2.
    rewrite Zpos_P_of_succ_nat in H2.
    rewrite SuccNat2Pos.id_succ in H2.

    rewrite SuccNat2Pos.id_succ.
    rewrite <- foldi__move_S_fuel.

    assert (forall a b, Z_to_uint_size (a + b) = Z_to_uint_size (unsigned (Z_to_uint_size a) + unsigned (Z_to_uint_size b))).
    intros.
    cbn.
    unfold Z_to_uint_size.
    unfold repr.
    apply mkint_eq.

    rewrite !Z_mod_modulus_eq.
    now rewrite Zplus_mod.

    rewrite H3.
    rewrite H2.
    setoid_rewrite add_zero.
    rewrite <- H3.
    f_equal.

    rewrite Nat2Z.inj_succ.

    f_equal.
    rewrite !nat_N_Z.
    setoid_rewrite Z2Nat.id ; try easy.

    rewrite unsigned_repr_alt.
    reflexivity.
    Lia.lia.

    rewrite unsigned_repr_alt.
    Lia.lia.
    Lia.lia.

    apply modulus_range_helper.
    Lia.lia.

    Lia.lia.

    easy.

    Lia.lia.
  - destruct_uint_size_as_nat n_0.
    easy. Lia.lia.
  - destruct_uint_size_as_nat n_0.
    easy. Lia.lia.
Qed.


