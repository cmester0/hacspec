(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Inductive piggy_bank_state :=
| Intact : piggy_bank_state
| Smashed : piggy_bank_state.

Definition piggy_init  : piggy_bank_state :=
  Intact.

Definition user_address := nseq (int8) (usize 32).

Notation "'context'" := ((
  user_address ×
  user_address ×
  int64 ×
  piggy_bank_state
)) : hacspec_scope.

Inductive piggy_insert_result :=
| PiggyInsertResultInl : (
  user_address ×
  user_address ×
  int64 ×
  piggy_bank_state
) -> piggy_insert_result
| PiggyInsertResultInr : piggy_insert_result.

Inductive piggy_smash_result :=
| PiggySmashResultInl : (context × user_address × int64) -> piggy_smash_result
| PiggySmashResultInr : piggy_smash_result.

Definition piggy_insert
  (ctx_0 : context)
  (amount_1 : int64)
  : piggy_insert_result :=
  let '(owner_2, sender_3, balance_4, state_5) :=
    ctx_0 in 
  match state_5 with
  | Intact => PiggyInsertResultInl (
    (owner_2, sender_3, (balance_4) .+ (amount_1), state_5))
  | Smashed => PiggyInsertResultInr end.

Definition piggy_smash (ctx_6 : context) : piggy_smash_result :=
  let '(owner_7, sender_8, balance_9, state_10) :=
    ctx_6 in 
  match state_10 with
  | Intact => if (negb ((owner_7) array_eq (sender_8))):bool then (
    PiggySmashResultInr) else (
    PiggySmashResultInl (
      ((owner_7, sender_8, balance_9, Smashed), owner_7, balance_9)))
  | Smashed => PiggySmashResultInr end.

Definition test_init_smash_zero
  (user_11 : user_address)
  (start_val_12 : int64)
  : bool :=
  match piggy_smash ((user_11, user_11, start_val_12, piggy_init )) with
  | PiggySmashResultInl (_, _, balance_13) => (balance_13) =.? (start_val_12)
  | PiggySmashResultInr => false end.

Theorem test_init_smash_zero_correct : forall user_11 : user_address ,forall start_val_12 : int64 ,test_init_smash_zero user_11 start_val_12 = true.
Proof.
  intros.

  unfold test_init_smash_zero.
  unfold piggy_init.
  unfold piggy_smash.
  unfold "array_eq".
  
  rewrite (proj2 (Vector.eqb_eq (@int WORDSIZE8) eq int_eqb_eq (usize 32) _ _) (eq_refl)).
  
  apply eq_true.
Qed.

Definition test_increment_then_smash
  (user_14 : user_address)
  (start_val_15 : int64)
  (increment_16 : int64)
  : bool :=
  match piggy_insert ((user_14, user_14, start_val_15, piggy_init )) (
    increment_16) with
  | PiggyInsertResultInl (a_17, b_18, c_19, d_20) => match piggy_smash (
    (a_17, b_18, c_19, d_20)) with
  | PiggySmashResultInl (_, _, balance_21) => (balance_21) =.? (
    (start_val_15) .+ (increment_16))
  | PiggySmashResultInr => false end
  | PiggyInsertResultInr => false end.

Theorem test_increment_then_smash_correct : forall user_14 : user_address ,forall start_val_15 : int64 ,forall increment_16 : int64 ,test_increment_then_smash user_14 start_val_15 increment_16 = true.
Proof.
  intros.

  unfold test_increment_then_smash.
  unfold piggy_init.
  unfold piggy_insert.
  unfold piggy_smash.
  unfold "array_eq".
  
  rewrite (proj2 (Vector.eqb_eq (@int WORDSIZE8) eq int_eqb_eq (usize 32) _ _) (eq_refl)).
  
  apply eq_true.
Qed.


Definition test_re_smash_fails
  (user_22 : user_address)
  (start_val_23 : int64)
  : bool :=
  match piggy_smash ((user_22, user_22, start_val_23, piggy_init )) with
  | PiggySmashResultInl (ctx_24, _, _) => match piggy_smash (ctx_24) with
  | PiggySmashResultInl (ctx_25, _, _) => false
  | PiggySmashResultInr => true end
  | PiggySmashResultInr => false end.

Theorem test_re_smash_fails_correct : forall user_22 : user_address ,forall start_val_23 : int64 ,test_re_smash_fails user_22 start_val_23 = true.
Proof.
  intros.

  unfold test_re_smash_fails.
  unfold piggy_init.
  unfold piggy_insert.
  unfold piggy_smash.
  unfold "array_eq".
  
  rewrite (proj2 (Vector.eqb_eq (@int WORDSIZE8) eq int_eqb_eq (usize 32) _ _) (eq_refl)).
  reflexivity.
Qed.


Definition test_transfer_to_smash_fails
  (user_26 : user_address)
  (start_val_27 : int64)
  (increment_28 : int64)
  : bool :=
  match piggy_smash ((user_26, user_26, start_val_27, piggy_init )) with
  | PiggySmashResultInl (ctx_29, _, _) => match piggy_insert (ctx_29) (
    increment_28) with
  | PiggyInsertResultInl _ => false
  | PiggyInsertResultInr => true end
  | PiggySmashResultInr => false end.

Theorem test_transfer_to_smash_fails_correct : forall user_26 : user_address ,forall start_val_27 : int64 ,forall increment_28 : int64 ,test_transfer_to_smash_fails user_26 start_val_27 increment_28 = true.
Proof.  
  intros.

  unfold test_transfer_to_smash_fails.
  unfold piggy_init.
  unfold piggy_insert.
  unfold piggy_smash.
  unfold "array_eq".
  
  rewrite (proj2 (Vector.eqb_eq (@int WORDSIZE8) eq int_eqb_eq (usize 32) _ _) (eq_refl)).
  reflexivity.
Qed.


Definition test_transfer_to_smash_fails_zero
  (user_30 : user_address)
  (sender_31 : user_address)
  (start_val_32 : int64)
  (increment_33 : int64)
  : bool :=
  negb (
    ((user_30) array_neq (sender_31)) && (
      match piggy_smash ((user_30, sender_31, start_val_32, piggy_init )) with
      | PiggySmashResultInl (ctx_34, _, _) => match piggy_insert (ctx_34) (
        increment_33) with
      | PiggyInsertResultInl _ => true
      | PiggyInsertResultInr => false end
      | PiggySmashResultInr => false end)).

Theorem test_transfer_to_smash_fails_zero_correct : forall user_30 : user_address ,forall sender_31 : user_address ,forall start_val_32 : int64 ,forall increment_33 : int64 ,test_transfer_to_smash_fails_zero user_30 sender_31 start_val_32 increment_33 = true.
Proof.
  intros.

  unfold test_transfer_to_smash_fails_zero.
  unfold piggy_init.
  unfold piggy_insert.
  unfold piggy_smash.
  unfold "array_eq".
  
  destruct (Vector.eqb int eq sender_31 user_30) eqn:a.
  - apply (Vector.eqb_eq _ _ int_eqb_eq) in a.
    subst.
    rewrite (proj2 (Vector.eqb_eq (@int WORDSIZE8) eq int_eqb_eq (usize 32) _ _) (eq_refl)).
    reflexivity.
  - assert (sender_31 <> user_30).
    { unfold "<>".
      intros.
      subst.
      rewrite (proj2 (Vector.eqb_eq (@int WORDSIZE8) eq int_eqb_eq (usize 32) user_30 user_30) (eq_refl)) in a.
      discriminate. }
    pose (proj2 (Vector.eqb_eq (@int WORDSIZE8) eq int_eqb_eq (usize 32) user_30 sender_31)).
    assert (forall P b , (P <-> b = true) -> ((P -> False) -> b = false)).
    + intros.      
      inversion H0.
      destruct b.
      * exfalso.
        apply H1.
        apply H3.
        reflexivity.
      * reflexivity.
    + 
      unfold "<>" in H.
      rewrite (H0 (sender_31 = user_30) (Vector.eqb int eq user_30 sender_31 )).
      reflexivity.
      split.
      * intros.
        exfalso.
        apply H.
        apply H1.
      * intros.
        exfalso.

        assert (Vector.eqb int eq sender_31 user_30 = true).
        -- apply (Vector.eqb_eq (@int WORDSIZE8) eq int_eqb_eq (usize 32)) in H1.
           subst.
           apply (Vector.eqb_eq (@int WORDSIZE8) eq int_eqb_eq (usize 32)).
           reflexivity.
        -- rewrite a in H2.
           discriminate.
      * apply H.
Qed.
