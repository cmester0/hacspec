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

Definition user_address := nseq (uint8) (usize 32).

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
  | Intact => PiggySmashResultInl (
    ((owner_7, sender_8, balance_9, Smashed), owner_7, balance_9))
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
  cbn.
  auto using eq_true.
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
  cbn.
  auto using eq_true.
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
  cbn.
  auto using eq_true.
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
  cbn.
  auto using eq_true.
Qed.


