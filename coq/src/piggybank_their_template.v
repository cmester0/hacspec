(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
From QuickChick Require Import QuickChick. Import QcNotation.
Require Import QuickChickLib.
Require Import Hacspec.Lib.

Inductive piggy_bank_state :=
| Intact : piggy_bank_state
| Smashed : piggy_bank_state.
Instance show_piggy_bank_state : Show (piggy_bank_state) :=
Build_Show (piggy_bank_state) (fun x => match x with
  | Intact => "Intact"%string
  | Smashed => "Smashed"%string
  end).
Definition g_piggy_bank_state : G (piggy_bank_state) :=
 elems [Intact ;Smashed].
Instance gen_piggy_bank_state : Gen (piggy_bank_state) := Build_Gen piggy_bank_state g_piggy_bank_state.


Definition piggy_init  : piggy_bank_state :=
  Intact.

Definition user_address := nseq (int8) (usize 32).

Notation "'context'" := ((
  user_address ×
  user_address ×
  int64 ×
  piggy_bank_state
)) : hacspec_scope.
Instance show_context : Show (context) :=
Build_Show context (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  let (x, x2) := x in
  append ("("%string) (append (show x) (append (","%string) (append (show x0) (append (","%string) (append (show x1) (append (","%string) (append (show x2) (")"%string))))))))).
Definition g_context : G (context) :=
bindGen arbitrary (fun x0 : user_address =>
  bindGen arbitrary (fun x1 : user_address =>
  bindGen arbitrary (fun x2 : int64 =>
  bindGen arbitrary (fun x3 : piggy_bank_state =>
  returnGen (x0,x1,x2,x3))))).
Instance gen_context : Gen (context) := Build_Gen context g_context.


Inductive piggy_insert_result :=
| PiggyInsertResultInl : (
  user_address ×
  user_address ×
  int64 ×
  piggy_bank_state
) -> piggy_insert_result
| PiggyInsertResultInr : piggy_insert_result.
Instance show_piggy_insert_result : Show (piggy_insert_result) :=
Build_Show (piggy_insert_result) (fun x => match x with
  | PiggyInsertResultInl (x0, x1, x2, x3) => append (show x0) (append (show x1) (append (show x2) (append (show x3) "PiggyInsertResultInl"%string )))
  | PiggyInsertResultInr => "PiggyInsertResultInr"%string
  end).
Definition g_piggy_insert_result : G (piggy_insert_result) :=
bindGen arbitrary (fun x => elems [PiggyInsertResultInl x ;PiggyInsertResultInr]).
Instance gen_piggy_insert_result : Gen (piggy_insert_result) := Build_Gen piggy_insert_result g_piggy_insert_result.


Inductive piggy_smash_result :=
| PiggySmashResultInl : (context × user_address × int64) -> piggy_smash_result
| PiggySmashResultInrOwnerSender : piggy_smash_result
| PiggySmashResultInrSmashed : piggy_smash_result.
Instance show_piggy_smash_result : Show (piggy_smash_result) :=
Build_Show (piggy_smash_result) (fun x => match x with
  | PiggySmashResultInl (x0, x1, x2) => append (show x0) (append (show x1) (append (show x2) "PiggySmashResultInl"%string ))
  | PiggySmashResultInrOwnerSender => "PiggySmashResultInrOwnerSender"%string
  | PiggySmashResultInrSmashed => "PiggySmashResultInrSmashed"%string
  end).
Definition g_piggy_smash_result : G (piggy_smash_result) :=
bindGen arbitrary (fun x =>  elems [PiggySmashResultInl x ;PiggySmashResultInrOwnerSender ;PiggySmashResultInrSmashed]).
Instance gen_piggy_smash_result : Gen (piggy_smash_result) := Build_Gen piggy_smash_result g_piggy_smash_result.


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
    PiggySmashResultInrOwnerSender) else (
    PiggySmashResultInl (
      ((owner_7, sender_8, balance_9, Smashed), owner_7, balance_9)))
  | Smashed => PiggySmashResultInrSmashed end.

Definition test_init  : bool :=
  let state_11 :=
    piggy_init  in 
  match state_11 with | Intact => true | Smashed => false end.
QuickChick (test_init).


Theorem test_init_correct : test_init = true.
Proof. Admitted.


Definition test_insert_intact  : bool :=
  let ctx_12 :=
    (
      array_from_list int8 (
        let l :=
          [
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0
          ] in  l),
      array_from_list int8 (
        let l :=
          [
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0
          ] in  l),
      repr 100,
      Intact
    ) in 
  let result_13 : piggy_insert_result :=
    piggy_insert (ctx_12) (repr 100) in 
  match result_13 with
  | PiggyInsertResultInl (owner_14, sender_15, balance_16, state_17
  ) => match state_17 with
  | Intact => true
  | Smashed => false end
  | PiggyInsertResultInr => false end.
QuickChick (test_insert_intact).


Theorem test_insert_intact_correct : test_insert_intact = true.
Proof. Admitted.


Definition test_insert_smashed  : bool :=
  let ctx_18 :=
    (
      array_from_list int8 (
        let l :=
          [
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0
          ] in  l),
      array_from_list int8 (
        let l :=
          [
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0
          ] in  l),
      repr 100,
      Smashed
    ) in 
  let result_19 :=
    piggy_insert (ctx_18) (repr 100) in 
  match result_19 with
  | PiggyInsertResultInl (_, _, _, _) => false
  | PiggyInsertResultInr => true end.
QuickChick (test_insert_smashed).


Theorem test_insert_smashed_correct : test_insert_smashed = true.
Proof. Admitted.


Definition test_smash_intact  : bool :=
  let ctx_20 :=
    (
      array_from_list int8 (
        let l :=
          [
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0
          ] in  l),
      array_from_list int8 (
        let l :=
          [
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0
          ] in  l),
      repr 100,
      Intact
    ) in 
  let result_21 :=
    piggy_smash (ctx_20) in 
  match result_21 with
  | PiggySmashResultInl ((_, _, _, state_22), _, balance_23
  ) => match state_22 with
  | Intact => false
  | Smashed => (balance_23) =.? (repr 100) end
  | PiggySmashResultInrSmashed => false
  | PiggySmashResultInrOwnerSender => false end.
QuickChick (test_smash_intact).


Theorem test_smash_intact_correct : test_smash_intact = true.
Proof. Admitted.


Definition test_smash_intact_not_owner  : bool :=
  let ctx_24 :=
    (
      array_from_list int8 (
        let l :=
          [
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0
          ] in  l),
      array_from_list int8 (
        let l :=
          [
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1;
            repr 1
          ] in  l),
      repr 100,
      Intact
    ) in 
  let result_25 :=
    piggy_smash (ctx_24) in 
  match result_25 with
  | PiggySmashResultInl (_, _, _) => false
  | PiggySmashResultInrSmashed => false
  | PiggySmashResultInrOwnerSender => true end.
QuickChick (test_smash_intact_not_owner).


Theorem test_smash_intact_not_owner_correct : test_smash_intact_not_owner = true.
Proof. Admitted.


Definition test_smash_smashed  : bool :=
  let ctx_26 :=
    (
      array_from_list int8 (
        let l :=
          [
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0
          ] in  l),
      array_from_list int8 (
        let l :=
          [
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0;
            repr 0
          ] in  l),
      repr 100,
      Smashed
    ) in 
  let result_27 :=
    piggy_smash (ctx_26) in 
  match result_27 with
  | PiggySmashResultInl (_, _, _) => false
  | PiggySmashResultInrSmashed => true
  | PiggySmashResultInrOwnerSender => false end.
QuickChick (test_smash_smashed).


Theorem test_smash_smashed_correct : test_smash_smashed = true.
Proof. Admitted.


