(* [[file:piggybank.org::*  - Coq code][ - Coq code:1]] *)
(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
From QuickChick Require Import QuickChick.
Require Import QuickChickLib.
(*  - Coq code:1 ends here *)

(* [[file:piggybank.org::*  - Coq code][ - Coq code:2]] *)
Require Import Hacspec.Lib.
(*  - Coq code:2 ends here *)

(* [[file:piggybank.org::*  - Coq code][ - Coq code:3]] *)
Require Import Hacspec.Concordium.
(*  - Coq code:3 ends here *)

(* [[file:piggybank.org::*  - Coq code][ - Coq code:4]] *)
Inductive piggy_bank_state_hacspec_t :=
| Intact : piggy_bank_state_hacspec_t
| Smashed : piggy_bank_state_hacspec_t.

Definition eqb_piggy_bank_state_hacspec_t (x y : piggy_bank_state_hacspec_t) : bool :=
match x with
   | Intact => match y with | Intact=> true | _ => false end
   | Smashed => match y with | Smashed=> true | _ => false end
   end.

Definition eqb_leibniz_piggy_bank_state_hacspec_t (x y : piggy_bank_state_hacspec_t) : eqb_piggy_bank_state_hacspec_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_piggy_bank_state_hacspec_t : EqDec (piggy_bank_state_hacspec_t) :=
Build_EqDec (piggy_bank_state_hacspec_t) (eqb_piggy_bank_state_hacspec_t) (eqb_leibniz_piggy_bank_state_hacspec_t).

Global Instance show_piggy_bank_state_hacspec_t : Show (piggy_bank_state_hacspec_t) :=
 @Build_Show (piggy_bank_state_hacspec_t) (fun x =>
 match x with
 Intact => ("Intact")%string
 | Smashed => ("Smashed")%string
 end).
Definition g_piggy_bank_state_hacspec_t : G (piggy_bank_state_hacspec_t) := oneOf_ (returnGen Intact) [returnGen Intact;returnGen Smashed].
Global Instance gen_piggy_bank_state_hacspec_t : Gen (piggy_bank_state_hacspec_t) := Build_Gen piggy_bank_state_hacspec_t g_piggy_bank_state_hacspec_t.

(*  - Coq code:4 ends here *)

(* [[file:piggybank.org::*  - Coq code][ - Coq code:5]] *)
Definition piggy_init_hacspec  : piggy_bank_state_hacspec_t :=
  Intact.
(*  - Coq code:5 ends here *)

(* [[file:piggybank.org::*  - Coq code][ - Coq code:6]] *)
Definition user_address_t := nseq (int8) (usize 32).
Instance show_user_address_t : Show (user_address_t) := Build_Show (user_address_t) show.
Definition g_user_address_t : G (user_address_t) := arbitrary.
Instance gen_user_address_t : Gen (user_address_t) := Build_Gen user_address_t g_user_address_t.
(*  - Coq code:6 ends here *)

(* [[file:piggybank.org::*  - Coq code][ - Coq code:7]] *)
Notation "'piggy_insert_result_t'" := ((result unit unit)) : hacspec_scope.
(*  - Coq code:7 ends here *)

(* [[file:piggybank.org::*  - Coq code][ - Coq code:8]] *)
Definition piggy_insert_hacspec
  (state_0 : piggy_bank_state_hacspec_t)
  : piggy_insert_result_t :=
  match state_0 with
  | Intact => @Ok unit unit (tt)
  | Smashed => @Err unit unit (tt)
  end.
(*  - Coq code:8 ends here *)

(* [[file:piggybank.org::*  - Coq code][ - Coq code:9]] *)
Notation "'context_t'" := ((user_address_t × user_address_t × int64
)) : hacspec_scope.
Instance show_context_t : Show (context_t) :=
Build_Show context_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_context_t : G (context_t) :=
bindGen arbitrary (fun x0 : user_address_t =>
  bindGen arbitrary (fun x1 : user_address_t =>
  bindGen arbitrary (fun x2 : int64 =>
  returnGen (x0,x1,x2)))).
Instance gen_context_t : Gen (context_t) := Build_Gen context_t g_context_t.
(*  - Coq code:9 ends here *)

(* [[file:piggybank.org::*  - Coq code][ - Coq code:10]] *)
Inductive smash_error_t :=
| NotOwner : smash_error_t
| AlreadySmashed : smash_error_t.

Definition eqb_smash_error_t (x y : smash_error_t) : bool :=
match x with
   | NotOwner => match y with | NotOwner=> true | _ => false end
   | AlreadySmashed => match y with | AlreadySmashed=> true | _ => false end
   end.

Definition eqb_leibniz_smash_error_t (x y : smash_error_t) : eqb_smash_error_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_smash_error_t : EqDec (smash_error_t) :=
Build_EqDec (smash_error_t) (eqb_smash_error_t) (eqb_leibniz_smash_error_t).

Global Instance show_smash_error_t : Show (smash_error_t) :=
 @Build_Show (smash_error_t) (fun x =>
 match x with
 NotOwner => ("NotOwner")%string
 | AlreadySmashed => ("AlreadySmashed")%string
 end).
Definition g_smash_error_t : G (smash_error_t) := oneOf_ (returnGen NotOwner) [returnGen NotOwner;returnGen AlreadySmashed].
Global Instance gen_smash_error_t : Gen (smash_error_t) := Build_Gen smash_error_t g_smash_error_t.

(*  - Coq code:10 ends here *)

(* [[file:piggybank.org::*  - Coq code][ - Coq code:11]] *)
Notation "'piggy_smash_result_t'" := ((
  result piggy_bank_state_hacspec_t smash_error_t)) : hacspec_scope.
(*  - Coq code:11 ends here *)

(* [[file:piggybank.org::*  - Coq code][ - Coq code:12]] *)
Definition piggy_smash_hacspec
  (ctx_1 : context_t)
  (state_2 : piggy_bank_state_hacspec_t)
  : piggy_smash_result_t :=
  let '(owner_3, sender_4, balance_5) :=
    ctx_1 in 
  ifbnd negb ((owner_3) array_eq (sender_4)) : bool
  thenbnd (bind (@Err piggy_bank_state_hacspec_t smash_error_t (NotOwner)) (
      fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  ifbnd negb ((state_2) =.? (Intact)) : bool
  thenbnd (bind (@Err piggy_bank_state_hacspec_t smash_error_t (
        AlreadySmashed)) (fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  @Ok piggy_bank_state_hacspec_t smash_error_t (Smashed))).
(*  - Coq code:12 ends here *)

(* [[file:piggybank.org::*  - Coq code][ - Coq code:13]] *)
Definition test_init_hacspec  : bool :=
  (piggy_init_hacspec ) =.? (Intact).
(*  - Coq code:13 ends here *)

(* [[file:piggybank.org::*  - Coq code][ - Coq code:14]] *)
Definition test_insert_intact  : bool :=
  (piggy_insert_hacspec (Intact)) =.? (@Ok unit unit (tt)).
(*  - Coq code:14 ends here *)

(* [[file:piggybank.org::*  - Coq code][ - Coq code:15]] *)
Definition test_insert_smashed  : bool :=
  (piggy_insert_hacspec (Smashed)) =.? (@Err unit unit (tt)).
(*  - Coq code:15 ends here *)

(* [[file:piggybank.org::*  - Coq code][ - Coq code:16]] *)
Definition test_smash_intact
  (owner_6 : user_address_t)
  (balance_7 : int64)
  : bool :=
  let sender_8 : user_address_t :=
    owner_6 in 
  let ctx_9 : (user_address_t × user_address_t × int64) :=
    (owner_6, sender_8, balance_7) in 
  (piggy_smash_hacspec (ctx_9) (Intact)) =.? (
    @Ok piggy_bank_state_hacspec_t smash_error_t (Smashed)).
QuickChick (
  forAll g_user_address_t (fun owner_6 : user_address_t => forAll g_int64 (fun balance_7 : int64 => test_smash_intact owner_6 balance_7))).
(*  - Coq code:16 ends here *)

(* [[file:piggybank.org::*  - Coq code][ - Coq code:17]] *)
Definition test_smash_intact_not_owner
  (owner_10 : user_address_t)
  (sender_11 : user_address_t)
  (balance_12 : int64)
  : bool :=
  let ctx_13 : (user_address_t × user_address_t × int64) :=
    (owner_10, sender_11, balance_12) in 
  ((owner_10) array_eq (sender_11)) || ((piggy_smash_hacspec (ctx_13) (
        Intact)) =.? (@Err piggy_bank_state_hacspec_t smash_error_t (
        NotOwner))).
QuickChick (
  forAll g_user_address_t (fun owner_10 : user_address_t => forAll g_user_address_t (fun sender_11 : user_address_t => forAll g_int64 (fun balance_12 : int64 => test_smash_intact_not_owner owner_10 sender_11 balance_12)))).
(*  - Coq code:17 ends here *)

(* [[file:piggybank.org::*  - Coq code][ - Coq code:18]] *)
Definition test_smash_smashed
  (owner_14 : user_address_t)
  (balance_15 : int64)
  : bool :=
  let sender_16 : user_address_t :=
    owner_14 in 
  let ctx_17 : (user_address_t × user_address_t × int64) :=
    (owner_14, sender_16, balance_15) in 
  (piggy_smash_hacspec (ctx_17) (Smashed)) =.? (
    @Err piggy_bank_state_hacspec_t smash_error_t (AlreadySmashed)).
QuickChick (
  forAll g_user_address_t (fun owner_14 : user_address_t => forAll g_int64 (fun balance_15 : int64 => test_smash_smashed owner_14 balance_15))).
(*  - Coq code:18 ends here *)

