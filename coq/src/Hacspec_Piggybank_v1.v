(** This file was automatically generated using Hacspec **)

Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
From QuickChick Require Import QuickChick.
Require Import QuickChickLib.

Require Import ConCertLib.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import Automation.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ContractCommon.
From Coq Require Import Morphisms ZArith Basics.
Open Scope Z.
Set Nonrecursive Elimination Schemes.
  
  
Definition Setup := unit.
Require Import Hacspec_Lib.

Require Import Hacspec_Concordium.

Inductive piggy_bank_state_hacspec_t :=
| Intact : piggy_bank_state_hacspec_t
| Smashed : piggy_bank_state_hacspec_t.
Global Instance serializable_piggy_bank_state_hacspec_t : Serializable piggy_bank_state_hacspec_t :=
Derive Serializable piggy_bank_state_hacspec_t_rect<Intact,Smashed>.

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


Definition user_address_t := nseq (int8) (usize 32).
Instance show_user_address_t : Show (user_address_t) := Build_Show (user_address_t) show.
Definition g_user_address_t : G (user_address_t) := arbitrary.
Instance gen_user_address_t : Gen (user_address_t) := Build_Gen user_address_t g_user_address_t.

Notation "'context_t'" := ((user_address_t ∏ user_address_t ∏ int64
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

Definition piggy_init_hacspec : piggy_bank_state_hacspec_t :=
  Intact.

Record State := 
  build_state { balance : int64 ; owner : Address ; state : piggy_bank_state_hacspec_t}.
  Global Instance State_serializable : Serializable State := Derive Serializable State_rect<build_state>.
  Definition PiggyBank_State (chain : Chain) (ctx : ContractCallContext) (_ : Setup) : option State :=
  Some {| balance := 0 ; owner := ctx.(ctx_from); state := piggy_init_hacspec  |}.
Definition piggy_init
  : piggy_bank_state_hacspec_t :=
  piggy_init_hacspec .

Notation "'piggy_insert_result_t'" := ((result unit unit)) : hacspec_scope.

Definition piggy_insert_hacspec
  (ctx_0 : context_t)
  (amount_1 : int64)
  (state_2 : piggy_bank_state_hacspec_t): piggy_insert_result_t :=
  match state_2 with
  | Intact => @Ok unit unit (tt)
  | Smashed => @Err unit unit (tt)
  end.

Definition piggy_insert
  (ctx_3 : context_t)
  (amount_4 : int64)
  (state_5 : piggy_bank_state_hacspec_t): int64 :=
  let '(_, _, balance_6) :=
    ctx_3 in 
  (balance_6) .+ (amount_4).
Definition insert (amount : int64)(st : State) (ctx : context_t) :=
  {| balance := piggy_insert ctx amount st.(state) ; owner := st.(owner); state := st.(state) |}.


Inductive smash_error_t :=
| NotOwner : smash_error_t
| AlreadySmashed : smash_error_t.
Global Instance serializable_smash_error_t : Serializable smash_error_t :=
Derive Serializable smash_error_t_rect<NotOwner,AlreadySmashed>.

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


Notation "'piggy_smash_result_t'" := ((
  result piggy_bank_state_hacspec_t smash_error_t)) : hacspec_scope.

Definition piggy_smash_hacspec
  (ctx_7 : context_t)
  (state_8 : piggy_bank_state_hacspec_t): piggy_smash_result_t :=
  let '(owner_9, sender_10, balance_11) :=
    ctx_7 in 
  ifbnd negb ((owner_9) array_eq (sender_10)) : bool
  thenbnd (bind (@Err piggy_bank_state_hacspec_t smash_error_t (NotOwner)) (
      fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  ifbnd negb ((state_8) =.? (Intact)) : bool
  thenbnd (bind (@Err piggy_bank_state_hacspec_t smash_error_t (
        AlreadySmashed)) (fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  @Ok piggy_bank_state_hacspec_t smash_error_t (Smashed))).

Definition piggy_smash
  (ctx_12 : context_t)
  (state_13 : piggy_bank_state_hacspec_t): int64 :=
  @repr WORDSIZE64 0.
  Definition smash (st : State) (ctx : context_t) :=
  {| balance := piggy_smash ctx st.(state) ; owner := st.(owner); state := st.(state) |}.


Definition test_init_hacspec : bool :=
  (piggy_init_hacspec ) =.? (Intact).

Definition test_insert_intact
  (owner_14 : user_address_t)
  (balance_15 : int64)
  (amount_16 : int64): bool :=
  let sender_17 : user_address_t :=
    owner_14 in 
  let ctx_18 : (user_address_t ∏ user_address_t ∏ int64) :=
    (owner_14, sender_17, balance_15) in 
  (piggy_insert_hacspec (ctx_18) (amount_16) (Intact)) =.? (@Ok unit unit (tt)).
QuickChick (
  forAll g_user_address_t (fun owner_14 : user_address_t => forAll g_int64 (fun balance_15 : int64 => forAll g_int64 (fun amount_16 : int64 => test_insert_intact owner_14 balance_15 amount_16)))).

Definition test_insert_smashed
  (owner_19 : user_address_t)
  (balance_20 : int64)
  (amount_21 : int64): bool :=
  let sender_22 : user_address_t :=
    owner_19 in 
  let ctx_23 : (user_address_t ∏ user_address_t ∏ int64) :=
    (owner_19, sender_22, balance_20) in 
  (piggy_insert_hacspec (ctx_23) (amount_21) (Smashed)) =.? (@Err unit unit (
      tt)).
QuickChick (
  forAll g_user_address_t (fun owner_19 : user_address_t => forAll g_int64 (fun balance_20 : int64 => forAll g_int64 (fun amount_21 : int64 => test_insert_smashed owner_19 balance_20 amount_21)))).

Definition test_smash_intact
  (owner_24 : user_address_t)
  (balance_25 : int64): bool :=
  let sender_26 : user_address_t :=
    owner_24 in 
  let ctx_27 : (user_address_t ∏ user_address_t ∏ int64) :=
    (owner_24, sender_26, balance_25) in 
  (piggy_smash_hacspec (ctx_27) (Intact)) =.? (
    @Ok piggy_bank_state_hacspec_t smash_error_t (Smashed)).
QuickChick (
  forAll g_user_address_t (fun owner_24 : user_address_t => forAll g_int64 (fun balance_25 : int64 => test_smash_intact owner_24 balance_25))).

Definition test_smash_intact_not_owner
  (owner_28 : user_address_t)
  (sender_29 : user_address_t)
  (balance_30 : int64): bool :=
  let ctx_31 : (user_address_t ∏ user_address_t ∏ int64) :=
    (owner_28, sender_29, balance_30) in 
  ((owner_28) array_eq (sender_29)) || ((piggy_smash_hacspec (ctx_31) (
        Intact)) =.? (@Err piggy_bank_state_hacspec_t smash_error_t (
        NotOwner))).
QuickChick (
  forAll g_user_address_t (fun owner_28 : user_address_t => forAll g_user_address_t (fun sender_29 : user_address_t => forAll g_int64 (fun balance_30 : int64 => test_smash_intact_not_owner owner_28 sender_29 balance_30)))).

Definition test_smash_smashed
  (owner_32 : user_address_t)
  (balance_33 : int64): bool :=
  let sender_34 : user_address_t :=
    owner_32 in 
  let ctx_35 : (user_address_t ∏ user_address_t ∏ int64) :=
    (owner_32, sender_34, balance_33) in 
  (piggy_smash_hacspec (ctx_35) (Smashed)) =.? (
    @Err piggy_bank_state_hacspec_t smash_error_t (AlreadySmashed)).
QuickChick (
  forAll g_user_address_t (fun owner_32 : user_address_t => forAll g_int64 (fun balance_33 : int64 => test_smash_smashed owner_32 balance_33))).


Inductive Msg :=
| Insert
| Smash.

Global Instance Msg_serializable : Serializable Msg :=
Derive Serializable Msg_rect<Insert, Smash>.

Definition context_t_from_context (ctx : ContractCallContext) : context_t :=
  (ctx.(ctx_from), ctx.(ctx_origin), repr (ctx.(ctx_amount))).

Program Definition piggyBank_receive (chain : Chain) (ctx : ContractCallContext)
            (state : State) (msg : option Msg) : option (State * list ActionBody)
  := match msg with
     | Some Insert =>
         match state with
           {| state := st |} =>
             match piggy_insert_hacspec (context_t_from_context ctx) ctx.(ctx_amount) st with
               Ok x => Some (state, [])
             | Err _ => None
             end
         end
     | Some Smash =>
         match state with
           {| state := st |} =>
             match piggy_smash_hacspec (context_t_from_context ctx) st with
               Ok x => Some (state, [])
             | Err _ => None
             end
         end
     | None => None
     end.  

(** The piggybank contract *)
Definition piggyBank_contract : Contract Setup Msg State :=
  build_contract PiggyBank_State piggyBank_receive.
