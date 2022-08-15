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
Export Hacspec_Lib.

Require Import Hacspec_Concordium.
Export Hacspec_Concordium.

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
  (ctx_0 : context_t): piggy_bank_state_hacspec_t :=
  piggy_init_hacspec .

Notation "'piggy_insert_result_t'" := ((result unit unit)) : hacspec_scope.

Definition piggy_insert_hacspec
  (ctx_1 : context_t)
  (amount_2 : int64)
  (state_3 : piggy_bank_state_hacspec_t): piggy_insert_result_t :=
  match state_3 with
  | Intact => @Ok unit unit (tt)
  | Smashed => @Err unit unit (tt)
  end.

Definition piggy_insert
  (ctx_4 : context_t)
  (amount_5 : int64)
  (state_6 : piggy_bank_state_hacspec_t): int64 :=
  let '(_, _, balance_7) :=
    ctx_4 in 
  let _ : int32 := accept_hacspec  in 
  (balance_7) .+ (amount_5).
Definition insert (amount : int64)(st : State) (ctx : context_t) :=
  {| balance := amount .+ st.(balance) ; owner := st.(owner); state := st.(state) |}.


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
  (ctx_8 : context_t)
  (state_9 : piggy_bank_state_hacspec_t): piggy_smash_result_t :=
  let '(owner_10, sender_11, balance_12) :=
    ctx_8 in 
  ifbnd negb ((owner_10) array_eq (sender_11)) : bool
  thenbnd (bind (@Err piggy_bank_state_hacspec_t smash_error_t (NotOwner)) (
      fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  ifbnd negb ((state_9) =.? (Intact)) : bool
  thenbnd (bind (@Err piggy_bank_state_hacspec_t smash_error_t (
        AlreadySmashed)) (fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  @Ok piggy_bank_state_hacspec_t smash_error_t (Smashed))).

Definition piggy_smash
  (ctx_13 : context_t)
  (state_14 : piggy_bank_state_hacspec_t): int64 :=
  @repr WORDSIZE64 0.
  Definition smash (st : State) (ctx : context_t) :=
  {| balance := piggy_smash ctx st.(state) ; owner := st.(owner); state := Smashed |}.


Definition test_init_hacspec : bool :=
  (piggy_init_hacspec ) =.? (Intact).

Definition test_insert_intact
  (owner_15 : user_address_t)
  (balance_16 : int64)
  (amount_17 : int64): bool :=
  let sender_18 : user_address_t :=
    owner_15 in 
  let ctx_19 : (user_address_t ∏ user_address_t ∏ int64) :=
    (owner_15, sender_18, balance_16) in 
  (piggy_insert_hacspec (ctx_19) (amount_17) (Intact)) =.? (@Ok unit unit (tt)).
QuickChick (
  forAll g_user_address_t (fun owner_15 : user_address_t => forAll g_int64 (fun balance_16 : int64 => forAll g_int64 (fun amount_17 : int64 => test_insert_intact owner_15 balance_16 amount_17)))).

Definition test_insert_smashed
  (owner_20 : user_address_t)
  (balance_21 : int64)
  (amount_22 : int64): bool :=
  let sender_23 : user_address_t :=
    owner_20 in 
  let ctx_24 : (user_address_t ∏ user_address_t ∏ int64) :=
    (owner_20, sender_23, balance_21) in 
  (piggy_insert_hacspec (ctx_24) (amount_22) (Smashed)) =.? (@Err unit unit (
      tt)).
QuickChick (
  forAll g_user_address_t (fun owner_20 : user_address_t => forAll g_int64 (fun balance_21 : int64 => forAll g_int64 (fun amount_22 : int64 => test_insert_smashed owner_20 balance_21 amount_22)))).

Definition test_smash_intact
  (owner_25 : user_address_t)
  (balance_26 : int64): bool :=
  let sender_27 : user_address_t :=
    owner_25 in 
  let ctx_28 : (user_address_t ∏ user_address_t ∏ int64) :=
    (owner_25, sender_27, balance_26) in 
  (piggy_smash_hacspec (ctx_28) (Intact)) =.? (
    @Ok piggy_bank_state_hacspec_t smash_error_t (Smashed)).
QuickChick (
  forAll g_user_address_t (fun owner_25 : user_address_t => forAll g_int64 (fun balance_26 : int64 => test_smash_intact owner_25 balance_26))).

Definition test_smash_intact_not_owner
  (owner_29 : user_address_t)
  (sender_30 : user_address_t)
  (balance_31 : int64): bool :=
  let ctx_32 : (user_address_t ∏ user_address_t ∏ int64) :=
    (owner_29, sender_30, balance_31) in 
  ((owner_29) array_eq (sender_30)) || ((piggy_smash_hacspec (ctx_32) (
        Intact)) =.? (@Err piggy_bank_state_hacspec_t smash_error_t (
        NotOwner))).
QuickChick (
  forAll g_user_address_t (fun owner_29 : user_address_t => forAll g_user_address_t (fun sender_30 : user_address_t => forAll g_int64 (fun balance_31 : int64 => test_smash_intact_not_owner owner_29 sender_30 balance_31)))).

Definition test_smash_smashed
  (owner_33 : user_address_t)
  (balance_34 : int64): bool :=
  let sender_35 : user_address_t :=
    owner_33 in 
  let ctx_36 : (user_address_t ∏ user_address_t ∏ int64) :=
    (owner_33, sender_35, balance_34) in 
  (piggy_smash_hacspec (ctx_36) (Smashed)) =.? (
    @Err piggy_bank_state_hacspec_t smash_error_t (AlreadySmashed)).
QuickChick (
  forAll g_user_address_t (fun owner_33 : user_address_t => forAll g_int64 (fun balance_34 : int64 => test_smash_smashed owner_33 balance_34))).

Inductive Msg :=
| INSERT
| SMASH.
Global Instance Msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect<INSERT,SMASH>.
Definition Isome_nameI_receive (chain : Chain) (ctx : ContractCallContext) (state : State) (msg : option Msg) : option (State * list ActionBody) :=
  match msg with
  | Some INSERT => Some (insert (repr (ctx.(ctx_amount))) state (ctx.(ctx_from), ctx.(ctx_origin), repr (ctx.(ctx_amount))), [])
  | Some SMASH => Some (smash state (ctx.(ctx_from), ctx.(ctx_origin), repr (ctx.(ctx_amount))), [act_transfer state.(owner) state.(balance)])
  | None => None
  end.

Definition piggyBank_contract : Contract Setup Msg State :=
  build_contract PiggyBank_State Isome_nameI_receive.

(** * Functional correctness *)
Lemma piggybank_correct {prev_state next_state acts msg chain ctx} :
  prev_state.(state) = Intact -> Isome_nameI_receive chain ctx prev_state msg = Some (next_state, acts) ->
  match msg with
    | Some m => 
      match m with
      | INSERT => ctx.(ctx_amount) + unsigned (prev_state.(balance)) = unsigned (next_state.(balance))
      | SMASH => prev_state.(owner) = ctx.(ctx_from) -> next_state.(state) = Smashed /\ 
        next_state.(balance) = 0 /\ acts = [act_transfer prev_state.(owner) prev_state.(balance)]
      end
    | None => False
  end.
Proof.
  intros H1 H2. 
  unfold Isome_nameI_receive in H2. 
  destruct msg.
  destruct m.
  - destruct prev_state. unfold balance. unfold state in H1. rewrite H1 in H2 ; clear H1. unfold insert in *. 
    cbn in H2. inversion H2.
    Set Printing Coercions.
    Set Printing Implicit.
    
    unfold add.
    unfold int64_to_nat.
    unfold uint_size_to_nat.
    unfold from_uint_size.
    unfold Z_to_uint_size.
    repeat rewrite unsigned_repr.
    reflexivity. admit. admit. admit.
  - intros H3. destruct prev_state. cbn in *. rewrite H1 in H2. rewrite H3 in H2. unfold smash in *. unfold piggy_smash in *.
    destruct_address_eq.
    + unfold smash in H2. inversion H2. cbn. rewrite H3. auto. 
  - discriminate.
Admitted.

(** ** Owner never changes *)
Lemma owner_never_changes {prev_state next_state msg chain ctx acts}:
Isome_nameI_receive chain ctx prev_state msg = Some (next_state, acts) -> prev_state.(owner) = next_state.(owner).
Proof.
  intros H. 
  unfold Isome_nameI_receive in H. 
  destruct msg.
  destruct m; cbn in *; 
  destruct prev_state; cbn in * ; try easy.
  inversion H. cbn in *. reflexivity.
  - destruct_address_eq; inversion H; auto.
  - destruct_address_eq; inversion H; auto.
Qed.
