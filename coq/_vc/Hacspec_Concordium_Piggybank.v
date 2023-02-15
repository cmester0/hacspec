(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.

From QuickChick Require Import QuickChick.
Require Import QuickChickLib.

From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import Automation.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ContractCommon.
From Coq Require Import Morphisms ZArith Basics.
Open Scope Z.
Set Nonrecursive Elimination Schemes.
Require Import Hacspec_Lib.
Export Hacspec_Lib.

Require Import Hacspec_Concordium.
Export Hacspec_Concordium.

Require Import Concert_Lib.
Export Concert_Lib.

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
#[global] Instance gen_piggy_bank_state_hacspec_t : Gen (piggy_bank_state_hacspec_t) := Build_Gen piggy_bank_state_hacspec_t g_piggy_bank_state_hacspec_t.

Notation State := (context_t '× piggy_bank_state_hacspec_t).


Definition piggy_init_hacspec  : piggy_bank_state_hacspec_t :=
  Intact.


Definition piggy_init
  (ctx_0 : context_t)
  : (context_t '× piggy_bank_state_hacspec_t) :=
  (ctx_0, piggy_init_hacspec ).
Definition Setup := unit.
Definition PiggyBank_State (chain : Chain) (ctx : ContractCallContext) (setup : Setup) : ResultMonad.result (
  context_t '×
  piggy_bank_state_hacspec_t
) unit :=
  ResultMonad.Ok (piggy_init (Context (ctx.(ctx_from), ctx.(ctx_origin), repr ctx.(ctx_amount), 0 (* TODO *)))).


Theorem ensures_piggy_init : forall result_1 (ctx_0 : context_t),
 @piggy_init ctx_0 = result_1 ->
 (result_1 = (ctx_0, Intact)).
 Proof. Admitted.

Notation "'piggy_insert_result_t'" := ((result unit unit)) : hacspec_scope.

Definition piggy_insert_hacspec
  (ctx_2 : context_t)
  (amount_3 : int64)
  (state_4 : piggy_bank_state_hacspec_t)
  : piggy_insert_result_t :=
  match state_4 with
  | Intact => @Ok unit unit (tt)
  | Smashed => @Err unit unit (tt)
  end.


Definition piggy_insert
  (ctx_state_5 : (context_t '× piggy_bank_state_hacspec_t))
  (amount_6 : int64)
  : (option ((context_t '× piggy_bank_state_hacspec_t) '× list_action_t)) :=
  let '(ctx_7, state_8) :=
    ctx_state_5 in
  let 'Context ((a_9, c_10, balance_11, d_12)) :=
    ctx_7 in
  let _ : int32 :=
    accept_hacspec  in
  let temp_13 : (result unit unit) :=
    piggy_insert_hacspec (ctx_7) (amount_6) (state_8) in
  bind (match temp_13 with
    | Ok (_) => @Some unit (tt)
    | Err (_) => @None unit
    end) (fun _ => let s_14 : seq has_action_t :=
      seq_new_ (default : has_action_t) (usize 0) in
    let s_14 :=
      seq_upd s_14 (usize 0) (accept_action ) in
    @Some ((context_t '× piggy_bank_state_hacspec_t) '× list_action_t) ((
        (Context ((a_9, c_10, (balance_11) .+ (amount_6), d_12)), state_8),
        s_14
      ))).

Definition insert (amount : int64) (st : State) :=
  piggy_insert st amount.


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
#[global] Instance gen_smash_error_t : Gen (smash_error_t) := Build_Gen smash_error_t g_smash_error_t.


Notation "'piggy_smash_result_t'" := ((
  result piggy_bank_state_hacspec_t smash_error_t)) : hacspec_scope.

Definition piggy_smash_hacspec
  (ctx_15 : context_t)
  (state_16 : piggy_bank_state_hacspec_t)
  : piggy_smash_result_t :=
  let 'Context ((owner_17, sender_18, balance_19, metadata_20)) :=
    ctx_15 in
  ifbnd negb ((owner_17) array_eq (sender_18)) : bool
  thenbnd (bind (@Err piggy_bank_state_hacspec_t smash_error_t (NotOwner)) (
      fun _ => @Ok unit smash_error_t (tt)))
  else (tt) >> (fun 'tt =>
  ifbnd negb ((state_16) =.? (Intact)) : bool
  thenbnd (bind (@Err piggy_bank_state_hacspec_t smash_error_t (
        AlreadySmashed)) (fun _ => @Ok unit smash_error_t (tt)))
  else (tt) >> (fun 'tt =>
  @Ok piggy_bank_state_hacspec_t smash_error_t (Smashed))).


Theorem ensures_piggy_smash_hacspec : forall result_1 (ctx_15 : context_t) (
  state_16 : piggy_bank_state_hacspec_t),
 @piggy_smash_hacspec ctx_15 state_16 = result_1 ->
 (~ (state_16 = Intact) ->
   result_1 = @Err piggy_bank_state_hacspec_t smash_error_t (
     AlreadySmashed) \/ forall owner_21 : user_address_t,
   forall sender_22 : user_address_t,
   forall balance_23 : int64,
   forall metadata_24 : int64,
   ctx_15 = Context ((owner_21, sender_22, balance_23, metadata_24)) ->
   ~ (owner_21 = sender_22) ->
   result_1 = @Err piggy_bank_state_hacspec_t smash_error_t (NotOwner)).
 Proof. Admitted.

Definition piggy_smash
  (ctx_state_25 : (context_t '× piggy_bank_state_hacspec_t))
  : (option ((context_t '× piggy_bank_state_hacspec_t) '× list_action_t)) :=
  let '(ctx_26, state_27) :=
    ctx_state_25 in
  let 'Context ((a_28, c_29, balance_30, d_31)) :=
    ctx_26 in
  let _ : int32 :=
    accept_hacspec  in
  let smash_32 : (result piggy_bank_state_hacspec_t smash_error_t) :=
    piggy_smash_hacspec (ctx_26) (state_27) in
  bind (match smash_32 with
    | Ok (a_33) => @Some piggy_bank_state_hacspec_t (a_33)
    | Err (b_34) => @None piggy_bank_state_hacspec_t
    end) (fun new_state_35 => let s_36 : seq has_action_t :=
      seq_new_ (default : has_action_t) (usize 1) in
    @Some ((context_t '× piggy_bank_state_hacspec_t) '× list_action_t) ((
        (Context ((a_28, c_29, @repr WORDSIZE64 0, d_31)), new_state_35),
        s_36
      ))).

Definition smash (st : State) :=
  piggy_smash st.


Definition test_init_hacspec  : bool :=
  (piggy_init_hacspec ) =.? (Intact).


Definition test_insert_intact (ctx_37 : context_t) (amount_38 : int64) : bool :=
  (piggy_insert_hacspec (ctx_37) (amount_38) (Intact)) =.? (@Ok unit unit (tt)).

(*QuickChick (
  forAll g_context_t (fun ctx_37 : context_t =>forAll g_int64 (fun amount_38 : int64 =>test_insert_intact ctx_37 amount_38))).*)


Definition test_insert_smashed
  (ctx_39 : context_t)
  (amount_40 : int64)
  : bool :=
  (piggy_insert_hacspec (ctx_39) (amount_40) (Smashed)) =.? (@Err unit unit (
      tt)).

(*QuickChick (
  forAll g_context_t (fun ctx_39 : context_t =>forAll g_int64 (fun amount_40 : int64 =>test_insert_smashed ctx_39 amount_40))).*)


Definition test_smash_intact
  (owner_41 : user_address_t)
  (balance_42 : int64)
  (metadata_43 : int64)
  : bool :=
  let sender_44 : user_address_t :=
    owner_41 in
  let ctx_45 : context_t :=
    Context ((owner_41, sender_44, balance_42, metadata_43)) in
  (piggy_smash_hacspec (ctx_45) (Intact)) =.? (
    @Ok piggy_bank_state_hacspec_t smash_error_t (Smashed)).

(*QuickChick (
  forAll g_user_address_t (fun owner_41 : user_address_t =>forAll g_int64 (fun balance_42 : int64 =>forAll g_int64 (fun metadata_43 : int64 =>test_smash_intact owner_41 balance_42 metadata_43)))).*)


Definition test_smash_intact_not_owner
  (owner_46 : user_address_t)
  (sender_47 : user_address_t)
  (balance_48 : int64)
  (metadata_49 : int64)
  : bool :=
  let ctx_50 : context_t :=
    Context ((owner_46, sender_47, balance_48, metadata_49)) in
  ((owner_46) array_eq (sender_47)) || ((piggy_smash_hacspec (ctx_50) (
        Intact)) =.? (@Err piggy_bank_state_hacspec_t smash_error_t (
        NotOwner))).

(*QuickChick (
  forAll g_user_address_t (fun owner_46 : user_address_t =>forAll g_user_address_t (fun sender_47 : user_address_t =>forAll g_int64 (fun balance_48 : int64 =>forAll g_int64 (fun metadata_49 : int64 =>test_smash_intact_not_owner owner_46 sender_47 balance_48 metadata_49))))).*)


Definition test_smash_smashed
  (owner_51 : user_address_t)
  (balance_52 : int64)
  (metadata_53 : int64)
  : bool :=
  let sender_54 : user_address_t :=
    owner_51 in
  let ctx_55 : context_t :=
    Context ((owner_51, sender_54, balance_52, metadata_53)) in
  (piggy_smash_hacspec (ctx_55) (Smashed)) =.? (
    @Err piggy_bank_state_hacspec_t smash_error_t (AlreadySmashed)).

(*QuickChick (
  forAll g_user_address_t (fun owner_51 : user_address_t =>forAll g_int64 (fun balance_52 : int64 =>forAll g_int64 (fun metadata_53 : int64 =>test_smash_smashed owner_51 balance_52 metadata_53)))).*)


Inductive Msg :=
| INSERT
| SMASH.
Global Instance Msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect<INSERT,SMASH>.
Definition PiggyBank_receive (chain : Chain) (ctx : ContractCallContext) (state : State) (msg : option Msg) : ResultMonad.result (State * list ActionBody) unit :=
  to_action_body_list ctx (match msg with
    | Some (INSERT) => (insert (repr ctx.(ctx_amount)) state)
    | Some (SMASH) => (smash state)
    | None => None
    end).

Definition PiggyBank_contract : Blockchain.Contract Setup Msg State unit :=
  build_contract PiggyBank_State PiggyBank_receive.
