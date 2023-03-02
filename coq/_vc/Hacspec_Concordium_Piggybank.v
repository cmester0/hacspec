(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.

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


Inductive Msg :=
| INSERT.
Global Instance Msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect<INSERT>.
Definition PiggyBank_receive (chain : Chain) (ctx : ContractCallContext) (state : State) (msg : option Msg) : ResultMonad.result (State * list ActionBody) unit :=
  to_action_body_list ctx (match msg with
    | Some (INSERT) => (insert (repr ctx.(ctx_amount)) state)
    | None => None
    end).

Definition PiggyBank_contract : Blockchain.Contract Setup Msg State unit :=
  build_contract PiggyBank_State PiggyBank_receive.
