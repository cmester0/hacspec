(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:1]] *)

(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.
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
(* wccd - Coq code:1 ends here *)

(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:2]] *)
Require Import Hacspec_Lib.
Export Hacspec_Lib.
(* wccd - Coq code:2 ends here *)

(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:3]] *)
Require Import Hacspec_Concordium.
Export Hacspec_Concordium.
(* wccd - Coq code:3 ends here *)

(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:4]] *)
Require Import Concert_Lib.
Export Concert_Lib.
(* wccd - Coq code:4 ends here *)

(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:5]] *)
Require Import Cis1.
Export Cis1.
(* wccd - Coq code:5 ends here *)

(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:6]] *)
Notation "'contract_token_id_t'" := (token_id_unit_t) : hacspec_scope.
(* wccd - Coq code:6 ends here *)

(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:7]] *)
Definition token_id_wccd_v : contract_token_id_t :=
  TokenIdUnit (tt).
(* wccd - Coq code:7 ends here *)

(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:8]] *)
Inductive address_state_hacspec_t :=
| AddressStateHacspec : (token_amount_t ∏ public_byte_seq
) -> address_state_hacspec_t.
Global Instance serializable_address_state_hacspec_t : Serializable address_state_hacspec_t :=
  Derive Serializable address_state_hacspec_t_rect<AddressStateHacspec>.

(* wccd - Coq code:8 ends here *)

(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:9]] *)
Inductive state_hacspec_t :=
| StateHacspec : public_byte_seq -> state_hacspec_t.
Global Instance serializable_state_hacspec_t : Serializable state_hacspec_t :=
  Derive Serializable state_hacspec_t_rect<StateHacspec>.
Definition State := context_t ∏ state_hacspec_t.

(* wccd - Coq code:9 ends here *)

(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:10]] *)
Inductive unwrap_params_hacspec_t :=
| UnwrapParamsHacspec : (
  token_amount_t ∏
  public_byte_seq ∏
  receiver_hacspec_t ∏
  additional_data_hacspec_t
) -> unwrap_params_hacspec_t.
Global Instance serializable_unwrap_params_hacspec_t : Serializable unwrap_params_hacspec_t :=
  Derive Serializable unwrap_params_hacspec_t_rect<UnwrapParamsHacspec>.

(* wccd - Coq code:10 ends here *)

(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:11]] *)
Inductive wrap_params_hacspec_t :=
| WrapParamsHacspec : (receiver_hacspec_t ∏ additional_data_hacspec_t
) -> wrap_params_hacspec_t.
Global Instance serializable_wrap_params_hacspec_t : Serializable wrap_params_hacspec_t :=
  Derive Serializable wrap_params_hacspec_t_rect<WrapParamsHacspec>.

(* wccd - Coq code:11 ends here *)

(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:12]] *)
Definition contract_init (ctx_0 : context_t): (context_t ∏ state_hacspec_t) :=
  (ctx_0, StateHacspec (seq_new_ (default) (usize 0))).
Definition Setup := unit.
Definition CIS1_wCCD_State (chain : Chain) (ctx : ContractCallContext) (setup : Setup) : option (
  context_t ∏
  state_hacspec_t
) :=
  Some (contract_init (Context (ctx.(ctx_from), ctx.(ctx_origin), repr ctx.(ctx_amount), 0 (* TODO *)))).

(* wccd - Coq code:12 ends here *)

(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:13]] *)
Definition contract_wrap
  (ctx_1 : (context_t ∏ state_hacspec_t))
  (amount_2 : int64): (option ((context_t ∏ state_hacspec_t) ∏ list_action_t
    )) :=
  let '(Context ((owner_3, sender_4, balance_5, time_6)), state_7) :=
    ctx_1 in 
  let s_8 : seq has_action_t :=
    seq_new_ (default) (usize 0) in 
  @Some ((context_t ∏ state_hacspec_t) ∏ list_action_t) ((
      (Context ((owner_3, sender_4, balance_5, time_6)), state_7),
      s_8
    )).

Definition wrap (amount : int64) (st : State) (param : wrap_params_hacspec_t) :=
  contract_wrap st amount.

(* wccd - Coq code:13 ends here *)

(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:14]] *)
Definition contract_unwrap
  (ctx_9 : (context_t ∏ state_hacspec_t)): (option (
      (context_t ∏ state_hacspec_t) ∏
      list_action_t
    )) :=
  let '(Context ((owner_10, sender_11, balance_12, time_13)), state_14) :=
    ctx_9 in 
  let s_15 : seq has_action_t :=
    seq_new_ (default) (usize 0) in 
  @Some ((context_t ∏ state_hacspec_t) ∏ list_action_t) ((
      (Context ((owner_10, sender_11, balance_12, time_13)), state_14),
      s_15
    )).

Definition unwrap (st : State) (param : unwrap_params_hacspec_t) :=
  contract_unwrap st.

(* wccd - Coq code:14 ends here *)

(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:15]] *)
Notation "'transfer_parameter_hacspec_t'" := (unit) : hacspec_scope.
(* wccd - Coq code:15 ends here *)

(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:16]] *)
Definition contract_transfer
  (ctx_16 : (context_t ∏ state_hacspec_t)): (option (
      (context_t ∏ state_hacspec_t) ∏
      list_action_t
    )) :=
  let '(Context ((owner_17, sender_18, balance_19, time_20)), state_21) :=
    ctx_16 in 
  let s_22 : seq has_action_t :=
    seq_new_ (default) (usize 0) in 
  @Some ((context_t ∏ state_hacspec_t) ∏ list_action_t) ((
      (Context ((owner_17, sender_18, balance_19, time_20)), state_21),
      s_22
    )).

Definition transfer (st : State) (param : transfer_parameter_hacspec_t) :=
  contract_transfer st.

(* wccd - Coq code:16 ends here *)

(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:17]] *)
Definition contract_update_operator
  (ctx_23 : (context_t ∏ state_hacspec_t)): (option (
      (context_t ∏ state_hacspec_t) ∏
      list_action_t
    )) :=
  let '(Context ((owner_24, sender_25, balance_26, time_27)), state_28) :=
    ctx_23 in 
  let s_29 : seq has_action_t :=
    seq_new_ (default) (usize 0) in 
  @Some ((context_t ∏ state_hacspec_t) ∏ list_action_t) ((
      (Context ((owner_24, sender_25, balance_26, time_27)), state_28),
      s_29
    )).

Definition updateOperator (st : State) (param : update_operator_params_t) :=
  contract_update_operator st.

(* wccd - Coq code:17 ends here *)

(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:18]] *)
Definition contract_balance_of
  (ctx_30 : (context_t ∏ state_hacspec_t)): (option (
      (context_t ∏ state_hacspec_t) ∏
      list_action_t
    )) :=
  let '(Context ((owner_31, sender_32, balance_33, time_34)), state_35) :=
    ctx_30 in 
  let s_36 : seq has_action_t :=
    seq_new_ (default) (usize 0) in 
  @Some ((context_t ∏ state_hacspec_t) ∏ list_action_t) ((
      (Context ((owner_31, sender_32, balance_33, time_34)), state_35),
      s_36
    )).

Definition balanceOf (st : State) (
  param : contract_balance_of_query_params_t) :=
  contract_balance_of st.

(* wccd - Coq code:18 ends here *)

(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:19]] *)
Definition contract_operator_of
  (ctx_37 : (context_t ∏ state_hacspec_t)): (option (
      (context_t ∏ state_hacspec_t) ∏
      list_action_t
    )) :=
  let '(Context ((owner_38, sender_39, balance_40, time_41)), state_42) :=
    ctx_37 in 
  let s_43 : seq has_action_t :=
    seq_new_ (default) (usize 0) in 
  @Some ((context_t ∏ state_hacspec_t) ∏ list_action_t) ((
      (Context ((owner_38, sender_39, balance_40, time_41)), state_42),
      s_43
    )).

Definition operatorOf (st : State) (param : operator_of_query_params_t) :=
  contract_operator_of st.

(* wccd - Coq code:19 ends here *)

(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:20]] *)
Definition contract_token_metadata
  (ctx_44 : (context_t ∏ state_hacspec_t)): (option (
      (context_t ∏ state_hacspec_t) ∏
      list_action_t
    )) :=
  let '(Context ((owner_45, sender_46, balance_47, time_48)), state_49) :=
    ctx_44 in 
  let s_50 : seq has_action_t :=
    seq_new_ (default) (usize 0) in 
  @Some ((context_t ∏ state_hacspec_t) ∏ list_action_t) ((
      (Context ((owner_45, sender_46, balance_47, time_48)), state_49),
      s_50
    )).

Definition tokenMetadata (st : State) (
  param : contract_token_metadata_query_params_t) :=
  contract_token_metadata st.

(* wccd - Coq code:20 ends here *)

(* [[file:WCCD.org::* wccd - Coq code][wccd - Coq code:21]] *)
Inductive Msg :=
| WRAP
| UNWRAP
| TRANSFER
| UPDATEOPERATOR
| BALANCEOF
| OPERATOROF
| TOKENMETADATA.
Global Instance Msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect<WRAP,UNWRAP,TRANSFER,UPDATEOPERATOR,BALANCEOF,OPERATOROF,TOKENMETADATA>.
Definition CIS1_wCCD_receive (chain : Chain) (ctx : ContractCallContext) (state : State) (msg : option Msg) : option (State * list ActionBody) :=
  to_action_body_list ctx (match msg with
    | Some WRAP => (wrap (repr ctx.(ctx_amount)) state)
    | Some UNWRAP => (unwrap state)
    | Some TRANSFER => (transfer state)
    | Some UPDATEOPERATOR => (updateOperator state)
    | Some BALANCEOF => (balanceOf state)
    | Some OPERATOROF => (operatorOf state)
    | Some TOKENMETADATA => (tokenMetadata state)
    | None => None
    end).

Definition CIS1_wCCD_contract : Contract Setup Msg State :=
  build_contract CIS1_wCCD_State CIS1_wCCD_receive.

(* wccd - Coq code:21 ends here *)