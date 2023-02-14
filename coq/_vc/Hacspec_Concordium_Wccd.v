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

Require Import Cis1.
Export Cis1.

Notation "'contract_token_id_t'" := (token_id_unit_t) : hacspec_scope.

Definition token_id_wccd_v : contract_token_id_t :=
  TokenIdUnit (tt).

Inductive address_state_hacspec_t :=
| AddressStateHacspec : (token_amount_t '× public_byte_seq
) -> address_state_hacspec_t.
Global Instance serializable_address_state_hacspec_t : Serializable address_state_hacspec_t :=
  Derive Serializable address_state_hacspec_t_rect<AddressStateHacspec>.


Inductive state_hacspec_t :=
| StateHacspec : public_byte_seq -> state_hacspec_t.
Global Instance serializable_state_hacspec_t : Serializable state_hacspec_t :=
  Derive Serializable state_hacspec_t_rect<StateHacspec>.

Notation State := (context_t '× state_hacspec_t).


Inductive unwrap_params_hacspec_t :=
| UnwrapParamsHacspec : (
  token_amount_t '×
  public_byte_seq '×
  receiver_hacspec_t '×
  additional_data_hacspec_t
) -> unwrap_params_hacspec_t.
Global Instance serializable_unwrap_params_hacspec_t : Serializable unwrap_params_hacspec_t :=
  Derive Serializable unwrap_params_hacspec_t_rect<UnwrapParamsHacspec>.


Inductive wrap_params_hacspec_t :=
| WrapParamsHacspec : (receiver_hacspec_t '× additional_data_hacspec_t
) -> wrap_params_hacspec_t.
Global Instance serializable_wrap_params_hacspec_t : Serializable wrap_params_hacspec_t :=
  Derive Serializable wrap_params_hacspec_t_rect<WrapParamsHacspec>.


Definition contract_init
  (ctx_0 : context_t)
  
  : (context_t '× state_hacspec_t) :=
  (ctx_0, StateHacspec (seq_new_ (default : int8) (usize 0))).
Definition Setup := unit.
Definition CIS1_wCCD_State (chain : Chain) (ctx : ContractCallContext) (setup : Setup) : ResultMonad.result (
  context_t '×
  state_hacspec_t
) unit :=
  ResultMonad.Ok (contract_init (Context (ctx.(ctx_from), ctx.(ctx_origin), repr ctx.(ctx_amount), 0 (* TODO *)))).


Definition contract_wrap
  (ctx_1 : (context_t '× state_hacspec_t))
  (amount_2 : int64)
  (params_3 : wrap_params_hacspec_t)
  
  : (option ((context_t '× state_hacspec_t) '× list_action_t)) :=
  let '(Context ((owner_4, sender_5, balance_6, time_7)), state_8) :=
    ctx_1 in 
  let s_9 : seq has_action_t :=
    seq_new_ (default : has_action_t) (usize 0) in 
  @Some ((context_t '× state_hacspec_t) '× list_action_t) ((
      (Context ((owner_4, sender_5, balance_6, time_7)), state_8),
      s_9
    )).

Definition wrap (amount : int64) (st : State) (param : wrap_params_hacspec_t) :=
  contract_wrap st amount param.


Definition contract_unwrap
  (ctx_10 : (context_t '× state_hacspec_t))
  (param_11 : unwrap_params_hacspec_t)
  
  : (option ((context_t '× state_hacspec_t) '× list_action_t)) :=
  let '(Context ((owner_12, sender_13, balance_14, time_15)), state_16) :=
    ctx_10 in 
  let s_17 : seq has_action_t :=
    seq_new_ (default : has_action_t) (usize 0) in 
  @Some ((context_t '× state_hacspec_t) '× list_action_t) ((
      (Context ((owner_12, sender_13, balance_14, time_15)), state_16),
      s_17
    )).

Definition unwrap (st : State) (param : unwrap_params_hacspec_t) :=
  contract_unwrap st param.


Notation "'transfer_parameter_hacspec_t'" := (unit) : hacspec_scope.

Definition contract_transfer
  (ctx_18 : (context_t '× state_hacspec_t))
  (param_19 : transfer_parameter_hacspec_t)
  
  : (option ((context_t '× state_hacspec_t) '× list_action_t)) :=
  let '(Context ((owner_20, sender_21, balance_22, time_23)), state_24) :=
    ctx_18 in 
  let s_25 : seq has_action_t :=
    seq_new_ (default : has_action_t) (usize 0) in 
  @Some ((context_t '× state_hacspec_t) '× list_action_t) ((
      (Context ((owner_20, sender_21, balance_22, time_23)), state_24),
      s_25
    )).

Definition transfer (st : State) (param : transfer_parameter_hacspec_t) :=
  contract_transfer st param.


Definition contract_update_operator
  (ctx_26 : (context_t '× state_hacspec_t))
  (param_27 : update_operator_params_hacspec_t)
  
  : (option ((context_t '× state_hacspec_t) '× list_action_t)) :=
  let '(Context ((owner_28, sender_29, balance_30, time_31)), state_32) :=
    ctx_26 in 
  let s_33 : seq has_action_t :=
    seq_new_ (default : has_action_t) (usize 0) in 
  @Some ((context_t '× state_hacspec_t) '× list_action_t) ((
      (Context ((owner_28, sender_29, balance_30, time_31)), state_32),
      s_33
    )).

Definition updateOperator (st : State) (
  param : update_operator_params_hacspec_t) :=
  contract_update_operator st param.


Notation "'balance_of_query_contract_token_id_t'" := ((
  contract_token_id_t '×
  user_address_t
)) : hacspec_scope.

Notation "'contract_balance_of_query_params_contract_token_id_t'" := ((
  (int64 '× int64) '×
  int64 '×
  seq balance_of_query_contract_token_id_t
)) : hacspec_scope.

Definition contract_balance_of
  (ctx_34 : (context_t '× state_hacspec_t))
  (param_35 : contract_balance_of_query_params_contract_token_id_t)
  
  : (option ((context_t '× state_hacspec_t) '× list_action_t)) :=
  let '(Context ((owner_36, sender_37, balance_38, time_39)), state_40) :=
    ctx_34 in 
  let s_41 : seq has_action_t :=
    seq_new_ (default : has_action_t) (usize 0) in 
  @Some ((context_t '× state_hacspec_t) '× list_action_t) ((
      (Context ((owner_36, sender_37, balance_38, time_39)), state_40),
      s_41
    )).

Definition balanceOf (st : State) (
  param : contract_balance_of_query_params_contract_token_id_t) :=
  contract_balance_of st param.


Definition contract_operator_of
  (ctx_42 : (context_t '× state_hacspec_t))
  (param_43 : operator_of_query_params_t)
  
  : (option ((context_t '× state_hacspec_t) '× list_action_t)) :=
  let '(Context ((owner_44, sender_45, balance_46, time_47)), state_48) :=
    ctx_42 in 
  let s_49 : seq has_action_t :=
    seq_new_ (default : has_action_t) (usize 0) in 
  @Some ((context_t '× state_hacspec_t) '× list_action_t) ((
      (Context ((owner_44, sender_45, balance_46, time_47)), state_48),
      s_49
    )).

Definition operatorOf (st : State) (param : operator_of_query_params_t) :=
  contract_operator_of st param.


Notation "'contract_token_metadata_query_params_t'" := ((
  (int64 '× int64) '×
  int64 '×
  seq contract_token_id_t
)) : hacspec_scope.

Definition contract_token_metadata
  (ctx_50 : (context_t '× state_hacspec_t))
  (param_51 : contract_token_metadata_query_params_t)
  
  : (option ((context_t '× state_hacspec_t) '× list_action_t)) :=
  let '(Context ((owner_52, sender_53, balance_54, time_55)), state_56) :=
    ctx_50 in 
  let s_57 : seq has_action_t :=
    seq_new_ (default : has_action_t) (usize 0) in 
  @Some ((context_t '× state_hacspec_t) '× list_action_t) ((
      (Context ((owner_52, sender_53, balance_54, time_55)), state_56),
      s_57
    )).

Definition tokenMetadata (st : State) (
  param : contract_token_metadata_query_params_t) :=
  contract_token_metadata st param.


Inductive Msg :=
| WRAP (_ : wrap_params_hacspec_t)
| UNWRAP (_ : unwrap_params_hacspec_t)
| TRANSFER (_ : transfer_parameter_hacspec_t)
| UPDATEOPERATOR (_ : update_operator_params_hacspec_t)
| BALANCEOF (_ : contract_balance_of_query_params_contract_token_id_t)
| OPERATOROF (_ : operator_of_query_params_t)
| TOKENMETADATA (_ : contract_token_metadata_query_params_t).
Global Instance Msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect<WRAP,UNWRAP,TRANSFER,UPDATEOPERATOR,BALANCEOF,OPERATOROF,TOKENMETADATA>.
Definition CIS1_wCCD_receive (chain : Chain) (ctx : ContractCallContext) (state : State) (msg : option Msg) : ResultMonad.result (State * list ActionBody) unit :=
  to_action_body_list ctx (match msg with
    | Some (WRAP param) => (wrap (repr ctx.(ctx_amount)) state param)
    | Some (UNWRAP param) => (unwrap state param)
    | Some (TRANSFER param) => (transfer state param)
    | Some (UPDATEOPERATOR param) => (updateOperator state param)
    | Some (BALANCEOF param) => (balanceOf state param)
    | Some (OPERATOROF param) => (operatorOf state param)
    | Some (TOKENMETADATA param) => (tokenMetadata state param)
    | None => None
    end).

Definition CIS1_wCCD_contract : Blockchain.Contract Setup Msg State unit :=
  build_contract CIS1_wCCD_State CIS1_wCCD_receive.
