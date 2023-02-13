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

Definition transfer_event_tag_v : int8 :=
  @repr WORDSIZE8 255.

Definition mint_event_tag_v : int8 :=
  (@repr WORDSIZE8 255) .- (@repr WORDSIZE8 1).

Definition burn_event_tag_v : int8 :=
  (@repr WORDSIZE8 255) .- (@repr WORDSIZE8 2).

Definition update_operator_event_tag_v : int8 :=
  (@repr WORDSIZE8 255) .- (@repr WORDSIZE8 3).

Definition token_metadata_event_tag_v : int8 :=
  (@repr WORDSIZE8 255) .- (@repr WORDSIZE8 4).

Definition sha256_t := nseq (int8) (usize 32).

Inductive metadata_url_t :=
| MetadataUrl : (string_t '× (option sha256_t)) -> metadata_url_t.
Global Instance serializable_metadata_url_t : Serializable metadata_url_t :=
  Derive Serializable metadata_url_t_rect<MetadataUrl>.


Inductive token_id_vec_t :=
| TokenIdVec : public_byte_seq -> token_id_vec_t.
Global Instance serializable_token_id_vec_t : Serializable token_id_vec_t :=
  Derive Serializable token_id_vec_t_rect<TokenIdVec>.


Inductive token_id_uint32_t :=
| TokenIdU32 : int32 -> token_id_uint32_t.
Global Instance serializable_token_id_uint32_t : Serializable token_id_uint32_t :=
  Derive Serializable token_id_uint32_t_rect<TokenIdU32>.


Inductive token_id_uint16_t :=
| TokenIdU16 : int16 -> token_id_uint16_t.
Global Instance serializable_token_id_uint16_t : Serializable token_id_uint16_t :=
  Derive Serializable token_id_uint16_t_rect<TokenIdU16>.


Inductive token_id_uint8_t :=
| TokenIdU8 : int8 -> token_id_uint8_t.
Global Instance serializable_token_id_uint8_t : Serializable token_id_uint8_t :=
  Derive Serializable token_id_uint8_t_rect<TokenIdU8>.


Inductive token_id_unit_t :=
| TokenIdUnit : unit -> token_id_unit_t.
Global Instance serializable_token_id_unit_t : Serializable token_id_unit_t :=
  Derive Serializable token_id_unit_t_rect<TokenIdUnit>.


Notation "'token_amount_t'" := (int64) : hacspec_scope.

Inductive operator_update_t :=
| Remove : operator_update_t
| Add : operator_update_t.
Global Instance serializable_operator_update_t : Serializable operator_update_t :=
  Derive Serializable operator_update_t_rect<Remove,Add>.


Inductive update_operator_event_t :=
| UpdateOperatorEvent : (operator_update_t '× user_address_t '× user_address_t
) -> update_operator_event_t.
Global Instance serializable_update_operator_event_t : Serializable update_operator_event_t :=
  Derive Serializable update_operator_event_t_rect<UpdateOperatorEvent>.


Inductive receiver_hacspec_t :=
| Account : public_byte_seq -> receiver_hacspec_t
| Contract : (public_byte_seq '× string_t) -> receiver_hacspec_t.
Global Instance serializable_receiver_hacspec_t : Serializable receiver_hacspec_t :=
  Derive Serializable receiver_hacspec_t_rect<Account,Contract>.


Inductive additional_data_hacspec_t :=
| AdditionalDataHacspec : seq int8 -> additional_data_hacspec_t.
Global Instance serializable_additional_data_hacspec_t : Serializable additional_data_hacspec_t :=
  Derive Serializable additional_data_hacspec_t_rect<AdditionalDataHacspec>.


Inductive update_operator_hacspec_t :=
| UpdateOperatorHacspec : (operator_update_t '× user_address_t
) -> update_operator_hacspec_t.
Global Instance serializable_update_operator_hacspec_t : Serializable update_operator_hacspec_t :=
  Derive Serializable update_operator_hacspec_t_rect<UpdateOperatorHacspec>.


Inductive update_operator_params_hacspec_t :=
| UpdateOperatorParamsHacspec : seq update_operator_hacspec_t -> update_operator_params_hacspec_t.
Global Instance serializable_update_operator_params_hacspec_t : Serializable update_operator_params_hacspec_t :=
  Derive Serializable update_operator_params_hacspec_t_rect<UpdateOperatorParamsHacspec>.


Inductive operator_of_query_t :=
| OperatorOfQuery : (user_address_t '× user_address_t) -> operator_of_query_t.
Global Instance serializable_operator_of_query_t : Serializable operator_of_query_t :=
  Derive Serializable operator_of_query_t_rect<OperatorOfQuery>.


Inductive operator_of_query_params_t :=
| OperatorOfQueryParams : (
  (int64 '× int64) '×
  int64 '×
  seq operator_of_query_t
) -> operator_of_query_params_t.
Global Instance serializable_operator_of_query_params_t : Serializable operator_of_query_params_t :=
  Derive Serializable operator_of_query_params_t_rect<OperatorOfQueryParams>.


