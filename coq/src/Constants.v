(** This file was automatically generated using Hacspec **)

Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.

Require Import ConCertLib.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import Automation.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ContractCommon.
From Coq Require Import Morphisms ZArith Basics.
Open Scope Z.
Set Nonrecursive Elimination Schemes.
Definition max_contract_state_size_v : int32 :=
  @repr WORDSIZE32 16384.

Definition max_log_size_v : uint_size :=
  usize 512.

Definition max_num_logs_v : uint_size :=
  usize 64.

