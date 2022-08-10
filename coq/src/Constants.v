(** This file was automatically generated using Hacspec **)

Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.

Definition max_contract_state_size_v : int32 :=
  @repr WORDSIZE32 16384.

Definition max_log_size_v : uint_size :=
  usize 512.

Definition max_num_logs_v : uint_size :=
  usize 64.

