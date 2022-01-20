(* [[file:concordium.org::*Coq code][Coq code:1]] *)
(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
(* Coq code:1 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:2]] *)
Definition max_contract_state_size_v : int32 :=
  @repr WORDSIZE32 16384.
(* Coq code:2 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:3]] *)
Definition max_log_size_v : uint_size :=
  usize 512.
(* Coq code:3 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:4]] *)
Definition max_num_logs_v : uint_size :=
  usize 64.
(* Coq code:4 ends here *)

