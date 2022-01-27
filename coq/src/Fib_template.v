(* [[file:fib.org::*  - Coq code][ - Coq code:1]] *)
(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
(*  - Coq code:1 ends here *)

(* [[file:fib.org::*  - Coq code][ - Coq code:2]] *)
Require Import Hacspec.Lib.
(*  - Coq code:2 ends here *)

(* [[file:fib.org::*  - Coq code][ - Coq code:3]] *)
Require Import Hacspec.Concordium.
(*  - Coq code:3 ends here *)

(* [[file:fib.org::*  - Coq code][ - Coq code:4]] *)
Notation "'state_hacspec_t'" := (int64) : hacspec_scope.
(*  - Coq code:4 ends here *)

(* [[file:fib.org::*  - Coq code][ - Coq code:5]] *)
Definition contract_init_hacspec  : state_hacspec_t :=
  @repr WORDSIZE64 0.
(*  - Coq code:5 ends here *)

(* [[file:fib.org::*  - Coq code][ - Coq code:6]] *)
Inductive action_t :=
| Start : int64 -> action_t
| Continuation0 : (int64 × int64) -> action_t
| Continuation1 : (int64 × int64) -> action_t
| Value : int64 -> action_t.
(*  - Coq code:6 ends here *)

(* [[file:fib.org::*  - Coq code][ - Coq code:7]] *)
Definition contract_receive_hacspec (action_0 : action_t) : action_t :=
  match action_0 with
  | Start n_1 => (if ((n_1) <=.? (@repr WORDSIZE64 1)):bool then (Value (
        @repr WORDSIZE64 1)) else (Continuation0 ((
          n_1,
          (n_1) .- (@repr WORDSIZE64 2)
        ))))
  | Continuation0 (n_2, p_3) => Continuation1 ((
      p_3,
      (n_2) .- (@repr WORDSIZE64 1)
    ))
  | Continuation1 (p_4, q_5) => Value ((p_4) .+ (q_5))
  | Value v_6 => Value (v_6)
  end.
(*  - Coq code:7 ends here *)

(* [[file:fib.org::*  - Coq code][ - Coq code:8]] *)
Definition fib (n_7 : int64) : int64 :=
  (if ((n_7) =.? (@repr WORDSIZE64 1)):bool then (@repr WORDSIZE64 1) else ((
        fib ((n_7) .- (@repr WORDSIZE64 2))) .+ (fib ((n_7) .- (
            @repr WORDSIZE64 1))))).
(*  - Coq code:8 ends here *)

