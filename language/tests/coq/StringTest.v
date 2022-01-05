(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import String.
Require Import Hacspec.Lib.

Definition string_test  : unit :=
  let a_0 : string :=
    string_from ("hello") in 
  tt.

