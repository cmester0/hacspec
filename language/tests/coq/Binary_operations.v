(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Definition test_usize_operations (i_0 : uint_size) : unit :=
  let o_1 : uint_size :=
    (usize 8) ./ ((i_0) .& (usize 7)) in 
  let o_2 : uint_size :=
    (usize 8) .+ ((i_0) .| (usize 7)) in 
  let o_3 : uint_size :=
    (usize 8) .- ((i_0) .+ (usize 7)) in 
  let o_4 : uint_size :=
    (usize 8) .* ((i_0) .- (usize 7)) in 
  let o_5 : uint_size :=
    (usize 8) .& ((i_0) .* (usize 7)) in 
  let o_6 : bool :=
    (usize 8) <.? (usize 4) in 
  let o_7 : bool :=
    (usize 8) <=.? (usize 4) in 
  let o_8 : bool :=
    (usize 8) >.? (usize 4) in 
  let o_9 : bool :=
    (usize 8) >=.? (usize 4) in 
  let o_10 : bool :=
    (usize 8) !=.? (usize 4) in 
  let o_11 : bool :=
    (usize 8) =.? (usize 4) in 
  tt.

