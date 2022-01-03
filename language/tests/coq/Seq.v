(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Definition word := nseq (uint8) (usize 4).

Definition seq_test
  (key_0 : byte_seq)
  (word_1 : word)
  : (result byte_seq unit) :=
  let byte_seq_2 : seq uint8 :=
    seq_new_ (secret (@repr WORDSIZE8 0)) (usize 10) in 
  let byte_seq_2 :=
    seq_update_start (byte_seq_2) (key_0) in 
  bind (foldibnd (usize 0) to (usize 10) for byte_seq_2>> (fun j_3 byte_seq_2 =>
    let _ : word :=
      array_from_slice (secret (@repr WORDSIZE8 0)) (4) (byte_seq_2) ((
          usize 4) * (usize 1)) (usize 4) in 
    bind (@Ok byte_seq unit (seq_update (byte_seq_2) (usize 4) (word_1))) (
      fun byte_seq_2  => Ok ((byte_seq_2))))) (fun byte_seq_2 =>
    @Ok byte_seq unit (byte_seq_2)).

