(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Definition seq_test  : unit :=
  let a_0 : seq uint8 :=
    seq_new_ (default) (usize 10) in 
  let b_1 : seq uint8 :=
    seq_new_ (default) (usize 10) in 
  let a_0 :=
    seq_reserve (a_0) (usize 5) in 
  let _ : uint_size :=
    seq_len (a_0) in 
  let _ : seq uint8 :=
    seq_slice (a_0) (usize 0) (usize 4) in 
  let a_0 :=
    seq_into_slice (a_0) (usize 0) (usize 4) in 
  let '(a_2, c_3) :=
    seq_split_off (a_0) (usize 4) in 
  let a_2 :=
    seq_truncate (a_2) (usize 2) in 
  let a_2 :=
    seq_concat (a_2) (c_3) in 
  let a_2 :=
    seq_concat_owned (a_2) (b_1) in 
  let a_2 :=
    seq_push (a_2) (secret (@repr WORDSIZE8 4) : int8) in 
  let a_2 :=
    seq_push_owned (a_2) (secret (@repr WORDSIZE8 5) : int8) in 
  let _ : uint_size :=
    seq_num_chunks (a_2) (usize 3) in 
  let _ : uint_size :=
    seq_num_exact_chunks (a_2) (usize 3) in 
  let '(n_4, a_5) :=
    seq_get_chunk (a_2) (usize 3) (usize 1) in 
  let a_5 :=
    seq_get_exact_chunk (a_5) (usize 3) (usize 1) in 
  let a_5 :=
    seq_get_remainder_chunk (a_5) (usize 3) in 
  let a_5 :=
    seq_set_chunk (a_5) (usize 3) (usize 1) (seq_new_ (default) (usize 3)) in 
  let a_5 :=
    seq_set_exact_chunk (a_5) (usize 3) (usize 1) (seq_new_ (default) (
        usize 3)) in 
  let _ : seq uint8 :=
    seq_create (usize 10) in 
  let a_5 :=
    seq_update_slice (a_5) (usize 10) (seq_new_ (default) (usize 1)) (usize 0) (
      usize 1) in 
  let a_5 :=
    seq_update (a_5) (usize 2) (seq_new_ (default) (usize 1)) in 
  let a_5 :=
    seq_update_start (a_5) (seq_new_ (default) (usize 1)) in 
  let _ : seq uint8 :=
    seq_from_seq (a_5) in 
  tt.

Definition word_t := nseq (uint8) (usize 4).

Definition seq_loop_result_test
  (key_6 : byte_seq)
  (word_7 : word_t)
  : (result byte_seq unit) :=
  let byte_seq_8 : seq uint8 :=
    seq_new_ (default) (usize 10) in 
  let byte_seq_8 :=
    seq_update_start (byte_seq_8) (key_6) in 
  result_bind (foldibnd (usize 0) to (
      usize 10) for byte_seq_8>> (fun j_9 byte_seq_8 =>
    let _ : word_t :=
      array_from_slice (default) (4) (byte_seq_8) ((usize 4) .* (usize 1)) (
        usize 4) in 
    result_bind (@Ok byte_seq unit (seq_update (byte_seq_8) (usize 4) (
          word_7))) (fun byte_seq_8  => Ok ((byte_seq_8))))) (fun byte_seq_8 =>
    @Ok byte_seq unit (byte_seq_8)).

