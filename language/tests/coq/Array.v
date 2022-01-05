(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import String.
Require Import Hacspec.Lib.

Definition arr_t_t := nseq (int8) (usize 4).

Definition array_test  : unit :=
  let a_0 : arr_t_t :=
    array_new_ (default) (4) in 
  let _ : uint_size :=
    4  in 
  let _ : arr_t_t :=
    array_from_slice (default) (4) (seq_new_ (default) (usize 4)) (usize 0) (
      usize 4) in 
  let _ : seq int8 :=
    array_concat (a_0) (seq_new_ (default) (usize 4)) in 
  let _ : arr_t_t :=
    array_from_slice_range (default) (4) (seq_new_ (default) (usize 4)) ((
        usize 0,
        usize 4
      )) in 
  let _ : seq int8 :=
    array_slice (a_0) (usize 0) (usize 4) in 
  let _ : seq int8 :=
    array_slice_range (a_0) ((usize 0, usize 4)) in 
  let _ : uint_size :=
    array_num_chunks (a_0) (usize 2) in 
  let _ : uint_size :=
    array_get_chunk_len (a_0) (usize 3) (usize 1) in 
  let '(n_1, s_2) :=
    array_get_chunk (a_0) (usize 2) (usize 1) in 
  let _ : arr_t_t :=
    array_set_chunk (a_0) (usize 2) (usize 1) (s_2) in 
  let _ : arr_t_t :=
    array_default  in 
  let _ : arr_t_t :=
    array_create (usize 4) in 
  let _ : uint_size :=
    array_len (a_0) in 
  let _ : arr_t_t :=
    array_update_slice (a_0) (usize 0) (seq_new_ (default) (usize 4)) (
      usize 0) (usize 2) in 
  let _ : arr_t_t :=
    array_update (a_0) (usize 2) (seq_new_ (default) (usize 4)) in 
  let _ : arr_t_t :=
    array_update_start (a_0) (seq_new_ (default) (usize 4)) in 
  let _ : arr_t_t :=
    array_from_seq (4) (seq_new_ (default) (usize 4)) in 
  tt.

