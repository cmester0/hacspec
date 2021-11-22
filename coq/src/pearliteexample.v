(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Definition binary_search
  (arr_0 : seq uint_size)
  (elem_1 : uint_size) `{(seq_len (arr_0)) <=.? (usize 18446744073709551615)} `{forall i_2 j_3,
  (((usize 0) <=.? (i_2)) && ((i_2) <.? (j_3))) && ((j_3) <.? (seq_len (arr_0))) ->
  (seq_index (arr_0) (i_2)) <=.? (seq_index (arr_0) (j_3))}
  : (result uint_size uint_size) :=
  ifbnd (seq_len (arr_0)) =.? (usize 0) : bool
  thenbnd (result_bind (@Err unit uint_size (usize 0)) (fun _ => Ok (tt) ))
  else (tt) >> (fun 'tt =>
  let size_4 : uint_size := seq_len (arr_0) in 
  let base_5 : uint_size := usize 0 in 
  let result_6 : (result uint_size uint_size) :=
    @Err uint_size uint_size (usize 0) in 
  let '(size_4, base_5, result_6) :=
    foldi (usize 1) (seq_len (arr_0)) (fun k_7 '(size_4, base_5, result_6) =>
      let '(size_4, base_5, result_6) := if (size_4) !=.? (usize 1):bool then (
          let half_8 : uint_size := (size_4) / (usize 2) in 
          let mid_9 : uint_size := (base_5) + (half_8) in 
          let base_5 :=
            (if ((seq_index (arr_0) (mid_9)) >.? (elem_1)):bool then (base_5) else (mid_9)) in 
          let size_4 := (size_4) - (half_8) in 
          (size_4, base_5, result_6) ) else ( let cmp_10 : uint_size :=
            seq_index (arr_0) (base_5) in 
          let '(result_6) := if (cmp_10) =.? (elem_1):bool then (
              let result_6 := @Ok uint_size uint_size (base_5) in 
              (result_6) ) else ( let '(result_6) :=
                if (cmp_10) <.? (elem_1):bool then ( let result_6 :=
                    @Err uint_size uint_size ((base_5) + (usize 1)) in 
                  (result_6) ) else ( let result_6 :=
                    @Err uint_size uint_size (base_5) in 
                  (result_6) ) in 
              (result_6) ) in 
          (size_4, base_5, result_6) ) in 
      (size_4, base_5, result_6))
    (size_4, base_5, result_6) in 
  result_6).

Theorem ensures_binary_search : forall result_11 (arr_0 : seq uint_size) (elem_1 : uint_size),
forall {H_0 : (seq_len (arr_0)) <=.? (usize 18446744073709551615)},
forall {H_1 : forall i_2 j_3,
(((usize 0) <=.? (i_2)) && ((i_2) <.? (j_3))) && ((j_3) <.? (seq_len (arr_0))) ->
(seq_index (arr_0) (i_2)) <=.? (seq_index (arr_0) (j_3))},
@binary_search arr_0 elem_1 H_0 H_1 = result_11 ->
forall x_12,
result_11 = @Ok uint_size uint_size (x_12) ->
seq_index (arr_0) (x_12) = elem_1/\forall x_13,
result_11 = @Err uint_size uint_size (x_13) ->
forall i_14,
(i_14) <.? (x_13) ->
(seq_index (arr_0) (i_14)) <=.? (elem_1)/\forall x_15,
result_11 = @Err uint_size uint_size (x_15) ->
forall i_16,
((x_15) <.? (i_16)) && ((i_16) <.? (seq_len (arr_0))) ->
(elem_1) <.? (seq_index (arr_0) (i_16)).
Proof.
Admitted.
