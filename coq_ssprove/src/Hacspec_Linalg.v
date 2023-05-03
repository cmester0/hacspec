(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp.word Require Import ssrZ word.
From Jasmin Require Import word.

From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.

Require Import ChoiceEquality.
Require Import LocationUtility.
Require Import Hacspec_Lib_Comparable.
Require Import Hacspec_Lib_Pre.
Require Import Hacspec_Lib.

Open Scope hacspec_scope.
Import choice.Choice.Exports.

Obligation Tactic := try timeout 8 solve_ssprove_obligations.


Notation "'dim_type_t'" := (uint_size) : hacspec_scope.

Notation "'scalar_t'" := (int128) : hacspec_scope.

Notation "'dims_t'" := ((dim_type_t × dim_type_t)) : hacspec_scope.

Notation "'matrix_t'" := ((dims_t × seq scalar_t)) : hacspec_scope.

Notation "'mat_res_t'" := ((result int8 matrix_t)) : hacspec_scope.

Notation "'scal_res_t'" := ((result int8 scalar_t)) : hacspec_scope.

Definition dimension_sequence_length_mismatch_v : int8 :=
  @repr U8 10.

Definition index_out_of_bounds_v : int8 :=
  @repr U8 11.

Definition slice_out_of_bounds_v : int8 :=
  @repr U8 12.

Definition dimension_mismatch_v : int8 :=
  @repr U8 13.


Notation "'new__inp'" :=(
  dim_type_t × dim_type_t × seq scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'new__out'" :=(
  mat_res_t : choice_type) (in custom pack_type at level 2).
Definition NEW : nat :=
  933.
Program Definition new_ (rows_931 : dim_type_t) (cols_932 : dim_type_t) (
    seq_930 : seq scalar_t)
  : both (fset.fset0) [interface] (mat_res_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (((seq_len (lift_to_both0 seq_930)) >.? (
              lift_to_both0 (usize 0))) && (((lift_to_both0 rows_931) .* (
                lift_to_both0 cols_932)) =.? (seq_len (lift_to_both0 seq_930))))
        then @Ok matrix_t int8 (prod_b(
            prod_b(lift_to_both0 rows_931, lift_to_both0 cols_932),
            lift_to_both0 seq_930
          ))
        else @Err matrix_t int8 (
          lift_to_both0 dimension_sequence_length_mismatch_v))
      ) : both (fset.fset0) [interface] (mat_res_t)).
Fail Next Obligation.

Definition ret_934_loc : ChoiceEqualityLocation :=
  (seq int128 ; 935%nat).
Notation "'repeat_inp'" :=(
  dim_type_t × dim_type_t × scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'repeat_out'" :=(
  matrix_t : choice_type) (in custom pack_type at level 2).
Definition REPEAT : nat :=
  940.
Program Definition repeat (n_936 : dim_type_t) (m_937 : dim_type_t) (
    scalar_939 : scalar_t)
  : both (CEfset ([ret_934_loc])) [interface] (matrix_t) :=
  ((letbm ret_934 : seq int128 loc( ret_934_loc ) :=
        seq_new_ (default : scalar_t) ((lift_to_both0 n_936) .* (
            lift_to_both0 m_937)) in
      letb ret_934 :=
        foldi_both' (lift_to_both0 (usize 0)) ((lift_to_both0 n_936) .* (
              lift_to_both0 m_937)) ret_934 (L := (CEfset ([ret_934_loc]))) (
            I := [interface]) (fun i_938 ret_934 =>
            letb ret_934 : seq int128 :=
              seq_upd ret_934 (lift_to_both0 i_938) (is_pure (
                  lift_to_both0 scalar_939)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 ret_934)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          prod_b(lift_to_both0 n_936, lift_to_both0 m_937),
          lift_to_both0 ret_934
        ))
      ) : both (CEfset ([ret_934_loc])) [interface] (matrix_t)).
Fail Next Obligation.


Notation "'zeros_inp'" :=(
  dim_type_t × dim_type_t : choice_type) (in custom pack_type at level 2).
Notation "'zeros_out'" :=(
  matrix_t : choice_type) (in custom pack_type at level 2).
Definition ZEROS : nat :=
  943.
Program Definition zeros (n_941 : dim_type_t) (m_942 : dim_type_t)
  : both (CEfset ([ret_934_loc])) [interface] (matrix_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (repeat (
          lift_to_both0 n_941) (lift_to_both0 m_942) (pub_int128_zero ))
      ) : both (CEfset ([ret_934_loc])) [interface] (matrix_t)).
Fail Next Obligation.


Notation "'ones_inp'" :=(
  dim_type_t × dim_type_t : choice_type) (in custom pack_type at level 2).
Notation "'ones_out'" :=(
  matrix_t : choice_type) (in custom pack_type at level 2).
Definition ONES : nat :=
  946.
Program Definition ones (n_944 : dim_type_t) (m_945 : dim_type_t)
  : both (CEfset ([ret_934_loc])) [interface] (matrix_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (repeat (
          lift_to_both0 n_944) (lift_to_both0 m_945) (pub_int128_one ))
      ) : both (CEfset ([ret_934_loc])) [interface] (matrix_t)).
Fail Next Obligation.

Definition ret_947_loc : ChoiceEqualityLocation :=
  (seq int128 ; 948%nat).
Notation "'identity_inp'" :=(
  dim_type_t × dim_type_t : choice_type) (in custom pack_type at level 2).
Notation "'identity_out'" :=(
  matrix_t : choice_type) (in custom pack_type at level 2).
Definition IDENTITY : nat :=
  953.
Program Definition identity (n_949 : dim_type_t) (m_950 : dim_type_t)
  : both (CEfset ([ret_947_loc])) [interface] (matrix_t) :=
  ((letbm ret_947 : seq int128 loc( ret_947_loc ) :=
        seq_new_ (default : scalar_t) ((lift_to_both0 n_949) .* (
            lift_to_both0 m_950)) in
      letb ret_947 :=
        foldi_both' (lift_to_both0 (usize 0)) (min (lift_to_both0 n_949) (
              lift_to_both0 m_950)) ret_947 (L := (CEfset ([ret_947_loc]))) (
            I := [interface]) (fun i_951 ret_947 =>
            letb index_952 : uint_size :=
              ((lift_to_both0 i_951) .* (min (lift_to_both0 n_949) (
                    lift_to_both0 m_950))) .+ (lift_to_both0 i_951) in
            letb ret_947 : seq int128 :=
              seq_upd ret_947 (lift_to_both0 index_952) (is_pure (
                  pub_int128_one )) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 ret_947)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          prod_b(lift_to_both0 n_949, lift_to_both0 m_950),
          lift_to_both0 ret_947
        ))
      ) : both (CEfset ([ret_947_loc])) [interface] (matrix_t)).
Fail Next Obligation.


Notation "'index_inp'" :=(
  matrix_t × dim_type_t × dim_type_t : choice_type) (in custom pack_type at level 2).
Notation "'index_out'" :=(
  scal_res_t : choice_type) (in custom pack_type at level 2).
Definition INDEX : nat :=
  962.
Program Definition index (m_954 : matrix_t) (i_959 : dim_type_t) (
    j_960 : dim_type_t)
  : both (fset.fset0) [interface] (scal_res_t) :=
  ((letb '(dim_955, seq_956) : (dims_t '× seq scalar_t) :=
        lift_to_both0 m_954 in
      letb '(rows_957, cols_958) : (dim_type_t '× dim_type_t) :=
        lift_to_both0 dim_955 in
      letb index_961 : uint_size :=
        ((lift_to_both0 i_959) .* (lift_to_both0 cols_958)) .+ (
          lift_to_both0 j_960) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 index_961) >=.? ((
              lift_to_both0 rows_957) .* (lift_to_both0 cols_958)))
        then @Err scalar_t int8 (lift_to_both0 index_out_of_bounds_v)
        else @Ok scalar_t int8 (seq_index (seq_956) (lift_to_both0 index_961)))
      ) : both (fset.fset0) [interface] (scal_res_t)).
Fail Next Obligation.

Definition ret_963_loc : ChoiceEqualityLocation :=
  (seq int128 ; 964%nat).
Notation "'transpose_inp'" :=(
  matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'transpose_out'" :=(
  matrix_t : choice_type) (in custom pack_type at level 2).
Definition TRANSPOSE : nat :=
  974.
Program Definition transpose (matrix_965 : matrix_t)
  : both (CEfset ([ret_963_loc])) [interface] (matrix_t) :=
  ((letb '(dim_966, seq_967) : (dims_t '× seq scalar_t) :=
        lift_to_both0 matrix_965 in
      letb '(rows_968, cols_969) : (dim_type_t '× dim_type_t) :=
        lift_to_both0 dim_966 in
      letbm ret_963 : seq int128 loc( ret_963_loc ) :=
        seq_new_ (default : scalar_t) (seq_len (lift_to_both0 seq_967)) in
      letb ret_963 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 rows_968) ret_963 (
            L := (CEfset ([ret_963_loc]))) (I := [interface]) (
            fun i_970 ret_963 =>
            letb ret_963 :=
              foldi_both' (lift_to_both0 (usize 0)) (
                  lift_to_both0 cols_969) ret_963 (L := (CEfset (
                      [ret_963_loc]))) (I := [interface]) (fun j_971 ret_963 =>
                  letb seq_index_972 : uint_size :=
                    ((lift_to_both0 i_970) .* (lift_to_both0 cols_969)) .+ (
                      lift_to_both0 j_971) in
                  letb ret_index_973 : uint_size :=
                    ((lift_to_both0 j_971) .* (lift_to_both0 rows_968)) .+ (
                      lift_to_both0 i_970) in
                  letb ret_963 : seq int128 :=
                    seq_upd ret_963 (lift_to_both0 ret_index_973) (is_pure (
                        seq_index (seq_967) (lift_to_both0 seq_index_972))) in
                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 ret_963)
                  ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 ret_963)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          prod_b(lift_to_both0 cols_969, lift_to_both0 rows_968),
          lift_to_both0 ret_963
        ))
      ) : both (CEfset ([ret_963_loc])) [interface] (matrix_t)).
Fail Next Obligation.

Definition res_976_loc : ChoiceEqualityLocation :=
  ((result (int8) (matrix_t)) ; 977%nat).
Definition ret_975_loc : ChoiceEqualityLocation :=
  (seq int128 ; 978%nat).
Notation "'slice_inp'" :=(
  matrix_t × dims_t × dims_t : choice_type) (in custom pack_type at level 2).
Notation "'slice_out'" :=(
  mat_res_t : choice_type) (in custom pack_type at level 2).
Definition SLICE : nat :=
  995.
Program Definition slice (matrix_979 : matrix_t) (start_984 : dims_t) (
    len_987 : dims_t)
  : both (CEfset ([ret_975_loc ; res_976_loc])) [interface] (mat_res_t) :=
  ((letb '(dim_980, seq_981) : (dims_t '× seq scalar_t) :=
        lift_to_both0 matrix_979 in
      letb '(rows_982, cols_983) : (dim_type_t '× dim_type_t) :=
        lift_to_both0 dim_980 in
      letb '(start_row_985, start_col_986) : (dim_type_t '× dim_type_t) :=
        lift_to_both0 start_984 in
      letb '(len_rows_988, len_cols_989) : (dim_type_t '× dim_type_t) :=
        lift_to_both0 len_987 in
      letb start_index_990 : uint_size :=
        ((lift_to_both0 start_row_985) .* (lift_to_both0 cols_983)) .+ (
          lift_to_both0 start_col_986) in
      letbm ret_975 : seq int128 loc( ret_975_loc ) :=
        seq_new_ (default : scalar_t) ((lift_to_both0 len_rows_988) .* (
            lift_to_both0 len_cols_989)) in
      letbm res_976 : (result (int8) (matrix_t)) loc( res_976_loc ) :=
        @Err matrix_t int8 (lift_to_both0 slice_out_of_bounds_v) in
      letb '(ret_975, res_976) :=
        if ((lift_to_both0 start_index_990) .+ ((
              lift_to_both0 len_rows_988) .* (
              lift_to_both0 len_cols_989))) <=.? ((lift_to_both0 rows_982) .* (
            lift_to_both0 cols_983)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([ret_975_loc ; res_976_loc])) (
          L2 := CEfset ([ret_975_loc ; res_976_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb ret_975 :=
            foldi_both' (lift_to_both0 (usize 0)) (
                lift_to_both0 len_rows_988) ret_975 (L := (CEfset (
                    [ret_975_loc ; res_976_loc]))) (I := [interface]) (
                fun i_991 ret_975 =>
                letb ret_975 :=
                  foldi_both' (lift_to_both0 (usize 0)) (
                      lift_to_both0 len_cols_989) ret_975 (L := (CEfset (
                          [ret_975_loc ; res_976_loc]))) (I := [interface]) (
                      fun j_992 ret_975 =>
                      letb ret_index_993 : uint_size :=
                        ((lift_to_both0 i_991) .* (
                            lift_to_both0 len_cols_989)) .+ (
                          lift_to_both0 j_992) in
                      letb seq_index_994 : uint_size :=
                        (((lift_to_both0 start_row_985) .+ (
                              lift_to_both0 i_991)) .* (
                            lift_to_both0 cols_983)) .+ ((
                            lift_to_both0 start_col_986) .+ (
                            lift_to_both0 j_992)) in
                      letb ret_975 : seq int128 :=
                        seq_upd ret_975 (lift_to_both0 ret_index_993) (is_pure (
                            seq_index (seq_981) (
                              lift_to_both0 seq_index_994))) in
                      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                        lift_to_both0 ret_975)
                      ) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 ret_975)
                ) in
          letbm res_976 loc( res_976_loc ) :=
            new_ (lift_to_both0 len_rows_988) (lift_to_both0 len_cols_989) (
              lift_to_both0 ret_975) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 ret_975,
              lift_to_both0 res_976
            ))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 ret_975,
            lift_to_both0 res_976
          ))
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 res_976)
      ) : both (CEfset ([ret_975_loc ; res_976_loc])) [interface] (mat_res_t)).
Fail Next Obligation.

Definition ret_996_loc : ChoiceEqualityLocation :=
  (seq int128 ; 997%nat).
Notation "'scale_inp'" :=(
  matrix_t × scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'scale_out'" :=(
  matrix_t : choice_type) (in custom pack_type at level 2).
Definition SCALE : nat :=
  1003.
Program Definition scale (matrix_998 : matrix_t) (scalar_1002 : scalar_t)
  : both (CEfset ([ret_996_loc])) [interface] (matrix_t) :=
  ((letb '(dim_999, seq_1000) : (dims_t '× seq scalar_t) :=
        lift_to_both0 matrix_998 in
      letbm ret_996 : seq int128 loc( ret_996_loc ) :=
        seq_new_ (default : scalar_t) (seq_len (lift_to_both0 seq_1000)) in
      letb ret_996 :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 seq_1000)) ret_996 (L := (CEfset ([ret_996_loc]))) (
            I := [interface]) (fun i_1001 ret_996 =>
            letb ret_996 : seq int128 :=
              seq_upd ret_996 (lift_to_both0 i_1001) (is_pure ((
                    lift_to_both0 scalar_1002) .* (seq_index (seq_1000) (
                      lift_to_both0 i_1001)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 ret_996)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 dim_999,
          lift_to_both0 ret_996
        ))
      ) : both (CEfset ([ret_996_loc])) [interface] (matrix_t)).
Fail Next Obligation.

Definition ret_1004_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1006%nat).
Definition res_1005_loc : ChoiceEqualityLocation :=
  ((result (int8) (matrix_t)) ; 1007%nat).
Notation "'add_inp'" :=(
  matrix_t × matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'add_out'" :=(
  mat_res_t : choice_type) (in custom pack_type at level 2).
Definition ADD : nat :=
  1015.
Program Definition add (matrix_1_1008 : matrix_t) (matrix_2_1011 : matrix_t)
  : both (CEfset ([ret_1004_loc ; res_1005_loc])) [interface] (mat_res_t) :=
  ((letb '(m1_dim_1009, m1_s_1010) : (dims_t '× seq scalar_t) :=
        lift_to_both0 matrix_1_1008 in
      letb '(m2_dim_1012, m2_s_1013) : (dims_t '× seq scalar_t) :=
        lift_to_both0 matrix_2_1011 in
      letbm ret_1004 : seq int128 loc( ret_1004_loc ) :=
        seq_new_ (default : scalar_t) (seq_len (lift_to_both0 m1_s_1010)) in
      letbm res_1005 : (result (int8) (matrix_t)) loc( res_1005_loc ) :=
        @Err matrix_t int8 (lift_to_both0 dimension_mismatch_v) in
      letb '(ret_1004, res_1005) :=
        if (lift_to_both0 m1_dim_1009) =.? (
          lift_to_both0 m2_dim_1012) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([ret_1004_loc ; res_1005_loc])) (
          L2 := CEfset ([ret_1004_loc ; res_1005_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb ret_1004 :=
            foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                  lift_to_both0 m1_s_1010)) ret_1004 (L := (CEfset (
                    [ret_1004_loc ; res_1005_loc]))) (I := [interface]) (
                fun i_1014 ret_1004 =>
                letb ret_1004 : seq int128 :=
                  seq_upd ret_1004 (lift_to_both0 i_1014) (is_pure ((seq_index (
                          m1_s_1010) (lift_to_both0 i_1014)) .+ (seq_index (
                          m2_s_1013) (lift_to_both0 i_1014)))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 ret_1004)
                ) in
          letbm res_1005 loc( res_1005_loc ) :=
            @Ok matrix_t int8 (prod_b(
                lift_to_both0 m1_dim_1009,
                lift_to_both0 ret_1004
              )) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 ret_1004,
              lift_to_both0 res_1005
            ))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 ret_1004,
            lift_to_both0 res_1005
          ))
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 res_1005)
      ) : both (CEfset ([ret_1004_loc ; res_1005_loc])) [interface] (
      mat_res_t)).
Fail Next Obligation.

Definition ret_1016_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1018%nat).
Definition res_1017_loc : ChoiceEqualityLocation :=
  ((result (int8) (matrix_t)) ; 1019%nat).
Notation "'sub_inp'" :=(
  matrix_t × matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'sub_out'" :=(
  mat_res_t : choice_type) (in custom pack_type at level 2).
Definition SUB : nat :=
  1027.
Program Definition sub (matrix_1_1020 : matrix_t) (matrix_2_1023 : matrix_t)
  : both (CEfset ([ret_1016_loc ; res_1017_loc])) [interface] (mat_res_t) :=
  ((letb '(m1_dim_1021, m1_s_1022) : (dims_t '× seq scalar_t) :=
        lift_to_both0 matrix_1_1020 in
      letb '(m2_dim_1024, m2_s_1025) : (dims_t '× seq scalar_t) :=
        lift_to_both0 matrix_2_1023 in
      letbm ret_1016 : seq int128 loc( ret_1016_loc ) :=
        seq_new_ (default : scalar_t) (seq_len (lift_to_both0 m1_s_1022)) in
      letbm res_1017 : (result (int8) (matrix_t)) loc( res_1017_loc ) :=
        @Err matrix_t int8 (lift_to_both0 dimension_mismatch_v) in
      letb '(ret_1016, res_1017) :=
        if (lift_to_both0 m1_dim_1021) =.? (
          lift_to_both0 m2_dim_1024) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([ret_1016_loc ; res_1017_loc])) (
          L2 := CEfset ([ret_1016_loc ; res_1017_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb ret_1016 :=
            foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                  lift_to_both0 m1_s_1022)) ret_1016 (L := (CEfset (
                    [ret_1016_loc ; res_1017_loc]))) (I := [interface]) (
                fun i_1026 ret_1016 =>
                letb ret_1016 : seq int128 :=
                  seq_upd ret_1016 (lift_to_both0 i_1026) (is_pure ((seq_index (
                          m1_s_1022) (lift_to_both0 i_1026)) .- (seq_index (
                          m2_s_1025) (lift_to_both0 i_1026)))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 ret_1016)
                ) in
          letbm res_1017 loc( res_1017_loc ) :=
            @Ok matrix_t int8 (prod_b(
                lift_to_both0 m1_dim_1021,
                lift_to_both0 ret_1016
              )) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 ret_1016,
              lift_to_both0 res_1017
            ))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 ret_1016,
            lift_to_both0 res_1017
          ))
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 res_1017)
      ) : both (CEfset ([ret_1016_loc ; res_1017_loc])) [interface] (
      mat_res_t)).
Fail Next Obligation.

Definition res_1029_loc : ChoiceEqualityLocation :=
  ((result (int8) (matrix_t)) ; 1030%nat).
Definition ret_1028_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1031%nat).
Notation "'component_mul_inp'" :=(
  matrix_t × matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'component_mul_out'" :=(
  mat_res_t : choice_type) (in custom pack_type at level 2).
Definition COMPONENT_MUL : nat :=
  1039.
Program Definition component_mul (matrix_1_1032 : matrix_t) (
    matrix_2_1035 : matrix_t)
  : both (CEfset ([ret_1028_loc ; res_1029_loc])) [interface] (mat_res_t) :=
  ((letb '(m1_dim_1033, m1_s_1034) : (dims_t '× seq scalar_t) :=
        lift_to_both0 matrix_1_1032 in
      letb '(m2_dim_1036, m2_s_1037) : (dims_t '× seq scalar_t) :=
        lift_to_both0 matrix_2_1035 in
      letbm ret_1028 : seq int128 loc( ret_1028_loc ) :=
        seq_new_ (default : scalar_t) (seq_len (lift_to_both0 m1_s_1034)) in
      letbm res_1029 : (result (int8) (matrix_t)) loc( res_1029_loc ) :=
        @Err matrix_t int8 (lift_to_both0 dimension_mismatch_v) in
      letb '(ret_1028, res_1029) :=
        if (lift_to_both0 m1_dim_1033) =.? (
          lift_to_both0 m2_dim_1036) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([ret_1028_loc ; res_1029_loc])) (
          L2 := CEfset ([ret_1028_loc ; res_1029_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb ret_1028 :=
            foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                  lift_to_both0 m1_s_1034)) ret_1028 (L := (CEfset (
                    [ret_1028_loc ; res_1029_loc]))) (I := [interface]) (
                fun i_1038 ret_1028 =>
                letb ret_1028 : seq int128 :=
                  seq_upd ret_1028 (lift_to_both0 i_1038) (is_pure ((seq_index (
                          m1_s_1034) (lift_to_both0 i_1038)) .* (seq_index (
                          m2_s_1037) (lift_to_both0 i_1038)))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 ret_1028)
                ) in
          letbm res_1029 loc( res_1029_loc ) :=
            @Ok matrix_t int8 (prod_b(
                lift_to_both0 m1_dim_1033,
                lift_to_both0 ret_1028
              )) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 ret_1028,
              lift_to_both0 res_1029
            ))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 ret_1028,
            lift_to_both0 res_1029
          ))
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 res_1029)
      ) : both (CEfset ([ret_1028_loc ; res_1029_loc])) [interface] (
      mat_res_t)).
Fail Next Obligation.

Definition ret_1040_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1043%nat).
Definition acc_1042_loc : ChoiceEqualityLocation :=
  (int128 ; 1044%nat).
Definition res_1041_loc : ChoiceEqualityLocation :=
  ((result (int8) (matrix_t)) ; 1045%nat).
Notation "'mul_inp'" :=(
  matrix_t × matrix_t : choice_type) (in custom pack_type at level 2).
Notation "'mul_out'" :=(
  mat_res_t : choice_type) (in custom pack_type at level 2).
Definition MUL : nat :=
  1062.
Program Definition mul (matrix_1_1046 : matrix_t) (matrix_2_1049 : matrix_t)
  : both (CEfset ([ret_1040_loc ; res_1041_loc ; acc_1042_loc])) [interface] (
    mat_res_t) :=
  ((letb '(dim_1_1047, seq_1_1048) : (dims_t '× seq scalar_t) :=
        lift_to_both0 matrix_1_1046 in
      letb '(dim_2_1050, seq_2_1051) : (dims_t '× seq scalar_t) :=
        lift_to_both0 matrix_2_1049 in
      letb '(l_1052, m_1053) : (dim_type_t '× dim_type_t) :=
        lift_to_both0 dim_1_1047 in
      letb '(m_1054, n_1055) : (dim_type_t '× dim_type_t) :=
        lift_to_both0 dim_2_1050 in
      letbm ret_1040 : seq int128 loc( ret_1040_loc ) :=
        seq_new_ (default : scalar_t) ((lift_to_both0 l_1052) .* (
            lift_to_both0 n_1055)) in
      letbm res_1041 : (result (int8) (matrix_t)) loc( res_1041_loc ) :=
        @Err matrix_t int8 (lift_to_both0 dimension_mismatch_v) in
      letb '(ret_1040, res_1041) :=
        if (lift_to_both0 m_1053) =.? (
          lift_to_both0 m_1054) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [ret_1040_loc ; res_1041_loc ; acc_1042_loc])) (L2 := CEfset (
            [ret_1040_loc ; res_1041_loc ; acc_1042_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb ret_1040 :=
            foldi_both' (lift_to_both0 (usize 0)) (
                lift_to_both0 l_1052) ret_1040 (L := (CEfset (
                    [ret_1040_loc ; res_1041_loc ; acc_1042_loc]))) (
                I := [interface]) (fun i_1056 ret_1040 =>
                letb ret_1040 :=
                  foldi_both' (lift_to_both0 (usize 0)) (
                      lift_to_both0 n_1055) ret_1040 (L := (CEfset (
                          [ret_1040_loc ; res_1041_loc ; acc_1042_loc]))) (
                      I := [interface]) (fun j_1057 ret_1040 =>
                      letbm acc_1042 : int128 loc( acc_1042_loc ) :=
                        pub_int128_zero  in
                      letb index_1058 : uint_size :=
                        ((lift_to_both0 i_1056) .* (lift_to_both0 n_1055)) .+ (
                          lift_to_both0 j_1057) in
                      letb acc_1042 :=
                        foldi_both' (lift_to_both0 (usize 0)) (
                            lift_to_both0 m_1053) acc_1042 (L := (CEfset (
                                [ret_1040_loc ; res_1041_loc ; acc_1042_loc]))) (
                            I := [interface]) (fun k_1059 acc_1042 =>
                            letb index_1_1060 : uint_size :=
                              ((lift_to_both0 i_1056) .* (
                                  lift_to_both0 m_1053)) .+ (
                                lift_to_both0 k_1059) in
                            letb index_2_1061 : uint_size :=
                              ((lift_to_both0 k_1059) .* (
                                  lift_to_both0 n_1055)) .+ (
                                lift_to_both0 j_1057) in
                            letbm acc_1042 loc( acc_1042_loc ) :=
                              (lift_to_both0 acc_1042) .+ ((seq_index (
                                    seq_1_1048) (
                                    lift_to_both0 index_1_1060)) .* (seq_index (
                                    seq_2_1051) (
                                    lift_to_both0 index_2_1061))) in
                            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                              lift_to_both0 acc_1042)
                            ) in
                      letb ret_1040 : seq int128 :=
                        seq_upd ret_1040 (lift_to_both0 index_1058) (is_pure (
                            lift_to_both0 acc_1042)) in
                      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                        lift_to_both0 ret_1040)
                      ) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 ret_1040)
                ) in
          letbm res_1041 loc( res_1041_loc ) :=
            new_ (lift_to_both0 l_1052) (lift_to_both0 n_1055) (
              lift_to_both0 ret_1040) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 ret_1040,
              lift_to_both0 res_1041
            ))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 ret_1040,
            lift_to_both0 res_1041
          ))
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 res_1041)
      ) : both (CEfset (
        [ret_1040_loc ; res_1041_loc ; acc_1042_loc])) [interface] (mat_res_t)).
Fail Next Obligation.

