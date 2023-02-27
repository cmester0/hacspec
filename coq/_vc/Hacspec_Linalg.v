(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.
Export Hacspec_Lib.

Notation "'dim_type_t'" := (uint_size) : hacspec_scope.

Notation "'scalar_t'" := (int128) : hacspec_scope.

Notation "'dims_t'" := ((dim_type_t '× dim_type_t)) : hacspec_scope.

Notation "'matrix_t'" := ((dims_t '× seq scalar_t)) : hacspec_scope.

Notation "'mat_res_t'" := ((result matrix_t int8)) : hacspec_scope.

Notation "'scal_res_t'" := ((result scalar_t int8)) : hacspec_scope.

Definition dimension_sequence_length_mismatch_v : int8 :=
  @repr WORDSIZE8 10.

Definition index_out_of_bounds_v : int8 :=
  @repr WORDSIZE8 11.

Definition slice_out_of_bounds_v : int8 :=
  @repr WORDSIZE8 12.

Definition dimension_mismatch_v : int8 :=
  @repr WORDSIZE8 13.

Definition new_
  (rows_731 : dim_type_t)
  (cols_732 : dim_type_t)
  (seq_733 : seq scalar_t)
  
  : mat_res_t :=
  (if (((seq_len (seq_733)) >.? (usize 0)) && (((rows_731) * (cols_732)) =.? (
          seq_len (seq_733)))):bool then (@Ok matrix_t int8 ((
          (rows_731, cols_732),
          seq_733
        ))) else (@Err matrix_t int8 (dimension_sequence_length_mismatch_v))).


Definition repeat
  (n_734 : dim_type_t)
  (m_735 : dim_type_t)
  (scalar_736 : scalar_t)
  
  : matrix_t :=
  let ret_737 : seq int128 :=
    seq_new_ (default : scalar_t) ((n_734) * (m_735)) in 
  let ret_737 :=
    foldi (usize 0) ((n_734) * (m_735)) (fun i_738 ret_737 =>
      let ret_737 :=
        seq_upd ret_737 (i_738) (scalar_736) in 
      (ret_737))
    ret_737 in 
  ((n_734, m_735), ret_737).


Definition zeros (n_739 : dim_type_t) (m_740 : dim_type_t)  : matrix_t :=
  repeat (n_739) (m_740) (pub_int128_zero ).


Definition ones (n_741 : dim_type_t) (m_742 : dim_type_t)  : matrix_t :=
  repeat (n_741) (m_742) (pub_int128_one ).


Definition identity (n_743 : dim_type_t) (m_744 : dim_type_t)  : matrix_t :=
  let ret_745 : seq int128 :=
    seq_new_ (default : scalar_t) ((n_743) * (m_744)) in 
  let ret_745 :=
    foldi (usize 0) (min (n_743) (m_744)) (fun i_746 ret_745 =>
      let index_747 : uint_size :=
        ((i_746) * (min (n_743) (m_744))) + (i_746) in 
      let ret_745 :=
        seq_upd ret_745 (index_747) (pub_int128_one ) in 
      (ret_745))
    ret_745 in 
  ((n_743, m_744), ret_745).


Definition index
  (m_748 : matrix_t)
  (i_749 : dim_type_t)
  (j_750 : dim_type_t)
  
  : scal_res_t :=
  let '(dim_751, seq_752) :=
    m_748 in 
  let '(rows_753, cols_754) :=
    dim_751 in 
  let index_755 : uint_size :=
    ((i_749) * (cols_754)) + (j_750) in 
  (if ((index_755) >=.? ((rows_753) * (cols_754))):bool then (
      @Err scalar_t int8 (index_out_of_bounds_v)) else (@Ok scalar_t int8 (
        seq_index (seq_752) (index_755)))).


Definition transpose (matrix_756 : matrix_t)  : matrix_t :=
  let '(dim_757, seq_758) :=
    matrix_756 in 
  let '(rows_759, cols_760) :=
    dim_757 in 
  let ret_761 : seq int128 :=
    seq_new_ (default : scalar_t) (seq_len (seq_758)) in 
  let ret_761 :=
    foldi (usize 0) (rows_759) (fun i_762 ret_761 =>
      let ret_761 :=
        foldi (usize 0) (cols_760) (fun j_763 ret_761 =>
          let seq_index_764 : uint_size :=
            ((i_762) * (cols_760)) + (j_763) in 
          let ret_index_765 : uint_size :=
            ((j_763) * (rows_759)) + (i_762) in 
          let ret_761 :=
            seq_upd ret_761 (ret_index_765) (seq_index (seq_758) (
                seq_index_764)) in 
          (ret_761))
        ret_761 in 
      (ret_761))
    ret_761 in 
  ((cols_760, rows_759), ret_761).


Definition slice
  (matrix_766 : matrix_t)
  (start_767 : dims_t)
  (len_768 : dims_t)
  
  : mat_res_t :=
  let '(dim_769, seq_770) :=
    matrix_766 in 
  let '(rows_771, cols_772) :=
    dim_769 in 
  let '(start_row_773, start_col_774) :=
    start_767 in 
  let '(len_rows_775, len_cols_776) :=
    len_768 in 
  let start_index_777 : uint_size :=
    ((start_row_773) * (cols_772)) + (start_col_774) in 
  let ret_778 : seq int128 :=
    seq_new_ (default : scalar_t) ((len_rows_775) * (len_cols_776)) in 
  let res_779 : (result matrix_t int8) :=
    @Err matrix_t int8 (slice_out_of_bounds_v) in 
  let '(ret_778, res_779) :=
    if ((start_index_777) + ((len_rows_775) * (len_cols_776))) <=.? ((
        rows_771) * (cols_772)):bool then (let ret_778 :=
        foldi (usize 0) (len_rows_775) (fun i_780 ret_778 =>
          let ret_778 :=
            foldi (usize 0) (len_cols_776) (fun j_781 ret_778 =>
              let ret_index_782 : uint_size :=
                ((i_780) * (len_cols_776)) + (j_781) in 
              let seq_index_783 : uint_size :=
                (((start_row_773) + (i_780)) * (cols_772)) + ((
                    start_col_774) + (j_781)) in 
              let ret_778 :=
                seq_upd ret_778 (ret_index_782) (seq_index (seq_770) (
                    seq_index_783)) in 
              (ret_778))
            ret_778 in 
          (ret_778))
        ret_778 in 
      let res_779 :=
        new_ (len_rows_775) (len_cols_776) (ret_778) in 
      (ret_778, res_779)) else ((ret_778, res_779)) in 
  res_779.


Definition scale (matrix_784 : matrix_t) (scalar_785 : scalar_t)  : matrix_t :=
  let '(dim_786, seq_787) :=
    matrix_784 in 
  let ret_788 : seq int128 :=
    seq_new_ (default : scalar_t) (seq_len (seq_787)) in 
  let ret_788 :=
    foldi (usize 0) (seq_len (seq_787)) (fun i_789 ret_788 =>
      let ret_788 :=
        seq_upd ret_788 (i_789) ((scalar_785) .* (seq_index (seq_787) (
              i_789))) in 
      (ret_788))
    ret_788 in 
  (dim_786, ret_788).


Definition add
  (matrix_1_790 : matrix_t)
  (matrix_2_791 : matrix_t)
  
  : mat_res_t :=
  let '(m1_dim_792, m1_s_793) :=
    matrix_1_790 in 
  let '(m2_dim_794, m2_s_795) :=
    matrix_2_791 in 
  let ret_796 : seq int128 :=
    seq_new_ (default : scalar_t) (seq_len (m1_s_793)) in 
  let res_797 : (result matrix_t int8) :=
    @Err matrix_t int8 (dimension_mismatch_v) in 
  let '(ret_796, res_797) :=
    if (m1_dim_792) =.? (m2_dim_794):bool then (let ret_796 :=
        foldi (usize 0) (seq_len (m1_s_793)) (fun i_798 ret_796 =>
          let ret_796 :=
            seq_upd ret_796 (i_798) ((seq_index (m1_s_793) (i_798)) .+ (
                seq_index (m2_s_795) (i_798))) in 
          (ret_796))
        ret_796 in 
      let res_797 :=
        @Ok matrix_t int8 ((m1_dim_792, ret_796)) in 
      (ret_796, res_797)) else ((ret_796, res_797)) in 
  res_797.


Definition sub
  (matrix_1_799 : matrix_t)
  (matrix_2_800 : matrix_t)
  
  : mat_res_t :=
  let '(m1_dim_801, m1_s_802) :=
    matrix_1_799 in 
  let '(m2_dim_803, m2_s_804) :=
    matrix_2_800 in 
  let ret_805 : seq int128 :=
    seq_new_ (default : scalar_t) (seq_len (m1_s_802)) in 
  let res_806 : (result matrix_t int8) :=
    @Err matrix_t int8 (dimension_mismatch_v) in 
  let '(ret_805, res_806) :=
    if (m1_dim_801) =.? (m2_dim_803):bool then (let ret_805 :=
        foldi (usize 0) (seq_len (m1_s_802)) (fun i_807 ret_805 =>
          let ret_805 :=
            seq_upd ret_805 (i_807) ((seq_index (m1_s_802) (i_807)) .- (
                seq_index (m2_s_804) (i_807))) in 
          (ret_805))
        ret_805 in 
      let res_806 :=
        @Ok matrix_t int8 ((m1_dim_801, ret_805)) in 
      (ret_805, res_806)) else ((ret_805, res_806)) in 
  res_806.


Definition component_mul
  (matrix_1_808 : matrix_t)
  (matrix_2_809 : matrix_t)
  
  : mat_res_t :=
  let '(m1_dim_810, m1_s_811) :=
    matrix_1_808 in 
  let '(m2_dim_812, m2_s_813) :=
    matrix_2_809 in 
  let ret_814 : seq int128 :=
    seq_new_ (default : scalar_t) (seq_len (m1_s_811)) in 
  let res_815 : (result matrix_t int8) :=
    @Err matrix_t int8 (dimension_mismatch_v) in 
  let '(ret_814, res_815) :=
    if (m1_dim_810) =.? (m2_dim_812):bool then (let ret_814 :=
        foldi (usize 0) (seq_len (m1_s_811)) (fun i_816 ret_814 =>
          let ret_814 :=
            seq_upd ret_814 (i_816) ((seq_index (m1_s_811) (i_816)) .* (
                seq_index (m2_s_813) (i_816))) in 
          (ret_814))
        ret_814 in 
      let res_815 :=
        @Ok matrix_t int8 ((m1_dim_810, ret_814)) in 
      (ret_814, res_815)) else ((ret_814, res_815)) in 
  res_815.


Definition mul
  (matrix_1_817 : matrix_t)
  (matrix_2_818 : matrix_t)
  
  : mat_res_t :=
  let '(dim_1_819, seq_1_820) :=
    matrix_1_817 in 
  let '(dim_2_821, seq_2_822) :=
    matrix_2_818 in 
  let '(l_823, m_824) :=
    dim_1_819 in 
  let '(m_825, n_826) :=
    dim_2_821 in 
  let ret_827 : seq int128 :=
    seq_new_ (default : scalar_t) ((l_823) * (n_826)) in 
  let res_828 : (result matrix_t int8) :=
    @Err matrix_t int8 (dimension_mismatch_v) in 
  let '(ret_827, res_828) :=
    if (m_824) =.? (m_825):bool then (let ret_827 :=
        foldi (usize 0) (l_823) (fun i_829 ret_827 =>
          let ret_827 :=
            foldi (usize 0) (n_826) (fun j_830 ret_827 =>
              let acc_831 : int128 :=
                pub_int128_zero  in 
              let index_832 : uint_size :=
                ((i_829) * (n_826)) + (j_830) in 
              let acc_831 :=
                foldi (usize 0) (m_824) (fun k_833 acc_831 =>
                  let index_1_834 : uint_size :=
                    ((i_829) * (m_824)) + (k_833) in 
                  let index_2_835 : uint_size :=
                    ((k_833) * (n_826)) + (j_830) in 
                  let acc_831 :=
                    (acc_831) .+ ((seq_index (seq_1_820) (index_1_834)) .* (
                        seq_index (seq_2_822) (index_2_835))) in 
                  (acc_831))
                acc_831 in 
              let ret_827 :=
                seq_upd ret_827 (index_832) (acc_831) in 
              (ret_827))
            ret_827 in 
          (ret_827))
        ret_827 in 
      let res_828 :=
        new_ (l_823) (n_826) (ret_827) in 
      (ret_827, res_828)) else ((ret_827, res_828)) in 
  res_828.


