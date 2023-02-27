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

Require Import Hacspec_Sha3.
Export Hacspec_Sha3.

Definition strobe_r_v : int8 :=
  @repr WORDSIZE8 166.

Definition flag_i_v : int8 :=
  @repr WORDSIZE8 1.

Definition flag_a_v : int8 :=
  (@repr WORDSIZE8 1) shift_left (usize 1).

Definition flag_c_v : int8 :=
  (@repr WORDSIZE8 1) shift_left (usize 2).

Definition flag_m_v : int8 :=
  (@repr WORDSIZE8 1) shift_left (usize 4).

Definition flag_k_v : int8 :=
  (@repr WORDSIZE8 1) shift_left (usize 5).

Notation "'state_uint64_t'" := (state_t) : hacspec_scope.

Definition state_uint8_t := nseq (uint8) (usize 200).

Notation "'strobe_t'" := ((state_uint8_t '× int8 '× int8 '× int8
)) : hacspec_scope.

Definition transmute_state_to_u64
  (state_836 : state_uint8_t)
  
  : state_uint64_t :=
  let new_state_837 : state_t :=
    array_new_ (default : uint64) (25) in 
  let new_state_837 :=
    foldi (usize 0) (array_len (new_state_837)) (fun i_838 new_state_837 =>
      let word_839 : uint64_word_t :=
        array_new_ (default : uint8) (8) in 
      let word_839 :=
        foldi (usize 0) (array_len (word_839)) (fun j_840 word_839 =>
          let word_839 :=
            array_upd word_839 (j_840) (array_index (state_836) (((i_838) * (
                    usize 8)) + (j_840))) in 
          (word_839))
        word_839 in 
      let new_state_837 :=
        array_upd new_state_837 (i_838) (uint64_from_le_bytes (word_839)) in 
      (new_state_837))
    new_state_837 in 
  new_state_837.


Definition transmute_state_to_u8
  (state_841 : state_uint64_t)
  
  : state_uint8_t :=
  let new_state_842 : state_uint8_t :=
    array_new_ (default : uint8) (200) in 
  let new_state_842 :=
    foldi (usize 0) (array_len (state_841)) (fun i_843 new_state_842 =>
      let bytes_844 : seq uint8 :=
        uint64_to_le_bytes (array_index (state_841) (i_843)) in 
      let new_state_842 :=
        foldi (usize 0) (seq_len (bytes_844)) (fun j_845 new_state_842 =>
          let new_state_842 :=
            array_upd new_state_842 (((i_843) * (usize 8)) + (j_845)) (
              seq_index (bytes_844) (j_845)) in 
          (new_state_842))
        new_state_842 in 
      (new_state_842))
    new_state_842 in 
  new_state_842.


Definition run_f (strobe_846 : strobe_t)  : strobe_t :=
  let '(state_847, pos_848, pos_begin_849, cur_fl_850) :=
    strobe_846 in 
  let state_847 :=
    array_upd state_847 (pos_848) ((array_index (state_847) (pos_848)) .^ (
        secret (pos_begin_849) : int8)) in 
  let state_847 :=
    array_upd state_847 ((pos_848) .+ (@repr WORDSIZE8 1)) ((array_index (
          state_847) ((pos_848) .+ (@repr WORDSIZE8 1))) .^ (secret (
          @repr WORDSIZE8 4) : int8)) in 
  let state_847 :=
    array_upd state_847 ((strobe_r_v) .+ (@repr WORDSIZE8 1)) ((array_index (
          state_847) ((strobe_r_v) .+ (@repr WORDSIZE8 1))) .^ (secret (
          @repr WORDSIZE8 128) : int8)) in 
  let state_uint64_851 : state_t :=
    transmute_state_to_u64 (state_847) in 
  let state_847 :=
    transmute_state_to_u8 (keccakf1600 (state_uint64_851)) in 
  let pos_848 :=
    @repr WORDSIZE8 0 in 
  let pos_begin_849 :=
    @repr WORDSIZE8 0 in 
  (state_847, pos_848, pos_begin_849, cur_fl_850).


Definition absorb (strobe_852 : strobe_t) (data_853 : seq uint8)  : strobe_t :=
  let '(state_854, pos_855, pos_begin_856, cur_fl_857) :=
    strobe_852 in 
  let '(state_854, pos_855, pos_begin_856, cur_fl_857) :=
    foldi (usize 0) (seq_len (data_853)) (fun i_858 '(
        state_854,
        pos_855,
        pos_begin_856,
        cur_fl_857
      ) =>
      let state_854 :=
        array_upd state_854 (pos_855) ((array_index (state_854) (pos_855)) .^ (
            seq_index (data_853) (i_858))) in 
      let pos_855 :=
        (pos_855) .+ (@repr WORDSIZE8 1) in 
      let '(state_854, pos_855, pos_begin_856, cur_fl_857) :=
        if (pos_855) =.? (strobe_r_v):bool then (let '(
              s_859,
              p_860,
              pb_861,
              cf_862
            ) :=
            run_f ((state_854, pos_855, pos_begin_856, cur_fl_857)) in 
          let state_854 :=
            s_859 in 
          let pos_855 :=
            p_860 in 
          let pos_begin_856 :=
            pb_861 in 
          let cur_fl_857 :=
            cf_862 in 
          (state_854, pos_855, pos_begin_856, cur_fl_857)) else ((
            state_854,
            pos_855,
            pos_begin_856,
            cur_fl_857
          )) in 
      (state_854, pos_855, pos_begin_856, cur_fl_857))
    (state_854, pos_855, pos_begin_856, cur_fl_857) in 
  (state_854, pos_855, pos_begin_856, cur_fl_857).


Definition squeeze
  (strobe_863 : strobe_t)
  (data_864 : seq uint8)
  
  : (strobe_t '× seq uint8) :=
  let '(state_865, pos_866, pos_begin_867, cur_fl_868) :=
    strobe_863 in 
  let '(data_864, state_865, pos_866, pos_begin_867, cur_fl_868) :=
    foldi (usize 0) (seq_len (data_864)) (fun i_869 '(
        data_864,
        state_865,
        pos_866,
        pos_begin_867,
        cur_fl_868
      ) =>
      let data_864 :=
        seq_upd data_864 (i_869) (array_index (state_865) (pos_866)) in 
      let state_865 :=
        array_upd state_865 (pos_866) (uint8_classify (@repr WORDSIZE8 0)) in 
      let pos_866 :=
        (pos_866) .+ (@repr WORDSIZE8 1) in 
      let '(state_865, pos_866, pos_begin_867, cur_fl_868) :=
        if (pos_866) =.? (strobe_r_v):bool then (let '(
              s_870,
              p_871,
              pb_872,
              cf_873
            ) :=
            run_f (((state_865), pos_866, pos_begin_867, cur_fl_868)) in 
          let state_865 :=
            s_870 in 
          let pos_866 :=
            p_871 in 
          let pos_begin_867 :=
            pb_872 in 
          let cur_fl_868 :=
            cf_873 in 
          (state_865, pos_866, pos_begin_867, cur_fl_868)) else ((
            state_865,
            pos_866,
            pos_begin_867,
            cur_fl_868
          )) in 
      (data_864, state_865, pos_866, pos_begin_867, cur_fl_868))
    (data_864, state_865, pos_866, pos_begin_867, cur_fl_868) in 
  ((state_865, pos_866, pos_begin_867, cur_fl_868), data_864).


Definition begin_op
  (strobe_874 : strobe_t)
  (flags_875 : int8)
  (more_876 : bool)
  
  : strobe_t :=
  let '(state_877, pos_878, pos_begin_879, cur_fl_880) :=
    strobe_874 in 
  let ret_881 : (state_uint8_t '× int8 '× int8 '× int8) :=
    (state_877, pos_878, pos_begin_879, cur_fl_880) in 
  let '(state_877, pos_878, pos_begin_879, cur_fl_880, ret_881) :=
    if negb (more_876):bool then (let old_begin_882 : int8 :=
        pos_begin_879 in 
      let pos_begin_879 :=
        (pos_878) .+ (@repr WORDSIZE8 1) in 
      let cur_fl_880 :=
        flags_875 in 
      let data_883 : seq uint8 :=
        seq_new_ (default : uint8) (usize 2) in 
      let data_883 :=
        seq_upd data_883 (usize 0) (secret (old_begin_882) : int8) in 
      let data_883 :=
        seq_upd data_883 (usize 1) (secret (flags_875) : int8) in 
      let '(s_884, p_885, pb_886, cf_887) :=
        absorb ((state_877, pos_878, pos_begin_879, cur_fl_880)) (data_883) in 
      let state_877 :=
        s_884 in 
      let pos_878 :=
        p_885 in 
      let pos_begin_879 :=
        pb_886 in 
      let cur_fl_880 :=
        cf_887 in 
      let force_f_888 : bool :=
        (@repr WORDSIZE8 0) !=.? ((flags_875) .& ((flag_c_v) .| (flag_k_v))) in 
      let '(ret_881) :=
        if (force_f_888) && ((pos_878) !=.? (@repr WORDSIZE8 0)):bool then (
          let ret_881 :=
            run_f ((state_877, pos_878, pos_begin_879, cur_fl_880)) in 
          (ret_881)) else (let ret_881 :=
            (state_877, pos_878, pos_begin_879, cur_fl_880) in 
          (ret_881)) in 
      (state_877, pos_878, pos_begin_879, cur_fl_880, ret_881)) else ((
        state_877,
        pos_878,
        pos_begin_879,
        cur_fl_880,
        ret_881
      )) in 
  ret_881.


Definition new_strobe (protocol_label_889 : seq uint8)  : strobe_t :=
  let st_890 : state_uint8_t :=
    array_new_ (default : uint8) (200) in 
  let st_890 :=
    array_set_chunk (st_890) (usize 6) (usize 0) ([
        secret (@repr WORDSIZE8 1) : int8;
        secret (@repr WORDSIZE8 168) : int8;
        secret (@repr WORDSIZE8 1) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 1) : int8;
        secret (@repr WORDSIZE8 96) : int8
      ]) in 
  let st_890 :=
    array_set_chunk (st_890) (usize 6) (usize 1) ([
        secret (@repr WORDSIZE8 83) : int8;
        secret (@repr WORDSIZE8 84) : int8;
        secret (@repr WORDSIZE8 82) : int8;
        secret (@repr WORDSIZE8 79) : int8;
        secret (@repr WORDSIZE8 66) : int8;
        secret (@repr WORDSIZE8 69) : int8
      ]) in 
  let st_890 :=
    array_set_chunk (st_890) (usize 6) (usize 2) ([
        secret (@repr WORDSIZE8 118) : int8;
        secret (@repr WORDSIZE8 49) : int8;
        secret (@repr WORDSIZE8 46) : int8;
        secret (@repr WORDSIZE8 48) : int8;
        secret (@repr WORDSIZE8 46) : int8;
        secret (@repr WORDSIZE8 50) : int8
      ]) in 
  let st_uint64_891 : state_t :=
    transmute_state_to_u64 (st_890) in 
  let st_890 :=
    transmute_state_to_u8 (keccakf1600 (st_uint64_891)) in 
  meta_ad ((st_890, @repr WORDSIZE8 0, @repr WORDSIZE8 0, @repr WORDSIZE8 0)) (
    protocol_label_889) (false).


Definition meta_ad
  (strobe_892 : strobe_t)
  (data_893 : seq uint8)
  (more_894 : bool)
  
  : strobe_t :=
  let strobe_892 :=
    begin_op (strobe_892) ((flag_m_v) .| (flag_a_v)) (more_894) in 
  absorb (strobe_892) (data_893).


Definition ad
  (strobe_895 : strobe_t)
  (data_896 : seq uint8)
  (more_897 : bool)
  
  : strobe_t :=
  let strobe_895 :=
    begin_op (strobe_895) (flag_a_v) (more_897) in 
  absorb (strobe_895) (data_896).


Definition prf
  (strobe_898 : strobe_t)
  (data_899 : seq uint8)
  (more_900 : bool)
  
  : (strobe_t '× seq uint8) :=
  let strobe_898 :=
    begin_op (strobe_898) (((flag_i_v) .| (flag_a_v)) .| (flag_c_v)) (
      more_900) in 
  squeeze (strobe_898) (data_899).


