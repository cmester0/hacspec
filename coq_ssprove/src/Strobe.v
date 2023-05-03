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


Require Import Hacspec_Sha3.

Definition strobe_r_v : int8 :=
  @repr U8 166.

Definition flag_i_v : int8 :=
  @repr U8 1.

Definition flag_a_v : int8 :=
  ((@repr U8 1) shift_left (usize 1)).

Definition flag_c_v : int8 :=
  ((@repr U8 1) shift_left (usize 2)).

Definition flag_m_v : int8 :=
  ((@repr U8 1) shift_left (usize 4)).

Definition flag_k_v : int8 :=
  ((@repr U8 1) shift_left (usize 5)).

Notation "'state_uint64_t'" := (state_t) : hacspec_scope.

Definition state_uint8_t := nseq (uint8) (usize 200).

Notation "'strobe_t'" := ((state_uint8_t × int8 × int8 × int8
)) : hacspec_scope.

Definition new_state_1063_loc : ChoiceEqualityLocation :=
  (state_t ; 1065%nat).
Definition word_1064_loc : ChoiceEqualityLocation :=
  (uint64_word_t ; 1066%nat).
Notation "'transmute_state_to_u64_inp'" :=(
  state_uint8_t : choice_type) (in custom pack_type at level 2).
Notation "'transmute_state_to_u64_out'" :=(
  state_uint64_t : choice_type) (in custom pack_type at level 2).
Definition TRANSMUTE_STATE_TO_U64 : nat :=
  1070.
Program Definition transmute_state_to_u64 (state_1069 : state_uint8_t)
  : both (CEfset ([new_state_1063_loc ; word_1064_loc])) [interface] (
    state_uint64_t) :=
  ((letbm new_state_1063 : state_t loc( new_state_1063_loc ) :=
        array_new_ (default : uint64) (25) in
      letb new_state_1063 :=
        foldi_both' (lift_to_both0 (usize 0)) (array_len (
              lift_to_both0 new_state_1063)) new_state_1063 (L := (CEfset (
                [new_state_1063_loc ; word_1064_loc]))) (I := [interface]) (
            fun i_1067 new_state_1063 =>
            letbm word_1064 : uint64_word_t loc( word_1064_loc ) :=
              array_new_ (default : uint8) (8) in
            letb word_1064 :=
              foldi_both' (lift_to_both0 (usize 0)) (array_len (
                    lift_to_both0 word_1064)) word_1064 (L := (CEfset (
                      [new_state_1063_loc ; word_1064_loc]))) (
                  I := [interface]) (fun j_1068 word_1064 =>
                  letb word_1064 : uint64_word_t :=
                    array_upd word_1064 (lift_to_both0 j_1068) (is_pure (
                        array_index (state_1069) (((lift_to_both0 i_1067) .* (
                              lift_to_both0 (usize 8))) .+ (
                            lift_to_both0 j_1068)))) in
                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 word_1064)
                  ) in
            letb new_state_1063 : state_t :=
              array_upd new_state_1063 (lift_to_both0 i_1067) (is_pure (
                  uint64_from_le_bytes (lift_to_both0 word_1064))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 new_state_1063)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 new_state_1063)
      ) : both (CEfset ([new_state_1063_loc ; word_1064_loc])) [interface] (
      state_uint64_t)).
Fail Next Obligation.

Definition new_state_1071_loc : ChoiceEqualityLocation :=
  (state_uint8_t ; 1072%nat).
Notation "'transmute_state_to_u8_inp'" :=(
  state_uint64_t : choice_type) (in custom pack_type at level 2).
Notation "'transmute_state_to_u8_out'" :=(
  state_uint8_t : choice_type) (in custom pack_type at level 2).
Definition TRANSMUTE_STATE_TO_U8 : nat :=
  1077.
Program Definition transmute_state_to_u8 (state_1073 : state_uint64_t)
  : both (CEfset ([new_state_1071_loc])) [interface] (state_uint8_t) :=
  ((letbm new_state_1071 : state_uint8_t loc( new_state_1071_loc ) :=
        array_new_ (default : uint8) (200) in
      letb new_state_1071 :=
        foldi_both' (lift_to_both0 (usize 0)) (array_len (
              lift_to_both0 state_1073)) new_state_1071 (L := (CEfset (
                [new_state_1071_loc]))) (I := [interface]) (
            fun i_1074 new_state_1071 =>
            letb bytes_1075 : seq uint8 :=
              uint64_to_le_bytes (array_index (state_1073) (
                  lift_to_both0 i_1074)) in
            letb new_state_1071 :=
              foldi_both' (lift_to_both0 (usize 0)) (seq_len (
                    lift_to_both0 bytes_1075)) new_state_1071 (L := (CEfset (
                      [new_state_1071_loc]))) (I := [interface]) (
                  fun j_1076 new_state_1071 =>
                  letb new_state_1071 : state_uint8_t :=
                    array_upd new_state_1071 (((lift_to_both0 i_1074) .* (
                          lift_to_both0 (usize 8))) .+ (lift_to_both0 j_1076)) (
                      is_pure (seq_index (bytes_1075) (
                          lift_to_both0 j_1076))) in
                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 new_state_1071)
                  ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 new_state_1071)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 new_state_1071)
      ) : both (CEfset ([new_state_1071_loc])) [interface] (state_uint8_t)).
Fail Next Obligation.

Definition pos_1079_loc : ChoiceEqualityLocation :=
  (int8 ; 1081%nat).
Definition state_1078_loc : ChoiceEqualityLocation :=
  (state_uint8_t ; 1082%nat).
Definition pos_begin_1080_loc : ChoiceEqualityLocation :=
  (int8 ; 1083%nat).
Notation "'run_f_inp'" :=(
  strobe_t : choice_type) (in custom pack_type at level 2).
Notation "'run_f_out'" :=(
  strobe_t : choice_type) (in custom pack_type at level 2).
Definition RUN_F : nat :=
  1087.
Program Definition run_f (strobe_1084 : strobe_t)
  : both (CEfset (
      [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc])) [interface] (
    strobe_t) :=
  ((letb '(state_1078, pos_1079, pos_begin_1080, cur_fl_1085) : (
          state_uint8_t '×
          int8 '×
          int8 '×
          int8
        ) :=
        lift_to_both0 strobe_1084 in
      letb state_1078 : state_uint8_t :=
        array_upd state_1078 (lift_to_both0 pos_1079) (is_pure ((array_index (
                state_1078) (lift_to_both0 pos_1079)) .^ (secret (
                lift_to_both0 pos_begin_1080)))) in
      letb state_1078 : state_uint8_t :=
        array_upd state_1078 ((lift_to_both0 pos_1079) .+ (lift_to_both0 (
              @repr U8 1))) (is_pure ((array_index (state_1078) ((
                  lift_to_both0 pos_1079) .+ (lift_to_both0 (@repr U8 1)))) .^ (
              secret (lift_to_both0 (@repr U8 4))))) in
      letb state_1078 : state_uint8_t :=
        array_upd state_1078 ((lift_to_both0 strobe_r_v) .+ (lift_to_both0 (
              @repr U8 1))) (is_pure ((array_index (state_1078) ((
                  lift_to_both0 strobe_r_v) .+ (lift_to_both0 (
                    @repr U8 1)))) .^ (secret (lift_to_both0 (
                  @repr U8 128))))) in
      letb state_uint64_1086 : state_t :=
        transmute_state_to_u64 (lift_to_both0 state_1078) in
      letbm state_1078 loc( state_1078_loc ) :=
        transmute_state_to_u8 (keccakf1600 (lift_to_both0 state_uint64_1086)) in
      letbm pos_1079 loc( pos_1079_loc ) := lift_to_both0 (@repr U8 0) in
      letbm pos_begin_1080 loc( pos_begin_1080_loc ) :=
        lift_to_both0 (@repr U8 0) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 state_1078,
          lift_to_both0 pos_1079,
          lift_to_both0 pos_begin_1080,
          lift_to_both0 cur_fl_1085
        ))
      ) : both (CEfset (
        [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc])) [interface] (
      strobe_t)).
Fail Next Obligation.

Definition state_1088_loc : ChoiceEqualityLocation :=
  (state_uint8_t ; 1092%nat).
Definition pos_begin_1090_loc : ChoiceEqualityLocation :=
  (int8 ; 1093%nat).
Definition cur_fl_1091_loc : ChoiceEqualityLocation :=
  (int8 ; 1094%nat).
Definition pos_1089_loc : ChoiceEqualityLocation :=
  (int8 ; 1095%nat).
Notation "'absorb_inp'" :=(
  strobe_t × seq uint8 : choice_type) (in custom pack_type at level 2).
Notation "'absorb_out'" :=(
  strobe_t : choice_type) (in custom pack_type at level 2).
Definition ABSORB : nat :=
  1103.
Program Definition absorb (strobe_1096 : strobe_t) (data_1097 : seq uint8)
  : both (CEfset (
      [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1088_loc ; pos_1089_loc ; pos_begin_1090_loc ; cur_fl_1091_loc])) [interface] (
    strobe_t) :=
  ((letb '(state_1088, pos_1089, pos_begin_1090, cur_fl_1091) : (
          state_uint8_t '×
          int8 '×
          int8 '×
          int8
        ) :=
        lift_to_both0 strobe_1096 in
      letb '(state_1088, pos_1089, pos_begin_1090, cur_fl_1091) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 data_1097)) prod_ce(
            state_1088,
            pos_1089,
            pos_begin_1090,
            cur_fl_1091
          ) (L := (CEfset (
                [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1088_loc ; pos_1089_loc ; pos_begin_1090_loc ; cur_fl_1091_loc]))) (
            I := [interface]) (fun i_1098 '(
              state_1088,
              pos_1089,
              pos_begin_1090,
              cur_fl_1091
            ) =>
            letb state_1088 : state_uint8_t :=
              array_upd state_1088 (lift_to_both0 pos_1089) (is_pure ((
                    array_index (state_1088) (lift_to_both0 pos_1089)) .^ (
                    seq_index (data_1097) (lift_to_both0 i_1098)))) in
            letbm pos_1089 loc( pos_1089_loc ) :=
              (lift_to_both0 pos_1089) .+ (lift_to_both0 (@repr U8 1)) in
            letb '(state_1088, pos_1089, pos_begin_1090, cur_fl_1091) :=
              if (lift_to_both0 pos_1089) =.? (
                lift_to_both0 strobe_r_v) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1088_loc ; pos_1089_loc ; pos_begin_1090_loc ; cur_fl_1091_loc])) (
                L2 := CEfset (
                  [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1088_loc ; pos_1089_loc ; pos_begin_1090_loc ; cur_fl_1091_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb '(s_1099, p_1100, pb_1101, cf_1102) : (
                    state_uint8_t '×
                    int8 '×
                    int8 '×
                    int8
                  ) :=
                  run_f (prod_b(
                      lift_to_both0 state_1088,
                      lift_to_both0 pos_1089,
                      lift_to_both0 pos_begin_1090,
                      lift_to_both0 cur_fl_1091
                    )) in
                letbm state_1088 loc( state_1088_loc ) :=
                  lift_to_both0 s_1099 in
                letbm pos_1089 loc( pos_1089_loc ) := lift_to_both0 p_1100 in
                letbm pos_begin_1090 loc( pos_begin_1090_loc ) :=
                  lift_to_both0 pb_1101 in
                letbm cur_fl_1091 loc( cur_fl_1091_loc ) :=
                  lift_to_both0 cf_1102 in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 state_1088,
                    lift_to_both0 pos_1089,
                    lift_to_both0 pos_begin_1090,
                    lift_to_both0 cur_fl_1091
                  ))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                  lift_to_both0 state_1088,
                  lift_to_both0 pos_1089,
                  lift_to_both0 pos_begin_1090,
                  lift_to_both0 cur_fl_1091
                ))
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 state_1088,
                lift_to_both0 pos_1089,
                lift_to_both0 pos_begin_1090,
                lift_to_both0 cur_fl_1091
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 state_1088,
          lift_to_both0 pos_1089,
          lift_to_both0 pos_begin_1090,
          lift_to_both0 cur_fl_1091
        ))
      ) : both (CEfset (
        [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1088_loc ; pos_1089_loc ; pos_begin_1090_loc ; cur_fl_1091_loc])) [interface] (
      strobe_t)).
Fail Next Obligation.

Definition state_1104_loc : ChoiceEqualityLocation :=
  (state_uint8_t ; 1108%nat).
Definition pos_1105_loc : ChoiceEqualityLocation :=
  (int8 ; 1109%nat).
Definition cur_fl_1107_loc : ChoiceEqualityLocation :=
  (int8 ; 1110%nat).
Definition pos_begin_1106_loc : ChoiceEqualityLocation :=
  (int8 ; 1111%nat).
Notation "'squeeze_inp'" :=(
  strobe_t × seq uint8 : choice_type) (in custom pack_type at level 2).
Notation "'squeeze_out'" :=((strobe_t '× seq uint8
  ) : choice_type) (in custom pack_type at level 2).
Definition SQUEEZE : nat :=
  1119.
Program Definition squeeze (strobe_1112 : strobe_t) (data_1113 : seq uint8)
  : both (CEfset (
      [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1104_loc ; pos_1105_loc ; pos_begin_1106_loc ; cur_fl_1107_loc])) [interface] (
    (strobe_t '× seq uint8)) :=
  ((letb '(state_1104, pos_1105, pos_begin_1106, cur_fl_1107) : (
          state_uint8_t '×
          int8 '×
          int8 '×
          int8
        ) :=
        lift_to_both0 strobe_1112 in
      letb '(data_1113, state_1104, pos_1105, pos_begin_1106, cur_fl_1107) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 data_1113)) prod_ce(
            data_1113,
            state_1104,
            pos_1105,
            pos_begin_1106,
            cur_fl_1107
          ) (L := (CEfset (
                [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1104_loc ; pos_1105_loc ; pos_begin_1106_loc ; cur_fl_1107_loc]))) (
            I := [interface]) (fun i_1114 '(
              data_1113,
              state_1104,
              pos_1105,
              pos_begin_1106,
              cur_fl_1107
            ) =>
            letb data_1113 : seq uint8 :=
              seq_upd data_1113 (lift_to_both0 i_1114) (is_pure (array_index (
                    state_1104) (lift_to_both0 pos_1105))) in
            letb state_1104 : state_uint8_t :=
              array_upd state_1104 (lift_to_both0 pos_1105) (is_pure (
                  uint8_classify (lift_to_both0 (@repr U8 0)))) in
            letbm pos_1105 loc( pos_1105_loc ) :=
              (lift_to_both0 pos_1105) .+ (lift_to_both0 (@repr U8 1)) in
            letb '(state_1104, pos_1105, pos_begin_1106, cur_fl_1107) :=
              if (lift_to_both0 pos_1105) =.? (
                lift_to_both0 strobe_r_v) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1104_loc ; pos_1105_loc ; pos_begin_1106_loc ; cur_fl_1107_loc])) (
                L2 := CEfset (
                  [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1104_loc ; pos_1105_loc ; pos_begin_1106_loc ; cur_fl_1107_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb '(s_1115, p_1116, pb_1117, cf_1118) : (
                    state_uint8_t '×
                    int8 '×
                    int8 '×
                    int8
                  ) :=
                  run_f (prod_b(
                      (lift_to_both0 state_1104),
                      lift_to_both0 pos_1105,
                      lift_to_both0 pos_begin_1106,
                      lift_to_both0 cur_fl_1107
                    )) in
                letbm state_1104 loc( state_1104_loc ) :=
                  lift_to_both0 s_1115 in
                letbm pos_1105 loc( pos_1105_loc ) := lift_to_both0 p_1116 in
                letbm pos_begin_1106 loc( pos_begin_1106_loc ) :=
                  lift_to_both0 pb_1117 in
                letbm cur_fl_1107 loc( cur_fl_1107_loc ) :=
                  lift_to_both0 cf_1118 in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 state_1104,
                    lift_to_both0 pos_1105,
                    lift_to_both0 pos_begin_1106,
                    lift_to_both0 cur_fl_1107
                  ))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                  lift_to_both0 state_1104,
                  lift_to_both0 pos_1105,
                  lift_to_both0 pos_begin_1106,
                  lift_to_both0 cur_fl_1107
                ))
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 data_1113,
                lift_to_both0 state_1104,
                lift_to_both0 pos_1105,
                lift_to_both0 pos_begin_1106,
                lift_to_both0 cur_fl_1107
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          prod_b(
            lift_to_both0 state_1104,
            lift_to_both0 pos_1105,
            lift_to_both0 pos_begin_1106,
            lift_to_both0 cur_fl_1107
          ),
          lift_to_both0 data_1113
        ))
      ) : both (CEfset (
        [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1104_loc ; pos_1105_loc ; pos_begin_1106_loc ; cur_fl_1107_loc])) [interface] (
      (strobe_t '× seq uint8))).
Fail Next Obligation.

Definition pos_1121_loc : ChoiceEqualityLocation :=
  (int8 ; 1126%nat).
Definition state_1120_loc : ChoiceEqualityLocation :=
  (state_uint8_t ; 1127%nat).
Definition cur_fl_1123_loc : ChoiceEqualityLocation :=
  (int8 ; 1128%nat).
Definition pos_begin_1122_loc : ChoiceEqualityLocation :=
  (int8 ; 1129%nat).
Definition ret_1124_loc : ChoiceEqualityLocation :=
  ((state_uint8_t '× int8 '× int8 '× int8) ; 1130%nat).
Definition data_1125_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 1131%nat).
Notation "'begin_op_inp'" :=(
  strobe_t × int8 × bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'begin_op_out'" :=(
  strobe_t : choice_type) (in custom pack_type at level 2).
Definition BEGIN_OP : nat :=
  1141.
Program Definition begin_op (strobe_1132 : strobe_t) (flags_1135 : int8) (
    more_1133 : bool_ChoiceEquality)
  : both (CEfset (
      [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1088_loc ; pos_1089_loc ; pos_begin_1090_loc ; cur_fl_1091_loc ; state_1120_loc ; pos_1121_loc ; pos_begin_1122_loc ; cur_fl_1123_loc ; ret_1124_loc ; data_1125_loc])) [interface] (
    strobe_t) :=
  ((letb '(state_1120, pos_1121, pos_begin_1122, cur_fl_1123) : (
          state_uint8_t '×
          int8 '×
          int8 '×
          int8
        ) :=
        lift_to_both0 strobe_1132 in
      letbm ret_1124 : (state_uint8_t '× int8 '× int8 '× int8
        ) loc( ret_1124_loc ) :=
        prod_b(
          lift_to_both0 state_1120,
          lift_to_both0 pos_1121,
          lift_to_both0 pos_begin_1122,
          lift_to_both0 cur_fl_1123
        ) in
      letb '(state_1120, pos_1121, pos_begin_1122, cur_fl_1123, ret_1124) :=
        if negb (lift_to_both0 more_1133) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1088_loc ; pos_1089_loc ; pos_begin_1090_loc ; cur_fl_1091_loc ; state_1120_loc ; pos_1121_loc ; pos_begin_1122_loc ; cur_fl_1123_loc ; ret_1124_loc ; data_1125_loc])) (
          L2 := CEfset (
            [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1088_loc ; pos_1089_loc ; pos_begin_1090_loc ; cur_fl_1091_loc ; state_1120_loc ; pos_1121_loc ; pos_begin_1122_loc ; cur_fl_1123_loc ; ret_1124_loc ; data_1125_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb old_begin_1134 : int8 := lift_to_both0 pos_begin_1122 in
          letbm pos_begin_1122 loc( pos_begin_1122_loc ) :=
            (lift_to_both0 pos_1121) .+ (lift_to_both0 (@repr U8 1)) in
          letbm cur_fl_1123 loc( cur_fl_1123_loc ) :=
            lift_to_both0 flags_1135 in
          letbm data_1125 : seq uint8 loc( data_1125_loc ) :=
            seq_new_ (default : uint8) (lift_to_both0 (usize 2)) in
          letb data_1125 : seq uint8 :=
            seq_upd data_1125 (lift_to_both0 (usize 0)) (is_pure (secret (
                  lift_to_both0 old_begin_1134))) in
          letb data_1125 : seq uint8 :=
            seq_upd data_1125 (lift_to_both0 (usize 1)) (is_pure (secret (
                  lift_to_both0 flags_1135))) in
          letb '(s_1136, p_1137, pb_1138, cf_1139) : (
              state_uint8_t '×
              int8 '×
              int8 '×
              int8
            ) :=
            absorb (prod_b(
                lift_to_both0 state_1120,
                lift_to_both0 pos_1121,
                lift_to_both0 pos_begin_1122,
                lift_to_both0 cur_fl_1123
              )) (lift_to_both0 data_1125) in
          letbm state_1120 loc( state_1120_loc ) := lift_to_both0 s_1136 in
          letbm pos_1121 loc( pos_1121_loc ) := lift_to_both0 p_1137 in
          letbm pos_begin_1122 loc( pos_begin_1122_loc ) :=
            lift_to_both0 pb_1138 in
          letbm cur_fl_1123 loc( cur_fl_1123_loc ) := lift_to_both0 cf_1139 in
          letb force_f_1140 : bool_ChoiceEquality :=
            (lift_to_both0 (@repr U8 0)) !=.? ((lift_to_both0 flags_1135) .& ((
                  lift_to_both0 flag_c_v) .| (lift_to_both0 flag_k_v))) in
          letb '(ret_1124) :=
            if (lift_to_both0 force_f_1140) && ((lift_to_both0 pos_1121) !=.? (
                lift_to_both0 (@repr U8 0))) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset (
                [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1088_loc ; pos_1089_loc ; pos_begin_1090_loc ; cur_fl_1091_loc ; state_1120_loc ; pos_1121_loc ; pos_begin_1122_loc ; cur_fl_1123_loc ; ret_1124_loc ; data_1125_loc])) (
              L2 := CEfset (
                [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1088_loc ; pos_1089_loc ; pos_begin_1090_loc ; cur_fl_1091_loc ; state_1120_loc ; pos_1121_loc ; pos_begin_1122_loc ; cur_fl_1123_loc ; ret_1124_loc ; data_1125_loc])) (
              I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letbm ret_1124 loc( ret_1124_loc ) :=
                run_f (prod_b(
                    lift_to_both0 state_1120,
                    lift_to_both0 pos_1121,
                    lift_to_both0 pos_begin_1122,
                    lift_to_both0 cur_fl_1123
                  )) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 ret_1124)
              )
            else  lift_scope (L1 := CEfset (
                [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1088_loc ; pos_1089_loc ; pos_begin_1090_loc ; cur_fl_1091_loc ; state_1120_loc ; pos_1121_loc ; pos_begin_1122_loc ; cur_fl_1123_loc ; ret_1124_loc ; data_1125_loc])) (
              L2 := CEfset (
                [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1088_loc ; pos_1089_loc ; pos_begin_1090_loc ; cur_fl_1091_loc ; state_1120_loc ; pos_1121_loc ; pos_begin_1122_loc ; cur_fl_1123_loc ; ret_1124_loc ; data_1125_loc])) (
              I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letbm ret_1124 loc( ret_1124_loc ) :=
                prod_b(
                  lift_to_both0 state_1120,
                  lift_to_both0 pos_1121,
                  lift_to_both0 pos_begin_1122,
                  lift_to_both0 cur_fl_1123
                ) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 ret_1124)
              ) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 state_1120,
              lift_to_both0 pos_1121,
              lift_to_both0 pos_begin_1122,
              lift_to_both0 cur_fl_1123,
              lift_to_both0 ret_1124
            ))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 state_1120,
            lift_to_both0 pos_1121,
            lift_to_both0 pos_begin_1122,
            lift_to_both0 cur_fl_1123,
            lift_to_both0 ret_1124
          ))
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 ret_1124)
      ) : both (CEfset (
        [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1088_loc ; pos_1089_loc ; pos_begin_1090_loc ; cur_fl_1091_loc ; state_1120_loc ; pos_1121_loc ; pos_begin_1122_loc ; cur_fl_1123_loc ; ret_1124_loc ; data_1125_loc])) [interface] (
      strobe_t)).
Fail Next Obligation.

Definition st_1142_loc : ChoiceEqualityLocation :=
  (state_uint8_t ; 1143%nat).
Notation "'new_strobe_inp'" :=(
  seq uint8 : choice_type) (in custom pack_type at level 2).
Notation "'new_strobe_out'" :=(
  strobe_t : choice_type) (in custom pack_type at level 2).
Definition NEW_STROBE : nat :=
  1146.
Program Definition new_strobe (protocol_label_1145 : seq uint8)
  : both (CEfset (
      [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; st_1142_loc])) [interface] (
    strobe_t) :=
  ((letbm st_1142 : state_uint8_t loc( st_1142_loc ) :=
        array_new_ (default : uint8) (200) in
      letbm st_1142 loc( st_1142_loc ) :=
        array_set_chunk (lift_to_both0 st_1142) (lift_to_both0 (usize 6)) (
          lift_to_both0 (usize 0)) ([
            secret (lift_to_both0 (@repr U8 1));
            secret (lift_to_both0 (@repr U8 168));
            secret (lift_to_both0 (@repr U8 1));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 1));
            secret (lift_to_both0 (@repr U8 96))
          ]) in
      letbm st_1142 loc( st_1142_loc ) :=
        array_set_chunk (lift_to_both0 st_1142) (lift_to_both0 (usize 6)) (
          lift_to_both0 (usize 1)) ([
            secret (lift_to_both0 (@repr U8 83));
            secret (lift_to_both0 (@repr U8 84));
            secret (lift_to_both0 (@repr U8 82));
            secret (lift_to_both0 (@repr U8 79));
            secret (lift_to_both0 (@repr U8 66));
            secret (lift_to_both0 (@repr U8 69))
          ]) in
      letbm st_1142 loc( st_1142_loc ) :=
        array_set_chunk (lift_to_both0 st_1142) (lift_to_both0 (usize 6)) (
          lift_to_both0 (usize 2)) ([
            secret (lift_to_both0 (@repr U8 118));
            secret (lift_to_both0 (@repr U8 49));
            secret (lift_to_both0 (@repr U8 46));
            secret (lift_to_both0 (@repr U8 48));
            secret (lift_to_both0 (@repr U8 46));
            secret (lift_to_both0 (@repr U8 50))
          ]) in
      letb st_uint64_1144 : state_t :=
        transmute_state_to_u64 (lift_to_both0 st_1142) in
      letbm st_1142 loc( st_1142_loc ) :=
        transmute_state_to_u8 (keccakf1600 (lift_to_both0 st_uint64_1144)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (meta_ad (prod_b(
            lift_to_both0 st_1142,
            lift_to_both0 (@repr U8 0),
            lift_to_both0 (@repr U8 0),
            lift_to_both0 (@repr U8 0)
          )) (lift_to_both0 protocol_label_1145) (lift_to_both0 (
            (false : bool_ChoiceEquality))))
      ) : both (CEfset (
        [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; st_1142_loc])) [interface] (
      strobe_t)).
Fail Next Obligation.


Notation "'meta_ad_inp'" :=(
  strobe_t × seq uint8 × bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'meta_ad_out'" :=(
  strobe_t : choice_type) (in custom pack_type at level 2).
Definition META_AD : nat :=
  1150.
Program Definition meta_ad (strobe_1147 : strobe_t) (data_1149 : seq uint8) (
    more_1148 : bool_ChoiceEquality)
  : both (CEfset (
      [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1088_loc ; pos_1089_loc ; pos_begin_1090_loc ; cur_fl_1091_loc ; state_1120_loc ; pos_1121_loc ; pos_begin_1122_loc ; cur_fl_1123_loc ; ret_1124_loc ; data_1125_loc])) [interface] (
    strobe_t) :=
  ((letbm strobe_1147 loc( strobe_1147_loc ) :=
        begin_op (lift_to_both0 strobe_1147) ((lift_to_both0 flag_m_v) .| (
            lift_to_both0 flag_a_v)) (lift_to_both0 more_1148) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (absorb (
          lift_to_both0 strobe_1147) (lift_to_both0 data_1149))
      ) : both (CEfset (
        [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1088_loc ; pos_1089_loc ; pos_begin_1090_loc ; cur_fl_1091_loc ; state_1120_loc ; pos_1121_loc ; pos_begin_1122_loc ; cur_fl_1123_loc ; ret_1124_loc ; data_1125_loc])) [interface] (
      strobe_t)).
Fail Next Obligation.


Notation "'ad_inp'" :=(
  strobe_t × seq uint8 × bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'ad_out'" :=(strobe_t : choice_type) (in custom pack_type at level 2).
Definition AD : nat :=
  1154.
Program Definition ad (strobe_1151 : strobe_t) (data_1153 : seq uint8) (
    more_1152 : bool_ChoiceEquality)
  : both (CEfset (
      [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1088_loc ; pos_1089_loc ; pos_begin_1090_loc ; cur_fl_1091_loc ; state_1120_loc ; pos_1121_loc ; pos_begin_1122_loc ; cur_fl_1123_loc ; ret_1124_loc ; data_1125_loc])) [interface] (
    strobe_t) :=
  ((letbm strobe_1151 loc( strobe_1151_loc ) :=
        begin_op (lift_to_both0 strobe_1151) (lift_to_both0 flag_a_v) (
          lift_to_both0 more_1152) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (absorb (
          lift_to_both0 strobe_1151) (lift_to_both0 data_1153))
      ) : both (CEfset (
        [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1088_loc ; pos_1089_loc ; pos_begin_1090_loc ; cur_fl_1091_loc ; state_1120_loc ; pos_1121_loc ; pos_begin_1122_loc ; cur_fl_1123_loc ; ret_1124_loc ; data_1125_loc])) [interface] (
      strobe_t)).
Fail Next Obligation.


Notation "'prf_inp'" :=(
  strobe_t × seq uint8 × bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'prf_out'" :=((strobe_t '× seq uint8
  ) : choice_type) (in custom pack_type at level 2).
Definition PRF : nat :=
  1158.
Program Definition prf (strobe_1155 : strobe_t) (data_1157 : seq uint8) (
    more_1156 : bool_ChoiceEquality)
  : both (CEfset (
      [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1088_loc ; pos_1089_loc ; pos_begin_1090_loc ; cur_fl_1091_loc ; state_1104_loc ; pos_1105_loc ; pos_begin_1106_loc ; cur_fl_1107_loc ; state_1120_loc ; pos_1121_loc ; pos_begin_1122_loc ; cur_fl_1123_loc ; ret_1124_loc ; data_1125_loc])) [interface] (
    (strobe_t '× seq uint8)) :=
  ((letbm strobe_1155 loc( strobe_1155_loc ) :=
        begin_op (lift_to_both0 strobe_1155) (((lift_to_both0 flag_i_v) .| (
              lift_to_both0 flag_a_v)) .| (lift_to_both0 flag_c_v)) (
          lift_to_both0 more_1156) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (squeeze (
          lift_to_both0 strobe_1155) (lift_to_both0 data_1157))
      ) : both (CEfset (
        [new_state_1063_loc ; word_1064_loc ; new_state_1071_loc ; state_1078_loc ; pos_1079_loc ; pos_begin_1080_loc ; state_1088_loc ; pos_1089_loc ; pos_begin_1090_loc ; cur_fl_1091_loc ; state_1104_loc ; pos_1105_loc ; pos_begin_1106_loc ; cur_fl_1107_loc ; state_1120_loc ; pos_1121_loc ; pos_begin_1122_loc ; cur_fl_1123_loc ; ret_1124_loc ; data_1125_loc])) [interface] (
      (strobe_t '× seq uint8))).
Fail Next Obligation.

