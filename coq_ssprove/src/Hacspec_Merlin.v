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


Require Import Strobe.

Notation "'transcript_t'" := (strobe_t) : hacspec_scope.


Notation "'merlin_protocol_label_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'merlin_protocol_label_out'" :=(
  seq uint8 : choice_type) (in custom pack_type at level 2).
Definition MERLIN_PROTOCOL_LABEL : nat :=
  1159.
Program Definition merlin_protocol_label 
  : both (fset.fset0) [interface] (seq uint8) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ([
          secret (lift_to_both0 (@repr U8 77));
          secret (lift_to_both0 (@repr U8 101));
          secret (lift_to_both0 (@repr U8 114));
          secret (lift_to_both0 (@repr U8 108));
          secret (lift_to_both0 (@repr U8 105));
          secret (lift_to_both0 (@repr U8 110));
          secret (lift_to_both0 (@repr U8 32));
          secret (lift_to_both0 (@repr U8 118));
          secret (lift_to_both0 (@repr U8 49));
          secret (lift_to_both0 (@repr U8 46));
          secret (lift_to_both0 (@repr U8 48))
        ])
      ) : both (fset.fset0) [interface] (seq uint8)).
Fail Next Obligation.


Notation "'encode_uint64_inp'" :=(
  uint64 : choice_type) (in custom pack_type at level 2).
Notation "'encode_uint64_out'" :=(
  seq uint8 : choice_type) (in custom pack_type at level 2).
Definition ENCODE_U64 : nat :=
  1161.
Program Definition encode_uint64 (x_1160 : uint64)
  : both (fset.fset0) [interface] (seq uint8) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_to_le_bytes (
          uint64_to_le_bytes (lift_to_both0 x_1160)))
      ) : both (fset.fset0) [interface] (seq uint8)).
Fail Next Obligation.


Notation "'encode_usize_as_u32_inp'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'encode_usize_as_u32_out'" :=(
  seq uint8 : choice_type) (in custom pack_type at level 2).
Definition ENCODE_USIZE_AS_U32 : nat :=
  1164.
Program Definition encode_usize_as_u32 (x_1162 : uint_size)
  : both (fset.fset0) [interface] (seq uint8) :=
  ((letb x_uint32_1163 : uint32 :=
        uint32_classify (pub_u32 (is_pure (lift_to_both0 x_1162))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_to_le_bytes (
          uint32_to_le_bytes (lift_to_both0 x_uint32_1163)))
      ) : both (fset.fset0) [interface] (seq uint8)).
Fail Next Obligation.


Notation "'new__inp'" :=(
  seq uint8 : choice_type) (in custom pack_type at level 2).
Notation "'new__out'" :=(
  transcript_t : choice_type) (in custom pack_type at level 2).
Definition NEW : nat :=
  1168.
Program Definition new_ (label_1167 : seq uint8)
  : both (fset.fset0) [interface] (transcript_t) :=
  ((letb transcript_1165 : (state_uint8_t '× int8 '× int8 '× int8) :=
        new_strobe (merlin_protocol_label ) in
      letb dom_sep_1166 : seq uint8 :=
        [
          secret (lift_to_both0 (@repr U8 100));
          secret (lift_to_both0 (@repr U8 111));
          secret (lift_to_both0 (@repr U8 109));
          secret (lift_to_both0 (@repr U8 45));
          secret (lift_to_both0 (@repr U8 115));
          secret (lift_to_both0 (@repr U8 101));
          secret (lift_to_both0 (@repr U8 112))
        ] in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (append_message (
          lift_to_both0 transcript_1165) (lift_to_both0 dom_sep_1166) (
          lift_to_both0 label_1167))
      ) : both (fset.fset0) [interface] (transcript_t)).
Fail Next Obligation.


Notation "'append_message_inp'" :=(
  transcript_t × seq uint8 × seq uint8 : choice_type) (in custom pack_type at level 2).
Notation "'append_message_out'" :=(
  transcript_t : choice_type) (in custom pack_type at level 2).
Definition APPEND_MESSAGE : nat :=
  1173.
Program Definition append_message (transcript_1171 : transcript_t) (
    label_1172 : seq uint8) (message_1169 : seq uint8)
  : both (fset.fset0) [interface] (transcript_t) :=
  ((letb data_len_1170 : seq uint8 :=
        array_to_be_bytes (uint32_to_le_bytes (uint32_classify (pub_u32 (
                is_pure (seq_len (lift_to_both0 message_1169)))))) in
      letbm transcript_1171 loc( transcript_1171_loc ) :=
        meta_ad (lift_to_both0 transcript_1171) (lift_to_both0 label_1172) (
          lift_to_both0 ((false : bool_ChoiceEquality))) in
      letbm transcript_1171 loc( transcript_1171_loc ) :=
        meta_ad (lift_to_both0 transcript_1171) (lift_to_both0 data_len_1170) (
          lift_to_both0 ((true : bool_ChoiceEquality))) in
      letbm transcript_1171 loc( transcript_1171_loc ) :=
        ad (lift_to_both0 transcript_1171) (lift_to_both0 message_1169) (
          lift_to_both0 ((false : bool_ChoiceEquality))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 transcript_1171)
      ) : both (fset.fset0) [interface] (transcript_t)).
Fail Next Obligation.


Notation "'challenge_bytes_inp'" :=(
  transcript_t × seq uint8 × seq uint8 : choice_type) (in custom pack_type at level 2).
Notation "'challenge_bytes_out'" :=((transcript_t '× seq uint8
  ) : choice_type) (in custom pack_type at level 2).
Definition CHALLENGE_BYTES : nat :=
  1178.
Program Definition challenge_bytes (transcript_1176 : transcript_t) (
    label_1177 : seq uint8) (dest_1174 : seq uint8)
  : both (fset.fset0) [interface] ((transcript_t '× seq uint8)) :=
  ((letb data_len_1175 : seq uint8 :=
        encode_usize_as_u32 (seq_len (lift_to_both0 dest_1174)) in
      letbm transcript_1176 loc( transcript_1176_loc ) :=
        meta_ad (lift_to_both0 transcript_1176) (lift_to_both0 label_1177) (
          lift_to_both0 ((false : bool_ChoiceEquality))) in
      letbm transcript_1176 loc( transcript_1176_loc ) :=
        meta_ad (lift_to_both0 transcript_1176) (lift_to_both0 data_len_1175) (
          lift_to_both0 ((true : bool_ChoiceEquality))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prf (
          lift_to_both0 transcript_1176) (lift_to_both0 dest_1174) (
          lift_to_both0 ((false : bool_ChoiceEquality))))
      ) : both (fset.fset0) [interface] ((transcript_t '× seq uint8))).
Fail Next Obligation.


Notation "'append_uint64_inp'" :=(
  transcript_t × seq uint8 × uint64 : choice_type) (in custom pack_type at level 2).
Notation "'append_uint64_out'" :=(
  transcript_t : choice_type) (in custom pack_type at level 2).
Definition APPEND_U64 : nat :=
  1182.
Program Definition append_uint64 (transcript_1179 : transcript_t) (
    label_1180 : seq uint8) (x_1181 : uint64)
  : both (fset.fset0) [interface] (transcript_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (append_message (
          lift_to_both0 transcript_1179) (lift_to_both0 label_1180) (
          encode_uint64 (lift_to_both0 x_1181)))
      ) : both (fset.fset0) [interface] (transcript_t)).
Fail Next Obligation.

