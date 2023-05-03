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


Require Import Hacspec_Sha256.

Definition block_len_v : uint_size :=
  k_size_v.

Definition prk_t := nseq (uint8) (hash_size_v).

Definition block_t := nseq (uint8) (block_len_v).

Definition i_pad_v : block_t :=
  @array_from_list uint8 [
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8;
    (secret (@repr U8 54)) : uint8
  ].

Definition o_pad_v : block_t :=
  @array_from_list uint8 [
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 92)) : uint8
  ].


Notation "'k_block_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'k_block_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Definition K_BLOCK : nat :=
  742.
Program Definition k_block (k_741 : byte_seq)
  : both (fset.fset0) [interface] (block_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((seq_len (lift_to_both0 k_741)) >.? (
            lift_to_both0 block_len_v))
        then array_update_start (array_new_ (default : uint8) (block_len_v)) (
          array_to_seq (hash (lift_to_both0 k_741)))
        else array_update_start (array_new_ (default : uint8) (block_len_v)) (
          lift_to_both0 k_741))
      ) : both (fset.fset0) [interface] (block_t)).
Fail Next Obligation.

Definition h_in_743_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 745%nat).
Definition h_in_744_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 746%nat).
Notation "'hmac_inp'" :=(
  byte_seq × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'hmac_out'" :=(prk_t : choice_type) (in custom pack_type at level 2).
Definition HMAC : nat :=
  751.
Program Definition hmac (k_747 : byte_seq) (txt_749 : byte_seq)
  : both (CEfset ([h_in_743_loc ; h_in_744_loc])) [interface] (prk_t) :=
  ((letb k_block_748 : block_t := k_block (lift_to_both0 k_747) in
      letbm h_in_743 : seq uint8 loc( h_in_743_loc ) :=
        seq_from_seq (array_to_seq ((lift_to_both0 k_block_748) array_xor (
            lift_to_both0 i_pad_v))) in
      letbm h_in_743 loc( h_in_743_loc ) :=
        seq_concat (lift_to_both0 h_in_743) (lift_to_both0 txt_749) in
      letb h_inner_750 : sha256_digest_t := hash (lift_to_both0 h_in_743) in
      letbm h_in_744 : seq uint8 loc( h_in_744_loc ) :=
        seq_from_seq (array_to_seq ((lift_to_both0 k_block_748) array_xor (
            lift_to_both0 o_pad_v))) in
      letbm h_in_744 loc( h_in_744_loc ) :=
        seq_concat (lift_to_both0 h_in_744) (
          array_to_seq (lift_to_both0 h_inner_750)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (
          hash_size_v) (array_to_seq (hash (lift_to_both0 h_in_744))))
      ) : both (CEfset ([h_in_743_loc ; h_in_744_loc])) [interface] (prk_t)).
Fail Next Obligation.

