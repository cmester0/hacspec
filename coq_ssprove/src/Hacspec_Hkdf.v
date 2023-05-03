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
Require Import Hacspec_Hmac.



Require Import Hacspec_Sha256.

Definition hash_len_v : uint_size :=
  ((usize 256) ./ (usize 8)).

Definition hkdf_error_t : ChoiceEquality :=
  unit_ChoiceEquality.
Definition InvalidOutputLength : hkdf_error_t :=
   tt.

Notation "'hkdf_byte_seq_result_t'" := ((
  result hkdf_error_t byte_seq)) : hacspec_scope.

Definition salt_or_zero_711_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 712%nat).
Notation "'extract_inp'" :=(
  byte_seq × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'extract_out'" :=(
  prk_t : choice_type) (in custom pack_type at level 2).
Definition EXTRACT : nat :=
  715.
Program Definition extract (salt_713 : byte_seq) (ikm_714 : byte_seq)
  : both (CEfset ([salt_or_zero_711_loc])) [interface] (prk_t) :=
  ((letbm salt_or_zero_711 : seq uint8 loc( salt_or_zero_711_loc ) :=
        seq_new_ (default : uint8) (lift_to_both0 hash_len_v) in
      letb '(salt_or_zero_711) :=
        if (seq_len (lift_to_both0 salt_713)) >.? (lift_to_both0 (
            usize 0)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([salt_or_zero_711_loc])) (L2 := CEfset (
            [salt_or_zero_711_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm salt_or_zero_711 loc( salt_or_zero_711_loc ) :=
            seq_from_seq (lift_to_both0 salt_713) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 salt_or_zero_711)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 salt_or_zero_711)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (_) (
          array_to_seq (hmac (lift_to_both0 salt_or_zero_711) (
            lift_to_both0 ikm_714))))
      ) : both (CEfset ([salt_or_zero_711_loc])) [interface] (prk_t)).
Fail Next Obligation.

Definition out_716_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 717%nat).
Notation "'build_hmac_txt_inp'" :=(
  byte_seq × byte_seq × uint8 : choice_type) (in custom pack_type at level 2).
Notation "'build_hmac_txt_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition BUILD_HMAC_TXT : nat :=
  721.
Program Definition build_hmac_txt (t_718 : byte_seq) (info_719 : byte_seq) (
    iteration_720 : uint8)
  : both (CEfset ([out_716_loc])) [interface] (byte_seq) :=
  ((letbm out_716 : seq uint8 loc( out_716_loc ) :=
        seq_new_ (default : uint8) (((seq_len (lift_to_both0 t_718)) .+ (
              seq_len (lift_to_both0 info_719))) .+ (lift_to_both0 (
              usize 1))) in
      letbm out_716 loc( out_716_loc ) :=
        seq_update (lift_to_both0 out_716) (lift_to_both0 (usize 0)) (
          lift_to_both0 t_718) in
      letbm out_716 loc( out_716_loc ) :=
        seq_update (lift_to_both0 out_716) (seq_len (lift_to_both0 t_718)) (
          lift_to_both0 info_719) in
      letb out_716 : seq uint8 :=
        seq_upd out_716 ((seq_len (lift_to_both0 t_718)) .+ (seq_len (
              lift_to_both0 info_719))) (is_pure (
            lift_to_both0 iteration_720)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 out_716)
      ) : both (CEfset ([out_716_loc])) [interface] (byte_seq)).
Fail Next Obligation.

Definition q_722_loc : ChoiceEqualityLocation :=
  (uint_size ; 723%nat).
Notation "'div_ceil_inp'" :=(
  uint_size × uint_size : choice_type) (in custom pack_type at level 2).
Notation "'div_ceil_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Definition DIV_CEIL : nat :=
  726.
Program Definition div_ceil (a_724 : uint_size) (b_725 : uint_size)
  : both (CEfset ([q_722_loc])) [interface] (uint_size) :=
  ((letbm q_722 : uint_size loc( q_722_loc ) :=
        (lift_to_both0 a_724) ./ (lift_to_both0 b_725) in
      letb '(q_722) :=
        if ((lift_to_both0 a_724) .% (lift_to_both0 b_725)) !=.? (
          lift_to_both0 (usize 0)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([q_722_loc])) (L2 := CEfset (
            [q_722_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm q_722 loc( q_722_loc ) :=
            (lift_to_both0 q_722) .+ (lift_to_both0 (usize 1)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 q_722)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 q_722)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 q_722)
      ) : both (CEfset ([q_722_loc])) [interface] (uint_size)).
Fail Next Obligation.


Notation "'check_output_limit_inp'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'check_output_limit_out'" :=((result (hkdf_error_t) (
      uint_size)) : choice_type) (in custom pack_type at level 2).
Definition CHECK_OUTPUT_LIMIT : nat :=
  729.
Program Definition check_output_limit (l_727 : uint_size)
  : both (CEfset ([q_722_loc])) [interface] ((result (hkdf_error_t) (
        uint_size))) :=
  ((letb n_728 : uint_size :=
        div_ceil (lift_to_both0 l_727) (lift_to_both0 hash_len_v) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 n_728) <=.? (
            lift_to_both0 (usize 255)))
        then @Ok uint_size hkdf_error_t (lift_to_both0 n_728)
        else @Err uint_size hkdf_error_t (InvalidOutputLength))
      ) : both (CEfset ([q_722_loc])) [interface] ((result (hkdf_error_t) (
          uint_size)))).
Fail Next Obligation.

Definition t_731_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 732%nat).
Definition t_i_730_loc : ChoiceEqualityLocation :=
  (prk_t ; 733%nat).
Notation "'expand_inp'" :=(
  byte_seq × byte_seq × uint_size : choice_type) (in custom pack_type at level 2).
Notation "'expand_out'" :=(
  hkdf_byte_seq_result_t : choice_type) (in custom pack_type at level 2).
Definition EXPAND : nat :=
  740.
Program Definition expand (prk_739 : byte_seq) (info_737 : byte_seq) (
    l_734 : uint_size)
  : both (CEfset (
      [out_716_loc ; q_722_loc ; t_i_730_loc ; t_731_loc])) [interface] (
    hkdf_byte_seq_result_t) :=
  ((letbnd(_) n_735 : uint_size := check_output_limit (lift_to_both0 l_734) in
      letbm t_i_730 : prk_t loc( t_i_730_loc ) :=
        array_new_ (default : uint8) (_) in
      letbm t_731 : seq uint8 loc( t_731_loc ) :=
        seq_new_ (default : uint8) ((lift_to_both0 n_735) .* (
            lift_to_both0 hash_size_v)) in
      letb '(t_i_730, t_731) :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 n_735) prod_ce(
            t_i_730,
            t_731
          ) (L := (CEfset (
                [out_716_loc ; q_722_loc ; t_i_730_loc ; t_731_loc]))) (
            I := [interface]) (fun i_736 '(t_i_730, t_731) =>
            letb hmac_txt_in_738 : seq uint8 :=
              if is_pure (I := [interface]) ((lift_to_both0 i_736) =.? (
                  lift_to_both0 (usize 0)))
              then build_hmac_txt (seq_new_ (default : uint8) (lift_to_both0 (
                    usize 0))) (lift_to_both0 info_737) (secret ((pub_u8 (
                      is_pure (lift_to_both0 i_736))) .+ (lift_to_both0 (
                      @repr U8 1))))
              else build_hmac_txt (seq_from_seq (
                  array_to_seq (lift_to_both0 t_i_730))) (
                lift_to_both0 info_737) (secret ((pub_u8 (is_pure (
                        lift_to_both0 i_736))) .+ (lift_to_both0 (
                      @repr U8 1)))) in
            letbm t_i_730 loc( t_i_730_loc ) :=
              hmac (lift_to_both0 prk_739) (lift_to_both0 hmac_txt_in_738) in
            letbm t_731 loc( t_731_loc ) :=
              seq_update (lift_to_both0 t_731) ((lift_to_both0 i_736) .* (
                  array_len (lift_to_both0 t_i_730))) (
                array_to_seq (lift_to_both0 t_i_730)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 t_i_730,
                lift_to_both0 t_731
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok byte_seq hkdf_error_t (seq_slice (lift_to_both0 t_731) (
            lift_to_both0 (usize 0)) (lift_to_both0 l_734)))
      ) : both (CEfset (
        [out_716_loc ; q_722_loc ; t_i_730_loc ; t_731_loc])) [interface] (
      hkdf_byte_seq_result_t)).
Fail Next Obligation.

