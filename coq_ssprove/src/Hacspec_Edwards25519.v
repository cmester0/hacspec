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


Require Import Hacspec_Sha512.

Definition field_canvas_t := nseq (int8) (usize 32).
Definition ed25519_field_element_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition scalar_canvas_t := nseq (int8) (usize 32).
Definition scalar_t :=
  nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed.

Definition big_scalar_canvas_t := nseq (int8) (usize 64).
Definition big_scalar_t :=
  nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed.

Definition big_integer_canvas_t := nseq (int8) (usize 32).
Definition big_integer_t :=
  nat_mod 0x8000000000000000000000000000000080000000000000000000000000000000.

Notation "'ed_point_t'" := ((
  ed25519_field_element_t ×
  ed25519_field_element_t ×
  ed25519_field_element_t ×
  ed25519_field_element_t
)) : hacspec_scope.

Definition compressed_ed_point_t := nseq (uint8) (usize 32).

Definition serialized_scalar_t := nseq (uint8) (usize 32).

Definition signature_t := nseq (uint8) (usize 64).

Notation "'public_key_t'" := (compressed_ed_point_t) : hacspec_scope.

Notation "'secret_key_t'" := (serialized_scalar_t) : hacspec_scope.

Definition error_t : ChoiceEquality :=
  unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality '+ unit_ChoiceEquality.
Definition InvalidPublickey : error_t :=
  inl (inl (inl (inl (inl tt)))).
Definition InvalidSignature : error_t :=
  inl (inl (inl (inl (inr tt)))).
Definition InvalidS : error_t :=
  inl (inl (inl (inr tt))).
Definition InvalidR : error_t :=
  inl (inl (inr tt)).
Definition SmallOrderPoint : error_t :=
  inl (inr tt).
Definition NotEnoughRandomness : error_t :=
  inr tt.

Notation "'verify_result_t'" := ((result error_t unit)) : hacspec_scope.

Definition base_v : compressed_ed_point_t :=
  @array_from_list uint8 [
    (secret (@repr U8 88)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8;
    (secret (@repr U8 102)) : uint8
  ].

Definition constant_p_v : serialized_scalar_t :=
  @array_from_list uint8 [
    (secret (@repr U8 237)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 127)) : uint8
  ].

Definition constant_l_v : serialized_scalar_t :=
  @array_from_list uint8 [
    (secret (@repr U8 237)) : uint8;
    (secret (@repr U8 211)) : uint8;
    (secret (@repr U8 245)) : uint8;
    (secret (@repr U8 92)) : uint8;
    (secret (@repr U8 26)) : uint8;
    (secret (@repr U8 99)) : uint8;
    (secret (@repr U8 18)) : uint8;
    (secret (@repr U8 88)) : uint8;
    (secret (@repr U8 214)) : uint8;
    (secret (@repr U8 156)) : uint8;
    (secret (@repr U8 247)) : uint8;
    (secret (@repr U8 162)) : uint8;
    (secret (@repr U8 222)) : uint8;
    (secret (@repr U8 249)) : uint8;
    (secret (@repr U8 222)) : uint8;
    (secret (@repr U8 20)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 16)) : uint8
  ].

Definition constant_p3_8_v : serialized_scalar_t :=
  @array_from_list uint8 [
    (secret (@repr U8 254)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 15)) : uint8
  ].

Definition constant_p1_4_v : serialized_scalar_t :=
  @array_from_list uint8 [
    (secret (@repr U8 251)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 255)) : uint8;
    (secret (@repr U8 31)) : uint8
  ].

Definition constant_d_v : serialized_scalar_t :=
  @array_from_list uint8 [
    (secret (@repr U8 163)) : uint8;
    (secret (@repr U8 120)) : uint8;
    (secret (@repr U8 89)) : uint8;
    (secret (@repr U8 19)) : uint8;
    (secret (@repr U8 202)) : uint8;
    (secret (@repr U8 77)) : uint8;
    (secret (@repr U8 235)) : uint8;
    (secret (@repr U8 117)) : uint8;
    (secret (@repr U8 171)) : uint8;
    (secret (@repr U8 216)) : uint8;
    (secret (@repr U8 65)) : uint8;
    (secret (@repr U8 65)) : uint8;
    (secret (@repr U8 77)) : uint8;
    (secret (@repr U8 10)) : uint8;
    (secret (@repr U8 112)) : uint8;
    (secret (@repr U8 0)) : uint8;
    (secret (@repr U8 152)) : uint8;
    (secret (@repr U8 232)) : uint8;
    (secret (@repr U8 121)) : uint8;
    (secret (@repr U8 119)) : uint8;
    (secret (@repr U8 121)) : uint8;
    (secret (@repr U8 64)) : uint8;
    (secret (@repr U8 199)) : uint8;
    (secret (@repr U8 140)) : uint8;
    (secret (@repr U8 115)) : uint8;
    (secret (@repr U8 254)) : uint8;
    (secret (@repr U8 111)) : uint8;
    (secret (@repr U8 43)) : uint8;
    (secret (@repr U8 238)) : uint8;
    (secret (@repr U8 108)) : uint8;
    (secret (@repr U8 3)) : uint8;
    (secret (@repr U8 82)) : uint8
  ].


Notation "'is_negative_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'is_negative_out'" :=(
  uint8 : choice_type) (in custom pack_type at level 2).
Definition IS_NEGATIVE : nat :=
  2632.
Program Definition is_negative (x_2631 : ed25519_field_element_t)
  : both (fset.fset0) [interface] (uint8) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (nat_mod_bit (lift_to_both0 x_2631) (
            lift_to_both0 (usize 0)))
        then secret (lift_to_both0 (@repr U8 1))
        else secret (lift_to_both0 (@repr U8 0)))
      ) : both (fset.fset0) [interface] (uint8)).
Fail Next Obligation.

Definition s_2633_loc : ChoiceEqualityLocation :=
  (byte_seq ; 2634%nat).
Notation "'compress_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_out'" :=(
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Definition COMPRESS : nat :=
  2642.
Program Definition compress (p_2635 : ed_point_t)
  : both (CEfset ([s_2633_loc])) [interface] (compressed_ed_point_t) :=
  ((letb '(x_2636, y_2637, z_2638, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 p_2635 in
      letb z_inv_2639 : ed25519_field_element_t :=
        nat_mod_inv (lift_to_both0 z_2638) in
      letb x_2640 : ed25519_field_element_t :=
        (lift_to_both0 x_2636) *% (lift_to_both0 z_inv_2639) in
      letb y_2641 : ed25519_field_element_t :=
        (lift_to_both0 y_2637) *% (lift_to_both0 z_inv_2639) in
      letbm s_2633 : byte_seq loc( s_2633_loc ) :=
        nat_mod_to_byte_seq_le (lift_to_both0 y_2641) in
      letb s_2633 : seq uint8 :=
        seq_upd s_2633 (lift_to_both0 (usize 31)) (is_pure ((seq_index (
                s_2633) (lift_to_both0 (usize 31))) .^ ((is_negative (
                  lift_to_both0 x_2640)) shift_left (lift_to_both0 (
                  usize 7))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_slice (
          default : uint8) (32) (lift_to_both0 s_2633) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 32)))
      ) : both (CEfset ([s_2633_loc])) [interface] (compressed_ed_point_t)).
Fail Next Obligation.

Definition result_2643_loc : ChoiceEqualityLocation :=
  ((option (ed25519_field_element_t)) ; 2644%nat).
Notation "'sqrt_inp'" :=(
  ed25519_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'sqrt_out'" :=((option (
      ed25519_field_element_t)) : choice_type) (in custom pack_type at level 2).
Definition SQRT : nat :=
  2650.
Program Definition sqrt (a_2647 : ed25519_field_element_t)
  : both (CEfset ([result_2643_loc])) [interface] ((option (
        ed25519_field_element_t))) :=
  ((letb p3_8_2645 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (
          array_to_seq (lift_to_both0 constant_p3_8_v)) in
      letb p1_4_2646 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (
          array_to_seq (lift_to_both0 constant_p1_4_v)) in
      letb x_c_2648 : ed25519_field_element_t :=
        nat_mod_pow_self (lift_to_both0 a_2647) (lift_to_both0 p3_8_2645) in
      letbm result_2643 : (option (
            ed25519_field_element_t)) loc( result_2643_loc ) :=
        @None ed25519_field_element_t in
      letb '(result_2643) :=
        if ((lift_to_both0 x_c_2648) *% (lift_to_both0 x_c_2648)) =.? (
          lift_to_both0 a_2647) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([result_2643_loc])) (L2 := CEfset (
            [result_2643_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm result_2643 loc( result_2643_loc ) :=
            some (lift_to_both0 x_c_2648) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_2643)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_2643)
         in
      letb '(result_2643) :=
        if ((lift_to_both0 x_c_2648) *% (lift_to_both0 x_c_2648)) =.? ((
            nat_mod_zero ) -% (lift_to_both0 a_2647)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([result_2643_loc])) (L2 := CEfset (
            [result_2643_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb x_2649 : ed25519_field_element_t :=
            (nat_mod_pow_self (nat_mod_two ) (lift_to_both0 p1_4_2646)) *% (
              lift_to_both0 x_c_2648) in
          letbm result_2643 loc( result_2643_loc ) :=
            some (lift_to_both0 x_2649) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_2643)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_2643)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 result_2643)
      ) : both (CEfset ([result_2643_loc])) [interface] ((option (
          ed25519_field_element_t)))).
Fail Next Obligation.


Notation "'check_canonical_point_inp'" :=(
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'check_canonical_point_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition CHECK_CANONICAL_POINT : nat :=
  2653.
Program Definition check_canonical_point (x_2651 : compressed_ed_point_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb x_2651 : compressed_ed_point_t :=
        array_upd x_2651 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                x_2651) (lift_to_both0 (usize 31))) .& (secret (lift_to_both0 (
                  @repr U8 127))))) in
      letb x_2652 : big_integer_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 x_2651)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 x_2652) <.? (nat_mod_from_byte_seq_le (
            array_to_seq (lift_to_both0 constant_p_v))))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.

Definition y_s_2654_loc : ChoiceEqualityLocation :=
  (compressed_ed_point_t ; 2656%nat).
Definition x_2655_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 2657%nat).
Notation "'decompress_inp'" :=(
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'decompress_out'" :=((option (
      ed_point_t)) : choice_type) (in custom pack_type at level 2).
Definition DECOMPRESS : nat :=
  2668.
Program Definition decompress (q_2659 : compressed_ed_point_t)
  : both (CEfset ([result_2643_loc ; y_s_2654_loc ; x_2655_loc])) [interface] ((
      option (ed_point_t))) :=
  ((letb d_2658 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 constant_d_v)) in
      letb x_s_2660 : uint8 :=
        ((array_index (q_2659) (lift_to_both0 (usize 31))) .& (secret (
              lift_to_both0 (@repr U8 128)))) shift_right (lift_to_both0 (
            usize 7)) in
      letbm y_s_2654 : compressed_ed_point_t loc( y_s_2654_loc ) :=
        lift_to_both0 q_2659 in
      letb y_s_2654 : compressed_ed_point_t :=
        array_upd y_s_2654 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                y_s_2654) (lift_to_both0 (usize 31))) .& (secret (
                lift_to_both0 (@repr U8 127))))) in
      letbnd(ChoiceEqualityMonad.option_bind_both) 'tt :=
        if negb (check_canonical_point (
            lift_to_both0 y_s_2654)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([y_s_2654_loc])) (L2 := CEfset (
            [result_2643_loc ; y_s_2654_loc ; x_2655_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : ed_point_t :=
            @None ed_point_t in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Some unit_ChoiceEquality (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Some unit_ChoiceEquality (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letb y_2661 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 y_s_2654)) in
      letb z_2662 : ed25519_field_element_t := nat_mod_one  in
      letb yy_2663 : ed25519_field_element_t :=
        (lift_to_both0 y_2661) *% (lift_to_both0 y_2661) in
      letb u_2664 : ed25519_field_element_t :=
        (lift_to_both0 yy_2663) -% (lift_to_both0 z_2662) in
      letb v_2665 : ed25519_field_element_t :=
        ((lift_to_both0 d_2658) *% (lift_to_both0 yy_2663)) +% (
          lift_to_both0 z_2662) in
      letb xx_2666 : ed25519_field_element_t :=
        (lift_to_both0 u_2664) *% (nat_mod_inv (lift_to_both0 v_2665)) in
      letbndm(_) x_2655 : ed25519_field_element_t :=
        sqrt (lift_to_both0 xx_2666) in
      letb x_r_2667 : uint8 := is_negative (lift_to_both0 x_2655) in
      letbnd(ChoiceEqualityMonad.option_bind_both) 'tt :=
        if ((lift_to_both0 x_2655) =.? (nat_mod_zero )) && ((uint8_declassify (
              lift_to_both0 x_s_2660)) =.? (lift_to_both0 (
              @repr U8 1))) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [result_2643_loc ; y_s_2654_loc ; x_2655_loc])) (L2 := CEfset (
            [result_2643_loc ; y_s_2654_loc ; x_2655_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letbnd(
              _) _ : ed_point_t :=
            @None ed_point_t in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            @Some unit_ChoiceEquality (lift_to_both0 (
                (tt : unit_ChoiceEquality))))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          @Some unit_ChoiceEquality (lift_to_both0 (
              (tt : unit_ChoiceEquality))))
         in
      letb '(x_2655) :=
        if (uint8_declassify (lift_to_both0 x_r_2667)) !=.? (uint8_declassify (
            lift_to_both0 x_s_2660)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [result_2643_loc ; y_s_2654_loc ; x_2655_loc])) (L2 := CEfset (
            [result_2643_loc ; y_s_2654_loc ; x_2655_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x_2655 loc( x_2655_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 x_2655) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x_2655)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 x_2655)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (some (prod_b(
            lift_to_both0 x_2655,
            lift_to_both0 y_2661,
            lift_to_both0 z_2662,
            (lift_to_both0 x_2655) *% (lift_to_both0 y_2661)
          )))
      ) : both (CEfset (
        [result_2643_loc ; y_s_2654_loc ; x_2655_loc])) [interface] ((option (
          ed_point_t)))).
Fail Next Obligation.

Definition y_s_2669_loc : ChoiceEqualityLocation :=
  (compressed_ed_point_t ; 2671%nat).
Definition x_2670_loc : ChoiceEqualityLocation :=
  (ed25519_field_element_t ; 2672%nat).
Notation "'decompress_non_canonical_inp'" :=(
  compressed_ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'decompress_non_canonical_out'" :=((option (
      ed_point_t)) : choice_type) (in custom pack_type at level 2).
Definition DECOMPRESS_NON_CANONICAL : nat :=
  2683.
Program Definition decompress_non_canonical (p_2674 : compressed_ed_point_t)
  : both (CEfset ([result_2643_loc ; y_s_2669_loc ; x_2670_loc])) [interface] ((
      option (ed_point_t))) :=
  ((letb d_2673 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 constant_d_v)) in
      letb x_s_2675 : uint8 :=
        ((array_index (p_2674) (lift_to_both0 (usize 31))) .& (secret (
              lift_to_both0 (@repr U8 128)))) shift_right (lift_to_both0 (
            usize 7)) in
      letbm y_s_2669 : compressed_ed_point_t loc( y_s_2669_loc ) :=
        lift_to_both0 p_2674 in
      letb y_s_2669 : compressed_ed_point_t :=
        array_upd y_s_2669 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                y_s_2669) (lift_to_both0 (usize 31))) .& (secret (
                lift_to_both0 (@repr U8 127))))) in
      letb y_2676 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 y_s_2669)) in
      letb z_2677 : ed25519_field_element_t := nat_mod_one  in
      letb yy_2678 : ed25519_field_element_t :=
        (lift_to_both0 y_2676) *% (lift_to_both0 y_2676) in
      letb u_2679 : ed25519_field_element_t :=
        (lift_to_both0 yy_2678) -% (lift_to_both0 z_2677) in
      letb v_2680 : ed25519_field_element_t :=
        ((lift_to_both0 d_2673) *% (lift_to_both0 yy_2678)) +% (
          lift_to_both0 z_2677) in
      letb xx_2681 : ed25519_field_element_t :=
        (lift_to_both0 u_2679) *% (nat_mod_inv (lift_to_both0 v_2680)) in
      letbndm(_) x_2670 : ed25519_field_element_t :=
        sqrt (lift_to_both0 xx_2681) in
      letb x_r_2682 : uint8 := is_negative (lift_to_both0 x_2670) in
      letb '(x_2670) :=
        if (uint8_declassify (lift_to_both0 x_r_2682)) !=.? (uint8_declassify (
            lift_to_both0 x_s_2675)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [result_2643_loc ; y_s_2669_loc ; x_2670_loc])) (L2 := CEfset (
            [result_2643_loc ; y_s_2669_loc ; x_2670_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm x_2670 loc( x_2670_loc ) :=
            (nat_mod_zero ) -% (lift_to_both0 x_2670) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 x_2670)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 x_2670)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (some (prod_b(
            lift_to_both0 x_2670,
            lift_to_both0 y_2676,
            lift_to_both0 z_2677,
            (lift_to_both0 x_2670) *% (lift_to_both0 y_2676)
          )))
      ) : both (CEfset (
        [result_2643_loc ; y_s_2669_loc ; x_2670_loc])) [interface] ((option (
          ed_point_t)))).
Fail Next Obligation.

Definition s_2684_loc : ChoiceEqualityLocation :=
  (byte_seq ; 2685%nat).
Notation "'encode_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition ENCODE : nat :=
  2693.
Program Definition encode (p_2686 : ed_point_t)
  : both (CEfset ([s_2684_loc])) [interface] (byte_seq) :=
  ((letb '(x_2687, y_2688, z_2689, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 p_2686 in
      letb z_inv_2690 : ed25519_field_element_t :=
        nat_mod_inv (lift_to_both0 z_2689) in
      letb x_2691 : ed25519_field_element_t :=
        (lift_to_both0 x_2687) *% (lift_to_both0 z_inv_2690) in
      letb y_2692 : ed25519_field_element_t :=
        (lift_to_both0 y_2688) *% (lift_to_both0 z_inv_2690) in
      letbm s_2684 : byte_seq loc( s_2684_loc ) :=
        nat_mod_to_byte_seq_le (lift_to_both0 y_2692) in
      letb s_2684 : seq uint8 :=
        seq_upd s_2684 (lift_to_both0 (usize 31)) (is_pure ((seq_index (
                s_2684) (lift_to_both0 (usize 31))) .^ ((is_negative (
                  lift_to_both0 x_2691)) shift_left (lift_to_both0 (
                  usize 7))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_2684)
      ) : both (CEfset ([s_2684_loc])) [interface] (byte_seq)).
Fail Next Obligation.


Notation "'decode_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'decode_out'" :=((option (
      ed_point_t)) : choice_type) (in custom pack_type at level 2).
Definition DECODE : nat :=
  2696.
Program Definition decode (q_s_2694 : byte_seq)
  : both (CEfset ([result_2643_loc ; y_s_2654_loc ; x_2655_loc])) [interface] ((
      option (ed_point_t))) :=
  ((letb q_2695 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (lift_to_both0 q_s_2694) (
          lift_to_both0 (usize 0)) (lift_to_both0 (usize 32)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (decompress (
          lift_to_both0 q_2695))
      ) : both (CEfset (
        [result_2643_loc ; y_s_2654_loc ; x_2655_loc])) [interface] ((option (
          ed_point_t)))).
Fail Next Obligation.


Notation "'point_add_inp'" :=(
  ed_point_t × ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition POINT_ADD : nat :=
  2721.
Program Definition point_add (p_2699 : ed_point_t) (q_2704 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb d_c_2697 : ed25519_field_element_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 constant_d_v)) in
      letb two_2698 : ed25519_field_element_t := nat_mod_two  in
      letb '(x1_2700, y1_2701, z1_2702, t1_2703) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 p_2699 in
      letb '(x2_2705, y2_2706, z2_2707, t2_2708) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 q_2704 in
      letb a_2709 : ed25519_field_element_t :=
        ((lift_to_both0 y1_2701) -% (lift_to_both0 x1_2700)) *% ((
            lift_to_both0 y2_2706) -% (lift_to_both0 x2_2705)) in
      letb b_2710 : ed25519_field_element_t :=
        ((lift_to_both0 y1_2701) +% (lift_to_both0 x1_2700)) *% ((
            lift_to_both0 y2_2706) +% (lift_to_both0 x2_2705)) in
      letb c_2711 : ed25519_field_element_t :=
        (((lift_to_both0 t1_2703) *% (lift_to_both0 two_2698)) *% (
            lift_to_both0 d_c_2697)) *% (lift_to_both0 t2_2708) in
      letb d_2712 : ed25519_field_element_t :=
        ((lift_to_both0 z1_2702) *% (lift_to_both0 two_2698)) *% (
          lift_to_both0 z2_2707) in
      letb e_2713 : ed25519_field_element_t :=
        (lift_to_both0 b_2710) -% (lift_to_both0 a_2709) in
      letb f_2714 : ed25519_field_element_t :=
        (lift_to_both0 d_2712) -% (lift_to_both0 c_2711) in
      letb g_2715 : ed25519_field_element_t :=
        (lift_to_both0 d_2712) +% (lift_to_both0 c_2711) in
      letb h_2716 : ed25519_field_element_t :=
        (lift_to_both0 b_2710) +% (lift_to_both0 a_2709) in
      letb x3_2717 : ed25519_field_element_t :=
        (lift_to_both0 e_2713) *% (lift_to_both0 f_2714) in
      letb y3_2718 : ed25519_field_element_t :=
        (lift_to_both0 g_2715) *% (lift_to_both0 h_2716) in
      letb t3_2719 : ed25519_field_element_t :=
        (lift_to_both0 e_2713) *% (lift_to_both0 h_2716) in
      letb z3_2720 : ed25519_field_element_t :=
        (lift_to_both0 f_2714) *% (lift_to_both0 g_2715) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x3_2717,
          lift_to_both0 y3_2718,
          lift_to_both0 z3_2720,
          lift_to_both0 t3_2719
        ))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.


Notation "'point_identity_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'point_identity_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition POINT_IDENTITY : nat :=
  2722.
Program Definition point_identity 
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          nat_mod_zero ,
          nat_mod_one ,
          nat_mod_one ,
          nat_mod_zero 
        ))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.

Definition p_2723_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2725%nat).
Definition q_2724_loc : ChoiceEqualityLocation :=
  ((
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) ; 2726%nat).
Notation "'point_mul_inp'" :=(
  scalar_t × ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition POINT_MUL : nat :=
  2730.
Program Definition point_mul (s_2729 : scalar_t) (p_2727 : ed_point_t)
  : both (CEfset ([p_2723_loc ; q_2724_loc])) [interface] (ed_point_t) :=
  ((letbm p_2723 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( p_2723_loc ) :=
        lift_to_both0 p_2727 in
      letbm q_2724 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) loc( q_2724_loc ) :=
        point_identity  in
      letb '(p_2723, q_2724) :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 256)) prod_ce(p_2723, q_2724) (L := (CEfset (
                [p_2723_loc ; q_2724_loc]))) (I := [interface]) (fun i_2728 '(
              p_2723,
              q_2724
            ) =>
            letb '(q_2724) :=
              if nat_mod_bit (lift_to_both0 s_2729) (
                lift_to_both0 i_2728) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([p_2723_loc ; q_2724_loc])) (
                L2 := CEfset ([p_2723_loc ; q_2724_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm q_2724 loc( q_2724_loc ) :=
                  point_add (lift_to_both0 q_2724) (lift_to_both0 p_2723) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 q_2724)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 q_2724)
               in
            letbm p_2723 loc( p_2723_loc ) :=
              point_add (lift_to_both0 p_2723) (lift_to_both0 p_2723) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 p_2723,
                lift_to_both0 q_2724
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 q_2724)
      ) : both (CEfset ([p_2723_loc ; q_2724_loc])) [interface] (ed_point_t)).
Fail Next Obligation.


Notation "'point_mul_by_cofactor_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_mul_by_cofactor_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition POINT_MUL_BY_COFACTOR : nat :=
  2735.
Program Definition point_mul_by_cofactor (p_2731 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb p2_2732 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_add (lift_to_both0 p_2731) (lift_to_both0 p_2731) in
      letb p4_2733 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_add (lift_to_both0 p2_2732) (lift_to_both0 p2_2732) in
      letb p8_2734 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_add (lift_to_both0 p4_2733) (lift_to_both0 p4_2733) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 p8_2734)
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.


Notation "'point_neg_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_neg_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition POINT_NEG : nat :=
  2741.
Program Definition point_neg (p_2736 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb '(x_2737, y_2738, z_2739, t_2740) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 p_2736 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          (nat_mod_zero ) -% (lift_to_both0 x_2737),
          lift_to_both0 y_2738,
          lift_to_both0 z_2739,
          (nat_mod_zero ) -% (lift_to_both0 t_2740)
        ))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.


Notation "'point_eq_inp'" :=(
  ed_point_t × ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_eq_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition POINT_EQ : nat :=
  2750.
Program Definition point_eq (p_2742 : ed_point_t) (q_2746 : ed_point_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb '(x1_2743, y1_2744, z1_2745, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 p_2742 in
      letb '(x2_2747, y2_2748, z2_2749, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 q_2746 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((((
              lift_to_both0 x1_2743) *% (lift_to_both0 z2_2749)) =.? ((
              lift_to_both0 x2_2747) *% (lift_to_both0 z1_2745))) && (((
              lift_to_both0 y1_2744) *% (lift_to_both0 z2_2749)) =.? ((
              lift_to_both0 y2_2748) *% (lift_to_both0 z1_2745))))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'point_normalize_inp'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Notation "'point_normalize_out'" :=(
  ed_point_t : choice_type) (in custom pack_type at level 2).
Definition POINT_NORMALIZE : nat :=
  2759.
Program Definition point_normalize (q_2751 : ed_point_t)
  : both (fset.fset0) [interface] (ed_point_t) :=
  ((letb '(qx_2752, qy_2753, qz_2754, _) : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        lift_to_both0 q_2751 in
      letb px_2755 : ed25519_field_element_t :=
        (lift_to_both0 qx_2752) *% (nat_mod_inv (lift_to_both0 qz_2754)) in
      letb py_2756 : ed25519_field_element_t :=
        (lift_to_both0 qy_2753) *% (nat_mod_inv (lift_to_both0 qz_2754)) in
      letb pz_2757 : ed25519_field_element_t := nat_mod_one  in
      letb pt_2758 : ed25519_field_element_t :=
        (lift_to_both0 px_2755) *% (lift_to_both0 py_2756) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 px_2755,
          lift_to_both0 py_2756,
          lift_to_both0 pz_2757,
          lift_to_both0 pt_2758
        ))
      ) : both (fset.fset0) [interface] (ed_point_t)).
Fail Next Obligation.

Definition s_2760_loc : ChoiceEqualityLocation :=
  (serialized_scalar_t ; 2761%nat).
Notation "'secret_expand_inp'" :=(
  secret_key_t : choice_type) (in custom pack_type at level 2).
Notation "'secret_expand_out'" :=((serialized_scalar_t '× serialized_scalar_t
  ) : choice_type) (in custom pack_type at level 2).
Definition SECRET_EXPAND : nat :=
  2765.
Program Definition secret_expand (sk_2762 : secret_key_t)
  : both (CEfset ([s_2760_loc])) [interface] ((
      serialized_scalar_t '×
      serialized_scalar_t
    )) :=
  ((letb h_2763 : sha512_digest_t :=
        sha512 (seq_from_slice (lift_to_both0 sk_2762) (lift_to_both0 (
              usize 0)) (lift_to_both0 (usize 32))) in
      letb h_d_2764 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 h_2763)) (lift_to_both0 (usize 32)) (
          lift_to_both0 (usize 32)) in
      letbm s_2760 : serialized_scalar_t loc( s_2760_loc ) :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (lift_to_both0 h_2763)) (lift_to_both0 (usize 0)) (
          lift_to_both0 (usize 32)) in
      letb s_2760 : serialized_scalar_t :=
        array_upd s_2760 (lift_to_both0 (usize 0)) (is_pure ((array_index (
                s_2760) (lift_to_both0 (usize 0))) .& (secret (lift_to_both0 (
                  @repr U8 248))))) in
      letb s_2760 : serialized_scalar_t :=
        array_upd s_2760 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                s_2760) (lift_to_both0 (usize 31))) .& (secret (lift_to_both0 (
                  @repr U8 127))))) in
      letb s_2760 : serialized_scalar_t :=
        array_upd s_2760 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                s_2760) (lift_to_both0 (usize 31))) .| (secret (lift_to_both0 (
                  @repr U8 64))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 s_2760,
          lift_to_both0 h_d_2764
        ))
      ) : both (CEfset ([s_2760_loc])) [interface] ((
        serialized_scalar_t '×
        serialized_scalar_t
      ))).
Fail Next Obligation.


Notation "'secret_to_public_inp'" :=(
  secret_key_t : choice_type) (in custom pack_type at level 2).
Notation "'secret_to_public_out'" :=(
  public_key_t : choice_type) (in custom pack_type at level 2).
Definition SECRET_TO_PUBLIC : nat :=
  2771.
Program Definition secret_to_public (sk_2766 : secret_key_t)
  : both (CEfset (
      [s_2633_loc ; result_2643_loc ; y_s_2654_loc ; x_2655_loc ; p_2723_loc ; q_2724_loc ; s_2760_loc])) [interface] (
    public_key_t) :=
  ((letb '(s_2767, _) : (serialized_scalar_t '× serialized_scalar_t) :=
        secret_expand (lift_to_both0 sk_2766) in
      letb base_2768 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        option_unwrap (decompress (lift_to_both0 base_v)) in
      letb ss_2769 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 s_2767)) in
      letb a_2770 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (lift_to_both0 ss_2769) (lift_to_both0 base_2768) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (compress (
          lift_to_both0 a_2770))
      ) : both (CEfset (
        [s_2633_loc ; result_2643_loc ; y_s_2654_loc ; x_2655_loc ; p_2723_loc ; q_2724_loc ; s_2760_loc])) [interface] (
      public_key_t)).
Fail Next Obligation.


Notation "'check_canonical_scalar_inp'" :=(
  serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'check_canonical_scalar_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition CHECK_CANONICAL_SCALAR : nat :=
  2773.
Program Definition check_canonical_scalar (s_2772 : serialized_scalar_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((uint8_declassify ((array_index (
                  s_2772) (lift_to_both0 (usize 31))) .& (secret (
                  lift_to_both0 (@repr U8 224))))) !=.? (lift_to_both0 (
              @repr U8 0)))
        then lift_to_both0 ((false : bool_ChoiceEquality))
        else (nat_mod_from_byte_seq_le (
            array_to_seq (lift_to_both0 s_2772))) <.? (
          nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 constant_l_v))))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.

