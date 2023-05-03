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


Definition field_canvas_t := nseq (int8) (usize 32).
Definition x25519_field_element_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition scalar_canvas_t := nseq (int8) (usize 32).
Definition scalar_t :=
  nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000.

Notation "'point_t'" := ((x25519_field_element_t × x25519_field_element_t
)) : hacspec_scope.

Definition x25519_serialized_point_t := nseq (uint8) (usize 32).

Definition x25519_serialized_scalar_t := nseq (uint8) (usize 32).

Definition k_423_loc : ChoiceEqualityLocation :=
  (x25519_serialized_scalar_t ; 424%nat).
Notation "'mask_scalar_inp'" :=(
  x25519_serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'mask_scalar_out'" :=(
  x25519_serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Definition MASK_SCALAR : nat :=
  426.
Program Definition mask_scalar (s_425 : x25519_serialized_scalar_t)
  : both (CEfset ([k_423_loc])) [interface] (x25519_serialized_scalar_t) :=
  ((letbm k_423 : x25519_serialized_scalar_t loc( k_423_loc ) :=
        lift_to_both0 s_425 in
      letb k_423 : x25519_serialized_scalar_t :=
        array_upd k_423 (lift_to_both0 (usize 0)) (is_pure ((array_index (
                k_423) (lift_to_both0 (usize 0))) .& (secret (lift_to_both0 (
                  @repr U8 248))))) in
      letb k_423 : x25519_serialized_scalar_t :=
        array_upd k_423 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                k_423) (lift_to_both0 (usize 31))) .& (secret (lift_to_both0 (
                  @repr U8 127))))) in
      letb k_423 : x25519_serialized_scalar_t :=
        array_upd k_423 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                k_423) (lift_to_both0 (usize 31))) .| (secret (lift_to_both0 (
                  @repr U8 64))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 k_423)
      ) : both (CEfset ([k_423_loc])) [interface] (x25519_serialized_scalar_t)).
Fail Next Obligation.


Notation "'decode_scalar_inp'" :=(
  x25519_serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_scalar_out'" :=(
  scalar_t : choice_type) (in custom pack_type at level 2).
Definition DECODE_SCALAR : nat :=
  429.
Program Definition decode_scalar (s_427 : x25519_serialized_scalar_t)
  : both (CEfset ([k_423_loc])) [interface] (scalar_t) :=
  ((letb k_428 : x25519_serialized_scalar_t :=
        mask_scalar (lift_to_both0 s_427) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 k_428)))
      ) : both (CEfset ([k_423_loc])) [interface] (scalar_t)).
Fail Next Obligation.

Definition u_430_loc : ChoiceEqualityLocation :=
  (x25519_serialized_point_t ; 431%nat).
Notation "'decode_point_inp'" :=(
  x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Notation "'decode_point_out'" :=(
  point_t : choice_type) (in custom pack_type at level 2).
Definition DECODE_POINT : nat :=
  433.
Program Definition decode_point (u_432 : x25519_serialized_point_t)
  : both (CEfset ([u_430_loc])) [interface] (point_t) :=
  ((letbm u_430 : x25519_serialized_point_t loc( u_430_loc ) :=
        lift_to_both0 u_432 in
      letb u_430 : x25519_serialized_point_t :=
        array_upd u_430 (lift_to_both0 (usize 31)) (is_pure ((array_index (
                u_430) (lift_to_both0 (usize 31))) .& (secret (lift_to_both0 (
                  @repr U8 127))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          nat_mod_from_byte_seq_le (array_to_seq (lift_to_both0 u_430)),
          nat_mod_from_literal (
            0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
            lift_to_both0 (@repr U128 1))
        ))
      ) : both (CEfset ([u_430_loc])) [interface] (point_t)).
Fail Next Obligation.


Notation "'encode_point_inp'" :=(
  point_t : choice_type) (in custom pack_type at level 2).
Notation "'encode_point_out'" :=(
  x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Definition ENCODE_POINT : nat :=
  438.
Program Definition encode_point (p_434 : point_t)
  : both (fset.fset0) [interface] (x25519_serialized_point_t) :=
  ((letb '(x_435, y_436) : (x25519_field_element_t '× x25519_field_element_t
        ) :=
        lift_to_both0 p_434 in
      letb b_437 : x25519_field_element_t :=
        (lift_to_both0 x_435) *% (nat_mod_inv (lift_to_both0 y_436)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_update_start (
          array_new_ (default : uint8) (32)) (nat_mod_to_byte_seq_le (
            lift_to_both0 b_437)))
      ) : both (fset.fset0) [interface] (x25519_serialized_point_t)).
Fail Next Obligation.


Notation "'point_add_and_double_inp'" :=(point_t × (point_t '× point_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'point_add_and_double_out'" :=((point_t '× point_t
  ) : choice_type) (in custom pack_type at level 2).
Definition POINT_ADD_AND_DOUBLE : nat :=
  463.
Program Definition point_add_and_double (q_442 : point_t) (np_439 : (
      point_t '×
      point_t
    ))
  : both (fset.fset0) [interface] ((point_t '× point_t)) :=
  ((letb '(nq_440, nqp1_441) : (point_t '× point_t) := lift_to_both0 np_439 in
      letb '(x_1_443, z_1_444) : (
          x25519_field_element_t '×
          x25519_field_element_t
        ) :=
        lift_to_both0 q_442 in
      letb '(x_2_445, z_2_446) : (
          x25519_field_element_t '×
          x25519_field_element_t
        ) :=
        lift_to_both0 nq_440 in
      letb '(x_3_447, z_3_448) : (
          x25519_field_element_t '×
          x25519_field_element_t
        ) :=
        lift_to_both0 nqp1_441 in
      letb a_449 : x25519_field_element_t :=
        (lift_to_both0 x_2_445) +% (lift_to_both0 z_2_446) in
      letb aa_450 : x25519_field_element_t :=
        nat_mod_pow (lift_to_both0 a_449) (lift_to_both0 (@repr U128 2)) in
      letb b_451 : x25519_field_element_t :=
        (lift_to_both0 x_2_445) -% (lift_to_both0 z_2_446) in
      letb bb_452 : x25519_field_element_t :=
        (lift_to_both0 b_451) *% (lift_to_both0 b_451) in
      letb e_453 : x25519_field_element_t :=
        (lift_to_both0 aa_450) -% (lift_to_both0 bb_452) in
      letb c_454 : x25519_field_element_t :=
        (lift_to_both0 x_3_447) +% (lift_to_both0 z_3_448) in
      letb d_455 : x25519_field_element_t :=
        (lift_to_both0 x_3_447) -% (lift_to_both0 z_3_448) in
      letb da_456 : x25519_field_element_t :=
        (lift_to_both0 d_455) *% (lift_to_both0 a_449) in
      letb cb_457 : x25519_field_element_t :=
        (lift_to_both0 c_454) *% (lift_to_both0 b_451) in
      letb x_3_458 : x25519_field_element_t :=
        nat_mod_pow ((lift_to_both0 da_456) +% (lift_to_both0 cb_457)) (
          lift_to_both0 (@repr U128 2)) in
      letb z_3_459 : x25519_field_element_t :=
        (lift_to_both0 x_1_443) *% (nat_mod_pow ((lift_to_both0 da_456) -% (
              lift_to_both0 cb_457)) (lift_to_both0 (@repr U128 2))) in
      letb x_2_460 : x25519_field_element_t :=
        (lift_to_both0 aa_450) *% (lift_to_both0 bb_452) in
      letb e121665_461 : x25519_field_element_t :=
        nat_mod_from_literal (
          0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
          lift_to_both0 (@repr U128 121665)) in
      letb z_2_462 : x25519_field_element_t :=
        (lift_to_both0 e_453) *% ((lift_to_both0 aa_450) +% ((
              lift_to_both0 e121665_461) *% (lift_to_both0 e_453))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          prod_b(lift_to_both0 x_2_460, lift_to_both0 z_2_462),
          prod_b(lift_to_both0 x_3_458, lift_to_both0 z_3_459)
        ))
      ) : both (fset.fset0) [interface] ((point_t '× point_t))).
Fail Next Obligation.


Notation "'swap_inp'" :=((point_t '× point_t
  ) : choice_type) (in custom pack_type at level 2).
Notation "'swap_out'" :=((point_t '× point_t
  ) : choice_type) (in custom pack_type at level 2).
Definition SWAP : nat :=
  467.
Program Definition swap (x_464 : (point_t '× point_t))
  : both (fset.fset0) [interface] ((point_t '× point_t)) :=
  ((letb '(x0_465, x1_466) : (point_t '× point_t) := lift_to_both0 x_464 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x1_466,
          lift_to_both0 x0_465
        ))
      ) : both (fset.fset0) [interface] ((point_t '× point_t))).
Fail Next Obligation.

Definition acc_468_loc : ChoiceEqualityLocation :=
  ((point_t '× point_t) ; 469%nat).
Notation "'montgomery_ladder_inp'" :=(
  scalar_t × point_t : choice_type) (in custom pack_type at level 2).
Notation "'montgomery_ladder_out'" :=(
  point_t : choice_type) (in custom pack_type at level 2).
Definition MONTGOMERY_LADDER : nat :=
  475.
Program Definition montgomery_ladder (k_473 : scalar_t) (init_471 : point_t)
  : both (CEfset ([acc_468_loc])) [interface] (point_t) :=
  ((letb inf_470 : (x25519_field_element_t '× x25519_field_element_t) :=
        prod_b(
          nat_mod_from_literal (
            0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
            lift_to_both0 (@repr U128 1)),
          nat_mod_from_literal (
            0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
            lift_to_both0 (@repr U128 0))
        ) in
      letbm acc_468 : (point_t '× point_t) loc( acc_468_loc ) :=
        prod_b(lift_to_both0 inf_470, lift_to_both0 init_471) in
      letb acc_468 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 256)) acc_468 (L := (CEfset ([acc_468_loc]))) (
            I := [interface]) (fun i_472 acc_468 =>
            letb '(acc_468) :=
              if nat_mod_bit (lift_to_both0 k_473) ((lift_to_both0 (
                    usize 255)) .- (lift_to_both0 i_472)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([acc_468_loc])) (L2 := CEfset (
                  [acc_468_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm acc_468 loc( acc_468_loc ) :=
                  swap (lift_to_both0 acc_468) in
                letbm acc_468 loc( acc_468_loc ) :=
                  point_add_and_double (lift_to_both0 init_471) (
                    lift_to_both0 acc_468) in
                letbm acc_468 loc( acc_468_loc ) :=
                  swap (lift_to_both0 acc_468) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 acc_468)
                )
              else  lift_scope (L1 := CEfset ([acc_468_loc])) (L2 := CEfset (
                  [acc_468_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm acc_468 loc( acc_468_loc ) :=
                  point_add_and_double (lift_to_both0 init_471) (
                    lift_to_both0 acc_468) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 acc_468)
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 acc_468)
            ) in
      letb '(out_474, _) : (
          (x25519_field_element_t '× x25519_field_element_t) '×
          point_t
        ) :=
        lift_to_both0 acc_468 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 out_474)
      ) : both (CEfset ([acc_468_loc])) [interface] (point_t)).
Fail Next Obligation.


Notation "'x25519_scalarmult_inp'" :=(
  x25519_serialized_scalar_t × x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Notation "'x25519_scalarmult_out'" :=(
  x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Definition X25519_SCALARMULT : nat :=
  481.
Program Definition x25519_scalarmult (s_476 : x25519_serialized_scalar_t) (
    p_478 : x25519_serialized_point_t)
  : both (CEfset ([k_423_loc ; u_430_loc ; acc_468_loc])) [interface] (
    x25519_serialized_point_t) :=
  ((letb s_477 : scalar_t := decode_scalar (lift_to_both0 s_476) in
      letb p_479 : (x25519_field_element_t '× x25519_field_element_t) :=
        decode_point (lift_to_both0 p_478) in
      letb r_480 : (x25519_field_element_t '× x25519_field_element_t) :=
        montgomery_ladder (lift_to_both0 s_477) (lift_to_both0 p_479) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (encode_point (
          lift_to_both0 r_480))
      ) : both (CEfset ([k_423_loc ; u_430_loc ; acc_468_loc])) [interface] (
      x25519_serialized_point_t)).
Fail Next Obligation.

Definition base_482_loc : ChoiceEqualityLocation :=
  (x25519_serialized_point_t ; 483%nat).
Notation "'x25519_secret_to_public_inp'" :=(
  x25519_serialized_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'x25519_secret_to_public_out'" :=(
  x25519_serialized_point_t : choice_type) (in custom pack_type at level 2).
Definition X25519_SECRET_TO_PUBLIC : nat :=
  485.
Program Definition x25519_secret_to_public (s_484 : x25519_serialized_scalar_t)
  : both (CEfset (
      [k_423_loc ; u_430_loc ; acc_468_loc ; base_482_loc])) [interface] (
    x25519_serialized_point_t) :=
  ((letbm base_482 : x25519_serialized_point_t loc( base_482_loc ) :=
        array_new_ (default : uint8) (32) in
      letb base_482 : x25519_serialized_point_t :=
        array_upd base_482 (lift_to_both0 (usize 0)) (is_pure (secret (
              lift_to_both0 (@repr U8 9)))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (x25519_scalarmult (
          lift_to_both0 s_484) (lift_to_both0 base_482))
      ) : both (CEfset (
        [k_423_loc ; u_430_loc ; acc_468_loc ; base_482_loc])) [interface] (
      x25519_serialized_point_t)).
Fail Next Obligation.

