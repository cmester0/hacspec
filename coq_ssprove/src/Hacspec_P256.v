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


Definition error_t : ChoiceEquality :=
  unit_ChoiceEquality.
Definition InvalidAddition : error_t :=
   tt.

Definition bits_v : uint_size :=
  usize 256.

Definition field_canvas_t := nseq (int8) (usize 32).
Definition p256_field_element_t :=
  nat_mod 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff.

Definition scalar_canvas_t := nseq (int8) (usize 32).
Definition p256_scalar_t :=
  nat_mod 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551.

Notation "'affine_t'" := ((p256_field_element_t × p256_field_element_t
)) : hacspec_scope.

Notation "'affine_result_t'" := ((result error_t affine_t)) : hacspec_scope.

Notation "'p256_jacobian_t'" := ((
  p256_field_element_t ×
  p256_field_element_t ×
  p256_field_element_t
)) : hacspec_scope.

Notation "'jacobian_result_t'" := ((
  result error_t p256_jacobian_t)) : hacspec_scope.

Definition element_t := nseq (uint8) (usize 32).


Notation "'jacobian_to_affine_inp'" :=(
  p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Notation "'jacobian_to_affine_out'" :=(
  affine_t : choice_type) (in custom pack_type at level 2).
Definition JACOBIAN_TO_AFFINE : nat :=
  543.
Program Definition jacobian_to_affine (p_533 : p256_jacobian_t)
  : both (fset.fset0) [interface] (affine_t) :=
  ((letb '(x_534, y_535, z_536) : (
          p256_field_element_t '×
          p256_field_element_t '×
          p256_field_element_t
        ) :=
        lift_to_both0 p_533 in
      letb z2_537 : p256_field_element_t :=
        nat_mod_exp (lift_to_both0 z_536) (lift_to_both0 (@repr U32 2)) in
      letb z2i_538 : p256_field_element_t :=
        nat_mod_inv (lift_to_both0 z2_537) in
      letb z3_539 : p256_field_element_t :=
        (lift_to_both0 z_536) *% (lift_to_both0 z2_537) in
      letb z3i_540 : p256_field_element_t :=
        nat_mod_inv (lift_to_both0 z3_539) in
      letb x_541 : p256_field_element_t :=
        (lift_to_both0 x_534) *% (lift_to_both0 z2i_538) in
      letb y_542 : p256_field_element_t :=
        (lift_to_both0 y_535) *% (lift_to_both0 z3i_540) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_541,
          lift_to_both0 y_542
        ))
      ) : both (fset.fset0) [interface] (affine_t)).
Fail Next Obligation.


Notation "'affine_to_jacobian_inp'" :=(
  affine_t : choice_type) (in custom pack_type at level 2).
Notation "'affine_to_jacobian_out'" :=(
  p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Definition AFFINE_TO_JACOBIAN : nat :=
  547.
Program Definition affine_to_jacobian (p_544 : affine_t)
  : both (fset.fset0) [interface] (p256_jacobian_t) :=
  ((letb '(x_545, y_546) : (p256_field_element_t '× p256_field_element_t) :=
        lift_to_both0 p_544 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x_545,
          lift_to_both0 y_546,
          nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            lift_to_both0 (@repr U128 1))
        ))
      ) : both (fset.fset0) [interface] (p256_jacobian_t)).
Fail Next Obligation.


Notation "'point_double_inp'" :=(
  p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Notation "'point_double_out'" :=(
  p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Definition POINT_DOUBLE : nat :=
  564.
Program Definition point_double (p_548 : p256_jacobian_t)
  : both (fset.fset0) [interface] (p256_jacobian_t) :=
  ((letb '(x1_549, y1_550, z1_551) : (
          p256_field_element_t '×
          p256_field_element_t '×
          p256_field_element_t
        ) :=
        lift_to_both0 p_548 in
      letb delta_552 : p256_field_element_t :=
        nat_mod_exp (lift_to_both0 z1_551) (lift_to_both0 (@repr U32 2)) in
      letb gamma_553 : p256_field_element_t :=
        nat_mod_exp (lift_to_both0 y1_550) (lift_to_both0 (@repr U32 2)) in
      letb beta_554 : p256_field_element_t :=
        (lift_to_both0 x1_549) *% (lift_to_both0 gamma_553) in
      letb alpha_1_555 : p256_field_element_t :=
        (lift_to_both0 x1_549) -% (lift_to_both0 delta_552) in
      letb alpha_2_556 : p256_field_element_t :=
        (lift_to_both0 x1_549) +% (lift_to_both0 delta_552) in
      letb alpha_557 : p256_field_element_t :=
        (nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            lift_to_both0 (@repr U128 3))) *% ((lift_to_both0 alpha_1_555) *% (
            lift_to_both0 alpha_2_556)) in
      letb x3_558 : p256_field_element_t :=
        (nat_mod_exp (lift_to_both0 alpha_557) (lift_to_both0 (
              @repr U32 2))) -% ((nat_mod_from_literal (
              0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
              lift_to_both0 (@repr U128 8))) *% (lift_to_both0 beta_554)) in
      letb z3_559 : p256_field_element_t :=
        nat_mod_exp ((lift_to_both0 y1_550) +% (lift_to_both0 z1_551)) (
          lift_to_both0 (@repr U32 2)) in
      letb z3_560 : p256_field_element_t :=
        (lift_to_both0 z3_559) -% ((lift_to_both0 gamma_553) +% (
            lift_to_both0 delta_552)) in
      letb y3_1_561 : p256_field_element_t :=
        ((nat_mod_from_literal (
              0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
              lift_to_both0 (@repr U128 4))) *% (lift_to_both0 beta_554)) -% (
          lift_to_both0 x3_558) in
      letb y3_2_562 : p256_field_element_t :=
        (nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            lift_to_both0 (@repr U128 8))) *% ((lift_to_both0 gamma_553) *% (
            lift_to_both0 gamma_553)) in
      letb y3_563 : p256_field_element_t :=
        ((lift_to_both0 alpha_557) *% (lift_to_both0 y3_1_561)) -% (
          lift_to_both0 y3_2_562) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 x3_558,
          lift_to_both0 y3_563,
          lift_to_both0 z3_560
        ))
      ) : both (fset.fset0) [interface] (p256_jacobian_t)).
Fail Next Obligation.


Notation "'is_point_at_infinity_inp'" :=(
  p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Notation "'is_point_at_infinity_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition IS_POINT_AT_INFINITY : nat :=
  569.
Program Definition is_point_at_infinity (p_565 : p256_jacobian_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb '(x_566, y_567, z_568) : (
          p256_field_element_t '×
          p256_field_element_t '×
          p256_field_element_t
        ) :=
        lift_to_both0 p_565 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (nat_mod_equal (
          lift_to_both0 z_568) (nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            lift_to_both0 (@repr U128 0))))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'s1_equal_s2_inp'" :=(
  p256_field_element_t × p256_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'s1_equal_s2_out'" :=(
  jacobian_result_t : choice_type) (in custom pack_type at level 2).
Definition S1_EQUAL_S2 : nat :=
  572.
Program Definition s1_equal_s2 (s1_570 : p256_field_element_t) (
    s2_571 : p256_field_element_t)
  : both (fset.fset0) [interface] (jacobian_result_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) (nat_mod_equal (lift_to_both0 s1_570) (
            lift_to_both0 s2_571))
        then @Err p256_jacobian_t error_t (InvalidAddition)
        else @Ok p256_jacobian_t error_t (prod_b(
            nat_mod_from_literal (
              0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
              lift_to_both0 (@repr U128 0)),
            nat_mod_from_literal (
              0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
              lift_to_both0 (@repr U128 1)),
            nat_mod_from_literal (
              0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
              lift_to_both0 (@repr U128 0))
          )))
      ) : both (fset.fset0) [interface] (jacobian_result_t)).
Fail Next Obligation.

Definition result_573_loc : ChoiceEqualityLocation :=
  ((result (error_t) (p256_jacobian_t)) ; 574%nat).
Notation "'point_add_jacob_inp'" :=(
  p256_jacobian_t × p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_jacob_out'" :=(
  jacobian_result_t : choice_type) (in custom pack_type at level 2).
Definition POINT_ADD_JACOB : nat :=
  602.
Program Definition point_add_jacob (p_576 : p256_jacobian_t) (
    q_575 : p256_jacobian_t)
  : both (CEfset ([result_573_loc])) [interface] (jacobian_result_t) :=
  ((letbm result_573 : (result (error_t) (
            p256_jacobian_t)) loc( result_573_loc ) :=
        @Ok p256_jacobian_t error_t (lift_to_both0 q_575) in
      letb '(result_573) :=
        if negb (is_point_at_infinity (
            lift_to_both0 p_576)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([result_573_loc])) (L2 := CEfset (
            [result_573_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letb '(
              result_573
            ) :=
            if is_point_at_infinity (lift_to_both0 q_575) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset ([result_573_loc])) (L2 := CEfset (
                [result_573_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letbm result_573 loc( result_573_loc ) :=
                @Ok p256_jacobian_t error_t (lift_to_both0 p_576) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 result_573)
              )
            else  lift_scope (L1 := CEfset ([result_573_loc])) (L2 := CEfset (
                [result_573_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letb '(
                  x1_577,
                  y1_578,
                  z1_579
                ) : (
                  p256_field_element_t '×
                  p256_field_element_t '×
                  p256_field_element_t
                ) :=
                lift_to_both0 p_576 in
              letb '(x2_580, y2_581, z2_582) : (
                  p256_field_element_t '×
                  p256_field_element_t '×
                  p256_field_element_t
                ) :=
                lift_to_both0 q_575 in
              letb z1z1_583 : p256_field_element_t :=
                nat_mod_exp (lift_to_both0 z1_579) (lift_to_both0 (
                    @repr U32 2)) in
              letb z2z2_584 : p256_field_element_t :=
                nat_mod_exp (lift_to_both0 z2_582) (lift_to_both0 (
                    @repr U32 2)) in
              letb u1_585 : p256_field_element_t :=
                (lift_to_both0 x1_577) *% (lift_to_both0 z2z2_584) in
              letb u2_586 : p256_field_element_t :=
                (lift_to_both0 x2_580) *% (lift_to_both0 z1z1_583) in
              letb s1_587 : p256_field_element_t :=
                ((lift_to_both0 y1_578) *% (lift_to_both0 z2_582)) *% (
                  lift_to_both0 z2z2_584) in
              letb s2_588 : p256_field_element_t :=
                ((lift_to_both0 y2_581) *% (lift_to_both0 z1_579)) *% (
                  lift_to_both0 z1z1_583) in
              letb '(result_573) :=
                if nat_mod_equal (lift_to_both0 u1_585) (
                  lift_to_both0 u2_586) :bool_ChoiceEquality
                then lift_scope (L1 := CEfset ([result_573_loc])) (
                  L2 := CEfset ([result_573_loc])) (I1 := [interface]) (
                  I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                  letbm result_573 loc( result_573_loc ) :=
                    s1_equal_s2 (lift_to_both0 s1_587) (lift_to_both0 s2_588) in
                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 result_573)
                  )
                else  lift_scope (L1 := CEfset ([result_573_loc])) (
                  L2 := CEfset ([result_573_loc])) (I1 := [interface]) (
                  I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                  letb h_589 : p256_field_element_t :=
                    (lift_to_both0 u2_586) -% (lift_to_both0 u1_585) in
                  letb i_590 : p256_field_element_t :=
                    nat_mod_exp ((nat_mod_from_literal (
                          0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                          lift_to_both0 (@repr U128 2))) *% (
                        lift_to_both0 h_589)) (lift_to_both0 (@repr U32 2)) in
                  letb j_591 : p256_field_element_t :=
                    (lift_to_both0 h_589) *% (lift_to_both0 i_590) in
                  letb r_592 : p256_field_element_t :=
                    (nat_mod_from_literal (
                        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                        lift_to_both0 (@repr U128 2))) *% ((
                        lift_to_both0 s2_588) -% (lift_to_both0 s1_587)) in
                  letb v_593 : p256_field_element_t :=
                    (lift_to_both0 u1_585) *% (lift_to_both0 i_590) in
                  letb x3_1_594 : p256_field_element_t :=
                    (nat_mod_from_literal (
                        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                        lift_to_both0 (@repr U128 2))) *% (
                      lift_to_both0 v_593) in
                  letb x3_2_595 : p256_field_element_t :=
                    (nat_mod_exp (lift_to_both0 r_592) (lift_to_both0 (
                          @repr U32 2))) -% (lift_to_both0 j_591) in
                  letb x3_596 : p256_field_element_t :=
                    (lift_to_both0 x3_2_595) -% (lift_to_both0 x3_1_594) in
                  letb y3_1_597 : p256_field_element_t :=
                    ((nat_mod_from_literal (
                          0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                          lift_to_both0 (@repr U128 2))) *% (
                        lift_to_both0 s1_587)) *% (lift_to_both0 j_591) in
                  letb y3_2_598 : p256_field_element_t :=
                    (lift_to_both0 r_592) *% ((lift_to_both0 v_593) -% (
                        lift_to_both0 x3_596)) in
                  letb y3_599 : p256_field_element_t :=
                    (lift_to_both0 y3_2_598) -% (lift_to_both0 y3_1_597) in
                  letb z3_600 : p256_field_element_t :=
                    nat_mod_exp ((lift_to_both0 z1_579) +% (
                        lift_to_both0 z2_582)) (lift_to_both0 (@repr U32 2)) in
                  letb z3_601 : p256_field_element_t :=
                    ((lift_to_both0 z3_600) -% ((lift_to_both0 z1z1_583) +% (
                          lift_to_both0 z2z2_584))) *% (lift_to_both0 h_589) in
                  letbm result_573 loc( result_573_loc ) :=
                    @Ok p256_jacobian_t error_t (prod_b(
                        lift_to_both0 x3_596,
                        lift_to_both0 y3_599,
                        lift_to_both0 z3_601
                      )) in
                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 result_573)
                  ) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 result_573)
              ) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_573)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_573)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 result_573)
      ) : both (CEfset ([result_573_loc])) [interface] (jacobian_result_t)).
Fail Next Obligation.

Definition q_603_loc : ChoiceEqualityLocation :=
  ((p256_field_element_t '× p256_field_element_t '× p256_field_element_t
    ) ; 604%nat).
Notation "'ltr_mul_inp'" :=(
  p256_scalar_t × p256_jacobian_t : choice_type) (in custom pack_type at level 2).
Notation "'ltr_mul_out'" :=(
  jacobian_result_t : choice_type) (in custom pack_type at level 2).
Definition LTR_MUL : nat :=
  608.
Program Definition ltr_mul (k_606 : p256_scalar_t) (p_607 : p256_jacobian_t)
  : both (CEfset ([result_573_loc ; q_603_loc])) [interface] (
    jacobian_result_t) :=
  ((letbm q_603 : (
          p256_field_element_t '×
          p256_field_element_t '×
          p256_field_element_t
        ) loc( q_603_loc ) :=
        prod_b(
          nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            lift_to_both0 (@repr U128 0)),
          nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            lift_to_both0 (@repr U128 1)),
          nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            lift_to_both0 (@repr U128 0))
        ) in
      letbnd(ChoiceEqualityMonad.result_bind_both error_t) q_603 :=
        foldi_bind_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 bits_v) q_603 (L := (CEfset (
                [result_573_loc ; q_603_loc]))) (I := [interface]) (
            fun i_605 q_603 =>
            letbm q_603 loc( q_603_loc ) :=
              point_double (lift_to_both0 q_603) in
            letbnd(ChoiceEqualityMonad.result_bind_both error_t) '(q_603) :=
              if nat_mod_equal (nat_mod_get_bit (lift_to_both0 k_606) (((
                      lift_to_both0 bits_v) .- (lift_to_both0 (usize 1))) .- (
                    lift_to_both0 i_605))) (nat_mod_one ) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([result_573_loc ; q_603_loc])) (
                L2 := CEfset ([result_573_loc ; q_603_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbndm(_) q_603 :=
                  point_add_jacob (lift_to_both0 q_603) (lift_to_both0 p_607) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
                    (
                      p256_field_element_t '×
                      p256_field_element_t '×
                      p256_field_element_t
                    )
                  ) error_t (lift_to_both0 q_603))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
                  (
                    p256_field_element_t '×
                    p256_field_element_t '×
                    p256_field_element_t
                  )
                ) error_t (lift_to_both0 q_603))
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok (
                (
                  p256_field_element_t '×
                  p256_field_element_t '×
                  p256_field_element_t
                )
              ) error_t (lift_to_both0 q_603))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        @Ok p256_jacobian_t error_t (lift_to_both0 q_603))
      ) : both (CEfset ([result_573_loc ; q_603_loc])) [interface] (
      jacobian_result_t)).
Fail Next Obligation.


Notation "'p256_point_mul_inp'" :=(
  p256_scalar_t × affine_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_point_mul_out'" :=(
  affine_result_t : choice_type) (in custom pack_type at level 2).
Definition P256_POINT_MUL : nat :=
  612.
Program Definition p256_point_mul (k_609 : p256_scalar_t) (p_610 : affine_t)
  : both (CEfset ([result_573_loc ; q_603_loc])) [interface] (
    affine_result_t) :=
  ((letbnd(_) jac_611 : p256_jacobian_t :=
        ltr_mul (lift_to_both0 k_609) (affine_to_jacobian (
            lift_to_both0 p_610)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok affine_t error_t (
          jacobian_to_affine (lift_to_both0 jac_611)))
      ) : both (CEfset ([result_573_loc ; q_603_loc])) [interface] (
      affine_result_t)).
Fail Next Obligation.


Notation "'p256_point_mul_base_inp'" :=(
  p256_scalar_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_point_mul_base_out'" :=(
  affine_result_t : choice_type) (in custom pack_type at level 2).
Definition P256_POINT_MUL_BASE : nat :=
  615.
Program Definition p256_point_mul_base (k_614 : p256_scalar_t)
  : both (CEfset ([result_573_loc ; q_603_loc])) [interface] (
    affine_result_t) :=
  ((letb base_point_613 : (p256_field_element_t '× p256_field_element_t) :=
        prod_b(
          nat_mod_from_byte_seq_be (array_to_seq (@array_from_list uint8 ([
                (secret (lift_to_both0 (@repr U8 107))) : uint8;
                (secret (lift_to_both0 (@repr U8 23))) : uint8;
                (secret (lift_to_both0 (@repr U8 209))) : uint8;
                (secret (lift_to_both0 (@repr U8 242))) : uint8;
                (secret (lift_to_both0 (@repr U8 225))) : uint8;
                (secret (lift_to_both0 (@repr U8 44))) : uint8;
                (secret (lift_to_both0 (@repr U8 66))) : uint8;
                (secret (lift_to_both0 (@repr U8 71))) : uint8;
                (secret (lift_to_both0 (@repr U8 248))) : uint8;
                (secret (lift_to_both0 (@repr U8 188))) : uint8;
                (secret (lift_to_both0 (@repr U8 230))) : uint8;
                (secret (lift_to_both0 (@repr U8 229))) : uint8;
                (secret (lift_to_both0 (@repr U8 99))) : uint8;
                (secret (lift_to_both0 (@repr U8 164))) : uint8;
                (secret (lift_to_both0 (@repr U8 64))) : uint8;
                (secret (lift_to_both0 (@repr U8 242))) : uint8;
                (secret (lift_to_both0 (@repr U8 119))) : uint8;
                (secret (lift_to_both0 (@repr U8 3))) : uint8;
                (secret (lift_to_both0 (@repr U8 125))) : uint8;
                (secret (lift_to_both0 (@repr U8 129))) : uint8;
                (secret (lift_to_both0 (@repr U8 45))) : uint8;
                (secret (lift_to_both0 (@repr U8 235))) : uint8;
                (secret (lift_to_both0 (@repr U8 51))) : uint8;
                (secret (lift_to_both0 (@repr U8 160))) : uint8;
                (secret (lift_to_both0 (@repr U8 244))) : uint8;
                (secret (lift_to_both0 (@repr U8 161))) : uint8;
                (secret (lift_to_both0 (@repr U8 57))) : uint8;
                (secret (lift_to_both0 (@repr U8 69))) : uint8;
                (secret (lift_to_both0 (@repr U8 216))) : uint8;
                (secret (lift_to_both0 (@repr U8 152))) : uint8;
                (secret (lift_to_both0 (@repr U8 194))) : uint8;
                (secret (lift_to_both0 (@repr U8 150))) : uint8
              ]))),
          nat_mod_from_byte_seq_be (array_to_seq (@array_from_list uint8 ([
                (secret (lift_to_both0 (@repr U8 79))) : uint8;
                (secret (lift_to_both0 (@repr U8 227))) : uint8;
                (secret (lift_to_both0 (@repr U8 66))) : uint8;
                (secret (lift_to_both0 (@repr U8 226))) : uint8;
                (secret (lift_to_both0 (@repr U8 254))) : uint8;
                (secret (lift_to_both0 (@repr U8 26))) : uint8;
                (secret (lift_to_both0 (@repr U8 127))) : uint8;
                (secret (lift_to_both0 (@repr U8 155))) : uint8;
                (secret (lift_to_both0 (@repr U8 142))) : uint8;
                (secret (lift_to_both0 (@repr U8 231))) : uint8;
                (secret (lift_to_both0 (@repr U8 235))) : uint8;
                (secret (lift_to_both0 (@repr U8 74))) : uint8;
                (secret (lift_to_both0 (@repr U8 124))) : uint8;
                (secret (lift_to_both0 (@repr U8 15))) : uint8;
                (secret (lift_to_both0 (@repr U8 158))) : uint8;
                (secret (lift_to_both0 (@repr U8 22))) : uint8;
                (secret (lift_to_both0 (@repr U8 43))) : uint8;
                (secret (lift_to_both0 (@repr U8 206))) : uint8;
                (secret (lift_to_both0 (@repr U8 51))) : uint8;
                (secret (lift_to_both0 (@repr U8 87))) : uint8;
                (secret (lift_to_both0 (@repr U8 107))) : uint8;
                (secret (lift_to_both0 (@repr U8 49))) : uint8;
                (secret (lift_to_both0 (@repr U8 94))) : uint8;
                (secret (lift_to_both0 (@repr U8 206))) : uint8;
                (secret (lift_to_both0 (@repr U8 203))) : uint8;
                (secret (lift_to_both0 (@repr U8 182))) : uint8;
                (secret (lift_to_both0 (@repr U8 64))) : uint8;
                (secret (lift_to_both0 (@repr U8 104))) : uint8;
                (secret (lift_to_both0 (@repr U8 55))) : uint8;
                (secret (lift_to_both0 (@repr U8 191))) : uint8;
                (secret (lift_to_both0 (@repr U8 81))) : uint8;
                (secret (lift_to_both0 (@repr U8 245))) : uint8
              ])))
        ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (p256_point_mul (
          lift_to_both0 k_614) (lift_to_both0 base_point_613))
      ) : both (CEfset ([result_573_loc ; q_603_loc])) [interface] (
      affine_result_t)).
Fail Next Obligation.


Notation "'point_add_distinct_inp'" :=(
  affine_t × affine_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_distinct_out'" :=(
  affine_result_t : choice_type) (in custom pack_type at level 2).
Definition POINT_ADD_DISTINCT : nat :=
  619.
Program Definition point_add_distinct (p_616 : affine_t) (q_617 : affine_t)
  : both (CEfset ([result_573_loc])) [interface] (affine_result_t) :=
  ((letbnd(_) r_618 : p256_jacobian_t :=
        point_add_jacob (affine_to_jacobian (lift_to_both0 p_616)) (
          affine_to_jacobian (lift_to_both0 q_617)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (@Ok affine_t error_t (
          jacobian_to_affine (lift_to_both0 r_618)))
      ) : both (CEfset ([result_573_loc])) [interface] (affine_result_t)).
Fail Next Obligation.


Notation "'point_add_inp'" :=(
  affine_t × affine_t : choice_type) (in custom pack_type at level 2).
Notation "'point_add_out'" :=(
  affine_result_t : choice_type) (in custom pack_type at level 2).
Definition POINT_ADD : nat :=
  622.
Program Definition point_add (p_620 : affine_t) (q_621 : affine_t)
  : both (CEfset ([result_573_loc])) [interface] (affine_result_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((lift_to_both0 p_620) !=.? (
            lift_to_both0 q_621))
        then point_add_distinct (lift_to_both0 p_620) (lift_to_both0 q_621)
        else @Ok affine_t error_t (jacobian_to_affine (point_double (
              affine_to_jacobian (lift_to_both0 p_620)))))
      ) : both (CEfset ([result_573_loc])) [interface] (affine_result_t)).
Fail Next Obligation.

Definition all_zero_624_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 625%nat).
Definition valid_623_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 626%nat).
Notation "'p256_validate_private_key_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'p256_validate_private_key_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition P256_VALIDATE_PRIVATE_KEY : nat :=
  631.
Program Definition p256_validate_private_key (k_627 : byte_seq)
  : both (CEfset ([valid_623_loc ; all_zero_624_loc])) [interface] (
    bool_ChoiceEquality) :=
  ((letbm valid_623 : bool_ChoiceEquality loc( valid_623_loc ) :=
        lift_to_both0 ((true : bool_ChoiceEquality)) in
      letb k_element_628 : p256_scalar_t :=
        nat_mod_from_byte_seq_be (lift_to_both0 k_627) in
      letb k_element_bytes_629 : seq uint8 :=
        nat_mod_to_byte_seq_be (lift_to_both0 k_element_628) in
      letbm all_zero_624 : bool_ChoiceEquality loc( all_zero_624_loc ) :=
        lift_to_both0 ((true : bool_ChoiceEquality)) in
      letb '(valid_623, all_zero_624) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 k_627)) prod_ce(valid_623, all_zero_624) (L := (
              CEfset ([valid_623_loc ; all_zero_624_loc]))) (I := [interface]) (
            fun i_630 '(valid_623, all_zero_624) =>
            letb '(all_zero_624) :=
              if negb (uint8_equal (seq_index (k_627) (lift_to_both0 i_630)) (
                  secret (lift_to_both0 (@repr U8 0)))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [valid_623_loc ; all_zero_624_loc])) (L2 := CEfset (
                  [valid_623_loc ; all_zero_624_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm all_zero_624 loc( all_zero_624_loc ) :=
                  lift_to_both0 ((false : bool_ChoiceEquality)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 all_zero_624)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 all_zero_624)
               in
            letb '(valid_623) :=
              if negb (uint8_equal (seq_index (k_element_bytes_629) (
                    lift_to_both0 i_630)) (seq_index (k_627) (
                    lift_to_both0 i_630))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [valid_623_loc ; all_zero_624_loc])) (L2 := CEfset (
                  [valid_623_loc ; all_zero_624_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm valid_623 loc( valid_623_loc ) :=
                  lift_to_both0 ((false : bool_ChoiceEquality)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 valid_623)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 valid_623)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 valid_623,
                lift_to_both0 all_zero_624
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 valid_623) && (negb (lift_to_both0 all_zero_624)))
      ) : both (CEfset ([valid_623_loc ; all_zero_624_loc])) [interface] (
      bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'p256_validate_public_key_inp'" :=(
  affine_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_validate_public_key_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition P256_VALIDATE_PUBLIC_KEY : nat :=
  638.
Program Definition p256_validate_public_key (p_633 : affine_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb b_632 : p256_field_element_t :=
        nat_mod_from_byte_seq_be ([
            secret (lift_to_both0 (@repr U8 90));
            secret (lift_to_both0 (@repr U8 198));
            secret (lift_to_both0 (@repr U8 53));
            secret (lift_to_both0 (@repr U8 216));
            secret (lift_to_both0 (@repr U8 170));
            secret (lift_to_both0 (@repr U8 58));
            secret (lift_to_both0 (@repr U8 147));
            secret (lift_to_both0 (@repr U8 231));
            secret (lift_to_both0 (@repr U8 179));
            secret (lift_to_both0 (@repr U8 235));
            secret (lift_to_both0 (@repr U8 189));
            secret (lift_to_both0 (@repr U8 85));
            secret (lift_to_both0 (@repr U8 118));
            secret (lift_to_both0 (@repr U8 152));
            secret (lift_to_both0 (@repr U8 134));
            secret (lift_to_both0 (@repr U8 188));
            secret (lift_to_both0 (@repr U8 101));
            secret (lift_to_both0 (@repr U8 29));
            secret (lift_to_both0 (@repr U8 6));
            secret (lift_to_both0 (@repr U8 176));
            secret (lift_to_both0 (@repr U8 204));
            secret (lift_to_both0 (@repr U8 83));
            secret (lift_to_both0 (@repr U8 176));
            secret (lift_to_both0 (@repr U8 246));
            secret (lift_to_both0 (@repr U8 59));
            secret (lift_to_both0 (@repr U8 206));
            secret (lift_to_both0 (@repr U8 60));
            secret (lift_to_both0 (@repr U8 62));
            secret (lift_to_both0 (@repr U8 39));
            secret (lift_to_both0 (@repr U8 210));
            secret (lift_to_both0 (@repr U8 96));
            secret (lift_to_both0 (@repr U8 75))
          ]) in
      letb point_at_infinity_634 : bool_ChoiceEquality :=
        is_point_at_infinity (affine_to_jacobian (lift_to_both0 p_633)) in
      letb '(x_635, y_636) : (p256_field_element_t '× p256_field_element_t) :=
        lift_to_both0 p_633 in
      letb on_curve_637 : bool_ChoiceEquality :=
        ((lift_to_both0 y_636) *% (lift_to_both0 y_636)) =.? (((((
                  lift_to_both0 x_635) *% (lift_to_both0 x_635)) *% (
                lift_to_both0 x_635)) -% ((nat_mod_from_literal (
                  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                  lift_to_both0 (@repr U128 3))) *% (lift_to_both0 x_635))) +% (
            lift_to_both0 b_632)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((negb (
            lift_to_both0 point_at_infinity_634)) && (
          lift_to_both0 on_curve_637))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.


Notation "'p256_calculate_w_inp'" :=(
  p256_field_element_t : choice_type) (in custom pack_type at level 2).
Notation "'p256_calculate_w_out'" :=(
  p256_field_element_t : choice_type) (in custom pack_type at level 2).
Definition P256_CALCULATE_W : nat :=
  644.
Program Definition p256_calculate_w (x_641 : p256_field_element_t)
  : both (fset.fset0) [interface] (p256_field_element_t) :=
  ((letb b_639 : p256_field_element_t :=
        nat_mod_from_byte_seq_be ([
            secret (lift_to_both0 (@repr U8 90));
            secret (lift_to_both0 (@repr U8 198));
            secret (lift_to_both0 (@repr U8 53));
            secret (lift_to_both0 (@repr U8 216));
            secret (lift_to_both0 (@repr U8 170));
            secret (lift_to_both0 (@repr U8 58));
            secret (lift_to_both0 (@repr U8 147));
            secret (lift_to_both0 (@repr U8 231));
            secret (lift_to_both0 (@repr U8 179));
            secret (lift_to_both0 (@repr U8 235));
            secret (lift_to_both0 (@repr U8 189));
            secret (lift_to_both0 (@repr U8 85));
            secret (lift_to_both0 (@repr U8 118));
            secret (lift_to_both0 (@repr U8 152));
            secret (lift_to_both0 (@repr U8 134));
            secret (lift_to_both0 (@repr U8 188));
            secret (lift_to_both0 (@repr U8 101));
            secret (lift_to_both0 (@repr U8 29));
            secret (lift_to_both0 (@repr U8 6));
            secret (lift_to_both0 (@repr U8 176));
            secret (lift_to_both0 (@repr U8 204));
            secret (lift_to_both0 (@repr U8 83));
            secret (lift_to_both0 (@repr U8 176));
            secret (lift_to_both0 (@repr U8 246));
            secret (lift_to_both0 (@repr U8 59));
            secret (lift_to_both0 (@repr U8 206));
            secret (lift_to_both0 (@repr U8 60));
            secret (lift_to_both0 (@repr U8 62));
            secret (lift_to_both0 (@repr U8 39));
            secret (lift_to_both0 (@repr U8 210));
            secret (lift_to_both0 (@repr U8 96));
            secret (lift_to_both0 (@repr U8 75))
          ]) in
      letb exp_640 : p256_field_element_t :=
        nat_mod_from_byte_seq_be ([
            secret (lift_to_both0 (@repr U8 63));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 255));
            secret (lift_to_both0 (@repr U8 192));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 64));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 64));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0));
            secret (lift_to_both0 (@repr U8 0))
          ]) in
      letb z_642 : p256_field_element_t :=
        ((((lift_to_both0 x_641) *% (lift_to_both0 x_641)) *% (
              lift_to_both0 x_641)) -% ((nat_mod_from_literal (
                0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                lift_to_both0 (@repr U128 3))) *% (lift_to_both0 x_641))) +% (
          lift_to_both0 b_639) in
      letb w_643 : p256_field_element_t :=
        nat_mod_pow_felem (lift_to_both0 z_642) (lift_to_both0 exp_640) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 w_643)
      ) : both (fset.fset0) [interface] (p256_field_element_t)).
Fail Next Obligation.

