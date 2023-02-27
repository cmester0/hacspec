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

Inductive error_t :=
| InvalidAddition : error_t.

Definition bits_v : uint_size :=
  usize 256.

Definition field_canvas_t := nseq (int8) (32).
Definition p256_field_element_t :=
  nat_mod 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff.

Definition scalar_canvas_t := nseq (int8) (32).
Definition p256_scalar_t :=
  nat_mod 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551.

Notation "'affine_t'" := ((p256_field_element_t '× p256_field_element_t
)) : hacspec_scope.

Notation "'affine_result_t'" := ((result affine_t error_t)) : hacspec_scope.

Notation "'p256_jacobian_t'" := ((
  p256_field_element_t '×
  p256_field_element_t '×
  p256_field_element_t
)) : hacspec_scope.

Notation "'jacobian_result_t'" := ((
  result p256_jacobian_t error_t)) : hacspec_scope.

Definition element_t := nseq (uint8) (usize 32).

Definition jacobian_to_affine (p_419 : p256_jacobian_t)  : affine_t :=
  let '(x_420, y_421, z_422) :=
    p_419 in 
  let z2_423 : p256_field_element_t :=
    nat_mod_exp (z_422) (@repr WORDSIZE32 (2)) in 
  let z2i_424 : p256_field_element_t :=
    nat_mod_inv (z2_423) in 
  let z3_425 : p256_field_element_t :=
    (z_422) *% (z2_423) in 
  let z3i_426 : p256_field_element_t :=
    nat_mod_inv (z3_425) in 
  let x_427 : p256_field_element_t :=
    (x_420) *% (z2i_424) in 
  let y_428 : p256_field_element_t :=
    (y_421) *% (z3i_426) in 
  (x_427, y_428).


Definition affine_to_jacobian (p_429 : affine_t)  : p256_jacobian_t :=
  let '(x_430, y_431) :=
    p_429 in 
  (
    x_430,
    y_431,
    nat_mod_from_literal (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
      @repr WORDSIZE128 1) : p256_field_element_t
  ).


Definition point_double (p_432 : p256_jacobian_t)  : p256_jacobian_t :=
  let '(x1_433, y1_434, z1_435) :=
    p_432 in 
  let delta_436 : p256_field_element_t :=
    nat_mod_exp (z1_435) (@repr WORDSIZE32 (2)) in 
  let gamma_437 : p256_field_element_t :=
    nat_mod_exp (y1_434) (@repr WORDSIZE32 (2)) in 
  let beta_438 : p256_field_element_t :=
    (x1_433) *% (gamma_437) in 
  let alpha_1_439 : p256_field_element_t :=
    (x1_433) -% (delta_436) in 
  let alpha_2_440 : p256_field_element_t :=
    (x1_433) +% (delta_436) in 
  let alpha_441 : p256_field_element_t :=
    (nat_mod_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        @repr WORDSIZE128 3) : p256_field_element_t) *% ((alpha_1_439) *% (
        alpha_2_440)) in 
  let x3_442 : p256_field_element_t :=
    (nat_mod_exp (alpha_441) (@repr WORDSIZE32 (2))) -% ((nat_mod_from_literal (
          0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
          @repr WORDSIZE128 8) : p256_field_element_t) *% (beta_438)) in 
  let z3_443 : p256_field_element_t :=
    nat_mod_exp ((y1_434) +% (z1_435)) (@repr WORDSIZE32 (2)) in 
  let z3_444 : p256_field_element_t :=
    (z3_443) -% ((gamma_437) +% (delta_436)) in 
  let y3_1_445 : p256_field_element_t :=
    ((nat_mod_from_literal (
          0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
          @repr WORDSIZE128 4) : p256_field_element_t) *% (beta_438)) -% (
      x3_442) in 
  let y3_2_446 : p256_field_element_t :=
    (nat_mod_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        @repr WORDSIZE128 8) : p256_field_element_t) *% ((gamma_437) *% (
        gamma_437)) in 
  let y3_447 : p256_field_element_t :=
    ((alpha_441) *% (y3_1_445)) -% (y3_2_446) in 
  (x3_442, y3_447, z3_444).


Definition is_point_at_infinity (p_448 : p256_jacobian_t)  : bool :=
  let '(x_449, y_450, z_451) :=
    p_448 in 
  nat_mod_equal (z_451) (nat_mod_from_literal (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
      @repr WORDSIZE128 0) : p256_field_element_t).


Definition s1_equal_s2
  (s1_452 : p256_field_element_t)
  (s2_453 : p256_field_element_t)
  
  : jacobian_result_t :=
  (if (nat_mod_equal (s1_452) (s2_453)):bool then (
      @Err p256_jacobian_t error_t (InvalidAddition)) else (
      @Ok p256_jacobian_t error_t ((
          nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr WORDSIZE128 0) : p256_field_element_t,
          nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr WORDSIZE128 1) : p256_field_element_t,
          nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr WORDSIZE128 0) : p256_field_element_t
        )))).


Definition point_add_jacob
  (p_454 : p256_jacobian_t)
  (q_455 : p256_jacobian_t)
  
  : jacobian_result_t :=
  let result_456 : (result p256_jacobian_t error_t) :=
    @Ok p256_jacobian_t error_t (q_455) in 
  let '(result_456) :=
    if negb (is_point_at_infinity (p_454)):bool then (let '(result_456) :=
        if is_point_at_infinity (q_455):bool then (let result_456 :=
            @Ok p256_jacobian_t error_t (p_454) in 
          (result_456)) else (let '(x1_457, y1_458, z1_459) :=
            p_454 in 
          let '(x2_460, y2_461, z2_462) :=
            q_455 in 
          let z1z1_463 : p256_field_element_t :=
            nat_mod_exp (z1_459) (@repr WORDSIZE32 (2)) in 
          let z2z2_464 : p256_field_element_t :=
            nat_mod_exp (z2_462) (@repr WORDSIZE32 (2)) in 
          let u1_465 : p256_field_element_t :=
            (x1_457) *% (z2z2_464) in 
          let u2_466 : p256_field_element_t :=
            (x2_460) *% (z1z1_463) in 
          let s1_467 : p256_field_element_t :=
            ((y1_458) *% (z2_462)) *% (z2z2_464) in 
          let s2_468 : p256_field_element_t :=
            ((y2_461) *% (z1_459)) *% (z1z1_463) in 
          let '(result_456) :=
            if nat_mod_equal (u1_465) (u2_466):bool then (let result_456 :=
                s1_equal_s2 (s1_467) (s2_468) in 
              (result_456)) else (let h_469 : p256_field_element_t :=
                (u2_466) -% (u1_465) in 
              let i_470 : p256_field_element_t :=
                nat_mod_exp ((nat_mod_from_literal (
                      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                      @repr WORDSIZE128 2) : p256_field_element_t) *% (h_469)) (
                  @repr WORDSIZE32 (2)) in 
              let j_471 : p256_field_element_t :=
                (h_469) *% (i_470) in 
              let r_472 : p256_field_element_t :=
                (nat_mod_from_literal (
                    0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                    @repr WORDSIZE128 2) : p256_field_element_t) *% ((
                    s2_468) -% (s1_467)) in 
              let v_473 : p256_field_element_t :=
                (u1_465) *% (i_470) in 
              let x3_1_474 : p256_field_element_t :=
                (nat_mod_from_literal (
                    0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                    @repr WORDSIZE128 2) : p256_field_element_t) *% (v_473) in 
              let x3_2_475 : p256_field_element_t :=
                (nat_mod_exp (r_472) (@repr WORDSIZE32 (2))) -% (j_471) in 
              let x3_476 : p256_field_element_t :=
                (x3_2_475) -% (x3_1_474) in 
              let y3_1_477 : p256_field_element_t :=
                ((nat_mod_from_literal (
                      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                      @repr WORDSIZE128 2) : p256_field_element_t) *% (
                    s1_467)) *% (j_471) in 
              let y3_2_478 : p256_field_element_t :=
                (r_472) *% ((v_473) -% (x3_476)) in 
              let y3_479 : p256_field_element_t :=
                (y3_2_478) -% (y3_1_477) in 
              let z3_480 : p256_field_element_t :=
                nat_mod_exp ((z1_459) +% (z2_462)) (@repr WORDSIZE32 (2)) in 
              let z3_481 : p256_field_element_t :=
                ((z3_480) -% ((z1z1_463) +% (z2z2_464))) *% (h_469) in 
              let result_456 :=
                @Ok p256_jacobian_t error_t ((x3_476, y3_479, z3_481)) in 
              (result_456)) in 
          (result_456)) in 
      (result_456)) else ((result_456)) in 
  result_456.


Definition ltr_mul
  (k_482 : p256_scalar_t)
  (p_483 : p256_jacobian_t)
  
  : jacobian_result_t :=
  let q_484 : (
      p256_field_element_t '×
      p256_field_element_t '×
      p256_field_element_t
    ) :=
    (
      nat_mod_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        @repr WORDSIZE128 0) : p256_field_element_t,
      nat_mod_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        @repr WORDSIZE128 1) : p256_field_element_t,
      nat_mod_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        @repr WORDSIZE128 0) : p256_field_element_t
    ) in 
  bind (foldibnd (usize 0) to (bits_v) for q_484 >> (fun i_485 q_484 =>
    let q_484 :=
      point_double (q_484) in 
    ifbnd nat_mod_equal (nat_mod_get_bit (k_482) (((bits_v) - (usize 1)) - (
          i_485))) (nat_mod_one ) : bool
    thenbnd (bind (point_add_jacob (q_484) (p_483)) (fun q_484  => @Ok (
          (
            p256_field_element_t '×
            p256_field_element_t '×
            p256_field_element_t
          )
        ) error_t ((q_484))))
    else ((q_484)) >> (fun '(q_484) =>
    @Ok (
      (p256_field_element_t '× p256_field_element_t '× p256_field_element_t)
    ) error_t ((q_484))))) (fun q_484 => @Ok p256_jacobian_t error_t (q_484)).


Definition p256_point_mul
  (k_486 : p256_scalar_t)
  (p_487 : affine_t)
  
  : affine_result_t :=
  bind (ltr_mul (k_486) (affine_to_jacobian (p_487))) (fun jac_488 =>
    @Ok affine_t error_t (jacobian_to_affine (jac_488))).


Definition p256_point_mul_base (k_489 : p256_scalar_t)  : affine_result_t :=
  let base_point_490 : (p256_field_element_t '× p256_field_element_t) :=
    (
      nat_mod_from_byte_seq_be (array_to_seq (array_from_list uint8 (let l :=
            [
              secret (@repr WORDSIZE8 107) : int8;
              secret (@repr WORDSIZE8 23) : int8;
              secret (@repr WORDSIZE8 209) : int8;
              secret (@repr WORDSIZE8 242) : int8;
              secret (@repr WORDSIZE8 225) : int8;
              secret (@repr WORDSIZE8 44) : int8;
              secret (@repr WORDSIZE8 66) : int8;
              secret (@repr WORDSIZE8 71) : int8;
              secret (@repr WORDSIZE8 248) : int8;
              secret (@repr WORDSIZE8 188) : int8;
              secret (@repr WORDSIZE8 230) : int8;
              secret (@repr WORDSIZE8 229) : int8;
              secret (@repr WORDSIZE8 99) : int8;
              secret (@repr WORDSIZE8 164) : int8;
              secret (@repr WORDSIZE8 64) : int8;
              secret (@repr WORDSIZE8 242) : int8;
              secret (@repr WORDSIZE8 119) : int8;
              secret (@repr WORDSIZE8 3) : int8;
              secret (@repr WORDSIZE8 125) : int8;
              secret (@repr WORDSIZE8 129) : int8;
              secret (@repr WORDSIZE8 45) : int8;
              secret (@repr WORDSIZE8 235) : int8;
              secret (@repr WORDSIZE8 51) : int8;
              secret (@repr WORDSIZE8 160) : int8;
              secret (@repr WORDSIZE8 244) : int8;
              secret (@repr WORDSIZE8 161) : int8;
              secret (@repr WORDSIZE8 57) : int8;
              secret (@repr WORDSIZE8 69) : int8;
              secret (@repr WORDSIZE8 216) : int8;
              secret (@repr WORDSIZE8 152) : int8;
              secret (@repr WORDSIZE8 194) : int8;
              secret (@repr WORDSIZE8 150) : int8
            ] in  l))) : p256_field_element_t,
      nat_mod_from_byte_seq_be (array_to_seq (array_from_list uint8 (let l :=
            [
              secret (@repr WORDSIZE8 79) : int8;
              secret (@repr WORDSIZE8 227) : int8;
              secret (@repr WORDSIZE8 66) : int8;
              secret (@repr WORDSIZE8 226) : int8;
              secret (@repr WORDSIZE8 254) : int8;
              secret (@repr WORDSIZE8 26) : int8;
              secret (@repr WORDSIZE8 127) : int8;
              secret (@repr WORDSIZE8 155) : int8;
              secret (@repr WORDSIZE8 142) : int8;
              secret (@repr WORDSIZE8 231) : int8;
              secret (@repr WORDSIZE8 235) : int8;
              secret (@repr WORDSIZE8 74) : int8;
              secret (@repr WORDSIZE8 124) : int8;
              secret (@repr WORDSIZE8 15) : int8;
              secret (@repr WORDSIZE8 158) : int8;
              secret (@repr WORDSIZE8 22) : int8;
              secret (@repr WORDSIZE8 43) : int8;
              secret (@repr WORDSIZE8 206) : int8;
              secret (@repr WORDSIZE8 51) : int8;
              secret (@repr WORDSIZE8 87) : int8;
              secret (@repr WORDSIZE8 107) : int8;
              secret (@repr WORDSIZE8 49) : int8;
              secret (@repr WORDSIZE8 94) : int8;
              secret (@repr WORDSIZE8 206) : int8;
              secret (@repr WORDSIZE8 203) : int8;
              secret (@repr WORDSIZE8 182) : int8;
              secret (@repr WORDSIZE8 64) : int8;
              secret (@repr WORDSIZE8 104) : int8;
              secret (@repr WORDSIZE8 55) : int8;
              secret (@repr WORDSIZE8 191) : int8;
              secret (@repr WORDSIZE8 81) : int8;
              secret (@repr WORDSIZE8 245) : int8
            ] in  l))) : p256_field_element_t
    ) in 
  p256_point_mul (k_489) (base_point_490).


Definition point_add_distinct
  (p_491 : affine_t)
  (q_492 : affine_t)
  
  : affine_result_t :=
  bind (point_add_jacob (affine_to_jacobian (p_491)) (affine_to_jacobian (
        q_492))) (fun r_493 => @Ok affine_t error_t (jacobian_to_affine (
        r_493))).


Definition point_add (p_494 : affine_t) (q_495 : affine_t)  : affine_result_t :=
  (if ((p_494) !=.? (q_495)):bool then (point_add_distinct (p_494) (
        q_495)) else (@Ok affine_t error_t (jacobian_to_affine (point_double (
            affine_to_jacobian (p_494)))))).


Definition p256_validate_private_key (k_496 : byte_seq)  : bool :=
  let valid_497 : bool :=
    true in 
  let k_element_498 : p256_scalar_t :=
    nat_mod_from_byte_seq_be (k_496) : p256_scalar_t in 
  let k_element_bytes_499 : seq uint8 :=
    nat_mod_to_byte_seq_be (k_element_498) in 
  let all_zero_500 : bool :=
    true in 
  let '(valid_497, all_zero_500) :=
    foldi (usize 0) (seq_len (k_496)) (fun i_501 '(valid_497, all_zero_500) =>
      let '(all_zero_500) :=
        if negb (uint8_equal (seq_index (k_496) (i_501)) (secret (
              @repr WORDSIZE8 0) : int8)):bool then (let all_zero_500 :=
            false in 
          (all_zero_500)) else ((all_zero_500)) in 
      let '(valid_497) :=
        if negb (uint8_equal (seq_index (k_element_bytes_499) (i_501)) (
            seq_index (k_496) (i_501))):bool then (let valid_497 :=
            false in 
          (valid_497)) else ((valid_497)) in 
      (valid_497, all_zero_500))
    (valid_497, all_zero_500) in 
  (valid_497) && (negb (all_zero_500)).


Definition p256_validate_public_key (p_502 : affine_t)  : bool :=
  let b_503 : p256_field_element_t :=
    nat_mod_from_byte_seq_be ([
        secret (@repr WORDSIZE8 90) : int8;
        secret (@repr WORDSIZE8 198) : int8;
        secret (@repr WORDSIZE8 53) : int8;
        secret (@repr WORDSIZE8 216) : int8;
        secret (@repr WORDSIZE8 170) : int8;
        secret (@repr WORDSIZE8 58) : int8;
        secret (@repr WORDSIZE8 147) : int8;
        secret (@repr WORDSIZE8 231) : int8;
        secret (@repr WORDSIZE8 179) : int8;
        secret (@repr WORDSIZE8 235) : int8;
        secret (@repr WORDSIZE8 189) : int8;
        secret (@repr WORDSIZE8 85) : int8;
        secret (@repr WORDSIZE8 118) : int8;
        secret (@repr WORDSIZE8 152) : int8;
        secret (@repr WORDSIZE8 134) : int8;
        secret (@repr WORDSIZE8 188) : int8;
        secret (@repr WORDSIZE8 101) : int8;
        secret (@repr WORDSIZE8 29) : int8;
        secret (@repr WORDSIZE8 6) : int8;
        secret (@repr WORDSIZE8 176) : int8;
        secret (@repr WORDSIZE8 204) : int8;
        secret (@repr WORDSIZE8 83) : int8;
        secret (@repr WORDSIZE8 176) : int8;
        secret (@repr WORDSIZE8 246) : int8;
        secret (@repr WORDSIZE8 59) : int8;
        secret (@repr WORDSIZE8 206) : int8;
        secret (@repr WORDSIZE8 60) : int8;
        secret (@repr WORDSIZE8 62) : int8;
        secret (@repr WORDSIZE8 39) : int8;
        secret (@repr WORDSIZE8 210) : int8;
        secret (@repr WORDSIZE8 96) : int8;
        secret (@repr WORDSIZE8 75) : int8
      ]) : p256_field_element_t in 
  let point_at_infinity_504 : bool :=
    is_point_at_infinity (affine_to_jacobian (p_502)) in 
  let '(x_505, y_506) :=
    p_502 in 
  let on_curve_507 : bool :=
    ((y_506) *% (y_506)) =.? (((((x_505) *% (x_505)) *% (x_505)) -% ((
            nat_mod_from_literal (
              0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
              @repr WORDSIZE128 3) : p256_field_element_t) *% (x_505))) +% (
        b_503)) in 
  (negb (point_at_infinity_504)) && (on_curve_507).


Definition p256_calculate_w
  (x_508 : p256_field_element_t)
  
  : p256_field_element_t :=
  let b_509 : p256_field_element_t :=
    nat_mod_from_byte_seq_be ([
        secret (@repr WORDSIZE8 90) : int8;
        secret (@repr WORDSIZE8 198) : int8;
        secret (@repr WORDSIZE8 53) : int8;
        secret (@repr WORDSIZE8 216) : int8;
        secret (@repr WORDSIZE8 170) : int8;
        secret (@repr WORDSIZE8 58) : int8;
        secret (@repr WORDSIZE8 147) : int8;
        secret (@repr WORDSIZE8 231) : int8;
        secret (@repr WORDSIZE8 179) : int8;
        secret (@repr WORDSIZE8 235) : int8;
        secret (@repr WORDSIZE8 189) : int8;
        secret (@repr WORDSIZE8 85) : int8;
        secret (@repr WORDSIZE8 118) : int8;
        secret (@repr WORDSIZE8 152) : int8;
        secret (@repr WORDSIZE8 134) : int8;
        secret (@repr WORDSIZE8 188) : int8;
        secret (@repr WORDSIZE8 101) : int8;
        secret (@repr WORDSIZE8 29) : int8;
        secret (@repr WORDSIZE8 6) : int8;
        secret (@repr WORDSIZE8 176) : int8;
        secret (@repr WORDSIZE8 204) : int8;
        secret (@repr WORDSIZE8 83) : int8;
        secret (@repr WORDSIZE8 176) : int8;
        secret (@repr WORDSIZE8 246) : int8;
        secret (@repr WORDSIZE8 59) : int8;
        secret (@repr WORDSIZE8 206) : int8;
        secret (@repr WORDSIZE8 60) : int8;
        secret (@repr WORDSIZE8 62) : int8;
        secret (@repr WORDSIZE8 39) : int8;
        secret (@repr WORDSIZE8 210) : int8;
        secret (@repr WORDSIZE8 96) : int8;
        secret (@repr WORDSIZE8 75) : int8
      ]) : p256_field_element_t in 
  let exp_510 : p256_field_element_t :=
    nat_mod_from_byte_seq_be ([
        secret (@repr WORDSIZE8 63) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 192) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 64) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 64) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8
      ]) : p256_field_element_t in 
  let z_511 : p256_field_element_t :=
    ((((x_508) *% (x_508)) *% (x_508)) -% ((nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr WORDSIZE128 3) : p256_field_element_t) *% (x_508))) +% (
      b_509) in 
  let w_512 : p256_field_element_t :=
    nat_mod_pow_felem (z_511) (exp_510) in 
  w_512.


