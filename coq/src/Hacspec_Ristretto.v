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

Notation "'ristretto_point_t'" := ((
  field_element_t '×
  field_element_t '×
  field_element_t '×
  field_element_t
)) : hacspec_scope.

Notation "'decode_result_t'" := ((
  result ristretto_point_t int8)) : hacspec_scope.

Definition ristretto_point_encoded_t := nseq (uint8) (usize 32).

Definition byte_string_t := nseq (uint8) (usize 64).

Definition field_canvas_t := nseq (int8) (32).
Definition field_element_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition scalar_canvas_t := nseq (int8) (32).
Definition scalar_t :=
  nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed.

Definition decoding_error_v : int8 :=
  @repr WORDSIZE8 20.

Definition p   : field_element_t :=
  nat_mod_from_byte_seq_be ([
      secret (@repr WORDSIZE8 127) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 237) : int8
    ]) : field_element_t.


Definition d   : field_element_t :=
  nat_mod_from_byte_seq_be ([
      secret (@repr WORDSIZE8 82) : int8;
      secret (@repr WORDSIZE8 3) : int8;
      secret (@repr WORDSIZE8 108) : int8;
      secret (@repr WORDSIZE8 238) : int8;
      secret (@repr WORDSIZE8 43) : int8;
      secret (@repr WORDSIZE8 111) : int8;
      secret (@repr WORDSIZE8 254) : int8;
      secret (@repr WORDSIZE8 115) : int8;
      secret (@repr WORDSIZE8 140) : int8;
      secret (@repr WORDSIZE8 199) : int8;
      secret (@repr WORDSIZE8 64) : int8;
      secret (@repr WORDSIZE8 121) : int8;
      secret (@repr WORDSIZE8 119) : int8;
      secret (@repr WORDSIZE8 121) : int8;
      secret (@repr WORDSIZE8 232) : int8;
      secret (@repr WORDSIZE8 152) : int8;
      secret (@repr WORDSIZE8 0) : int8;
      secret (@repr WORDSIZE8 112) : int8;
      secret (@repr WORDSIZE8 10) : int8;
      secret (@repr WORDSIZE8 77) : int8;
      secret (@repr WORDSIZE8 65) : int8;
      secret (@repr WORDSIZE8 65) : int8;
      secret (@repr WORDSIZE8 216) : int8;
      secret (@repr WORDSIZE8 171) : int8;
      secret (@repr WORDSIZE8 117) : int8;
      secret (@repr WORDSIZE8 235) : int8;
      secret (@repr WORDSIZE8 77) : int8;
      secret (@repr WORDSIZE8 202) : int8;
      secret (@repr WORDSIZE8 19) : int8;
      secret (@repr WORDSIZE8 89) : int8;
      secret (@repr WORDSIZE8 120) : int8;
      secret (@repr WORDSIZE8 163) : int8
    ]) : field_element_t.


Definition sqrt_m1   : field_element_t :=
  nat_mod_from_byte_seq_be ([
      secret (@repr WORDSIZE8 43) : int8;
      secret (@repr WORDSIZE8 131) : int8;
      secret (@repr WORDSIZE8 36) : int8;
      secret (@repr WORDSIZE8 128) : int8;
      secret (@repr WORDSIZE8 79) : int8;
      secret (@repr WORDSIZE8 193) : int8;
      secret (@repr WORDSIZE8 223) : int8;
      secret (@repr WORDSIZE8 11) : int8;
      secret (@repr WORDSIZE8 43) : int8;
      secret (@repr WORDSIZE8 77) : int8;
      secret (@repr WORDSIZE8 0) : int8;
      secret (@repr WORDSIZE8 153) : int8;
      secret (@repr WORDSIZE8 61) : int8;
      secret (@repr WORDSIZE8 251) : int8;
      secret (@repr WORDSIZE8 215) : int8;
      secret (@repr WORDSIZE8 167) : int8;
      secret (@repr WORDSIZE8 47) : int8;
      secret (@repr WORDSIZE8 67) : int8;
      secret (@repr WORDSIZE8 24) : int8;
      secret (@repr WORDSIZE8 6) : int8;
      secret (@repr WORDSIZE8 173) : int8;
      secret (@repr WORDSIZE8 47) : int8;
      secret (@repr WORDSIZE8 228) : int8;
      secret (@repr WORDSIZE8 120) : int8;
      secret (@repr WORDSIZE8 196) : int8;
      secret (@repr WORDSIZE8 238) : int8;
      secret (@repr WORDSIZE8 27) : int8;
      secret (@repr WORDSIZE8 39) : int8;
      secret (@repr WORDSIZE8 74) : int8;
      secret (@repr WORDSIZE8 14) : int8;
      secret (@repr WORDSIZE8 160) : int8;
      secret (@repr WORDSIZE8 176) : int8
    ]) : field_element_t.


Definition invsqrt_a_minus_d   : field_element_t :=
  nat_mod_from_byte_seq_be ([
      secret (@repr WORDSIZE8 120) : int8;
      secret (@repr WORDSIZE8 108) : int8;
      secret (@repr WORDSIZE8 137) : int8;
      secret (@repr WORDSIZE8 5) : int8;
      secret (@repr WORDSIZE8 207) : int8;
      secret (@repr WORDSIZE8 175) : int8;
      secret (@repr WORDSIZE8 252) : int8;
      secret (@repr WORDSIZE8 162) : int8;
      secret (@repr WORDSIZE8 22) : int8;
      secret (@repr WORDSIZE8 194) : int8;
      secret (@repr WORDSIZE8 123) : int8;
      secret (@repr WORDSIZE8 145) : int8;
      secret (@repr WORDSIZE8 254) : int8;
      secret (@repr WORDSIZE8 1) : int8;
      secret (@repr WORDSIZE8 216) : int8;
      secret (@repr WORDSIZE8 64) : int8;
      secret (@repr WORDSIZE8 157) : int8;
      secret (@repr WORDSIZE8 47) : int8;
      secret (@repr WORDSIZE8 22) : int8;
      secret (@repr WORDSIZE8 23) : int8;
      secret (@repr WORDSIZE8 90) : int8;
      secret (@repr WORDSIZE8 65) : int8;
      secret (@repr WORDSIZE8 114) : int8;
      secret (@repr WORDSIZE8 190) : int8;
      secret (@repr WORDSIZE8 153) : int8;
      secret (@repr WORDSIZE8 200) : int8;
      secret (@repr WORDSIZE8 253) : int8;
      secret (@repr WORDSIZE8 170) : int8;
      secret (@repr WORDSIZE8 128) : int8;
      secret (@repr WORDSIZE8 93) : int8;
      secret (@repr WORDSIZE8 64) : int8;
      secret (@repr WORDSIZE8 234) : int8
    ]) : field_element_t.


Definition sqrt_ad_minus_one   : field_element_t :=
  nat_mod_from_byte_seq_be ([
      secret (@repr WORDSIZE8 55) : int8;
      secret (@repr WORDSIZE8 105) : int8;
      secret (@repr WORDSIZE8 49) : int8;
      secret (@repr WORDSIZE8 191) : int8;
      secret (@repr WORDSIZE8 43) : int8;
      secret (@repr WORDSIZE8 131) : int8;
      secret (@repr WORDSIZE8 72) : int8;
      secret (@repr WORDSIZE8 172) : int8;
      secret (@repr WORDSIZE8 15) : int8;
      secret (@repr WORDSIZE8 60) : int8;
      secret (@repr WORDSIZE8 252) : int8;
      secret (@repr WORDSIZE8 201) : int8;
      secret (@repr WORDSIZE8 49) : int8;
      secret (@repr WORDSIZE8 245) : int8;
      secret (@repr WORDSIZE8 209) : int8;
      secret (@repr WORDSIZE8 253) : int8;
      secret (@repr WORDSIZE8 175) : int8;
      secret (@repr WORDSIZE8 157) : int8;
      secret (@repr WORDSIZE8 142) : int8;
      secret (@repr WORDSIZE8 12) : int8;
      secret (@repr WORDSIZE8 27) : int8;
      secret (@repr WORDSIZE8 120) : int8;
      secret (@repr WORDSIZE8 84) : int8;
      secret (@repr WORDSIZE8 189) : int8;
      secret (@repr WORDSIZE8 126) : int8;
      secret (@repr WORDSIZE8 151) : int8;
      secret (@repr WORDSIZE8 246) : int8;
      secret (@repr WORDSIZE8 160) : int8;
      secret (@repr WORDSIZE8 73) : int8;
      secret (@repr WORDSIZE8 123) : int8;
      secret (@repr WORDSIZE8 46) : int8;
      secret (@repr WORDSIZE8 27) : int8
    ]) : field_element_t.


Definition one_minus_d_sq   : field_element_t :=
  nat_mod_from_byte_seq_be ([
      secret (@repr WORDSIZE8 2) : int8;
      secret (@repr WORDSIZE8 144) : int8;
      secret (@repr WORDSIZE8 114) : int8;
      secret (@repr WORDSIZE8 168) : int8;
      secret (@repr WORDSIZE8 178) : int8;
      secret (@repr WORDSIZE8 179) : int8;
      secret (@repr WORDSIZE8 224) : int8;
      secret (@repr WORDSIZE8 215) : int8;
      secret (@repr WORDSIZE8 153) : int8;
      secret (@repr WORDSIZE8 148) : int8;
      secret (@repr WORDSIZE8 171) : int8;
      secret (@repr WORDSIZE8 221) : int8;
      secret (@repr WORDSIZE8 190) : int8;
      secret (@repr WORDSIZE8 112) : int8;
      secret (@repr WORDSIZE8 223) : int8;
      secret (@repr WORDSIZE8 228) : int8;
      secret (@repr WORDSIZE8 44) : int8;
      secret (@repr WORDSIZE8 129) : int8;
      secret (@repr WORDSIZE8 161) : int8;
      secret (@repr WORDSIZE8 56) : int8;
      secret (@repr WORDSIZE8 205) : int8;
      secret (@repr WORDSIZE8 94) : int8;
      secret (@repr WORDSIZE8 53) : int8;
      secret (@repr WORDSIZE8 15) : int8;
      secret (@repr WORDSIZE8 226) : int8;
      secret (@repr WORDSIZE8 124) : int8;
      secret (@repr WORDSIZE8 9) : int8;
      secret (@repr WORDSIZE8 193) : int8;
      secret (@repr WORDSIZE8 148) : int8;
      secret (@repr WORDSIZE8 95) : int8;
      secret (@repr WORDSIZE8 193) : int8;
      secret (@repr WORDSIZE8 118) : int8
    ]) : field_element_t.


Definition d_minus_one_sq   : field_element_t :=
  nat_mod_from_byte_seq_be ([
      secret (@repr WORDSIZE8 89) : int8;
      secret (@repr WORDSIZE8 104) : int8;
      secret (@repr WORDSIZE8 179) : int8;
      secret (@repr WORDSIZE8 122) : int8;
      secret (@repr WORDSIZE8 246) : int8;
      secret (@repr WORDSIZE8 108) : int8;
      secret (@repr WORDSIZE8 34) : int8;
      secret (@repr WORDSIZE8 65) : int8;
      secret (@repr WORDSIZE8 76) : int8;
      secret (@repr WORDSIZE8 220) : int8;
      secret (@repr WORDSIZE8 211) : int8;
      secret (@repr WORDSIZE8 47) : int8;
      secret (@repr WORDSIZE8 82) : int8;
      secret (@repr WORDSIZE8 155) : int8;
      secret (@repr WORDSIZE8 78) : int8;
      secret (@repr WORDSIZE8 235) : int8;
      secret (@repr WORDSIZE8 210) : int8;
      secret (@repr WORDSIZE8 158) : int8;
      secret (@repr WORDSIZE8 74) : int8;
      secret (@repr WORDSIZE8 44) : int8;
      secret (@repr WORDSIZE8 176) : int8;
      secret (@repr WORDSIZE8 30) : int8;
      secret (@repr WORDSIZE8 25) : int8;
      secret (@repr WORDSIZE8 153) : int8;
      secret (@repr WORDSIZE8 49) : int8;
      secret (@repr WORDSIZE8 173) : int8;
      secret (@repr WORDSIZE8 90) : int8;
      secret (@repr WORDSIZE8 170) : int8;
      secret (@repr WORDSIZE8 68) : int8;
      secret (@repr WORDSIZE8 237) : int8;
      secret (@repr WORDSIZE8 77) : int8;
      secret (@repr WORDSIZE8 32) : int8
    ]) : field_element_t.


Definition base_point_encoded   : ristretto_point_encoded_t :=
  array_from_seq (32) ([
      secret (@repr WORDSIZE8 226) : int8;
      secret (@repr WORDSIZE8 242) : int8;
      secret (@repr WORDSIZE8 174) : int8;
      secret (@repr WORDSIZE8 10) : int8;
      secret (@repr WORDSIZE8 106) : int8;
      secret (@repr WORDSIZE8 188) : int8;
      secret (@repr WORDSIZE8 78) : int8;
      secret (@repr WORDSIZE8 113) : int8;
      secret (@repr WORDSIZE8 168) : int8;
      secret (@repr WORDSIZE8 132) : int8;
      secret (@repr WORDSIZE8 169) : int8;
      secret (@repr WORDSIZE8 97) : int8;
      secret (@repr WORDSIZE8 197) : int8;
      secret (@repr WORDSIZE8 0) : int8;
      secret (@repr WORDSIZE8 81) : int8;
      secret (@repr WORDSIZE8 95) : int8;
      secret (@repr WORDSIZE8 88) : int8;
      secret (@repr WORDSIZE8 227) : int8;
      secret (@repr WORDSIZE8 11) : int8;
      secret (@repr WORDSIZE8 106) : int8;
      secret (@repr WORDSIZE8 165) : int8;
      secret (@repr WORDSIZE8 130) : int8;
      secret (@repr WORDSIZE8 221) : int8;
      secret (@repr WORDSIZE8 141) : int8;
      secret (@repr WORDSIZE8 182) : int8;
      secret (@repr WORDSIZE8 166) : int8;
      secret (@repr WORDSIZE8 89) : int8;
      secret (@repr WORDSIZE8 69) : int8;
      secret (@repr WORDSIZE8 224) : int8;
      secret (@repr WORDSIZE8 141) : int8;
      secret (@repr WORDSIZE8 45) : int8;
      secret (@repr WORDSIZE8 118) : int8
    ]).


Definition base_point   : ristretto_point_t :=
  result_unwrap (decode (base_point_encoded )).


Definition identity_point   : ristretto_point_t :=
  (fe (usize 0), fe (usize 1), fe (usize 1), fe (usize 0)).


Definition fe (x_590 : uint_size)  : field_element_t :=
  nat_mod_from_literal (
    0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
    pub_u128 (x_590)) : field_element_t.


Definition geq_p (x_591 : seq uint8)  : bool :=
  let p_seq_592 : seq uint8 :=
    [
      secret (@repr WORDSIZE8 237) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 127) : int8
    ] in 
  let res_593 : bool :=
    true in 
  let res_593 :=
    foldi (usize 0) (seq_len (p_seq_592)) (fun index_594 res_593 =>
      let x_index_595 : int8 :=
        uint8_declassify (seq_index (x_591) (index_594)) in 
      let p_index_596 : int8 :=
        uint8_declassify (seq_index (p_seq_592) (index_594)) in 
      let '(res_593) :=
        if (x_index_595) !=.? (p_index_596):bool then (let res_593 :=
            (x_index_595) >.? (p_index_596) in 
          (res_593)) else ((res_593)) in 
      (res_593))
    res_593 in 
  res_593.


Definition is_negative (e_597 : field_element_t)  : bool :=
  ((e_597) rem (fe (usize 2))) =.? (fe (usize 1)).


Definition eq (u_598 : field_element_t) (v_599 : field_element_t)  : bool :=
  (u_598) =.? (v_599).


Definition select
  (u_600 : field_element_t)
  (cond_601 : bool)
  (v_602 : field_element_t)
  
  : field_element_t :=
  (if (cond_601):bool then (u_600) else (v_602)).


Definition neg_fe (u_603 : field_element_t)  : field_element_t :=
  (fe (usize 0)) -% (u_603).


Definition abs (u_604 : field_element_t)  : field_element_t :=
  select (neg_fe (u_604)) (is_negative (u_604)) (u_604).


Definition sqrt_ratio_m1
  (u_605 : field_element_t)
  (v_606 : field_element_t)
  
  : (bool '× field_element_t) :=
  let v3_607 : field_element_t :=
    (nat_mod_pow (v_606) (@repr WORDSIZE128 2)) *% (v_606) in 
  let v7_608 : field_element_t :=
    (nat_mod_pow (v3_607) (@repr WORDSIZE128 2)) *% (v_606) in 
  let r_609 : field_element_t :=
    ((u_605) *% (v3_607)) *% (nat_mod_pow_felem ((u_605) *% (v7_608)) (((
            p ) -% (fe (usize 5))) /% (fe (usize 8)))) in 
  let check_610 : field_element_t :=
    (v_606) *% (nat_mod_pow (r_609) (@repr WORDSIZE128 2)) in 
  let correct_sign_sqrt_611 : bool :=
    eq (check_610) (u_605) in 
  let flipped_sign_sqrt_612 : bool :=
    eq (check_610) (neg_fe (u_605)) in 
  let flipped_sign_sqrt_i_613 : bool :=
    eq (check_610) ((neg_fe (u_605)) *% (sqrt_m1 )) in 
  let r_prime_614 : field_element_t :=
    (sqrt_m1 ) *% (r_609) in 
  let r_609 :=
    select (r_prime_614) ((flipped_sign_sqrt_612) || (
        flipped_sign_sqrt_i_613)) (r_609) in 
  let r_609 :=
    abs (r_609) in 
  let was_square_615 : bool :=
    (correct_sign_sqrt_611) || (flipped_sign_sqrt_612) in 
  (was_square_615, r_609).


Definition map (t_616 : field_element_t)  : ristretto_point_t :=
  let one_617 : field_element_t :=
    fe (usize 1) in 
  let minus_one_618 : field_element_t :=
    neg_fe (one_617) in 
  let r_619 : field_element_t :=
    (sqrt_m1 ) *% (nat_mod_pow (t_616) (@repr WORDSIZE128 2)) in 
  let u_620 : field_element_t :=
    ((r_619) +% (one_617)) *% (one_minus_d_sq ) in 
  let v_621 : field_element_t :=
    ((minus_one_618) -% ((r_619) *% (d ))) *% ((r_619) +% (d )) in 
  let '(was_square_622, s_623) :=
    sqrt_ratio_m1 (u_620) (v_621) in 
  let s_prime_624 : field_element_t :=
    neg_fe (abs ((s_623) *% (t_616))) in 
  let s_623 :=
    select (s_623) (was_square_622) (s_prime_624) in 
  let c_625 : field_element_t :=
    select (minus_one_618) (was_square_622) (r_619) in 
  let n_626 : field_element_t :=
    (((c_625) *% ((r_619) -% (one_617))) *% (d_minus_one_sq )) -% (v_621) in 
  let w0_627 : field_element_t :=
    ((fe (usize 2)) *% (s_623)) *% (v_621) in 
  let w1_628 : field_element_t :=
    (n_626) *% (sqrt_ad_minus_one ) in 
  let w2_629 : field_element_t :=
    (one_617) -% (nat_mod_pow (s_623) (@repr WORDSIZE128 2)) in 
  let w3_630 : field_element_t :=
    (one_617) +% (nat_mod_pow (s_623) (@repr WORDSIZE128 2)) in 
  (
    (w0_627) *% (w3_630),
    (w2_629) *% (w1_628),
    (w1_628) *% (w3_630),
    (w0_627) *% (w2_629)
  ).


Definition one_way_map (b_631 : byte_string_t)  : ristretto_point_t :=
  let r0_bytes_632 : seq uint8 :=
    array_slice (b_631) (usize 0) (usize 32) in 
  let r1_bytes_633 : seq uint8 :=
    array_slice (b_631) (usize 32) (usize 32) in 
  let r0_bytes_634 : seq int8 :=
    seq_declassify (r0_bytes_632) in 
  let r1_bytes_635 : seq int8 :=
    seq_declassify (r1_bytes_633) in 
  let r0_bytes_634 :=
    seq_upd r0_bytes_634 (usize 31) ((seq_index (r0_bytes_634) (usize 31)) .% (
        @repr WORDSIZE8 128)) in 
  let r1_bytes_635 :=
    seq_upd r1_bytes_635 (usize 31) ((seq_index (r1_bytes_635) (usize 31)) .% (
        @repr WORDSIZE8 128)) in 
  let r0_636 : field_element_t :=
    nat_mod_from_public_byte_seq_le (r0_bytes_634) in 
  let r1_637 : field_element_t :=
    nat_mod_from_public_byte_seq_le (r1_bytes_635) in 
  let p1_638 : (
      field_element_t '×
      field_element_t '×
      field_element_t '×
      field_element_t
    ) :=
    map (r0_636) in 
  let p2_639 : (
      field_element_t '×
      field_element_t '×
      field_element_t '×
      field_element_t
    ) :=
    map (r1_637) in 
  add (p1_638) (p2_639).


Definition encode (u_640 : ristretto_point_t)  : ristretto_point_encoded_t :=
  let '(x0_641, y0_642, z0_643, t0_644) :=
    u_640 in 
  let u1_645 : field_element_t :=
    ((z0_643) +% (y0_642)) *% ((z0_643) -% (y0_642)) in 
  let u2_646 : field_element_t :=
    (x0_641) *% (y0_642) in 
  let '(_, invsqrt_647) :=
    sqrt_ratio_m1 (fe (usize 1)) ((u1_645) *% (nat_mod_pow (u2_646) (
          @repr WORDSIZE128 2))) in 
  let den1_648 : field_element_t :=
    (invsqrt_647) *% (u1_645) in 
  let den2_649 : field_element_t :=
    (invsqrt_647) *% (u2_646) in 
  let z_inv_650 : field_element_t :=
    ((den1_648) *% (den2_649)) *% (t0_644) in 
  let ix0_651 : field_element_t :=
    (x0_641) *% (sqrt_m1 ) in 
  let iy0_652 : field_element_t :=
    (y0_642) *% (sqrt_m1 ) in 
  let enchanted_denominator_653 : field_element_t :=
    (den1_648) *% (invsqrt_a_minus_d ) in 
  let rotate_654 : bool :=
    is_negative ((t0_644) *% (z_inv_650)) in 
  let x_655 : field_element_t :=
    select (iy0_652) (rotate_654) (x0_641) in 
  let y_656 : field_element_t :=
    select (ix0_651) (rotate_654) (y0_642) in 
  let z_657 : field_element_t :=
    z0_643 in 
  let den_inv_658 : field_element_t :=
    select (enchanted_denominator_653) (rotate_654) (den2_649) in 
  let y_656 :=
    select (neg_fe (y_656)) (is_negative ((x_655) *% (z_inv_650))) (y_656) in 
  let s_659 : field_element_t :=
    abs ((den_inv_658) *% ((z_657) -% (y_656))) in 
  array_update_start (array_new_ (default : uint8) (32)) (
    nat_mod_to_byte_seq_le (s_659)).


Definition decode (u_660 : ristretto_point_encoded_t)  : decode_result_t :=
  let ret_661 : (result ristretto_point_t int8) :=
    @Err ristretto_point_t int8 (decoding_error_v) in 
  let s_662 : field_element_t :=
    nat_mod_from_byte_seq_le (array_to_seq (u_660)) : field_element_t in 
  let '(ret_661) :=
    if (negb (geq_p (array_to_le_bytes (u_660)))) && (negb (is_negative (
          s_662))):bool then (let one_663 : field_element_t :=
        fe (usize 1) in 
      let ss_664 : field_element_t :=
        nat_mod_pow (s_662) (@repr WORDSIZE128 2) in 
      let u1_665 : field_element_t :=
        (one_663) -% (ss_664) in 
      let u2_666 : field_element_t :=
        (one_663) +% (ss_664) in 
      let u2_sqr_667 : field_element_t :=
        nat_mod_pow (u2_666) (@repr WORDSIZE128 2) in 
      let v_668 : field_element_t :=
        (neg_fe ((d ) *% (nat_mod_pow (u1_665) (@repr WORDSIZE128 2)))) -% (
          u2_sqr_667) in 
      let '(was_square_669, invsqrt_670) :=
        sqrt_ratio_m1 (one_663) ((v_668) *% (u2_sqr_667)) in 
      let den_x_671 : field_element_t :=
        (invsqrt_670) *% (u2_666) in 
      let den_y_672 : field_element_t :=
        ((invsqrt_670) *% (den_x_671)) *% (v_668) in 
      let x_673 : field_element_t :=
        abs (((s_662) +% (s_662)) *% (den_x_671)) in 
      let y_674 : field_element_t :=
        (u1_665) *% (den_y_672) in 
      let t_675 : field_element_t :=
        (x_673) *% (y_674) in 
      let '(ret_661) :=
        if negb (((negb (was_square_669)) || (is_negative (t_675))) || ((
              y_674) =.? (fe (usize 0)))):bool then (let ret_661 :=
            @Ok ristretto_point_t int8 ((x_673, y_674, one_663, t_675)) in 
          (ret_661)) else ((ret_661)) in 
      (ret_661)) else ((ret_661)) in 
  ret_661.


Definition equals
  (u_676 : ristretto_point_t)
  (v_677 : ristretto_point_t)
  
  : bool :=
  let '(x1_678, y1_679, _, _) :=
    u_676 in 
  let '(x2_680, y2_681, _, _) :=
    v_677 in 
  (((x1_678) *% (y2_681)) =.? ((x2_680) *% (y1_679))) || (((y1_679) *% (
        y2_681)) =.? ((x1_678) *% (x2_680))).


Definition add
  (u_682 : ristretto_point_t)
  (v_683 : ristretto_point_t)
  
  : ristretto_point_t :=
  let '(x1_684, y1_685, z1_686, t1_687) :=
    u_682 in 
  let '(x2_688, y2_689, z2_690, t2_691) :=
    v_683 in 
  let a_692 : field_element_t :=
    ((y1_685) -% (x1_684)) *% ((y2_689) +% (x2_688)) in 
  let b_693 : field_element_t :=
    ((y1_685) +% (x1_684)) *% ((y2_689) -% (x2_688)) in 
  let c_694 : field_element_t :=
    ((fe (usize 2)) *% (z1_686)) *% (t2_691) in 
  let d_695 : field_element_t :=
    ((fe (usize 2)) *% (t1_687)) *% (z2_690) in 
  let e_696 : field_element_t :=
    (d_695) +% (c_694) in 
  let f_697 : field_element_t :=
    (b_693) -% (a_692) in 
  let g_698 : field_element_t :=
    (b_693) +% (a_692) in 
  let h_699 : field_element_t :=
    (d_695) -% (c_694) in 
  let x3_700 : field_element_t :=
    (e_696) *% (f_697) in 
  let y3_701 : field_element_t :=
    (g_698) *% (h_699) in 
  let t3_702 : field_element_t :=
    (e_696) *% (h_699) in 
  let z3_703 : field_element_t :=
    (f_697) *% (g_698) in 
  (x3_700, y3_701, z3_703, t3_702).


Definition neg (u_704 : ristretto_point_t)  : ristretto_point_t :=
  let '(x1_705, y1_706, z1_707, t1_708) :=
    u_704 in 
  (neg_fe (x1_705), y1_706, neg_fe (z1_707), t1_708).


Definition sub
  (u_709 : ristretto_point_t)
  (v_710 : ristretto_point_t)
  
  : ristretto_point_t :=
  add (u_709) (neg (v_710)).


Definition double (u_711 : ristretto_point_t)  : ristretto_point_t :=
  let '(x1_712, y1_713, z1_714, _) :=
    u_711 in 
  let a_715 : field_element_t :=
    nat_mod_pow (x1_712) (@repr WORDSIZE128 2) in 
  let b_716 : field_element_t :=
    nat_mod_pow (y1_713) (@repr WORDSIZE128 2) in 
  let c_717 : field_element_t :=
    (fe (usize 2)) *% (nat_mod_pow (z1_714) (@repr WORDSIZE128 2)) in 
  let h_718 : field_element_t :=
    (a_715) +% (b_716) in 
  let e_719 : field_element_t :=
    (h_718) -% (nat_mod_pow ((x1_712) +% (y1_713)) (@repr WORDSIZE128 2)) in 
  let g_720 : field_element_t :=
    (a_715) -% (b_716) in 
  let f_721 : field_element_t :=
    (c_717) +% (g_720) in 
  let x2_722 : field_element_t :=
    (e_719) *% (f_721) in 
  let y2_723 : field_element_t :=
    (g_720) *% (h_718) in 
  let t2_724 : field_element_t :=
    (e_719) *% (h_718) in 
  let z2_725 : field_element_t :=
    (f_721) *% (g_720) in 
  (x2_722, y2_723, z2_725, t2_724).


Definition mul
  (k_726 : scalar_t)
  (p_727 : ristretto_point_t)
  
  : ristretto_point_t :=
  let res_728 : (
      field_element_t '×
      field_element_t '×
      field_element_t '×
      field_element_t
    ) :=
    identity_point  in 
  let temp_729 : (
      field_element_t '×
      field_element_t '×
      field_element_t '×
      field_element_t
    ) :=
    p_727 in 
  let '(res_728, temp_729) :=
    foldi (usize 0) (usize 256) (fun i_730 '(res_728, temp_729) =>
      let '(res_728) :=
        if (nat_mod_get_bit (k_726) (i_730)) =.? (nat_mod_from_literal (
            0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed) (
            @repr WORDSIZE128 1) : scalar_t):bool then (let res_728 :=
            add (res_728) (temp_729) in 
          (res_728)) else ((res_728)) in 
      let temp_729 :=
        double (temp_729) in 
      (res_728, temp_729))
    (res_728, temp_729) in 
  res_728.


