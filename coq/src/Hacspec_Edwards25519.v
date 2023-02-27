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

Require Import Hacspec_Sha512.
Export Hacspec_Sha512.

Definition field_canvas_t := nseq (int8) (32).
Definition ed25519_field_element_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition scalar_canvas_t := nseq (int8) (32).
Definition scalar_t :=
  nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed.

Definition big_scalar_canvas_t := nseq (int8) (64).
Definition big_scalar_t :=
  nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed.

Definition big_integer_canvas_t := nseq (int8) (32).
Definition big_integer_t :=
  nat_mod 0x8000000000000000000000000000000080000000000000000000000000000000.

Notation "'ed_point_t'" := ((
  ed25519_field_element_t '×
  ed25519_field_element_t '×
  ed25519_field_element_t '×
  ed25519_field_element_t
)) : hacspec_scope.

Definition compressed_ed_point_t := nseq (uint8) (usize 32).

Definition serialized_scalar_t := nseq (uint8) (usize 32).

Definition signature_t := nseq (uint8) (usize 64).

Notation "'public_key_t'" := (compressed_ed_point_t) : hacspec_scope.

Notation "'secret_key_t'" := (serialized_scalar_t) : hacspec_scope.

Inductive error_t :=
| InvalidPublickey : error_t
| InvalidSignature : error_t
| InvalidS : error_t
| InvalidR : error_t
| SmallOrderPoint : error_t
| NotEnoughRandomness : error_t.

Notation "'verify_result_t'" := ((result unit error_t)) : hacspec_scope.

Definition base_v : compressed_ed_point_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 88) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8
      ] in  l).

Definition constant_p_v : serialized_scalar_t :=
  array_from_list uint8 (let l :=
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
      ] in  l).

Definition constant_l_v : serialized_scalar_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 237) : int8;
        secret (@repr WORDSIZE8 211) : int8;
        secret (@repr WORDSIZE8 245) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 26) : int8;
        secret (@repr WORDSIZE8 99) : int8;
        secret (@repr WORDSIZE8 18) : int8;
        secret (@repr WORDSIZE8 88) : int8;
        secret (@repr WORDSIZE8 214) : int8;
        secret (@repr WORDSIZE8 156) : int8;
        secret (@repr WORDSIZE8 247) : int8;
        secret (@repr WORDSIZE8 162) : int8;
        secret (@repr WORDSIZE8 222) : int8;
        secret (@repr WORDSIZE8 249) : int8;
        secret (@repr WORDSIZE8 222) : int8;
        secret (@repr WORDSIZE8 20) : int8;
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
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 16) : int8
      ] in  l).

Definition constant_p3_8_v : serialized_scalar_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 254) : int8;
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
        secret (@repr WORDSIZE8 15) : int8
      ] in  l).

Definition constant_p1_4_v : serialized_scalar_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 251) : int8;
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
        secret (@repr WORDSIZE8 31) : int8
      ] in  l).

Definition constant_d_v : serialized_scalar_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 163) : int8;
        secret (@repr WORDSIZE8 120) : int8;
        secret (@repr WORDSIZE8 89) : int8;
        secret (@repr WORDSIZE8 19) : int8;
        secret (@repr WORDSIZE8 202) : int8;
        secret (@repr WORDSIZE8 77) : int8;
        secret (@repr WORDSIZE8 235) : int8;
        secret (@repr WORDSIZE8 117) : int8;
        secret (@repr WORDSIZE8 171) : int8;
        secret (@repr WORDSIZE8 216) : int8;
        secret (@repr WORDSIZE8 65) : int8;
        secret (@repr WORDSIZE8 65) : int8;
        secret (@repr WORDSIZE8 77) : int8;
        secret (@repr WORDSIZE8 10) : int8;
        secret (@repr WORDSIZE8 112) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 152) : int8;
        secret (@repr WORDSIZE8 232) : int8;
        secret (@repr WORDSIZE8 121) : int8;
        secret (@repr WORDSIZE8 119) : int8;
        secret (@repr WORDSIZE8 121) : int8;
        secret (@repr WORDSIZE8 64) : int8;
        secret (@repr WORDSIZE8 199) : int8;
        secret (@repr WORDSIZE8 140) : int8;
        secret (@repr WORDSIZE8 115) : int8;
        secret (@repr WORDSIZE8 254) : int8;
        secret (@repr WORDSIZE8 111) : int8;
        secret (@repr WORDSIZE8 43) : int8;
        secret (@repr WORDSIZE8 238) : int8;
        secret (@repr WORDSIZE8 108) : int8;
        secret (@repr WORDSIZE8 3) : int8;
        secret (@repr WORDSIZE8 82) : int8
      ] in  l).

Definition is_negative (x_1975 : ed25519_field_element_t)  : uint8 :=
  (if (nat_mod_bit (x_1975) (usize 0)):bool then (secret (
        @repr WORDSIZE8 1) : int8) else (secret (@repr WORDSIZE8 0) : int8)).


Definition compress (p_1976 : ed_point_t)  : compressed_ed_point_t :=
  let '(x_1977, y_1978, z_1979, _) :=
    p_1976 in 
  let z_inv_1980 : ed25519_field_element_t :=
    nat_mod_inv (z_1979) in 
  let x_1981 : ed25519_field_element_t :=
    (x_1977) *% (z_inv_1980) in 
  let y_1982 : ed25519_field_element_t :=
    (y_1978) *% (z_inv_1980) in 
  let s_1983 : byte_seq :=
    nat_mod_to_byte_seq_le (y_1982) in 
  let s_1983 :=
    seq_upd s_1983 (usize 31) ((seq_index (s_1983) (usize 31)) .^ ((
          is_negative (x_1981)) shift_left (usize 7))) in 
  array_from_slice (default : uint8) (32) (s_1983) (usize 0) (usize 32).


Definition sqrt
  (a_1984 : ed25519_field_element_t)
  
  : (option ed25519_field_element_t) :=
  let p3_8_1985 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_p3_8_v)) : ed25519_field_element_t in 
  let p1_4_1986 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_p1_4_v)) : ed25519_field_element_t in 
  let x_c_1987 : ed25519_field_element_t :=
    nat_mod_pow_self (a_1984) (p3_8_1985) in 
  let result_1988 : (option ed25519_field_element_t) :=
    @None ed25519_field_element_t in 
  let '(result_1988) :=
    if ((x_c_1987) *% (x_c_1987)) =.? (a_1984):bool then (let result_1988 :=
        some (x_c_1987) in 
      (result_1988)) else ((result_1988)) in 
  let '(result_1988) :=
    if ((x_c_1987) *% (x_c_1987)) =.? ((nat_mod_zero ) -% (a_1984)):bool then (
      let x_1989 : ed25519_field_element_t :=
        (nat_mod_pow_self (nat_mod_two ) (p1_4_1986)) *% (x_c_1987) in 
      let result_1988 :=
        some (x_1989) in 
      (result_1988)) else ((result_1988)) in 
  result_1988.


Definition check_canonical_point (x_1990 : compressed_ed_point_t)  : bool :=
  let x_1990 :=
    array_upd x_1990 (usize 31) ((array_index (x_1990) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  let x_1991 : big_integer_t :=
    nat_mod_from_byte_seq_le (array_to_seq (x_1990)) : big_integer_t in 
  (x_1991) <.? (nat_mod_from_byte_seq_le (
      array_to_seq (constant_p_v)) : big_integer_t).


Definition decompress (q_1992 : compressed_ed_point_t)  : (option ed_point_t) :=
  let d_1993 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_d_v)) : ed25519_field_element_t in 
  let x_s_1994 : uint8 :=
    ((array_index (q_1992) (usize 31)) .& (secret (
          @repr WORDSIZE8 128) : int8)) shift_right (usize 7) in 
  let y_s_1995 : compressed_ed_point_t :=
    q_1992 in 
  let y_s_1995 :=
    array_upd y_s_1995 (usize 31) ((array_index (y_s_1995) (usize 31)) .& (
        secret (@repr WORDSIZE8 127) : int8)) in 
  ifbnd negb (check_canonical_point (y_s_1995)) : bool
  thenbnd (bind (@None ed_point_t) (fun _ => @Some unit (tt)))
  else (tt) >> (fun 'tt =>
  let y_1996 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (y_s_1995)) : ed25519_field_element_t in 
  let z_1997 : ed25519_field_element_t :=
    nat_mod_one  in 
  let yy_1998 : ed25519_field_element_t :=
    (y_1996) *% (y_1996) in 
  let u_1999 : ed25519_field_element_t :=
    (yy_1998) -% (z_1997) in 
  let v_2000 : ed25519_field_element_t :=
    ((d_1993) *% (yy_1998)) +% (z_1997) in 
  let xx_2001 : ed25519_field_element_t :=
    (u_1999) *% (nat_mod_inv (v_2000)) in 
  bind (sqrt (xx_2001)) (fun x_2002 => let x_r_2003 : uint8 :=
      is_negative (x_2002) in 
    ifbnd ((x_2002) =.? (nat_mod_zero )) && ((uint8_declassify (x_s_1994)) =.? (
        @repr WORDSIZE8 1)) : bool
    thenbnd (bind (@None ed_point_t) (fun _ => @Some unit (tt)))
    else (tt) >> (fun 'tt =>
    let '(x_2002) :=
      if (uint8_declassify (x_r_2003)) !=.? (uint8_declassify (
          x_s_1994)):bool then (let x_2002 :=
          (nat_mod_zero ) -% (x_2002) in 
        (x_2002)) else ((x_2002)) in 
    some ((x_2002, y_1996, z_1997, (x_2002) *% (y_1996)))))).


Definition decompress_non_canonical
  (p_2004 : compressed_ed_point_t)
  
  : (option ed_point_t) :=
  let d_2005 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_d_v)) : ed25519_field_element_t in 
  let x_s_2006 : uint8 :=
    ((array_index (p_2004) (usize 31)) .& (secret (
          @repr WORDSIZE8 128) : int8)) shift_right (usize 7) in 
  let y_s_2007 : compressed_ed_point_t :=
    p_2004 in 
  let y_s_2007 :=
    array_upd y_s_2007 (usize 31) ((array_index (y_s_2007) (usize 31)) .& (
        secret (@repr WORDSIZE8 127) : int8)) in 
  let y_2008 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (y_s_2007)) : ed25519_field_element_t in 
  let z_2009 : ed25519_field_element_t :=
    nat_mod_one  in 
  let yy_2010 : ed25519_field_element_t :=
    (y_2008) *% (y_2008) in 
  let u_2011 : ed25519_field_element_t :=
    (yy_2010) -% (z_2009) in 
  let v_2012 : ed25519_field_element_t :=
    ((d_2005) *% (yy_2010)) +% (z_2009) in 
  let xx_2013 : ed25519_field_element_t :=
    (u_2011) *% (nat_mod_inv (v_2012)) in 
  bind (sqrt (xx_2013)) (fun x_2014 => let x_r_2015 : uint8 :=
      is_negative (x_2014) in 
    let '(x_2014) :=
      if (uint8_declassify (x_r_2015)) !=.? (uint8_declassify (
          x_s_2006)):bool then (let x_2014 :=
          (nat_mod_zero ) -% (x_2014) in 
        (x_2014)) else ((x_2014)) in 
    some ((x_2014, y_2008, z_2009, (x_2014) *% (y_2008)))).


Definition encode (p_2016 : ed_point_t)  : byte_seq :=
  let '(x_2017, y_2018, z_2019, _) :=
    p_2016 in 
  let z_inv_2020 : ed25519_field_element_t :=
    nat_mod_inv (z_2019) in 
  let x_2021 : ed25519_field_element_t :=
    (x_2017) *% (z_inv_2020) in 
  let y_2022 : ed25519_field_element_t :=
    (y_2018) *% (z_inv_2020) in 
  let s_2023 : byte_seq :=
    nat_mod_to_byte_seq_le (y_2022) in 
  let s_2023 :=
    seq_upd s_2023 (usize 31) ((seq_index (s_2023) (usize 31)) .^ ((
          is_negative (x_2021)) shift_left (usize 7))) in 
  s_2023.


Definition decode (q_s_2024 : byte_seq)  : (option ed_point_t) :=
  let q_2025 : compressed_ed_point_t :=
    array_from_slice (default : uint8) (32) (q_s_2024) (usize 0) (usize 32) in 
  decompress (q_2025).


Definition point_add
  (p_2026 : ed_point_t)
  (q_2027 : ed_point_t)
  
  : ed_point_t :=
  let d_c_2028 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_d_v)) : ed25519_field_element_t in 
  let two_2029 : ed25519_field_element_t :=
    nat_mod_two  in 
  let '(x1_2030, y1_2031, z1_2032, t1_2033) :=
    p_2026 in 
  let '(x2_2034, y2_2035, z2_2036, t2_2037) :=
    q_2027 in 
  let a_2038 : ed25519_field_element_t :=
    ((y1_2031) -% (x1_2030)) *% ((y2_2035) -% (x2_2034)) in 
  let b_2039 : ed25519_field_element_t :=
    ((y1_2031) +% (x1_2030)) *% ((y2_2035) +% (x2_2034)) in 
  let c_2040 : ed25519_field_element_t :=
    (((t1_2033) *% (two_2029)) *% (d_c_2028)) *% (t2_2037) in 
  let d_2041 : ed25519_field_element_t :=
    ((z1_2032) *% (two_2029)) *% (z2_2036) in 
  let e_2042 : ed25519_field_element_t :=
    (b_2039) -% (a_2038) in 
  let f_2043 : ed25519_field_element_t :=
    (d_2041) -% (c_2040) in 
  let g_2044 : ed25519_field_element_t :=
    (d_2041) +% (c_2040) in 
  let h_2045 : ed25519_field_element_t :=
    (b_2039) +% (a_2038) in 
  let x3_2046 : ed25519_field_element_t :=
    (e_2042) *% (f_2043) in 
  let y3_2047 : ed25519_field_element_t :=
    (g_2044) *% (h_2045) in 
  let t3_2048 : ed25519_field_element_t :=
    (e_2042) *% (h_2045) in 
  let z3_2049 : ed25519_field_element_t :=
    (f_2043) *% (g_2044) in 
  (x3_2046, y3_2047, z3_2049, t3_2048).


Definition point_identity   : ed_point_t :=
  (nat_mod_zero , nat_mod_one , nat_mod_one , nat_mod_zero ).


Definition point_mul (s_2050 : scalar_t) (p_2051 : ed_point_t)  : ed_point_t :=
  let p_2052 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    p_2051 in 
  let q_2053 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let '(p_2052, q_2053) :=
    foldi (usize 0) (usize 256) (fun i_2054 '(p_2052, q_2053) =>
      let '(q_2053) :=
        if nat_mod_bit (s_2050) (i_2054):bool then (let q_2053 :=
            point_add (q_2053) (p_2052) in 
          (q_2053)) else ((q_2053)) in 
      let p_2052 :=
        point_add (p_2052) (p_2052) in 
      (p_2052, q_2053))
    (p_2052, q_2053) in 
  q_2053.


Definition point_mul_by_cofactor (p_2055 : ed_point_t)  : ed_point_t :=
  let p2_2056 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_add (p_2055) (p_2055) in 
  let p4_2057 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_add (p2_2056) (p2_2056) in 
  let p8_2058 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_add (p4_2057) (p4_2057) in 
  p8_2058.


Definition point_neg (p_2059 : ed_point_t)  : ed_point_t :=
  let '(x_2060, y_2061, z_2062, t_2063) :=
    p_2059 in 
  ((nat_mod_zero ) -% (x_2060), y_2061, z_2062, (nat_mod_zero ) -% (t_2063)).


Definition point_eq (p_2064 : ed_point_t) (q_2065 : ed_point_t)  : bool :=
  let '(x1_2066, y1_2067, z1_2068, _) :=
    p_2064 in 
  let '(x2_2069, y2_2070, z2_2071, _) :=
    q_2065 in 
  (((x1_2066) *% (z2_2071)) =.? ((x2_2069) *% (z1_2068))) && (((y1_2067) *% (
        z2_2071)) =.? ((y2_2070) *% (z1_2068))).


Definition point_normalize (q_2072 : ed_point_t)  : ed_point_t :=
  let '(qx_2073, qy_2074, qz_2075, _) :=
    q_2072 in 
  let px_2076 : ed25519_field_element_t :=
    (qx_2073) *% (nat_mod_inv (qz_2075)) in 
  let py_2077 : ed25519_field_element_t :=
    (qy_2074) *% (nat_mod_inv (qz_2075)) in 
  let pz_2078 : ed25519_field_element_t :=
    nat_mod_one  in 
  let pt_2079 : ed25519_field_element_t :=
    (px_2076) *% (py_2077) in 
  (px_2076, py_2077, pz_2078, pt_2079).


Definition secret_expand
  (sk_2080 : secret_key_t)
  
  : (serialized_scalar_t '× serialized_scalar_t) :=
  let h_2081 : sha512_digest_t :=
    sha512 (seq_from_slice (sk_2080) (usize 0) (usize 32)) in 
  let h_d_2082 : serialized_scalar_t :=
    array_from_slice (default : uint8) (32) (array_to_seq (h_2081)) (usize 32) (
      usize 32) in 
  let s_2083 : serialized_scalar_t :=
    array_from_slice (default : uint8) (32) (array_to_seq (h_2081)) (usize 0) (
      usize 32) in 
  let s_2083 :=
    array_upd s_2083 (usize 0) ((array_index (s_2083) (usize 0)) .& (secret (
          @repr WORDSIZE8 248) : int8)) in 
  let s_2083 :=
    array_upd s_2083 (usize 31) ((array_index (s_2083) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  let s_2083 :=
    array_upd s_2083 (usize 31) ((array_index (s_2083) (usize 31)) .| (secret (
          @repr WORDSIZE8 64) : int8)) in 
  (s_2083, h_d_2082).


Definition secret_to_public (sk_2084 : secret_key_t)  : public_key_t :=
  let '(s_2085, _) :=
    secret_expand (sk_2084) in 
  let base_2086 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let ss_2087 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (s_2085)) : scalar_t in 
  let a_2088 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_mul (ss_2087) (base_2086) in 
  compress (a_2088).


Definition check_canonical_scalar (s_2089 : serialized_scalar_t)  : bool :=
  (if ((uint8_declassify ((array_index (s_2089) (usize 31)) .& (secret (
              @repr WORDSIZE8 224) : int8))) !=.? (
        @repr WORDSIZE8 0)):bool then (false) else ((nat_mod_from_byte_seq_le (
          array_to_seq (s_2089)) : big_integer_t) <.? (
        nat_mod_from_byte_seq_le (
          array_to_seq (constant_l_v)) : big_integer_t))).


