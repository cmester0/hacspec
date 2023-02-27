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

Definition field_canvas_t := nseq (int8) (32).
Definition x25519_field_element_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition scalar_canvas_t := nseq (int8) (32).
Definition scalar_t :=
  nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000.

Notation "'point_t'" := ((x25519_field_element_t '× x25519_field_element_t
)) : hacspec_scope.

Definition x25519_serialized_point_t := nseq (uint8) (usize 32).

Definition x25519_serialized_scalar_t := nseq (uint8) (usize 32).

Definition mask_scalar
  (s_327 : x25519_serialized_scalar_t)
  
  : x25519_serialized_scalar_t :=
  let k_328 : x25519_serialized_scalar_t :=
    s_327 in 
  let k_328 :=
    array_upd k_328 (usize 0) ((array_index (k_328) (usize 0)) .& (secret (
          @repr WORDSIZE8 248) : int8)) in 
  let k_328 :=
    array_upd k_328 (usize 31) ((array_index (k_328) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  let k_328 :=
    array_upd k_328 (usize 31) ((array_index (k_328) (usize 31)) .| (secret (
          @repr WORDSIZE8 64) : int8)) in 
  k_328.


Definition decode_scalar (s_329 : x25519_serialized_scalar_t)  : scalar_t :=
  let k_330 : x25519_serialized_scalar_t :=
    mask_scalar (s_329) in 
  nat_mod_from_byte_seq_le (array_to_seq (k_330)) : scalar_t.


Definition decode_point (u_331 : x25519_serialized_point_t)  : point_t :=
  let u_332 : x25519_serialized_point_t :=
    u_331 in 
  let u_332 :=
    array_upd u_332 (usize 31) ((array_index (u_332) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  (
    nat_mod_from_byte_seq_le (array_to_seq (u_332)) : x25519_field_element_t,
    nat_mod_from_literal (
      0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
      @repr WORDSIZE128 1) : x25519_field_element_t
  ).


Definition encode_point (p_333 : point_t)  : x25519_serialized_point_t :=
  let '(x_334, y_335) :=
    p_333 in 
  let b_336 : x25519_field_element_t :=
    (x_334) *% (nat_mod_inv (y_335)) in 
  array_update_start (array_new_ (default : uint8) (32)) (
    nat_mod_to_byte_seq_le (b_336)).


Definition point_add_and_double
  (q_337 : point_t)
  (np_338 : (point_t '× point_t))
  
  : (point_t '× point_t) :=
  let '(nq_339, nqp1_340) :=
    np_338 in 
  let '(x_1_341, z_1_342) :=
    q_337 in 
  let '(x_2_343, z_2_344) :=
    nq_339 in 
  let '(x_3_345, z_3_346) :=
    nqp1_340 in 
  let a_347 : x25519_field_element_t :=
    (x_2_343) +% (z_2_344) in 
  let aa_348 : x25519_field_element_t :=
    nat_mod_pow (a_347) (@repr WORDSIZE128 2) in 
  let b_349 : x25519_field_element_t :=
    (x_2_343) -% (z_2_344) in 
  let bb_350 : x25519_field_element_t :=
    (b_349) *% (b_349) in 
  let e_351 : x25519_field_element_t :=
    (aa_348) -% (bb_350) in 
  let c_352 : x25519_field_element_t :=
    (x_3_345) +% (z_3_346) in 
  let d_353 : x25519_field_element_t :=
    (x_3_345) -% (z_3_346) in 
  let da_354 : x25519_field_element_t :=
    (d_353) *% (a_347) in 
  let cb_355 : x25519_field_element_t :=
    (c_352) *% (b_349) in 
  let x_3_356 : x25519_field_element_t :=
    nat_mod_pow ((da_354) +% (cb_355)) (@repr WORDSIZE128 2) in 
  let z_3_357 : x25519_field_element_t :=
    (x_1_341) *% (nat_mod_pow ((da_354) -% (cb_355)) (@repr WORDSIZE128 2)) in 
  let x_2_358 : x25519_field_element_t :=
    (aa_348) *% (bb_350) in 
  let e121665_359 : x25519_field_element_t :=
    nat_mod_from_literal (
      0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
      @repr WORDSIZE128 121665) : x25519_field_element_t in 
  let z_2_360 : x25519_field_element_t :=
    (e_351) *% ((aa_348) +% ((e121665_359) *% (e_351))) in 
  ((x_2_358, z_2_360), (x_3_356, z_3_357)).


Definition swap (x_361 : (point_t '× point_t))  : (point_t '× point_t) :=
  let '(x0_362, x1_363) :=
    x_361 in 
  (x1_363, x0_362).


Definition montgomery_ladder
  (k_364 : scalar_t)
  (init_365 : point_t)
  
  : point_t :=
  let inf_366 : (x25519_field_element_t '× x25519_field_element_t) :=
    (
      nat_mod_from_literal (
        0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
        @repr WORDSIZE128 1) : x25519_field_element_t,
      nat_mod_from_literal (
        0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
        @repr WORDSIZE128 0) : x25519_field_element_t
    ) in 
  let acc_367 : (point_t '× point_t) :=
    (inf_366, init_365) in 
  let acc_367 :=
    foldi (usize 0) (usize 256) (fun i_368 acc_367 =>
      let '(acc_367) :=
        if nat_mod_bit (k_364) ((usize 255) - (i_368)):bool then (let acc_367 :=
            swap (acc_367) in 
          let acc_367 :=
            point_add_and_double (init_365) (acc_367) in 
          let acc_367 :=
            swap (acc_367) in 
          (acc_367)) else (let acc_367 :=
            point_add_and_double (init_365) (acc_367) in 
          (acc_367)) in 
      (acc_367))
    acc_367 in 
  let '(out_369, _) :=
    acc_367 in 
  out_369.


Definition x25519_scalarmult
  (s_370 : x25519_serialized_scalar_t)
  (p_371 : x25519_serialized_point_t)
  
  : x25519_serialized_point_t :=
  let s_372 : scalar_t :=
    decode_scalar (s_370) in 
  let p_373 : (x25519_field_element_t '× x25519_field_element_t) :=
    decode_point (p_371) in 
  let r_374 : (x25519_field_element_t '× x25519_field_element_t) :=
    montgomery_ladder (s_372) (p_373) in 
  encode_point (r_374).


Definition x25519_secret_to_public
  (s_375 : x25519_serialized_scalar_t)
  
  : x25519_serialized_point_t :=
  let base_376 : x25519_serialized_point_t :=
    array_new_ (default : uint8) (32) in 
  let base_376 :=
    array_upd base_376 (usize 0) (secret (@repr WORDSIZE8 9) : int8) in 
  x25519_scalarmult (s_375) (base_376).


