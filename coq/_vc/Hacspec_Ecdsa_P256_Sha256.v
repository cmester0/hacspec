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

Require Import Hacspec_P256.
Export Hacspec_P256.

Require Import Hacspec_Sha256.
Export Hacspec_Sha256.

Inductive error_t :=
| InvalidScalar : error_t
| InvalidSignature : error_t.

Notation "'p256_public_key_t'" := (affine_t) : hacspec_scope.

Notation "'p256_secret_key_t'" := (p256_scalar_t) : hacspec_scope.

Notation "'p256_signature_t'" := ((p256_scalar_t '× p256_scalar_t
)) : hacspec_scope.

Notation "'p256_signature_result_t'" := ((
  result p256_signature_t error_t)) : hacspec_scope.

Notation "'p256_verify_result_t'" := ((result unit error_t)) : hacspec_scope.

Notation "'check_result_t'" := ((result unit error_t)) : hacspec_scope.

Notation "'arithmetic_result_t'" := ((result affine_t error_t)) : hacspec_scope.

Definition check_scalar_zero (r_377 : p256_scalar_t)  : check_result_t :=
  (if (nat_mod_equal (r_377) (nat_mod_zero )):bool then (@Err unit error_t (
        InvalidScalar)) else (@Ok unit error_t (tt))).


Definition ecdsa_point_mul_base
  (x_378 : p256_scalar_t)
  
  : arithmetic_result_t :=
  match p256_point_mul_base (x_378) with
  | Ok (s_379) => @Ok affine_t error_t (s_379)
  | Err (_) => @Err affine_t error_t (InvalidScalar)
  end.


Definition ecdsa_point_mul
  (k_380 : p256_scalar_t)
  (p_381 : affine_t)
  
  : arithmetic_result_t :=
  match p256_point_mul (k_380) (p_381) with
  | Ok (s_382) => @Ok affine_t error_t (s_382)
  | Err (_) => @Err affine_t error_t (InvalidScalar)
  end.


Definition ecdsa_point_add
  (p_383 : affine_t)
  (q_384 : affine_t)
  
  : arithmetic_result_t :=
  match point_add (p_383) (q_384) with
  | Ok (s_385) => @Ok affine_t error_t (s_385)
  | Err (_) => @Err affine_t error_t (InvalidScalar)
  end.


Definition sign
  (payload_386 : byte_seq)
  (sk_387 : p256_secret_key_t)
  (nonce_388 : p256_scalar_t)
  
  : p256_signature_result_t :=
  bind (check_scalar_zero (nonce_388)) (fun _ => bind (ecdsa_point_mul_base (
        nonce_388)) (fun '(k_x_389, k_y_390) => let r_391 : p256_scalar_t :=
        nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
            k_x_389)) : p256_scalar_t in 
      bind (check_scalar_zero (r_391)) (fun _ =>
        let payload_hash_392 : sha256_digest_t :=
          hash (payload_386) in 
        let payload_hash_393 : p256_scalar_t :=
          nat_mod_from_byte_seq_be (
            array_to_seq (payload_hash_392)) : p256_scalar_t in 
        let rsk_394 : p256_scalar_t :=
          (r_391) *% (sk_387) in 
        let hash_rsk_395 : p256_scalar_t :=
          (payload_hash_393) +% (rsk_394) in 
        let nonce_inv_396 : p256_scalar_t :=
          nat_mod_inv (nonce_388) in 
        let s_397 : p256_scalar_t :=
          (nonce_inv_396) *% (hash_rsk_395) in 
        @Ok p256_signature_t error_t ((r_391, s_397))))).


Definition ecdsa_p256_sha256_sign
  (payload_398 : byte_seq)
  (sk_399 : p256_secret_key_t)
  (nonce_400 : p256_scalar_t)
  
  : p256_signature_result_t :=
  sign (payload_398) (sk_399) (nonce_400).


Definition verify
  (payload_401 : byte_seq)
  (pk_402 : p256_public_key_t)
  (signature_403 : p256_signature_t)
  
  : p256_verify_result_t :=
  let '(r_404, s_405) :=
    signature_403 in 
  let payload_hash_406 : sha256_digest_t :=
    hash (payload_401) in 
  let payload_hash_407 : p256_scalar_t :=
    nat_mod_from_byte_seq_be (
      array_to_seq (payload_hash_406)) : p256_scalar_t in 
  let s_inv_408 : p256_scalar_t :=
    nat_mod_inv (s_405) in 
  let u1_409 : p256_scalar_t :=
    (payload_hash_407) *% (s_inv_408) in 
  bind (ecdsa_point_mul_base (u1_409)) (fun u1_410 =>
    let u2_411 : p256_scalar_t :=
      (r_404) *% (s_inv_408) in 
    bind (ecdsa_point_mul (u2_411) (pk_402)) (fun u2_412 => bind (
        ecdsa_point_add (u1_410) (u2_412)) (fun '(x_413, y_414) =>
        let x_415 : p256_scalar_t :=
          nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
              x_413)) : p256_scalar_t in 
        (if ((x_415) =.? (r_404)):bool then (@Ok unit error_t (tt)) else (
            @Err unit error_t (InvalidSignature)))))).


Definition ecdsa_p256_sha256_verify
  (payload_416 : byte_seq)
  (pk_417 : p256_public_key_t)
  (signature_418 : p256_signature_t)
  
  : p256_verify_result_t :=
  verify (payload_416) (pk_417) (signature_418).


