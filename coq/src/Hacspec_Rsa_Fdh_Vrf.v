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

Require Import Hacspec_Sha256.
Export Hacspec_Sha256.

Require Import Hacspec_Rsa_Pkcs1.
Export Hacspec_Rsa_Pkcs1.

Definition int_byte_t := nseq (uint8) (usize 1).

Definition one_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 1) : int8] in  l).

Definition two_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 2) : int8] in  l).

Definition suite_string_v : int_byte_t :=
  one_v.

Definition vrf_mgf1
  (n_2494 : rsa_int_t)
  (alpha_2495 : byte_seq)
  
  : byte_seq_result_t :=
  bind (i2osp (rsa_int_from_literal (@cast _ uint128 _ (byte_size_v))) (
      @repr WORDSIZE32 (4))) (fun mgf_salt1_2496 => bind (i2osp (n_2494) (
        byte_size_v)) (fun mgf_salt2_2497 => let mgf_salt_2498 : seq uint8 :=
        seq_concat (mgf_salt1_2496) (mgf_salt2_2497) in 
      let mgf_string_2499 : seq uint8 :=
        seq_concat (seq_concat (array_concat (suite_string_v) (
              array_to_seq (one_v))) (mgf_salt_2498)) (alpha_2495) in 
      bind (mgf1 (mgf_string_2499) ((@cast _ uint32 _ (byte_size_v)) - (
            usize 1))) (fun mgf_2500 => @Ok seq uint8 error_t (mgf_2500)))).


Definition prove
  (sk_2501 : sk_t)
  (alpha_2502 : byte_seq)
  
  : byte_seq_result_t :=
  let '(n_2503, d_2504) :=
    (sk_2501) in 
  bind (vrf_mgf1 (n_2503) (alpha_2502)) (fun em_2505 =>
    let m_2506 : rsa_int_t :=
      os2ip (em_2505) in 
    bind (rsasp1 (sk_2501) (m_2506)) (fun s_2507 => i2osp (s_2507) (
        byte_size_v))).


Definition proof_to_hash (pi_string_2508 : byte_seq)  : byte_seq_result_t :=
  let hash_string_2509 : seq uint8 :=
    array_concat (suite_string_v) (array_concat (two_v) (pi_string_2508)) in 
  @Ok seq uint8 error_t (array_slice (sha256 (hash_string_2509)) (usize 0) (
      usize 32)).


Definition verify
  (pk_2510 : pk_t)
  (alpha_2511 : byte_seq)
  (pi_string_2512 : byte_seq)
  
  : byte_seq_result_t :=
  let '(n_2513, e_2514) :=
    (pk_2510) in 
  let s_2515 : rsa_int_t :=
    os2ip (pi_string_2512) in 
  bind (rsavp1 (pk_2510) (s_2515)) (fun m_2516 => bind (vrf_mgf1 (n_2513) (
        alpha_2511)) (fun em_prime_2517 => let m_prime_2518 : rsa_int_t :=
        os2ip (em_prime_2517) in 
      (if ((m_2516) =.? (m_prime_2518)):bool then (proof_to_hash (
            pi_string_2512)) else (@Err seq uint8 error_t (
            VerificationFailed))))).


