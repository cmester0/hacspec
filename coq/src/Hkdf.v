(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Hmac.

Require Import Hacspec.Lib.

Require Import Hacspec.Sha256.

Definition hash_len_v : uint_size :=
  (usize 256) / (usize 8).

Inductive hkdf_error_t :=
| InvalidOutputLength : hkdf_error_t.

Notation "'hkdf_byte_seq_result_t'" := ((
  result byte_seq hkdf_error_t)) : hacspec_scope.

Definition extract (salt_0 : byte_seq) (ikm_1 : byte_seq) : prk_t :=
  let salt_or_zero_2 : seq uint8 :=
    seq_new_ (default) (hash_len_v) in 
  let '(salt_or_zero_2) :=
    if (seq_len (salt_0)) >.? (usize 0):bool then (let salt_or_zero_2 :=
        seq_from_seq (salt_0) in 
      (salt_or_zero_2)) else ((salt_or_zero_2)) in 
  array_from_seq (_) (hmac (salt_or_zero_2) (ikm_1)).

Definition build_hmac_txt
  (t_3 : byte_seq)
  (info_4 : byte_seq)
  (iteration_5 : uint8)
  : byte_seq :=
  let out_6 : seq uint8 :=
    seq_new_ (default) (((seq_len (t_3)) + (seq_len (info_4))) + (usize 1)) in 
  let out_6 :=
    seq_update (out_6) (usize 0) (t_3) in 
  let out_6 :=
    seq_update (out_6) (seq_len (t_3)) (info_4) in 
  let out_6 :=
    seq_upd out_6 ((seq_len (t_3)) + (seq_len (info_4))) (iteration_5) in 
  out_6.

Definition div_ceil (a_7 : uint_size) (b_8 : uint_size) : uint_size :=
  let q_9 : uint_size :=
    (a_7) / (b_8) in 
  let '(q_9) :=
    if ((a_7) %% (b_8)) !=.? (usize 0):bool then (let q_9 :=
        (q_9) + (usize 1) in 
      (q_9)) else ((q_9)) in 
  q_9.

Definition check_output_limit
  (l_10 : uint_size)
  : (result uint_size hkdf_error_t) :=
  let n_11 : uint_size :=
    div_ceil (l_10) (hash_len_v) in 
  (if ((n_11) <=.? (usize 255)):bool then (@Ok uint_size hkdf_error_t (
        n_11)) else (@Err uint_size hkdf_error_t (InvalidOutputLength))).

Definition expand
  (prk_12 : byte_seq)
  (info_13 : byte_seq)
  (l_14 : uint_size)
  : hkdf_byte_seq_result_t :=
  result_bind (check_output_limit (l_14)) (fun n_15 => let t_i_16 : prk_t :=
      array_new_ (default) (_) in 
    let t_17 : seq uint8 :=
      seq_new_ (default) ((n_15) * (hash_size_v)) in 
    let '(t_i_16, t_17) :=
      foldi (usize 0) (n_15) (fun i_18 '(t_i_16, t_17) =>
        let hmac_txt_in_19 : seq uint8 :=
          (if ((i_18) =.? (usize 0)):bool then (build_hmac_txt (seq_new_ (
                  default) (usize 0)) (info_13) (secret ((pub_u8 (i_18)) .+ (
                    @repr WORDSIZE8 1)) : int8)) else (build_hmac_txt (
                seq_from_seq (t_i_16)) (info_13) (secret ((pub_u8 (i_18)) .+ (
                    @repr WORDSIZE8 1)) : int8))) in 
        let t_i_16 :=
          hmac (prk_12) (hmac_txt_in_19) in 
        let t_17 :=
          seq_update (t_17) ((i_18) * (array_len (t_i_16))) (t_i_16) in 
        (t_i_16, t_17))
      (t_i_16, t_17) in 
    @Ok byte_seq hkdf_error_t (seq_slice (t_17) (usize 0) (l_14))).

