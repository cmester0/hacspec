(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Hmac.
Export Hacspec_Hmac.

Require Import Hacspec_Lib.
Export Hacspec_Lib.

Require Import Hacspec_Sha256.
Export Hacspec_Sha256.

Definition hash_len_v : uint_size :=
  (usize 256) / (usize 8).

Inductive hkdf_error_t :=
| InvalidOutputLength : hkdf_error_t.

Notation "'hkdf_byte_seq_result_t'" := ((
  result byte_seq hkdf_error_t)) : hacspec_scope.

Definition extract (salt_563 : byte_seq) (ikm_564 : byte_seq)  : prk_t :=
  let salt_or_zero_565 : seq uint8 :=
    seq_new_ (default : uint8) (hash_len_v) in 
  let '(salt_or_zero_565) :=
    if (seq_len (salt_563)) >.? (usize 0):bool then (let salt_or_zero_565 :=
        seq_from_seq (salt_563) in 
      (salt_or_zero_565)) else ((salt_or_zero_565)) in 
  array_from_seq (_) (array_to_seq (hmac (salt_or_zero_565) (ikm_564))).


Definition build_hmac_txt
  (t_566 : byte_seq)
  (info_567 : byte_seq)
  (iteration_568 : uint8)
  
  : byte_seq :=
  let out_569 : seq uint8 :=
    seq_new_ (default : uint8) (((seq_len (t_566)) + (seq_len (info_567))) + (
        usize 1)) in 
  let out_569 :=
    seq_update (out_569) (usize 0) (t_566) in 
  let out_569 :=
    seq_update (out_569) (seq_len (t_566)) (info_567) in 
  let out_569 :=
    seq_upd out_569 ((seq_len (t_566)) + (seq_len (info_567))) (
      iteration_568) in 
  out_569.


Definition div_ceil (a_570 : uint_size) (b_571 : uint_size)  : uint_size :=
  let q_572 : uint_size :=
    (a_570) / (b_571) in 
  let '(q_572) :=
    if ((a_570) %% (b_571)) !=.? (usize 0):bool then (let q_572 :=
        (q_572) + (usize 1) in 
      (q_572)) else ((q_572)) in 
  q_572.


Definition check_output_limit
  (l_573 : uint_size)
  
  : (result uint_size hkdf_error_t) :=
  let n_574 : uint_size :=
    div_ceil (l_573) (hash_len_v) in 
  (if ((n_574) <=.? (usize 255)):bool then (@Ok uint_size hkdf_error_t (
        n_574)) else (@Err uint_size hkdf_error_t (InvalidOutputLength))).


Definition expand
  (prk_575 : byte_seq)
  (info_576 : byte_seq)
  (l_577 : uint_size)
  
  : hkdf_byte_seq_result_t :=
  bind (check_output_limit (l_577)) (fun n_578 => let t_i_579 : prk_t :=
      array_new_ (default : uint8) (_) in 
    let t_580 : seq uint8 :=
      seq_new_ (default : uint8) ((n_578) * (hash_size_v)) in 
    let '(t_i_579, t_580) :=
      foldi (usize 0) (n_578) (fun i_581 '(t_i_579, t_580) =>
        let hmac_txt_in_582 : seq uint8 :=
          (if ((i_581) =.? (usize 0)):bool then (build_hmac_txt (seq_new_ (
                  default : uint8) (usize 0)) (info_576) (secret ((pub_u8 (
                      i_581)) .+ (@repr WORDSIZE8 1)) : int8)) else (
              build_hmac_txt (seq_from_seq (array_to_seq (t_i_579))) (
                info_576) (secret ((pub_u8 (i_581)) .+ (
                    @repr WORDSIZE8 1)) : int8))) in 
        let t_i_579 :=
          hmac (prk_575) (hmac_txt_in_582) in 
        let t_580 :=
          seq_update (t_580) ((i_581) * (array_len (t_i_579))) (
            array_to_seq (t_i_579)) in 
        (t_i_579, t_580))
      (t_i_579, t_580) in 
    @Ok byte_seq hkdf_error_t (seq_slice (t_580) (usize 0) (l_577))).


