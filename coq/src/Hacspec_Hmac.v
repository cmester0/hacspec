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

Definition block_len_v : uint_size :=
  k_size_v.

Definition prk_t := nseq (uint8) (hash_size_v).

Definition block_t := nseq (uint8) (block_len_v).

Definition i_pad_v : block_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8
      ] in  l).

Definition o_pad_v : block_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8
      ] in  l).

Definition k_block (k_583 : byte_seq)  : block_t :=
  (if ((seq_len (k_583)) >.? (block_len_v)):bool then (array_update_start (
        array_new_ (default : uint8) (block_len_v)) (array_to_seq (hash (
          k_583)))) else (array_update_start (array_new_ (default : uint8) (
          block_len_v)) (k_583))).


Definition hmac (k_584 : byte_seq) (txt_585 : byte_seq)  : prk_t :=
  let k_block_586 : block_t :=
    k_block (k_584) in 
  let h_in_587 : seq uint8 :=
    seq_from_seq (array_to_seq ((k_block_586) array_xor (i_pad_v))) in 
  let h_in_587 :=
    seq_concat (h_in_587) (txt_585) in 
  let h_inner_588 : sha256_digest_t :=
    hash (h_in_587) in 
  let h_in_589 : seq uint8 :=
    seq_from_seq (array_to_seq ((k_block_586) array_xor (o_pad_v))) in 
  let h_in_589 :=
    seq_concat (h_in_589) (array_to_seq (h_inner_588)) in 
  array_from_seq (hash_size_v) (array_to_seq (hash (h_in_589))).


