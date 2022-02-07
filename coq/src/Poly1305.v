(** This file was automatically generated using Hacspec **)
From Coq Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra ssreflect seq tuple ssrnat.
Set Warnings "-ambiguous-paths,-notation-overridden,-notation-incompatible-format".
From extructures Require Import ord fset fmap.
From Crypt Require Import RulesStateProb Package Prelude.
Import PackageNotation.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.


Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.

From mathcomp Require Import fingroup.fingroup.

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.

Require Import Hacspec.Lib.






Remark poly_key_t_nat : forall n, n mod (@modulus WORDSIZE32) = n -> nseq uint8 (usize n) = nseq_nat uint8 (Z.to_nat n).
Proof.
  intros n H.
  unfold nseq.
  (* unfold nseq_nat. *)
  unfold usize.
  unfold from_uint_size.
  unfold nat_uint_sizable.
  unfold Z_uint_sizable.
  rewrite unsigned_repr_id.
  reflexivity.
Qed.

Definition poly_key_t := nseq (uint8) (usize 32).
Definition of_poly_key_t : poly_key_t -> nseq_nat uint8 32.
  intros.
  assert (32%nat = Z.to_nat 32) by reflexivity.
  rewrite H.
  rewrite <- (poly_key_t_nat) by reflexivity.
  apply X.
Qed.

Definition blocksize_v : uint_size :=
   (usize 16).

Definition poly_block_t := nseq (uint8) (usize 16).

Definition poly1305_tag_t := nseq_nat (uint8) ((* usize *) 16).

Notation "'sub_block_t'" := (byte_seq) : hacspec_scope.

Notation "'block_index_t'" := (uint_size) : hacspec_scope.

Definition field_canvas_t := nseq_nat (int8) ((* usize *) 17).
Definition field_element_t := 'fin 0x03fffffffffffffffffffffffffffffffb.

Notation "'poly_state_t'" := ((
  field_element_t '×
  field_element_t '×
  poly_key_t
)) : hacspec_scope.


(* Compute @repr WORDSIZE128 21267647620597763993911028882763415551. *)

(* Global Coercion nseq_nat_to_nseq {T n} (v : nseq_nat T n) : nseq T (usize n). *)
(* Proof. *)
(*   unfold nseq. *)
(*   cbn. *)
(*   unfold unsigned. *)
(*   unfold repr. *)
(*   do 2 rewrite Nat2Z.id. *)
(*   unfold inord. *)

Remark asdf : exists n, poly_block_t = nseq_nat uint8 n.
Proof.
  unfold poly_block_t.
  unfold nseq.

  assert (from_uint_size (usize 16) = 16).
  2 : {
    rewrite H.
    exists (16%nat).
    reflexivity.
  }.
  
  unfold usize.
  unfold from_uint_size.
  unfold Z_uint_sizable.
  
  apply unsigned_repr_id.
Qed.
   
Program Definition temp (b_0 : poly_block_t) :=
  let n_1 : uint128 :=
    uint128_from_le_bytes ((* array_from_seq (16) *) b_0) in 
  n_1.

Definition poly1305_encode_r (b_0 : poly_block_t) : field_element_t :=
  let n_1 : uint128 :=
    uint128_from_le_bytes ((* array_from_seq (16) *) (b_0)) in 
  let n_1 :=
    (n_1) .& (secret (
        @Lib.repr WORDSIZE128 21267647620597763993911028882763415551) : int128) in 
   (chFin_from_secret_literal (n_1)).

Definition poly1305_encode_block (b_2 : poly_block_t) : field_element_t :=
  let n_3 : uint128 :=
    uint128_from_le_bytes ((* array_from_seq (16) *) (b_2)) in 
  let f_4 : field_element_t :=
    chFin_from_secret_literal (n_3) in 
   ((f_4) +% (chFin_pow2 (0x03fffffffffffffffffffffffffffffffb) (
        (* usize *) 128) : field_element_t)).

Definition poly1305_encode_last
  (pad_len_5 : block_index_t)
  (b_6 : sub_block_t) : field_element_t :=
  let n_7 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default) (16) (b_6) ((* usize *) 0) (seq_len (b_6))) in 
  let f_8 : field_element_t :=
    chFin_from_secret_literal (n_7) in 
   ((f_8) +% (chFin_pow2 (0x03fffffffffffffffffffffffffffffffb) (((* usize *) 8) * (
          from_uint_size (pad_len_5))) : field_element_t)).

Definition poly1305_init (k_9 : poly_key_t) : poly_state_t :=
  let r_10 : field_element_t :=
    poly1305_encode_r (array_from_slice (default) (16) (seq_from_array k_9) ((* usize *) 0) (
        (* usize *) 16)) in 
   ((chFin_zero , r_10, k_9)).

Definition poly1305_update_block
  (b_11 : poly_block_t)
  (st_12 : poly_state_t) : poly_state_t :=
  let '(acc_13, r_14, k_15) :=
    st_12 in 
   ((((poly1305_encode_block (b_11)) +% (acc_13)) *% (r_14), r_14, k_15)).

Definition poly1305_update_blocks
  (m_16 : byte_seq)
  (st_17 : poly_state_t) : poly_state_t :=
  let st_18 : (field_element_t '× field_element_t '× poly_key_t) :=
    st_17 in 
  let n_blocks_19 : uint_size :=
    usize ((seq_len (m_16)) / (from_uint_size blocksize_v)) in 
  let st_18 :=
    foldi (usize 0) (n_blocks_19) (fun i_20 st_18 =>
      let block_21 : poly_block_t :=
        array_from_seq (16) (seq_get_exact_chunk (m_16) (blocksize_v) (
            i_20)) in 
      let st_18 :=
        poly1305_update_block (block_21) (st_18) in 
       ((st_18)))
    st_18 in 
   (st_18).

Definition poly1305_update_last
  (pad_len_22 : uint_size)
  (b_23 : sub_block_t)
  (st_24 : poly_state_t) : poly_state_t :=
  let st_25 : (field_element_t '× field_element_t '× poly_key_t) :=
    st_24 in 
  let '(st_25) :=
    if (seq_len (b_23)) !=.? ((* usize *) 0%N):bool then (let '(acc_26, r_27, k_28) :=
        st_25 in 
      let st_25 :=
        (
          ((poly1305_encode_last (pad_len_22) (b_23)) +% (acc_26)) *% (r_27),
          r_27,
          k_28
        ) in 
       ((st_25))) else ( ((st_25))) in 
   (st_25).

Definition poly1305_update
  (m_29 : byte_seq)
  (st_30 : poly_state_t) : poly_state_t :=
  let st_31 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_update_blocks (m_29) (st_30) in 
  let last_32 : seq uint8 :=
    seq_get_remainder_chunk (m_29) (blocksize_v) in 
   (poly1305_update_last (usize (seq_len (last_32))) (last_32) (st_31)).

Definition poly1305_finish (st_33 : poly_state_t) : poly1305_tag_t.
Proof.
  destruct st_33 as [[acc_34 _] k_35].
  apply ((*   let '(a, k_35) := st_33 in *)
  (* let (acc_34, _) := a in *)
  (* let '(acc_34, _, k_35) := *)
  (*   st_33 in  *)
  let n_36 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default) (16) (seq_from_array k_35) ((* usize *) 16) ((* usize *) 16)) in 
  let aby_37 : seq uint8 :=
    chFin_to_byte_seq_le (acc_34) in 
  let a_38 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default) (16) (aby_37) ((* usize *) 0) (
        (* usize *) 16)) in 
   ((* array_from_seq (16) *) (uint128_to_le_bytes ((a_38) .+ (n_36))))
).
Defined.

  (* let (a, b) := st_33 in *)
  (* let (a0, _) := b in *)
  (* (* let '(acc_34, _, k_35) := *) *)
  (* (*   st_33 in  *) *)
  (* let n_36 : uint128 := *)
  (*   uint128_from_le_bytes (array_from_slice (default) (16) (seq_from_array k_35) ((* usize *) 16) ((* usize *) 16)) in  *)
  (* let aby_37 : seq uint8 := *)
  (*   chFin_to_byte_seq_le (acc_34) in  *)
  (* let a_38 : uint128 := *)
  (*   uint128_from_le_bytes (array_from_slice (default) (16) (aby_37) ((* usize *) 0) ( *)
  (*       (* usize *) 16)) in  *)
  (*  ((* array_from_seq (16) *) (uint128_to_le_bytes ((a_38) .+ (n_36)))). *)

Definition poly1305 (m_39 : byte_seq) (key_40 : poly_key_t) : poly1305_tag_t :=
  let st_41 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_init (key_40) in 
  let st_41 :=
    poly1305_update (m_39) (st_41) in 
   (poly1305_finish (st_41)).

