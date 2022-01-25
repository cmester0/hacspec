(** This file was automatically generated using Hacspec **)
From Coq Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_algebra .
From mathcomp Require Import all_ssreflect all_algebra ssreflect seq vector.
Locate seq.
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

Module test.
	Parameter L : {fset Location}.

Require Import Hacspec.Lib.

(* Check mathcomp.ssreflect.seq.nseq. *)

(* (T : choiceType) (s : seq T). *)
(* Check mathcomp.ssreflect.seq.seq. *)

(* Limit ring type to uint8 *)
Definition poly_key_t := nseq int8 (usize 32).
(* Definition poly_key_choice : choiceType := tuple_choiceType 32 usize_choiceType. *)

Definition blocksize_v : code L [interface] uint_size :=
  {code
     ret (usize 16)
  }.

Definition poly_block_t := nseq int8 (usize 16).

Definition poly1305_tag_t := nseq int8 (usize 16).

Notation "'sub_block_t'" := (byte_seq) : hacspec_scope.

Notation "'block_index_t'" := (uint_size) : hacspec_scope.

Definition field_canvas_t := nseq int8 (17).
Definition field_element_t :=
  Fp_finFieldType 0x03fffffffffffffffffffffffffffffffb.

Notation "'poly_state_t'" := ((field_element_t '× field_element_t '× poly_key_t
                             )) : hacspec_scope.
(* Check finFieldType. *)
(* Check poly_state_t. *)

Definition poly1305_encode_r
  (
    b_0 : poly_block_t) : code L [interface] field_element_t :=
  {code
  let n_1 : uint128 :=
    uint128_from_le_bytes (array_from_seq (16) (b_0)) in 
  (* let n_1 := *)
  (*   (n_1) .& (secret ( *)
  (*       @repr WORDSIZE128 21267647620597763993911028882763415551) : int128) in  *)
  ret (finFieldType_from_secret_literal (n_1))
}.

Definition poly1305_encode_block
  (
    b_2 : poly_block_t) : code L [interface] field_element_t :=
  {code
  let n_3 : uint128 :=
    uint128_from_le_bytes (array_from_seq (16) (b_2)) in 
  let f_4 : field_element_t :=
    finFieldType_from_secret_literal (n_3) in 
  ret ((f_4) +% (finFieldType_pow2 (0x03fffffffffffffffffffffffffffffffb) (
        usize 128) : field_element_t))
}.

Definition poly1305_encode_last
  (pad_len_5 : block_index_t)
  (
    b_6 : sub_block_t) : code L [interface] field_element_t :=
  {code
  let n_7 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default) (16) (b_6) (usize 0) (
        seq_len (b_6))) in 
  let f_8 : field_element_t :=
    finFieldType_from_secret_literal (n_7) in 
  ret ((f_8) +% (finFieldType_pow2 (0x03fffffffffffffffffffffffffffffffb) ((
          usize 8) * (pad_len_5)) : field_element_t))
}.

Definition poly1305_init
  (k_9 : poly_key_t) : code L [interface] (prod_choiceType (prod_choiceType field_element_t field_element_t) (poly_key_t)) :=
  {code
  r_10 ← poly1305_encode_r (array_from_slice (default) (usize 16) (k_9) (usize 0) (
        usize 16)) ;;
  ret ((finFieldType_zero, finFieldType_zero (* r_10 *) , k_9))  (* *)
}.

Definition poly1305_update_block
  (b_11 : poly_block_t)
  (
    st_12 : poly_state_t) : code L [interface] poly_state_t :=
  {code
  let '(acc_13, r_14, k_15) :=
    st_12 in
  temp ← (poly1305_encode_block (b_11)) ;;
  ret (((temp +% (acc_13)) *% (r_14), r_14, k_15))
}.

Notation "'foldibnd' s 'to' e 'for' z '>>' f" := (foldi s e (fun x y => bind y (f x)) (ret z)) (at level 50).
  

Definition poly1305_update_blocks
  (m_16 : byte_seq)
  (
    st_17 : poly_state_t) : code L [interface] poly_state_t :=
  {code
  let st_18 : (field_element_t '× field_element_t '× poly_key_t) :=
    st_17 in
  temp ← blocksize_v ;;
  let n_blocks_19 : uint_size :=
    @usize Z Z_uint_sizable ((seq_len (m_16)) / (temp)) in

  (* TODO , Turn into for loop over (@usize Z Z_uint_sizable 0) to (n_blocks_19) *)
  let block_21 : poly_block_t :=
    @array_from_seq _ (int_default) (usize 16) (seq_get_exact_chunk (m_16) (temp) (usize 0) (* <- should be indexed by for loop *)) in
  st_18 ← poly1305_update_block (block_21) st_18 ;;
  ret ((st_18))
  (* END TODO *)    
}.

Definition poly1305_update_last
  (pad_len_22 : uint_size)
  (b_23 : sub_block_t)
  (
    st_24 : poly_state_t) : code L [interface] poly_state_t :=
  {code
  let st_25 : (field_element_t '× field_element_t '× poly_key_t) :=
    st_24 in 
  let '(st_25) :=
    if (seq_len (b_23)) !=.? (usize 0):bool
    then (let '(acc_26, r_27, k_28) :=
            st_25 in
          temp ← (poly1305_encode_last (pad_len_22) (b_23)) ;;
          let st_25 :=
            (
              (temp +% (acc_26)) *% (r_27),
              r_27,
              k_28
            ) in 
          ret ((st_25)))
    else (ret ((st_25)))
  in 
  st_25
}.

Definition poly1305_update
  (m_29 : byte_seq)
  (
    st_30 : poly_state_t) : code L [interface] poly_state_t :=
  {code
   st_31 ← poly1305_update_blocks (m_29) (st_30) ;;
   temp ← blocksize_v ;;
  let last_32 : seq uint8 :=
    seq_get_remainder_chunk (m_29) (temp) in 
  poly1305_update_last (usize (seq_len (last_32))) (last_32) (st_31)
}.

Definition poly1305_finish
  (
    st_33 : poly_state_t) : code L [interface] poly1305_tag_t :=
  {code
  let '(acc_34, _, k_35) :=
    st_33 in
  let n_36 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default) (16) (k_35) (usize 16) (
        usize 16)) in
  let aby_37 : seq uint8 := finFieldType_to_byte_seq_le (acc_34) in
  let a_38 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default) (16) (aby_37) (usize 0) (
        usize 16)) in
  ret (array_from_seq (usize 16) (uint128_to_le_bytes ((a_38) .+ (n_36))))
}.

Definition poly1305
  (m_39 : byte_seq)
  (
    key_40 : poly_key_t) : code L [interface] poly1305_tag_t :=
  {code
  st_41 ← poly1305_init (key_40) ;;
  st_41 ← poly1305_update (m_39) (st_41) ;;
  poly1305_finish (st_41)
}.

