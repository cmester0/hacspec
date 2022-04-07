(** This file was automatically generated using Hacspec **)
(* From mathcomp Require Import choice fintype. *)
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From CoqWord Require Import ssrZ word.
From Jasmin Require Import word.
Require Import ChoiceEquality
.
Require Import Hacspec_Lib.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.


Obligation Tactic :=
(intros ; do 2 ssprove_valid'_2) ||
(try (Tactics.program_simpl; fail); simpl). (* Old Obligation Tactic *)

Require Import Hacspec_Lib.

Definition poly_key_t := nseq (uint8) (usize 32).

Definition blocksize_v : uint_size :=
  (usize 16).

Definition poly_block_t := nseq (uint8) (usize 16).

Definition poly1305_tag_t := nseq (uint8) (usize 16).

Notation "'sub_block_t'" := (byte_seq) : hacspec_scope.

Notation "'block_index_t'" := (uint_size) : hacspec_scope.

Definition field_canvas_t := nseq (int8) (17).
Definition field_element_t := nat_mod 0x03fffffffffffffffffffffffffffffffb.

Notation "'poly_state_t'" := ((
  field_element_t '×
  field_element_t '×
  poly_key_t
)) : hacspec_scope.

Definition n_3_loc : Location :=
  (@ct uint128 ; 7%nat).
Program Definition poly1305_encode_r
  (b_0 : poly_block_t)
  : code (fset (path.sort leb [ n_3_loc])) [interface] (@ct (
      field_element_t)) :=
  ({code
     temp_1 ←
      (array_from_seq (16) (array_to_seq (b_0))) ;;
     temp_2 ←
      (uint128_from_le_bytes (temp_1)) ;;
    #put n_3_loc := 
      (temp_2) ;;
    n_3 ← get n_3_loc ;;
     temp_4 ←
      (secret (@repr U128 21267647620597763993911028882763415551)) ;;
    n_3 ← get n_3_loc ;;
    #put n_3_loc := 
      ((n_3) .& (temp_4)) ;;
    n_3 ← get n_3_loc ;;
     temp_5 ←
      (nat_mod_from_secret_literal (n_3)) ;;
    @pkg_core_definition.ret field_element_t ( (temp_5))
    } : code ((fset (path.sort leb [ n_3_loc]))) [interface] _).


Program Definition poly1305_encode_block
  (b_8 : poly_block_t)
  : code fset.fset0 [interface] (@ct (field_element_t)) :=
  ({code
     temp_9 ←
      (array_from_seq (16) (array_to_seq (b_8))) ;;
     temp_10 ←
      (uint128_from_le_bytes (temp_9)) ;;
    let n_11 : uint128 :=
      (temp_10) in
    
     temp_12 ←
      (nat_mod_from_secret_literal (n_11)) ;;
    let f_13 : field_element_t :=
      (temp_12) in
    
     temp_14 ←
      (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (usize 128)) ;;
    @pkg_core_definition.ret field_element_t ( ((f_13) +% (temp_14)))
    } : code (fset.fset0) [interface] _).


Program Definition poly1305_encode_last
  (pad_len_22 : block_index_t)
  (b_15 : sub_block_t)
  : code fset.fset0 [interface] (@ct (field_element_t)) :=
  ({code
     temp_16 ←
      (seq_len (b_15)) ;;
     temp_17 ←
      (array_from_slice (default) (16) (b_15) (usize 0) (temp_16)) ;;
     temp_18 ←
      (uint128_from_le_bytes (temp_17)) ;;
    let n_19 : uint128 :=
      (temp_18) in
    
     temp_20 ←
      (nat_mod_from_secret_literal (n_19)) ;;
    let f_21 : field_element_t :=
      (temp_20) in
    
     temp_23 ←
      (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) * (
            pad_len_22))) ;;
    @pkg_core_definition.ret field_element_t ( ((f_21) +% (temp_23)))
    } : code (fset.fset0) [interface] _).


Program Definition poly1305_init
  (k_24 : poly_key_t)
  : code (fset (path.sort leb [ n_3_loc])) [interface] (@ct (poly_state_t)) :=
  ({code
     temp_25 ←
      (array_from_slice (default) (16) (array_to_seq (k_24)) (usize 0) (
          usize 16)) ;;
     temp_26 ←
      (poly1305_encode_r (temp_25)) ;;
    let r_28 : field_element_t :=
      (temp_26) in
    
     temp_27 ←
      (nat_mod_zero ) ;;
    @pkg_core_definition.ret (field_element_t '× field_element_t '× poly_key_t
    ) ( ((temp_27, r_28, k_24)))
    } : code ((fset (path.sort leb [ n_3_loc]))) [interface] _).


Program Definition poly1305_update_block
  (b_30 : poly_block_t)
  (st_29 : poly_state_t)
  : code fset.fset0 [interface] (@ct (poly_state_t)) :=
  ({code
    let '(acc_32, r_33, k_34) :=
      (st_29) in
    
     temp_31 ←
      (poly1305_encode_block (b_30)) ;;
    @pkg_core_definition.ret (field_element_t '× field_element_t '× poly_key_t
    ) ( ((((temp_31) +% (acc_32)) *% (r_33), r_33, k_34)))
    } : code (fset.fset0) [interface] _).

Definition st_43_loc : Location :=
  (@ct (field_element_t '× field_element_t '× poly_key_t) ; 47%nat).
Program Definition poly1305_update_blocks
  (m_36 : byte_seq)
  (st_35 : poly_state_t)
  : code (fset (path.sort leb [ st_43_loc])) [interface] (@ct (poly_state_t)) :=
  ({code
    #put st_43_loc := 
      (st_35) ;;
    st_43 ← get st_43_loc ;;
     temp_37 ←
      (seq_len (m_36)) ;;
    let n_blocks_38 : uint_size :=
      ((temp_37) / (blocksize_v) : uint_size_type) in
    
     st_43 ←
      (foldi (usize 0) (n_blocks_38) (fun i_39 st_43 =>
          {code
           temp_40 ←
           (seq_get_exact_chunk (m_36) ( (blocksize_v)) ( (i_39))) ;;
           temp_41 ←
            (array_from_seq (16) (temp_40 : seq int8)) ;;
          let block_42 : poly_block_t :=
            (temp_41) in
          
           temp_44 ←
            (poly1305_update_block (block_42) (st_43)) ;;
          st_43 ← get st_43_loc ;;
          #put st_43_loc := 
            (temp_44) ;;
          st_43 ← get st_43_loc ;;
          @pkg_core_definition.ret _ ( ((st_43)))
          } : code ((fset (path.sort leb [ st_43_loc]))) [interface] _)
        st_43) ;;
    
    @pkg_core_definition.ret (field_element_t '× field_element_t '× poly_key_t
    ) ( (st_43))
    } : code ((fset (path.sort leb [ st_43_loc]))) [interface] _).

Definition st_49_loc : Location :=
  (@ct (field_element_t '× field_element_t '× poly_key_t) ; 59%nat).
Program Definition poly1305_update_last
  (pad_len_52 : uint_size)
  (b_50 : sub_block_t)
  (st_48 : poly_state_t)
  : code (fset (path.sort leb [ st_49_loc])) [interface] (@ct (poly_state_t)) :=
  ({code
    #put st_49_loc := 
      (st_48) ;;
    st_49 ← get st_49_loc ;;
     temp_51 ←
      (seq_len (b_50)) ;;
     '(st_49) ←
      (if (temp_51) !=.? (usize 0):bool then ({code
          let '(acc_54, r_55, k_56) :=
            (st_49) in
          
           temp_53 ←
            (poly1305_encode_last (pad_len_52) (b_50)) ;;
          st_49 ← get st_49_loc ;;
          #put st_49_loc := 
            ((((temp_53) +% (acc_54)) *% (r_55), r_55, k_56)) ;;
          st_49 ← get st_49_loc ;;
          @pkg_core_definition.ret _ ( ((st_49)))
          } : code ((fset (path.sort leb [ st_49_loc]))) [interface] _) else (
          @pkg_core_definition.ret _ ( ((st_49))))) ;;
    
    @pkg_core_definition.ret (field_element_t '× field_element_t '× poly_key_t
    ) ( (st_49))
    } : code ((fset (path.sort leb [ st_49_loc]))) [interface] _).


Program Definition poly1305_update
  (m_60 : byte_seq)
  (st_61 : poly_state_t)
  : code (fset (path.sort leb [ st_49_loc ; st_43_loc])) [interface] (@ct (
      poly_state_t)) :=
  ({code
     temp_62 ←
      (poly1305_update_blocks (m_60) (st_61)) ;;
    let st_66 : (field_element_t '× field_element_t '× poly_key_t) :=
      (temp_62) in
    
     temp_63 ←
      (seq_get_remainder_chunk (m_60) ( (blocksize_v))) ;;
    let last_64 : seq uint8 :=
      (temp_63) in
    
     temp_65 ←
      (seq_len (last_64)) ;;
     temp_67 ←
      (poly1305_update_last (temp_65 : uint_size_type) (last_64) (st_66)) ;;
    @pkg_core_definition.ret poly_state_t ( (temp_67))
    } : code ((fset (path.sort leb [ st_49_loc ; st_43_loc]))) [interface] _).


Program Definition poly1305_finish
  (st_68 : poly_state_t)
  : code fset.fset0 [interface] (@ct (poly1305_tag_t)) :=
  ({code
    let '(acc_72, _, k_69) :=
      (st_68) in
    
     temp_70 ←
      (array_from_slice (default) (16) (array_to_seq (k_69)) (usize 16) (
          usize 16)) ;;
     temp_71 ←
      (uint128_from_le_bytes (temp_70)) ;;
    let n_78 : uint128 :=
      (temp_71) in
    
     temp_73 ←
      (nat_mod_to_byte_seq_le (acc_72)) ;;
    let aby_74 : seq uint8 :=
      (temp_73) in
    
     temp_75 ←
      (array_from_slice (default) (16) (aby_74) (usize 0) (usize 16)) ;;
     temp_76 ←
      (uint128_from_le_bytes (temp_75)) ;;
    let a_77 : uint128 :=
      (temp_76) in
    
     temp_79 ←
      (uint128_to_le_bytes ((a_77) .+ (n_78))) ;;
     temp_80 ←
      (array_from_seq (16) (array_to_seq (temp_79 : nseq int8 16))) ;;
    @pkg_core_definition.ret poly1305_tag_t ( (temp_80))
    } : code (fset.fset0) [interface] _).

Definition st_84_loc : Location :=
  (@ct (field_element_t '× field_element_t '× poly_key_t) ; 88%nat).
Program Definition poly1305
  (m_83 : byte_seq)
  (key_81 : poly_key_t)
  : code (
    fset (path.sort leb [ st_84_loc ; st_43_loc ; n_3_loc ; st_49_loc])) [interface] (
    @ct (poly1305_tag_t)) :=
  ({code
     temp_82 ←
      (poly1305_init (key_81)) ;;
    #put st_84_loc := 
      (temp_82) ;;
    st_84 ← get st_84_loc ;;
     temp_85 ←
      (poly1305_update (m_83) (st_84)) ;;
    st_84 ← get st_84_loc ;;
    #put st_84_loc := 
      (temp_85) ;;
    st_84 ← get st_84_loc ;;
     temp_86 ←
      (poly1305_finish (st_84)) ;;
    @pkg_core_definition.ret poly1305_tag_t ( (temp_86))
    } : code ((
        fset (path.sort leb [ st_84_loc ; st_43_loc ; n_3_loc ; st_49_loc]))) [interface] _).

