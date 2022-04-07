(** This file was automatically generated using Hacspec **)
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From CoqWord Require Import ssrZ word.
From Jasmin Require Import word.
Require Import ChoiceEquality.

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

Definition n_4_loc : Location :=
  (@ct uint128 ; 8%nat).
Program Definition poly1305_encode_r
  (b_0 : poly_block_t)
  : code (fset (path.sort leb [ n_4_loc])) [interface] (@ct (
      field_element_t)) :=
  ({code
     temp_1 ←
      (array_to_seq (b_0)) ;;
    let temp_1 : seq uint8 :=
      (temp_1) in
     temp_2 ←
      (array_from_seq (16) (temp_1)) ;;
     temp_3 ←
      (uint128_from_le_bytes (temp_2)) ;;
    #put n_4_loc := 
      (temp_3) ;;
    n_4 ← get n_4_loc ;;
     temp_5 ←
      (secret (@repr U128 21267647620597763993911028882763415551)) ;;
    let temp_5 : int128 :=
      (temp_5) in
    n_4 ← get n_4_loc ;;
    #put n_4_loc := 
      ((n_4) .& (temp_5)) ;;
    n_4 ← get n_4_loc ;;
     temp_6 ←
      (nat_mod_from_secret_literal (n_4)) ;;
    @pkg_core_definition.ret field_element_t ( (temp_6))
    } : code ((fset (path.sort leb [ n_4_loc]))) [interface] _).


Program Definition poly1305_encode_block
  (b_9 : poly_block_t)
  : code fset.fset0 [interface] (@ct (field_element_t)) :=
  ({code
     temp_10 ←
      (array_to_seq (b_9)) ;;
    let temp_10 : seq uint8 :=
      (temp_10) in
     temp_11 ←
      (array_from_seq (16) (temp_10)) ;;
     temp_12 ←
      (uint128_from_le_bytes (temp_11)) ;;
    let n_13 : uint128 :=
      (temp_12) in
    
     temp_14 ←
      (nat_mod_from_secret_literal (n_13)) ;;
    let f_15 : field_element_t :=
      (temp_14) in
    
     temp_16 ←
      (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (usize 128)) ;;
    let temp_16 : field_element_t :=
      (temp_16) in
    @pkg_core_definition.ret field_element_t ( ((f_15) +% (temp_16)))
    } : code (fset.fset0) [interface] _).


Program Definition poly1305_encode_last
  (pad_len_24 : block_index_t)
  (b_17 : sub_block_t)
  : code fset.fset0 [interface] (@ct (field_element_t)) :=
  ({code
     temp_18 ←
      (seq_len (b_17)) ;;
     temp_19 ←
      (array_from_slice (default) (16) (b_17) (usize 0) (temp_18)) ;;
     temp_20 ←
      (uint128_from_le_bytes (temp_19)) ;;
    let n_21 : uint128 :=
      (temp_20) in
    
     temp_22 ←
      (nat_mod_from_secret_literal (n_21)) ;;
    let f_23 : field_element_t :=
      (temp_22) in
    
     temp_25 ←
      (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) * (
            pad_len_24))) ;;
    let temp_25 : field_element_t :=
      (temp_25) in
    @pkg_core_definition.ret field_element_t ( ((f_23) +% (temp_25)))
    } : code (fset.fset0) [interface] _).


Program Definition poly1305_init
  (k_26 : poly_key_t)
  : code (fset (path.sort leb [ n_4_loc])) [interface] (@ct (poly_state_t)) :=
  ({code
     temp_27 ←
      (array_to_seq (k_26)) ;;
    let temp_27 : seq uint8 :=
      (temp_27) in
     temp_28 ←
      (array_from_slice (default) (16) (temp_27) (usize 0) (usize 16)) ;;
     temp_29 ←
      (poly1305_encode_r (temp_28)) ;;
    let r_31 : field_element_t :=
      (temp_29) in
    
     temp_30 ←
      (nat_mod_zero ) ;;
    @pkg_core_definition.ret (field_element_t '× field_element_t '× poly_key_t
    ) ( ((temp_30, r_31, k_26)))
    } : code ((fset (path.sort leb [ n_4_loc]))) [interface] _).


Program Definition poly1305_update_block
  (b_33 : poly_block_t)
  (st_32 : poly_state_t)
  : code fset.fset0 [interface] (@ct (poly_state_t)) :=
  ({code
    let '(acc_35, r_36, k_37) :=
      (st_32) in
    
     temp_34 ←
      (poly1305_encode_block (b_33)) ;;
    @pkg_core_definition.ret (field_element_t '× field_element_t '× poly_key_t
    ) ( ((((temp_34) +% (acc_35)) *% (r_36), r_36, k_37)))
    } : code (fset.fset0) [interface] _).

Definition st_46_loc : Location :=
  (@ct (field_element_t '× field_element_t '× poly_key_t) ; 50%nat).
Program Definition poly1305_update_blocks
  (m_39 : byte_seq)
  (st_38 : poly_state_t)
  : code (fset (path.sort leb [ st_46_loc])) [interface] (@ct (poly_state_t)) :=
  ({code
    #put st_46_loc := 
      (st_38) ;;
    st_46 ← get st_46_loc ;;
     temp_40 ←
      (seq_len (m_39)) ;;
    let n_blocks_41 : uint_size :=
      ((temp_40) / (blocksize_v) : uint_size_type) in
    
     st_46 ←
      (foldi (usize 0) (n_blocks_41) (fun i_42 st_46 =>
          {code
           temp_43 ←
            (seq_get_exact_chunk (m_39) ( (blocksize_v)) ( (i_42))) ;;
           temp_44 ←
            (array_from_seq (16) (temp_43 : seq int8)) ;;
          let block_45 : poly_block_t :=
            (temp_44) in
          
           temp_47 ←
            (poly1305_update_block (block_45) (st_46)) ;;
          st_46 ← get st_46_loc ;;
          #put st_46_loc := 
            (temp_47) ;;
          st_46 ← get st_46_loc ;;
          @pkg_core_definition.ret _ ( ((st_46)))
          } : code ((fset (path.sort leb [ st_46_loc]))) [interface] _)
        st_46) ;;
    
    @pkg_core_definition.ret (field_element_t '× field_element_t '× poly_key_t
    ) ( (st_46))
    } : code ((fset (path.sort leb [ st_46_loc]))) [interface] _).

Definition st_52_loc : Location :=
  (@ct (field_element_t '× field_element_t '× poly_key_t) ; 62%nat).
Program Definition poly1305_update_last
  (pad_len_55 : uint_size)
  (b_53 : sub_block_t)
  (st_51 : poly_state_t)
  : code (fset (path.sort leb [ st_52_loc])) [interface] (@ct (poly_state_t)) :=
  ({code
    #put st_52_loc := 
      (st_51) ;;
    st_52 ← get st_52_loc ;;
     temp_54 ←
      (seq_len (b_53)) ;;
     '(st_52) ←
      (if (temp_54) !=.? (usize 0):bool then ({code
          let '(acc_57, r_58, k_59) :=
            (st_52) in
          
           temp_56 ←
            (poly1305_encode_last (pad_len_55) (b_53)) ;;
          st_52 ← get st_52_loc ;;
          #put st_52_loc := 
            ((((temp_56) +% (acc_57)) *% (r_58), r_58, k_59)) ;;
          st_52 ← get st_52_loc ;;
          @pkg_core_definition.ret _ ( ((st_52)))
          } : code ((fset (path.sort leb [ st_52_loc]))) [interface] _) else (
          @pkg_core_definition.ret _ ( ((st_52))))) ;;
    
    @pkg_core_definition.ret (field_element_t '× field_element_t '× poly_key_t
    ) ( (st_52))
    } : code ((fset (path.sort leb [ st_52_loc]))) [interface] _).


Program Definition poly1305_update
  (m_63 : byte_seq)
  (st_64 : poly_state_t)
  : code (fset (path.sort leb [ st_52_loc ; st_46_loc])) [interface] (@ct (
      poly_state_t)) :=
  ({code
     temp_65 ←
      (poly1305_update_blocks (m_63) (st_64)) ;;
    let st_69 : (field_element_t '× field_element_t '× poly_key_t) :=
      (temp_65) in
    
     temp_66 ←
      (seq_get_remainder_chunk (m_63) ( (blocksize_v))) ;;
    let last_67 : seq uint8 :=
      (temp_66) in
    
     temp_68 ←
      (seq_len (last_67)) ;;
     temp_70 ←
      (poly1305_update_last (temp_68 : uint_size_type) (last_67) (st_69)) ;;
    @pkg_core_definition.ret poly_state_t ( (temp_70))
    } : code ((fset (path.sort leb [ st_52_loc ; st_46_loc]))) [interface] _).


Program Definition poly1305_finish
  (st_71 : poly_state_t)
  : code fset.fset0 [interface] (@ct (poly1305_tag_t)) :=
  ({code
    let '(acc_76, _, k_72) :=
      (st_71) in
    
     temp_73 ←
      (array_to_seq (k_72)) ;;
    let temp_73 : seq uint8 :=
      (temp_73) in
     temp_74 ←
      (array_from_slice (default) (16) (temp_73) (usize 16) (usize 16)) ;;
     temp_75 ←
      (uint128_from_le_bytes (temp_74)) ;;
    let n_82 : uint128 :=
      (temp_75) in
    
     temp_77 ←
      (nat_mod_to_byte_seq_le (acc_76)) ;;
    let aby_78 : seq uint8 :=
      (temp_77) in
    
     temp_79 ←
      (array_from_slice (default) (16) (aby_78) (usize 0) (usize 16)) ;;
     temp_80 ←
      (uint128_from_le_bytes (temp_79)) ;;
    let a_81 : uint128 :=
      (temp_80) in
    
     temp_83 ←
      (uint128_to_le_bytes ((a_81) .+ (n_82))) ;;
     temp_84 ←
      (array_to_seq (temp_83 : nseq int8 16)) ;;
    let temp_84 : seq uint8 :=
      (temp_84) in
     temp_85 ←
      (array_from_seq (16) (temp_84)) ;;
    @pkg_core_definition.ret poly1305_tag_t ( (temp_85))
    } : code (fset.fset0) [interface] _).

Definition st_89_loc : Location :=
  (@ct (field_element_t '× field_element_t '× poly_key_t) ; 93%nat).
Program Definition poly1305
  (m_88 : byte_seq)
  (key_86 : poly_key_t)
  : code (
    fset (path.sort leb [ st_46_loc ; n_4_loc ; st_52_loc ; st_89_loc])) [interface] (
    @ct (poly1305_tag_t)) :=
  ({code
     temp_87 ←
      (poly1305_init (key_86)) ;;
    #put st_89_loc := 
      (temp_87) ;;
    st_89 ← get st_89_loc ;;
     temp_90 ←
      (poly1305_update (m_88) (st_89)) ;;
    st_89 ← get st_89_loc ;;
    #put st_89_loc := 
      (temp_90) ;;
    st_89 ← get st_89_loc ;;
     temp_91 ←
      (poly1305_finish (st_89)) ;;
    @pkg_core_definition.ret poly1305_tag_t ( (temp_91))
    } : code ((
        fset (path.sort leb [ st_46_loc ; n_4_loc ; st_52_loc ; st_89_loc]))) [interface] _).

