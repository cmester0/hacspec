(** This file was automatically generated using Hacspec **)
From mathcomp Require Import choice (* all_ssreflect *) (* ssreflect *) (* seq tuple *).
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.

Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.


Obligation Tactic :=
try (Tactics.program_simpl; fail); simpl ; (* Old Obligation Tactic *)
intros ; do 2 ssprove_valid'_2.

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
Check (fun (k_23 : poly_key_t) => ((nat_mod_zero_pre, nat_mod_zero_pre, k_23) : @ct (poly_state_t))).

Definition n_3_loc : Location :=
  (@ct uint128 ; 7%nat).
Program Definition poly1305_encode_r
  (b_0 : poly_block_t)
  : code (fset [ n_3_loc]) [interface] (@ct (field_element_t)) :=
  ({code
     temp_1 ←
      (array_from_seq (16) (array_to_seq (b_0))) ;;
     temp_2 ←
      (uint128_from_le_bytes (temp_1)) ;;
    #put n_3_loc := 
      (temp_2) ;;
    n_3 ← get n_3_loc ;;
     temp_4 ←
      (secret (@repr WORDSIZE128 21267647620597763993911028882763415551)) ;;
    n_3 ← get n_3_loc ;;
    #put n_3_loc := 
      ((n_3) .& (temp_4)) ;;
    n_3 ← get n_3_loc ;;
     temp_5 ←
      (nat_mod_from_secret_literal (n_3)) ;;
    pkg_core_definition.ret ( (temp_5))
    } : code ((fset [ n_3_loc])) [interface] _).


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
    pkg_core_definition.ret ( ((f_13) +% (temp_14)))
    } : code (fset.fset0) [interface] _).


Program Definition poly1305_encode_last
  (pad_len_21 : block_index_t)
  (b_15 : sub_block_t)
  : code fset.fset0 [interface] (@ct (field_element_t)) :=
  ({code
     temp_16 ←
      (array_from_slice (default) (16) (b_15) (usize 0) (seq_len (b_15))) ;;
     temp_17 ←
      (uint128_from_le_bytes (temp_16)) ;;
    let n_18 : uint128 :=
      (temp_17) in
    
     temp_19 ←
      (nat_mod_from_secret_literal (n_18)) ;;
    let f_20 : field_element_t :=
      (temp_19) in
    
     temp_22 ←
      (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) * (
            pad_len_21 : uint_size_type))) ;;
    pkg_core_definition.ret ( ((f_20) +% (temp_22)))
    } : code (fset.fset0) [interface] _).

Program Definition poly1305_init
  (k_23 : poly_key_t)
  : code (fset [ n_3_loc]) [interface] (@ct (poly_state_t)) :=
  ({code
     temp_24 ←
      (array_from_slice (default) (16) (array_to_seq (k_23)) (usize 0) (
          usize 16)) ;;
     temp_25 ←
      (poly1305_encode_r (temp_24)) ;;
    let r_27 : field_element_t :=
      (temp_25) in
    
     temp_26 ←
      (nat_mod_zero ) ;;
    pkg_core_definition.ret ( ((temp_26, r_27, k_23) : @ct (poly_state_t)))
    } : code ((fset [ n_3_loc])) [interface] _).


Program Definition poly1305_update_block
  (b_29 : poly_block_t)
  (st_28 : poly_state_t)
  : code fset.fset0 [interface] (@ct (poly_state_t)) :=
  ({code
    let '(acc_31, r_32, k_33) :=
      (st_28) in
    
     temp_30 ←
      (poly1305_encode_block (b_29)) ;;
    pkg_core_definition.ret ( ((((temp_30) +% (acc_31)) *% (r_32), r_32, k_33)))
    } : code (fset.fset0) [interface] _).

Definition st_40_loc : Location :=
  (@ct (field_element_t '× field_element_t '× poly_key_t) ; 44%nat).
Program Definition poly1305_update_blocks
  (m_35 : byte_seq)
  (st_34 : poly_state_t)
  : (* code (fset [ st_40_loc]) [interface] *) raw_code (@ct (poly_state_t)) :=
  ((* {code *)
    #put st_40_loc := 
      (st_34) ;;
    st_40 ← get st_40_loc ;;
    let n_blocks_36 : uint_size :=
      ((seq_len (m_35)) / (blocksize_v : uint_size_type)) : uint_size_type in
    
     st_40 ←
      ({code foldi_pre (usize 0) (n_blocks_36) (fun i_37 st_40 =>
          (*  *)
           temp_38 ←
            (array_from_seq (16) (seq_get_exact_chunk_pre (m_35) ( (blocksize_v)) (
                   (i_37)))) ;;
          let block_39 : poly_block_t :=
            (temp_38) in
          
           temp_41 ←
            (poly1305_update_block (block_39) (st_40)) ;;
          st_40 ← get st_40_loc ;;
          #put st_40_loc := 
            (temp_41) ;;
          st_40 ← get st_40_loc ;;
          pkg_core_definition.ret ( ((st_40)))
                                           )
        st_40} : code ((fset [ st_40_loc])) [interface] _) ;;
    
    pkg_core_definition.ret ( (st_40))
    (* } : code ((fset [ st_40_loc])) [interface] _ *)).

Definition st_46_loc : Location :=
  (@ct (field_element_t '× field_element_t '× poly_key_t) ; 55%nat).
Program Definition poly1305_update_last
  (pad_len_48 : uint_size)
  (b_47 : sub_block_t)
  (st_45 : poly_state_t)
  : code (fset [ st_46_loc]) [interface] (@ct (poly_state_t)) :=
  ({code
    #put st_46_loc := 
      (st_45) ;;
    st_46 ← get st_46_loc ;;
     '(st_46) ←
      (if (seq_len (b_47)) !=.? (usize 0):bool then ({code
          let '(acc_50, r_51, k_52) :=
            (st_46) in
          
           temp_49 ←
            (poly1305_encode_last (pad_len_48) (b_47)) ;;
          st_46 ← get st_46_loc ;;
          #put st_46_loc := 
            ((((temp_49) +% (acc_50)) *% (r_51), r_51, k_52)) ;;
          st_46 ← get st_46_loc ;;
          pkg_core_definition.ret ( ((st_46)))
          } : code ((fset [ st_46_loc])) [interface] _) else (
          pkg_core_definition.ret ( ((st_46))))) ;;
    
    pkg_core_definition.ret ( (st_46))
    } : code ((fset [ st_46_loc])) [interface] _).


Program Definition poly1305_update
  (m_56 : byte_seq)
  (st_57 : poly_state_t)
  : code (fset [ st_40_loc ; st_46_loc]) [interface] (@ct (poly_state_t)) :=
  ({code
     temp_58 ←
      (poly1305_update_blocks (m_56) (st_57)) ;;
    let st_60 : (field_element_t '× field_element_t '× poly_key_t) :=
      (temp_58) in
    
    let last_59 : seq uint8 :=
      (seq_get_remainder_chunk (m_56) ( (blocksize_v))) in
    
     temp_61 ←
      (poly1305_update_last (seq_len (last_59)) (last_59) (st_60)) ;;
    pkg_core_definition.ret ( (temp_61))
    } : code ((fset [ st_40_loc ; st_46_loc])) [interface] _).


Program Definition poly1305_finish
  (st_62 : poly_state_t)
  : code fset.fset0 [interface] (@ct (poly1305_tag_t)) :=
  ({code
    let '(acc_66, _, k_63) :=
      (st_62) in
    
     temp_64 ←
      (array_from_slice (default) (16) (array_to_seq (k_63)) (usize 16) (
          usize 16)) ;;
     temp_65 ←
      (uint128_from_le_bytes (temp_64)) ;;
    let n_71 : uint128 :=
      (temp_65) in
    
    let aby_67 : seq uint8 :=
      (nat_mod_to_byte_seq_le (acc_66)) in
    
     temp_68 ←
      (array_from_slice (default) (16) (aby_67) (usize 0) (usize 16)) ;;
     temp_69 ←
      (uint128_from_le_bytes (temp_68)) ;;
    let a_70 : uint128 :=
      (temp_69) in
    
     temp_72 ←
      (uint128_to_le_bytes ((a_70) .+ (n_71))) ;;
     temp_73 ←
      (array_from_seq (16) (array_to_seq (temp_72))) ;;
    pkg_core_definition.ret ( (temp_73))
    } : code (fset.fset0) [interface] _).

Definition st_77_loc : Location :=
  (@ct (field_element_t '× field_element_t '× poly_key_t) ; 81%nat).
Program Definition poly1305
  (m_76 : byte_seq)
  (key_74 : poly_key_t)
  : code (fset [ st_40_loc ; n_3_loc ; st_77_loc ; st_46_loc]) [interface] (
    @ct (poly1305_tag_t)) :=
  ({code
     temp_75 ←
      (poly1305_init (key_74)) ;;
    #put st_77_loc := 
      (temp_75) ;;
    st_77 ← get st_77_loc ;;
     temp_78 ←
      (poly1305_update (m_76) (st_77)) ;;
    st_77 ← get st_77_loc ;;
    #put st_77_loc := 
      (temp_78) ;;
    st_77 ← get st_77_loc ;;
     temp_79 ←
      (poly1305_finish (st_77)) ;;
    pkg_core_definition.ret ( (temp_79))
    } : code ((
        fset [ st_40_loc ; n_3_loc ; st_77_loc ; st_46_loc])) [interface] _).

