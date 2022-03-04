(** This file was automatically generated using Hacspec **)
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.

Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
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

Definition n_5_loc : Location :=
  (choice_type_from_type uint128 ; 11%nat).
Program Definition poly1305_encode_r
  (b_0 : poly_block_t)
  : code (fset [ n_5_loc]) [interface] (choice_type_from_type (
      field_element_t)) :=
  ({code
     temp_2 ←
      (array_from_seq (16) (array_to_seq (b_0))) ;; 
    let temp_1 := type_from_choice_type_elem temp_2 in
     temp_4 ←
      (uint128_from_le_bytes (temp_1)) ;; 
    let temp_3 := type_from_choice_type_elem temp_4 in
    #put n_5_loc := choice_type_from_type_elem
      (temp_3) ;;
    n_5 ← get n_5_loc ;;
    let n_5 := type_from_choice_type_elem (n_5) in
     temp_7 ←
      (secret (@repr WORDSIZE128 21267647620597763993911028882763415551)) ;; 
    let temp_6 := type_from_choice_type_elem temp_7 : int128 in
    let n_5 :=
      ((n_5) .& (temp_6)) in 
     temp_9 ←
      (nat_mod_from_secret_literal (n_5)) ;; 
    let temp_8 := type_from_choice_type_elem temp_9 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_8))
    } : code ((fset [ n_5_loc])) [interface] _).
Admit Obligations.


Program Definition poly1305_encode_block
  (b_12 : poly_block_t)
  : code fset.fset0 [interface] (choice_type_from_type (field_element_t)) :=
  ({code
     temp_14 ←
      (array_from_seq (16) (array_to_seq (b_12))) ;; 
    let temp_13 := type_from_choice_type_elem temp_14 in
     temp_16 ←
      (uint128_from_le_bytes (temp_13)) ;; 
    let temp_15 := type_from_choice_type_elem temp_16 in
    let n_17 : uint128 :=
      (temp_15) in 
     temp_19 ←
      (nat_mod_from_secret_literal (n_17)) ;; 
    let temp_18 := type_from_choice_type_elem temp_19 in
    let f_20 : field_element_t :=
      (temp_18) in 
     temp_22 ←
      (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (usize 128)) ;; 
    let temp_21 := type_from_choice_type_elem temp_22 : field_element_t in
    pkg_core_definition.ret (choice_type_from_type_elem ((f_20) +% (temp_21)))
    } : code (fset.fset0) [interface] _).
Admit Obligations.


Program Definition poly1305_encode_last
  (pad_len_32 : block_index_t)
  (b_23 : sub_block_t)
  : code fset.fset0 [interface] (choice_type_from_type (field_element_t)) :=
  ({code
     temp_25 ←
      (array_from_slice (default) (16) (b_23) (usize 0) (seq_len (b_23))) ;; 
    let temp_24 := type_from_choice_type_elem temp_25 in
     temp_27 ←
      (uint128_from_le_bytes (temp_24)) ;; 
    let temp_26 := type_from_choice_type_elem temp_27 in
    let n_28 : uint128 :=
      (temp_26) in 
     temp_30 ←
      (nat_mod_from_secret_literal (n_28)) ;; 
    let temp_29 := type_from_choice_type_elem temp_30 in
    let f_31 : field_element_t :=
      (temp_29) in 
     temp_34 ←
      (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) * (
            pad_len_32))) ;; 
    let temp_33 := type_from_choice_type_elem temp_34 : field_element_t in
    pkg_core_definition.ret (choice_type_from_type_elem ((f_31) +% (temp_33)))
    } : code (fset.fset0) [interface] _).
Admit Obligations.


Program Definition poly1305_init
  (k_35 : poly_key_t)
  : code fset.fset0 [interface] (choice_type_from_type (poly_state_t)) :=
  ({code
     temp_37 ←
      (array_from_slice (default) (16) (array_to_seq (k_35)) (usize 0) (
          usize 16)) ;; 
    let temp_36 := type_from_choice_type_elem temp_37 in
     temp_39 ←
      (poly1305_encode_r (temp_36)) ;; 
    let temp_38 := type_from_choice_type_elem temp_39 in
    let r_42 : field_element_t :=
      (temp_38) in 
     temp_41 ←
      (nat_mod_zero ) ;; 
    let temp_40 := type_from_choice_type_elem temp_41 in
    pkg_core_definition.ret (choice_type_from_type_elem ((temp_40, r_42, k_35)))
    } : code ((fset [ n_5_loc])) [interface] _).
Admit Obligations.


Program Definition poly1305_update_block
  (b_45 : poly_block_t)
  (st_44 : poly_state_t)
  : code fset.fset0 [interface] (choice_type_from_type (poly_state_t)) :=
  ({code
    let '(acc_48, r_49, k_50) :=
      (st_44) in 
     temp_47 ←
      (poly1305_encode_block (b_45)) ;; 
    let temp_46 := type_from_choice_type_elem temp_47 in
    pkg_core_definition.ret (choice_type_from_type_elem ((
        ((temp_46) +% (acc_48)) *% (r_49),
        r_49,
        k_50
      )))
    } : code (fset.fset0) [interface] _).
Admit Obligations.

Definition st_58_loc : Location :=
  (choice_type_from_type poly_state_t ; 63%nat).
Program Definition poly1305_update_blocks
  (m_52 : byte_seq)
  (st_51 : poly_state_t)
  : code (fset [ st_58_loc]) [interface] (choice_type_from_type (
      poly_state_t)) :=
  ({code
    #put st_58_loc := choice_type_from_type_elem
      (st_51) ;;
    st_58 ← get st_58_loc ;;
    let st_58 := type_from_choice_type_elem (st_58) in
    let n_blocks_53 : uint_size :=
      ((seq_len (m_52)) / (blocksize_v)) in 
     temp_61 ←
      (foldi (usize 0) (n_blocks_53) (fun i_54 st_58 =>
          {code
           temp_56 ←
            (array_from_seq (16) (seq_get_exact_chunk (m_52) ( (blocksize_v)) (
                   (i_54)))) ;; 
          let temp_55 := type_from_choice_type_elem temp_56 in
          let block_57 : poly_block_t :=
            (temp_55) in 
           temp_60 ←
            (poly1305_update_block (block_57) (st_58)) ;; 
          let temp_59 := type_from_choice_type_elem temp_60 in
          let st_58 :=
            (temp_59) in 
          pkg_core_definition.ret (choice_type_from_type_elem ((st_58)))
          } : code (fset.fset0) [interface] _)
        st_58) ;; 
    let st_58 := type_from_choice_type_elem temp_61 in
    
    pkg_core_definition.ret (choice_type_from_type_elem (st_58))
    } : code ((fset [ st_58_loc])) [interface] _).
Admit Obligations.

Definition st_65_loc : Location :=
  (choice_type_from_type poly_state_t ; 75%nat).
Program Definition poly1305_update_last
  (pad_len_67 : uint_size)
  (b_66 : sub_block_t)
  (st_64 : poly_state_t)
  : code (fset [ st_65_loc]) [interface] (choice_type_from_type (
      poly_state_t)) :=
  ({code
    #put st_65_loc := choice_type_from_type_elem
      (st_64) ;;
    st_65 ← get st_65_loc ;;
    let st_65 := type_from_choice_type_elem (st_65) in
     temp_73 ←
      (if (seq_len (b_66)) !=.? (usize 0):bool then ({code
          let '(acc_70, r_71, k_72) :=
            (st_65) in 
           temp_69 ←
            (poly1305_encode_last (pad_len_67) (b_66)) ;; 
          let temp_68 := type_from_choice_type_elem temp_69 in
          let st_65 :=
            ((((temp_68) +% (acc_70)) *% (r_71), r_71, k_72)) in 
          pkg_core_definition.ret (choice_type_from_type_elem ((st_65)))
          } : code (fset.fset0) [interface] _) else (
          pkg_core_definition.ret (choice_type_from_type_elem ((st_65))))) ;; 
    let '(st_65) := type_from_choice_type_elem temp_73 in
    
    pkg_core_definition.ret (choice_type_from_type_elem (st_65))
    } : code ((fset [ st_65_loc])) [interface] _).
Admit Obligations.


Program Definition poly1305_update
  (m_76 : byte_seq)
  (st_77 : poly_state_t)
  : code fset.fset0 [interface] (choice_type_from_type (poly_state_t)) :=
  ({code
     temp_79 ←
      (poly1305_update_blocks (m_76) (st_77)) ;; 
    let temp_78 := type_from_choice_type_elem temp_79 in
    let st_81 : (field_element_t '× field_element_t '× poly_key_t) :=
      (temp_78) in 
    let last_80 : seq uint8 :=
      (seq_get_remainder_chunk (m_76) ( (blocksize_v))) in 
     temp_83 ←
      (poly1305_update_last (seq_len (last_80)) (last_80) (st_81)) ;; 
    let temp_82 := type_from_choice_type_elem temp_83 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_82))
    } : code ((fset [ st_58_loc ; st_65_loc])) [interface] _).
Admit Obligations.


Program Definition poly1305_finish
  (st_86 : poly_state_t)
  : code fset.fset0 [interface] (choice_type_from_type (poly1305_tag_t)) :=
  ({code
    let '(acc_92, _, k_87) :=
      (st_86) in 
     temp_89 ←
      (array_from_slice (default) (16) (array_to_seq (k_87)) (usize 16) (
          usize 16)) ;; 
    let temp_88 := type_from_choice_type_elem temp_89 in
     temp_91 ←
      (uint128_from_le_bytes (temp_88)) ;; 
    let temp_90 := type_from_choice_type_elem temp_91 in
    let n_99 : uint128 :=
      (temp_90) in 
    let aby_93 : seq uint8 :=
      (nat_mod_to_byte_seq_le (acc_92)) in 
     temp_95 ←
      (array_from_slice (default) (16) (aby_93) (usize 0) (usize 16)) ;; 
    let temp_94 := type_from_choice_type_elem temp_95 in
     temp_97 ←
      (uint128_from_le_bytes (temp_94)) ;; 
    let temp_96 := type_from_choice_type_elem temp_97 in
    let a_98 : uint128 :=
      (temp_96) in 
     temp_101 ←
      (uint128_to_le_bytes ((a_98) .+ (n_99))) ;; 
    let temp_100 := type_from_choice_type_elem temp_101 in
     temp_103 ←
      (array_from_seq (16) (array_to_seq (temp_100))) ;; 
    let temp_102 := type_from_choice_type_elem temp_103 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_102))
    } : code (fset.fset0) [interface] _).
Admit Obligations.

Definition st_108_loc : Location :=
  (choice_type_from_type poly_state_t ; 114%nat).
Program Definition poly1305
  (m_107 : byte_seq)
  (key_104 : poly_key_t)
  : code (fset [ st_108_loc]) [interface] (choice_type_from_type (
      poly1305_tag_t)) :=
  ({code
     temp_106 ←
      (poly1305_init (key_104)) ;; 
    let temp_105 := type_from_choice_type_elem temp_106 in
    #put st_108_loc := choice_type_from_type_elem
      (temp_105) ;;
    st_108 ← get st_108_loc ;;
    let st_108 := type_from_choice_type_elem (st_108) in
     temp_110 ←
      (poly1305_update (m_107) (st_108)) ;; 
    let temp_109 := type_from_choice_type_elem temp_110 in
    let st_108 :=
      (temp_109) in 
     temp_112 ←
      (poly1305_finish (st_108)) ;; 
    let temp_111 := type_from_choice_type_elem temp_112 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_111))
    } : code ((fset [ st_108_loc])) [interface] _).
Admit Obligations.

