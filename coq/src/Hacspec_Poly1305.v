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

Notation poly_key_t := (nseq (uint8_choice) (usize 32)).

Definition blocksize_v : uint_size :=
  (usize 16).

Notation poly_block_t := (nseq (uint8_choice) (usize 16)).

Notation poly1305_tag_t := (nseq (uint8_choice) (usize 16)).

Notation "'sub_block_t'" := (byte_seq) : hacspec_scope.

Notation "'block_index_t'" := (uint_size) : hacspec_scope.

Definition field_canvas_t := nseq (int8_choice) (17).
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
      (array_from_seq (16) (b_0)) ;; 
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
      (array_from_seq (16) (b_12)) ;; 
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

Definition n_43_loc : Location :=
  (choice_type_from_type _ ; 45%nat).
Program Definition poly1305_init
  (k_35 : poly_key_t)
  : code (fset [ n_43_loc]) [interface] (choice_type_from_type (
      poly_state_t)) :=
  ({code
     temp_37 ←
      (array_from_slice (default) (16) (k_35) (usize 0) (usize 16)) ;; 
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
    } : code ((fset [ n_43_loc])) [interface] _).
Admit Obligations.


Program Definition poly1305_update_block
  (b_47 : poly_block_t)
  (st_46 : poly_state_t)
  : code fset.fset0 [interface] (choice_type_from_type (poly_state_t)) :=
  ({code
    let '(acc_50, r_51, k_52) :=
      (st_46) in 
     temp_49 ←
      (poly1305_encode_block (b_47)) ;; 
    let temp_48 := type_from_choice_type_elem temp_49 in
    pkg_core_definition.ret (choice_type_from_type_elem ((
        ((temp_48) +% (acc_50)) *% (r_51),
        r_51,
        k_52
      )))
    } : code (fset.fset0) [interface] _).
Admit Obligations.

Definition st_60_loc : Location :=
  (choice_type_from_type (field_element_t '× field_element_t '× poly_key_t
    ) ; 65%nat).
Program Definition poly1305_update_blocks
  (m_54 : byte_seq)
  (st_53 : poly_state_t)
  : code (fset [ st_60_loc]) [interface] (choice_type_from_type (
      poly_state_t)) :=
  ({code
    #put st_60_loc := choice_type_from_type_elem
      (st_53) ;;
    st_60 ← get st_60_loc ;;
    let st_60 := type_from_choice_type_elem (st_60) in
    let n_blocks_55 : uint_size :=
      ((seq_len (m_54)) / (blocksize_v)) in 
     temp_63 ←
      (foldi (usize 0) (n_blocks_55) (fun i_56 st_60 =>
          {code
           temp_58 ←
            (array_from_seq (16) (seq_get_exact_chunk (m_54) (blocksize_v) (
                  i_56))) ;; 
          let temp_57 := type_from_choice_type_elem temp_58 in
          let block_59 : poly_block_t :=
            (temp_57) in 
           temp_62 ←
            (poly1305_update_block (block_59) (st_60)) ;; 
          let temp_61 := type_from_choice_type_elem temp_62 in
          let st_60 :=
            (temp_61) in 
          pkg_core_definition.ret (choice_type_from_type_elem ((st_60)))
          } : code (fset.fset0) [interface] _)
        st_60) ;; 
    let st_60 := type_from_choice_type_elem temp_63 in
    
    pkg_core_definition.ret (choice_type_from_type_elem (st_60))
    } : code ((fset [ st_60_loc])) [interface] _).
Admit Obligations.

Definition st_67_loc : Location :=
  (choice_type_from_type (field_element_t '× field_element_t '× poly_key_t
    ) ; 77%nat).
Program Definition poly1305_update_last
  (pad_len_69 : uint_size)
  (b_68 : sub_block_t)
  (st_66 : poly_state_t)
  : code (fset [ st_67_loc]) [interface] (choice_type_from_type (
      poly_state_t)) :=
  ({code
    #put st_67_loc := choice_type_from_type_elem
      (st_66) ;;
    st_67 ← get st_67_loc ;;
    let st_67 := type_from_choice_type_elem (st_67) in
     temp_75 ←
      (if (seq_len (b_68)) !=.? (usize 0):bool then ({code
          let '(acc_72, r_73, k_74) :=
            (st_67) in 
           temp_71 ←
            (poly1305_encode_last (pad_len_69) (b_68)) ;; 
          let temp_70 := type_from_choice_type_elem temp_71 in
          let st_67 :=
            ((((temp_70) +% (acc_72)) *% (r_73), r_73, k_74)) in 
          pkg_core_definition.ret (choice_type_from_type_elem ((st_67)))
          } : code (fset.fset0) [interface] _) else (
          pkg_core_definition.ret (choice_type_from_type_elem ((st_67))))) ;; 
    let '(st_67) := type_from_choice_type_elem temp_75 in
    
    pkg_core_definition.ret (choice_type_from_type_elem (st_67))
    } : code ((fset [ st_67_loc])) [interface] _).
Admit Obligations.

Definition st_86_loc : Location :=
  (choice_type_from_type _ ; 90%nat).
Definition st_87_loc : Location :=
  (choice_type_from_type _ ; 91%nat).
Program Definition poly1305_update
  (m_78 : byte_seq)
  (st_79 : poly_state_t)
  : code (fset [ st_86_loc ; st_87_loc]) [interface] (choice_type_from_type (
      poly_state_t)) :=
  ({code
     temp_81 ←
      (poly1305_update_blocks (m_78) (st_79)) ;; 
    let temp_80 := type_from_choice_type_elem temp_81 in
    let st_83 : (field_element_t '× field_element_t '× poly_key_t) :=
      (temp_80) in 
    let last_82 : seq uint8 :=
      (seq_get_remainder_chunk (m_78) (blocksize_v)) in 
     temp_85 ←
      (poly1305_update_last (seq_len (last_82)) (last_82) (st_83)) ;; 
    let temp_84 := type_from_choice_type_elem temp_85 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_84))
    } : code ((fset [ st_86_loc ; st_87_loc])) [interface] _).
Admit Obligations.


Program Definition poly1305_finish
  (st_92 : poly_state_t)
  : code fset.fset0 [interface] (choice_type_from_type (poly1305_tag_t)) :=
  ({code
    let '(acc_98, _, k_93) :=
      (st_92) in 
     temp_95 ←
      (array_from_slice (default) (16) (k_93) (usize 16) (usize 16)) ;; 
    let temp_94 := type_from_choice_type_elem temp_95 in
     temp_97 ←
      (uint128_from_le_bytes (temp_94)) ;; 
    let temp_96 := type_from_choice_type_elem temp_97 in
    let n_105 : uint128 :=
      (temp_96) in 
    let aby_99 : seq uint8 :=
      (nat_mod_to_byte_seq_le (acc_98)) in 
     temp_101 ←
      (array_from_slice (default) (16) (aby_99) (usize 0) (usize 16)) ;; 
    let temp_100 := type_from_choice_type_elem temp_101 in
     temp_103 ←
      (uint128_from_le_bytes (temp_100)) ;; 
    let temp_102 := type_from_choice_type_elem temp_103 in
    let a_104 : uint128 :=
      (temp_102) in 
     temp_107 ←
      (uint128_to_le_bytes ((a_104) .+ (n_105))) ;; 
    let temp_106 := type_from_choice_type_elem temp_107 in
     temp_109 ←
      (array_from_seq (16) (temp_106)) ;; 
    let temp_108 := type_from_choice_type_elem temp_109 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_108))
    } : code (fset.fset0) [interface] _).
Admit Obligations.

Definition st_114_loc : Location :=
  (choice_type_from_type (field_element_t '× field_element_t '× poly_key_t
    ) ; 120%nat).
Program Definition poly1305
  (m_113 : byte_seq)
  (key_110 : poly_key_t)
  : code (fset [ st_114_loc]) [interface] (choice_type_from_type (
      poly1305_tag_t)) :=
  ({code
     temp_112 ←
      (poly1305_init (key_110)) ;; 
    let temp_111 := type_from_choice_type_elem temp_112 in
    #put st_114_loc := choice_type_from_type_elem
      (temp_111) ;;
    st_114 ← get st_114_loc ;;
    let st_114 := type_from_choice_type_elem (st_114) in
     temp_116 ←
      (poly1305_update (m_113) (st_114)) ;; 
    let temp_115 := type_from_choice_type_elem temp_116 in
    let st_114 :=
      (temp_115) in 
     temp_118 ←
      (poly1305_finish (st_114)) ;; 
    let temp_117 := type_from_choice_type_elem temp_118 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_117))
    } : code ((fset [ st_114_loc])) [interface] _).
Admit Obligations.

