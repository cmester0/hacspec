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

Definition n_0_loc : Location :=
  (choice_type_from_type uint128 ; 1%nat).
Program Definition poly1305_encode_r
  (b_2 : poly_block_t)
  : code _ [interface] (choice_type_from_type (field_element_t)) :=
  ({code
     temp_4 ←
      (array_from_seq (16) (b_2)) ;; 
    let temp_3 := type_from_choice_type_elem temp_4 in
     temp_6 ←
      (uint128_from_le_bytes (temp_3)) ;; 
    let temp_5 := type_from_choice_type_elem temp_6 in
    #put n_0_loc := choice_type_from_type_elem
      (temp_5) ;;
    n_0 ← get n_0_loc ;;
    let n_0 := type_from_choice_type_elem (n_0) in
     temp_8 ←
      (secret (@repr WORDSIZE128 21267647620597763993911028882763415551)) ;; 
    let temp_7 := type_from_choice_type_elem temp_8 : int128 in
    let n_0 :=
      ((n_0) .& (temp_7)) in 
     temp_10 ←
      (nat_mod_from_secret_literal (n_0)) ;; 
    let temp_9 := type_from_choice_type_elem temp_10 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_9))
    } : code ((fset [ n_0_loc])) [interface] _).
Admit Obligations.


Program Definition poly1305_encode_block
  (b_11 : poly_block_t)
  : code _ [interface] (choice_type_from_type (field_element_t)) :=
  ({code
     temp_13 ←
      (array_from_seq (16) (b_11)) ;; 
    let temp_12 := type_from_choice_type_elem temp_13 in
     temp_15 ←
      (uint128_from_le_bytes (temp_12)) ;; 
    let temp_14 := type_from_choice_type_elem temp_15 in
    let n_16 : uint128 :=
      (temp_14) in 
     temp_18 ←
      (nat_mod_from_secret_literal (n_16)) ;; 
    let temp_17 := type_from_choice_type_elem temp_18 in
    let f_19 : field_element_t :=
      (temp_17) in 
     temp_21 ←
      (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (usize 128)) ;; 
    let temp_20 := type_from_choice_type_elem temp_21 : field_element_t in
    pkg_core_definition.ret (choice_type_from_type_elem ((f_19) +% (temp_20)))
    } : code (fset.fset0) [interface] _).
Admit Obligations.


Program Definition poly1305_encode_last
  (pad_len_31 : block_index_t)
  (b_22 : sub_block_t)
  : code _ [interface] (choice_type_from_type (field_element_t)) :=
  ({code
     temp_24 ←
      (array_from_slice (default) (16) (b_22) (usize 0) (seq_len (b_22))) ;; 
    let temp_23 := type_from_choice_type_elem temp_24 in
     temp_26 ←
      (uint128_from_le_bytes (temp_23)) ;; 
    let temp_25 := type_from_choice_type_elem temp_26 in
    let n_27 : uint128 :=
      (temp_25) in 
     temp_29 ←
      (nat_mod_from_secret_literal (n_27)) ;; 
    let temp_28 := type_from_choice_type_elem temp_29 in
    let f_30 : field_element_t :=
      (temp_28) in 
     temp_33 ←
      (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) * (
            pad_len_31))) ;; 
    let temp_32 := type_from_choice_type_elem temp_33 : field_element_t in
    pkg_core_definition.ret (choice_type_from_type_elem ((f_30) +% (temp_32)))
    } : code (fset.fset0) [interface] _).
Admit Obligations.


Program Definition poly1305_init
  (k_34 : poly_key_t)
  : code _ [interface] (choice_type_from_type (poly_state_t)) :=
  ({code
     temp_36 ←
      (array_from_slice (default) (16) (k_34) (usize 0) (usize 16)) ;; 
    let temp_35 := type_from_choice_type_elem temp_36 in
     temp_38 ←
      (poly1305_encode_r (temp_35)) ;; 
    let temp_37 := type_from_choice_type_elem temp_38 in
    let r_39 : field_element_t :=
      (temp_37) in 
     temp_41 ←
      (nat_mod_zero ) ;; 
    let temp_40 := type_from_choice_type_elem temp_41 in
    pkg_core_definition.ret (choice_type_from_type_elem ((temp_40, r_39, k_34)))
    } : code (fset.fset0) [interface] _).
Admit Obligations.


Program Definition poly1305_update_block
  (b_46 : poly_block_t)
  (st_42 : poly_state_t)
  : code _ [interface] (choice_type_from_type (poly_state_t)) :=
  ({code
    let '(acc_43, r_44, k_45) :=
      (st_42) in 
     temp_48 ←
      (poly1305_encode_block (b_46)) ;; 
    let temp_47 := type_from_choice_type_elem temp_48 in
    pkg_core_definition.ret (choice_type_from_type_elem ((
        ((temp_47) +% (acc_43)) *% (r_44),
        r_44,
        k_45
      )))
    } : code (fset.fset0) [interface] _).
Admit Obligations.

Definition st_49_loc : Location :=
  (choice_type_from_type (field_element_t '× field_element_t '× poly_key_t
    ) ; 50%nat).
Program Definition poly1305_update_blocks
  (m_52 : byte_seq)
  (st_51 : poly_state_t)
  : code _ [interface] (choice_type_from_type (poly_state_t)) :=
  ({code
    #put st_49_loc := choice_type_from_type_elem
      (st_51) ;;
    st_49 ← get st_49_loc ;;
    let st_49 := type_from_choice_type_elem (st_49) in
    let n_blocks_53 : uint_size :=
      ((seq_len (m_52)) / (blocksize_v)) in 
     temp_60 ←
      (foldi (usize 0) (n_blocks_53) (fun i_54 st_49 =>
          {code
           temp_56 ←
            (array_from_seq (16) (seq_get_exact_chunk (m_52) (blocksize_v) (
                  i_54))) ;; 
          let temp_55 := type_from_choice_type_elem temp_56 in
          let block_57 : poly_block_t :=
            (temp_55) in 
           temp_59 ←
            (poly1305_update_block (block_57) (st_49)) ;; 
          let temp_58 := type_from_choice_type_elem temp_59 in
          let st_49 :=
            (temp_58) in 
          pkg_core_definition.ret (choice_type_from_type_elem ((st_49)))
          } : code (fset.fset0) [interface] _)
        st_49) ;; 
    let st_49 := type_from_choice_type_elem temp_60 in
    
    pkg_core_definition.ret (choice_type_from_type_elem (st_49))
    } : code ((fset [ st_49_loc])) [interface] _).
Admit Obligations.

Definition st_61_loc : Location :=
  (choice_type_from_type (field_element_t '× field_element_t '× poly_key_t
    ) ; 62%nat).
Program Definition poly1305_update_last
  (pad_len_68 : uint_size)
  (b_64 : sub_block_t)
  (st_63 : poly_state_t)
  : code _ [interface] (choice_type_from_type (poly_state_t)) :=
  ({code
    #put st_61_loc := choice_type_from_type_elem
      (st_63) ;;
    st_61 ← get st_61_loc ;;
    let st_61 := type_from_choice_type_elem (st_61) in
     temp_71 ←
      (if (seq_len (b_64)) !=.? (usize 0):bool then ({code
          let '(acc_65, r_66, k_67) :=
            (st_61) in 
           temp_70 ←
            (poly1305_encode_last (pad_len_68) (b_64)) ;; 
          let temp_69 := type_from_choice_type_elem temp_70 in
          let st_61 :=
            ((((temp_69) +% (acc_65)) *% (r_66), r_66, k_67)) in 
          pkg_core_definition.ret (choice_type_from_type_elem ((st_61)))
          } : code (fset.fset0) [interface] _) else (
          pkg_core_definition.ret (choice_type_from_type_elem ((st_61))))) ;; 
    let '(st_61) := type_from_choice_type_elem temp_71 in
    
    pkg_core_definition.ret (choice_type_from_type_elem (st_61))
    } : code ((fset [ st_61_loc])) [interface] _).
Admit Obligations.


Program Definition poly1305_update
  (m_72 : byte_seq)
  (st_73 : poly_state_t)
  : code _ [interface] (choice_type_from_type (poly_state_t)) :=
  ({code
     temp_75 ←
      (poly1305_update_blocks (m_72) (st_73)) ;; 
    let temp_74 := type_from_choice_type_elem temp_75 in
    let st_76 : (field_element_t '× field_element_t '× poly_key_t) :=
      (temp_74) in 
    let last_77 : seq uint8 :=
      (seq_get_remainder_chunk (m_72) (blocksize_v)) in 
     temp_79 ←
      (poly1305_update_last (seq_len (last_77)) (last_77) (st_76)) ;; 
    let temp_78 := type_from_choice_type_elem temp_79 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_78))
    } : code (fset.fset0) [interface] _).
Admit Obligations.


Program Definition poly1305_finish
  (st_80 : poly_state_t)
  : code _ [interface] (choice_type_from_type (poly1305_tag_t)) :=
  ({code
    let '(acc_81, _, k_82) :=
      (st_80) in 
     temp_84 ←
      (array_from_slice (default) (16) (k_82) (usize 16) (usize 16)) ;; 
    let temp_83 := type_from_choice_type_elem temp_84 in
     temp_86 ←
      (uint128_from_le_bytes (temp_83)) ;; 
    let temp_85 := type_from_choice_type_elem temp_86 in
    let n_87 : uint128 :=
      (temp_85) in 
    let aby_88 : seq uint8 :=
      (nat_mod_to_byte_seq_le (acc_81)) in 
     temp_90 ←
      (array_from_slice (default) (16) (aby_88) (usize 0) (usize 16)) ;; 
    let temp_89 := type_from_choice_type_elem temp_90 in
     temp_92 ←
      (uint128_from_le_bytes (temp_89)) ;; 
    let temp_91 := type_from_choice_type_elem temp_92 in
    let a_93 : uint128 :=
      (temp_91) in 
     temp_95 ←
      (uint128_to_le_bytes ((a_93) .+ (n_87))) ;; 
    let temp_94 := type_from_choice_type_elem temp_95 in
     temp_97 ←
      (array_from_seq (16) (temp_94)) ;; 
    let temp_96 := type_from_choice_type_elem temp_97 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_96))
    } : code (fset.fset0) [interface] _).
Admit Obligations.

Definition st_98_loc : Location :=
  (choice_type_from_type (field_element_t '× field_element_t '× poly_key_t
    ) ; 99%nat).
Program Definition poly1305
  (m_103 : byte_seq)
  (key_100 : poly_key_t)
  : code _ [interface] (choice_type_from_type (poly1305_tag_t)) :=
  ({code
     temp_102 ←
      (poly1305_init (key_100)) ;; 
    let temp_101 := type_from_choice_type_elem temp_102 in
    #put st_98_loc := choice_type_from_type_elem
      (temp_101) ;;
    st_98 ← get st_98_loc ;;
    let st_98 := type_from_choice_type_elem (st_98) in
     temp_105 ←
      (poly1305_update (m_103) (st_98)) ;; 
    let temp_104 := type_from_choice_type_elem temp_105 in
    let st_98 :=
      (temp_104) in 
     temp_107 ←
      (poly1305_finish (st_98)) ;; 
    let temp_106 := type_from_choice_type_elem temp_107 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_106))
    } : code ((fset [ st_98_loc])) [interface] _).
Admit Obligations.

