(** This file was automatically generated using Hacspec **)
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.

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

Definition poly1305_encode_r
  (b_0 : poly_block_t)
  : code fset.fset0 [interface] (choice_type_from_type (field_element_t)) :=
  ({code
     temp_2 ←
      (array_from_seq (16) (b_0)) ;; 
    let temp_1 := type_from_choice_type_elem temp_2 in
     temp_4 ←
      (uint128_from_le_bytes (temp_1)) ;; 
    let temp_3 := type_from_choice_type_elem temp_4 in
    let n_5 : uint128 :=
      (temp_3) in 
     temp_7 ←
      (secret (@repr WORDSIZE128 21267647620597763993911028882763415551)) ;; 
    let temp_6 := type_from_choice_type_elem temp_7 : int128 in
    let n_5 :=
      ((n_5) .& (temp_6)) in 
     temp_9 ←
      (nat_mod_from_secret_literal (n_5)) ;; 
    let temp_8 := type_from_choice_type_elem temp_9 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_8))
    }).

Definition poly1305_encode_block
  (b_10 : poly_block_t)
  : code fset.fset0 [interface] (choice_type_from_type (field_element_t)) :=
  ({code
     temp_12 ←
      (array_from_seq (16) (b_10)) ;; 
    let temp_11 := type_from_choice_type_elem temp_12 in
     temp_14 ←
      (uint128_from_le_bytes (temp_11)) ;; 
    let temp_13 := type_from_choice_type_elem temp_14 in
    let n_15 : uint128 :=
      (temp_13) in 
     temp_17 ←
      (nat_mod_from_secret_literal (n_15)) ;; 
    let temp_16 := type_from_choice_type_elem temp_17 in
    let f_18 : field_element_t :=
      (temp_16) in 
     temp_20 ←
      (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (usize 128)) ;; 
    let temp_19 := type_from_choice_type_elem temp_20 : field_element_t in
    pkg_core_definition.ret (choice_type_from_type_elem ((f_18) +% (temp_19)))
    }).

Definition poly1305_encode_last
  (pad_len_21 : block_index_t)
  (b_22 : sub_block_t)
  : code fset.fset0 [interface] (choice_type_from_type (field_element_t)) :=
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
     temp_32 ←
      (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) * (
            pad_len_21))) ;; 
    let temp_31 := type_from_choice_type_elem temp_32 : field_element_t in
    pkg_core_definition.ret (choice_type_from_type_elem ((f_30) +% (temp_31)))
    }).

Definition poly1305_init
  (k_33 : poly_key_t)
  : code fset.fset0 [interface] (choice_type_from_type (poly_state_t)) :=
  ({code
     temp_35 ←
      (array_from_slice (default) (16) (k_33) (usize 0) (usize 16)) ;; 
    let temp_34 := type_from_choice_type_elem temp_35 in
     temp_37 ←
      (poly1305_encode_r (temp_34)) ;; 
    let temp_36 := type_from_choice_type_elem temp_37 in
    let r_38 : field_element_t :=
      (temp_36) in 
     temp_40 ←
      (nat_mod_zero ) ;; 
    let temp_39 := type_from_choice_type_elem temp_40 in
    pkg_core_definition.ret (choice_type_from_type_elem ((temp_39, r_38, k_33)))
    }).

Definition poly1305_update_block
  (b_41 : poly_block_t)
  (st_42 : poly_state_t)
  : code fset.fset0 [interface] (choice_type_from_type (poly_state_t)) :=
  ({code
    let '(acc_43, r_44, k_45) :=
      (st_42) in 
     temp_47 ←
      (poly1305_encode_block (b_41)) ;; 
    let temp_46 := type_from_choice_type_elem temp_47 in
    pkg_core_definition.ret (choice_type_from_type_elem ((
        ((temp_46) +% (acc_43)) *% (r_44),
        r_44,
        k_45
      )))
    }).

Definition poly1305_update_blocks
  (m_48 : byte_seq)
  (st_49 : poly_state_t)
  : code fset.fset0 [interface] (choice_type_from_type (poly_state_t)) :=
  ({code
    let st_50 : (field_element_t '× field_element_t '× poly_key_t) :=
      (st_49) in 
    let n_blocks_51 : uint_size :=
      ((seq_len (m_48)) / (blocksize_v)) in 
     temp_58 ←
      (foldi (usize 0) (n_blocks_51) (fun i_52 st_50 =>
          {code
           temp_54 ←
            (array_from_seq (16) (seq_get_exact_chunk (m_48) (blocksize_v) (
                  i_52))) ;; 
          let temp_53 := type_from_choice_type_elem temp_54 in
          let block_55 : poly_block_t :=
            (temp_53) in 
           temp_57 ←
            (poly1305_update_block (block_55) (st_50)) ;; 
          let temp_56 := type_from_choice_type_elem temp_57 in
          let st_50 :=
            (temp_56) in 
          pkg_core_definition.ret (choice_type_from_type_elem ((st_50)))
          })
        st_50) ;; 
    let st_50 := type_from_choice_type_elem temp_58 in
    
    pkg_core_definition.ret (choice_type_from_type_elem (st_50))
    }).

Definition poly1305_update_last
  (pad_len_59 : uint_size)
  (b_60 : sub_block_t)
  (st_61 : poly_state_t)
  : code fset.fset0 [interface] (choice_type_from_type (poly_state_t)) :=
  ({code
    let st_62 : (field_element_t '× field_element_t '× poly_key_t) :=
      (st_61) in 
     temp_68 ←
      (if (seq_len (b_60)) !=.? (usize 0):bool then ({code
          let '(acc_63, r_64, k_65) :=
            (st_62) in 
           temp_67 ←
            (poly1305_encode_last (pad_len_59) (b_60)) ;; 
          let temp_66 := type_from_choice_type_elem temp_67 in
          let st_62 :=
            ((((temp_66) +% (acc_63)) *% (r_64), r_64, k_65)) in 
          pkg_core_definition.ret (choice_type_from_type_elem ((st_62)))
          }) else (pkg_core_definition.ret (choice_type_from_type_elem ((st_62
            ))))) ;; 
    let '(st_62) := type_from_choice_type_elem temp_68 in
    
    pkg_core_definition.ret (choice_type_from_type_elem (st_62))
    }).

Definition poly1305_update
  (m_69 : byte_seq)
  (st_70 : poly_state_t)
  : code fset.fset0 [interface] (choice_type_from_type (poly_state_t)) :=
  ({code
     temp_72 ←
      (poly1305_update_blocks (m_69) (st_70)) ;; 
    let temp_71 := type_from_choice_type_elem temp_72 in
    let st_73 : (field_element_t '× field_element_t '× poly_key_t) :=
      (temp_71) in 
    let last_74 : seq uint8 :=
      (seq_get_remainder_chunk (m_69) (blocksize_v)) in 
     temp_76 ←
      (poly1305_update_last (seq_len (last_74)) (last_74) (st_73)) ;; 
    let temp_75 := type_from_choice_type_elem temp_76 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_75))
    }).

Definition poly1305_finish
  (st_77 : poly_state_t)
  : code fset.fset0 [interface] (choice_type_from_type (poly1305_tag_t)) :=
  ({code
    let '(acc_78, _, k_79) :=
      (st_77) in 
     temp_81 ←
      (array_from_slice (default) (16) (k_79) (usize 16) (usize 16)) ;; 
    let temp_80 := type_from_choice_type_elem temp_81 in
     temp_83 ←
      (uint128_from_le_bytes (temp_80)) ;; 
    let temp_82 := type_from_choice_type_elem temp_83 in
    let n_84 : uint128 :=
      (temp_82) in 
    let aby_85 : seq uint8 :=
      (nat_mod_to_byte_seq_le (acc_78)) in 
     temp_87 ←
      (array_from_slice (default) (16) (aby_85) (usize 0) (usize 16)) ;; 
    let temp_86 := type_from_choice_type_elem temp_87 in
     temp_89 ←
      (uint128_from_le_bytes (temp_86)) ;; 
    let temp_88 := type_from_choice_type_elem temp_89 in
    let a_90 : uint128 :=
      (temp_88) in 
     temp_92 ←
      (uint128_to_le_bytes ((a_90) .+ (n_84))) ;; 
    let temp_91 := type_from_choice_type_elem temp_92 in
     temp_94 ←
      (array_from_seq (16) (temp_91)) ;; 
    let temp_93 := type_from_choice_type_elem temp_94 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_93))
    }).

Definition poly1305
  (m_95 : byte_seq)
  (key_96 : poly_key_t)
  : code fset.fset0 [interface] (choice_type_from_type (poly1305_tag_t)) :=
  ({code
     temp_98 ←
      (poly1305_init (key_96)) ;; 
    let temp_97 := type_from_choice_type_elem temp_98 in
    let st_99 : (field_element_t '× field_element_t '× poly_key_t) :=
      (temp_97) in 
     temp_101 ←
      (poly1305_update (m_95) (st_99)) ;; 
    let temp_100 := type_from_choice_type_elem temp_101 in
    let st_99 :=
      (temp_100) in 
     temp_103 ←
      (poly1305_finish (st_99)) ;; 
    let temp_102 := type_from_choice_type_elem temp_103 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_102))
    }).

