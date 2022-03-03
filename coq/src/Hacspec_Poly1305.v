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

Definition poly_key_t := nseq (uint8) (usize 32 : uint_size_type).

Definition blocksize_v : uint_size :=
  (usize 16).

Definition poly_block_t := nseq (uint8) (usize 16 : uint_size_type).

Definition poly1305_tag_t := nseq (uint8) (usize 16 : uint_size_type).

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
  (@ct uint128 ; 11%nat).
Program Definition poly1305_encode_r
  (b_0 : poly_block_t)
  : code (fset [ n_5_loc]) [interface] ( (field_element_t)) :=
  ({code
     temp_2 ←
      (array_from_seq (16) (b_0)) ;; 
    let temp_1 := temp_2 in
     temp_4 ←
      (uint128_from_le_bytes (temp_1)) ;; 
    let temp_3 := temp_4 in
    #put n_5_loc := 
      (temp_3) ;;
    n_5 ← get n_5_loc ;;
     temp_7 ←
      (secret (@repr WORDSIZE128 21267647620597763993911028882763415551)) ;; 
    let temp_6 := temp_7 : int128 in
    let n_5 :=
      ((n_5) .& (temp_6)) in 
     temp_9 ←
      (nat_mod_from_secret_literal (n_5)) ;; 
    let temp_8 := temp_9 in
    pkg_core_definition.ret ( (temp_8))
    } : code ((fset [ n_5_loc])) [interface] _).


Program Definition poly1305_encode_block
  (b_12 : poly_block_t)
  : code fset.fset0 [interface] ( (field_element_t)) :=
  ({code
     temp_14 ←
      (array_from_seq (16) (b_12)) ;; 
    let temp_13 := temp_14 in
     temp_16 ←
      (uint128_from_le_bytes (temp_13)) ;; 
    let temp_15 := temp_16 in
    let n_17 : uint128 :=
      (temp_15) in 
     temp_19 ←
      (nat_mod_from_secret_literal (n_17)) ;; 
    let temp_18 := temp_19 in
    let f_20 : field_element_t :=
      (temp_18) in 
     temp_22 ←
      (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (usize 128 : uint_size_type)) ;; 
    let temp_21 := temp_22 : field_element_t in
    pkg_core_definition.ret ( ((f_20) +% (temp_21)))
    } : code (fset.fset0) [interface] _).


Program Definition poly1305_encode_last
  (pad_len_32 : block_index_t)
  (b_23 : sub_block_t)
  : code fset.fset0 [interface] ( (field_element_t)) :=
  ({code
     temp_25 ←
      (array_from_slice (default) (16) (b_23) (usize 0 : uint_size_type) (seq_len (b_23))) ;; 
    let temp_24 := temp_25 in
     temp_27 ←
      (uint128_from_le_bytes (temp_24)) ;; 
    let temp_26 := temp_27 in
    let n_28 : uint128 :=
      (temp_26) in 
     temp_30 ←
      (nat_mod_from_secret_literal (n_28)) ;; 
    let temp_29 := temp_30 in
    let f_31 : field_element_t :=
      (temp_29) in 
     temp_34 ←
      (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8 : uint_size_type) * (
            pad_len_32 : uint_size_type))) ;; 
    let temp_33 := temp_34 : field_element_t in
    pkg_core_definition.ret ( ((f_31) +% (temp_33)))
    } : code (fset.fset0) [interface] _).

Definition n_43_loc : Location :=
  ( _ ; 45%nat).
Program Definition poly1305_init
  (k_35 : poly_key_t)
  : code (fset [ n_43_loc]) [interface] ( (poly_state_t)) :=
  ({code
     temp_37 ←
      (array_from_slice (default) (16) (k_35) (usize 0) (usize 16)) ;; 
    let temp_36 := temp_37 in
     temp_39 ←
      (poly1305_encode_r (temp_36)) ;; 
    let temp_38 := temp_39 in
    let r_42 : field_element_t :=
      (temp_38) in 
     temp_41 ←
      (nat_mod_zero ) ;; 
    let temp_40 := temp_41 in
    pkg_core_definition.ret ( ((temp_40, r_42, k_35)))
    } : code ((fset [ n_43_loc])) [interface] _).


Program Definition poly1305_update_block
  (b_47 : poly_block_t)
  (st_46 : poly_state_t)
  : code fset.fset0 [interface] ( (poly_state_t)) :=
  ({code
    let '(acc_50, r_51, k_52) :=
      (st_46) in 
     temp_49 ←
      (poly1305_encode_block (b_47)) ;; 
    let temp_48 := temp_49 in
    pkg_core_definition.ret ( ((((temp_48) +% (acc_50)) *% (r_51), r_51, k_52)))
    } : code (fset.fset0) [interface] _).

Definition st_60_loc : Location :=
  ( (field_element_t '× field_element_t '× poly_key_t) ; 65%nat).
Program Definition poly1305_update_blocks
  (m_54 : byte_seq)
  (st_53 : poly_state_t)
  : code (fset [ st_60_loc]) [interface] ( (poly_state_t)) :=
  ({code
    #put st_60_loc := 
      (st_53) ;;
    st_60 ← get st_60_loc ;;
    let n_blocks_55 : uint_size :=
      ((seq_len (m_54)) / (blocksize_v)) in 
     temp_63 ←
      (foldi (usize 0) (n_blocks_55) (fun i_56 st_60 =>
          {code
           temp_58 ←
            (array_from_seq (16) (seq_get_exact_chunk (m_54) (blocksize_v) (
                  i_56))) ;; 
          let temp_57 := temp_58 in
          let block_59 : poly_block_t :=
            (temp_57) in 
           temp_62 ←
            (poly1305_update_block (block_59) (st_60)) ;; 
          let temp_61 := temp_62 in
          let st_60 :=
            (temp_61) in 
          pkg_core_definition.ret ( ((st_60)))
          } : code (fset.fset0) [interface] _)
        st_60) ;; 
    let st_60 := temp_63 in
    
    pkg_core_definition.ret ( (st_60))
    } : code ((fset [ st_60_loc])) [interface] _).

Definition st_67_loc : Location :=
  ( (field_element_t '× field_element_t '× poly_key_t) ; 77%nat).
Program Definition poly1305_update_last
  (pad_len_69 : uint_size)
  (b_68 : sub_block_t)
  (st_66 : poly_state_t)
  : code (fset [ st_67_loc]) [interface] ( (poly_state_t)) :=
  ({code
    #put st_67_loc := 
      (st_66) ;;
    st_67 ← get st_67_loc ;;
     temp_75 ←
      (if (seq_len (b_68)) !=.? (usize 0):bool then ({code
          let '(acc_72, r_73, k_74) :=
            (st_67) in 
           temp_71 ←
            (poly1305_encode_last (pad_len_69) (b_68)) ;; 
          let temp_70 := temp_71 in
          let st_67 :=
            ((((temp_70) +% (acc_72)) *% (r_73), r_73, k_74)) in 
          pkg_core_definition.ret ( ((st_67)))
          } : code (fset.fset0) [interface] _) else (pkg_core_definition.ret ( (
            (st_67))))) ;; 
    let '(st_67) := temp_75 in
    
    pkg_core_definition.ret ( (st_67))
    } : code ((fset [ st_67_loc])) [interface] _).

Definition st_86_loc : Location :=
  ( _ ; 90%nat).
Definition st_87_loc : Location :=
  ( _ ; 91%nat).
Program Definition poly1305_update
  (m_78 : byte_seq)
  (st_79 : poly_state_t)
  : code (fset [ st_86_loc ; st_87_loc]) [interface] ( (poly_state_t)) :=
  ({code
     temp_81 ←
      (poly1305_update_blocks (m_78) (st_79)) ;; 
    let temp_80 := temp_81 in
    let st_83 : (field_element_t '× field_element_t '× poly_key_t) :=
      (temp_80) in 
    let last_82 : seq uint8 :=
      (seq_get_remainder_chunk (m_78) (blocksize_v)) in 
     temp_85 ←
      (poly1305_update_last (seq_len (last_82)) (last_82) (st_83)) ;; 
    let temp_84 := temp_85 in
    pkg_core_definition.ret ( (temp_84))
    } : code ((fset [ st_86_loc ; st_87_loc])) [interface] _).


Program Definition poly1305_finish
  (st_92 : poly_state_t)
  : code fset.fset0 [interface] ( (poly1305_tag_t)) :=
  ({code
    let '(acc_98, _, k_93) :=
      (st_92) in 
     temp_95 ←
      (array_from_slice (default) (16) (k_93) (usize 16) (usize 16)) ;; 
    let temp_94 := temp_95 in
     temp_97 ←
      (uint128_from_le_bytes (temp_94)) ;; 
    let temp_96 := temp_97 in
    let n_105 : uint128 :=
      (temp_96) in 
    let aby_99 : seq uint8 :=
      (nat_mod_to_byte_seq_le (acc_98)) in 
     temp_101 ←
      (array_from_slice (default) (16) (aby_99) (usize 0) (usize 16)) ;; 
    let temp_100 := temp_101 in
     temp_103 ←
      (uint128_from_le_bytes (temp_100)) ;; 
    let temp_102 := temp_103 in
    let a_104 : uint128 :=
      (temp_102) in 
     temp_107 ←
      (uint128_to_le_bytes ((a_104) .+ (n_105))) ;; 
    let temp_106 := temp_107 in
     temp_109 ←
      (array_from_seq (16) (temp_106)) ;; 
    let temp_108 := temp_109 in
    pkg_core_definition.ret ( (temp_108))
    } : code (fset.fset0) [interface] _).

Definition st_114_loc : Location :=
  ( (field_element_t '× field_element_t '× poly_key_t) ; 120%nat).
Program Definition poly1305
  (m_113 : byte_seq)
  (key_110 : poly_key_t)
  : code (fset [ st_114_loc]) [interface] ( (poly1305_tag_t)) :=
  ({code
     temp_112 ←
      (poly1305_init (key_110)) ;; 
    let temp_111 := temp_112 in
    #put st_114_loc := 
      (temp_111) ;;
    st_114 ← get st_114_loc ;;
     temp_116 ←
      (poly1305_update (m_113) (st_114)) ;; 
    let temp_115 := temp_116 in
    let st_114 :=
      (temp_115) in 
     temp_118 ←
      (poly1305_finish (st_114)) ;; 
    let temp_117 := temp_118 in
    pkg_core_definition.ret ( (temp_117))
    } : code ((fset [ st_114_loc])) [interface] _).

