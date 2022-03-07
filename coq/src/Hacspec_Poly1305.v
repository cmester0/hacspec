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


Obligation Tactic :=
try (Tactics.program_simpl; fail); simpl ; (* Old Obligation Tactic *)
intros ; repeat ssprove_valid_2.

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


Program Definition poly1305_init
  (k_35 : poly_key_t)
  : code (fset [ n_5_loc]) [interface] (choice_type_from_type (poly_state_t)) :=
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
      (nat_mod_zero ) ;; let temp_40 := type_from_choice_type_elem temp_41 in
    pkg_core_definition.ret (choice_type_from_type_elem ((temp_40, r_42, k_35)))
    } : code ((fset [ n_5_loc])) [interface] _).


Program Definition poly1305_update_block
  (b_44 : poly_block_t)
  (st_43 : poly_state_t)
  : code fset.fset0 [interface] (choice_type_from_type (poly_state_t)) :=
  ({code
    let '(acc_47, r_48, k_49) :=
      (st_43) in 
     temp_46 ←
      (poly1305_encode_block (b_44)) ;;
    let temp_45 := type_from_choice_type_elem temp_46 in
    pkg_core_definition.ret (choice_type_from_type_elem ((
        ((temp_45) +% (acc_47)) *% (r_48),
        r_48,
        k_49
      )))
    } : code (fset.fset0) [interface] _).

Definition st_57_loc : Location :=
  (choice_type_from_type (field_element_t '× field_element_t '× poly_key_t
    ) ; 62%nat).
Program Definition poly1305_update_blocks
  (m_51 : byte_seq)
  (st_50 : poly_state_t)
  : code (fset [ st_57_loc]) [interface] (choice_type_from_type (
      poly_state_t)) :=
  ({code
    #put st_57_loc := choice_type_from_type_elem
      (st_50) ;;
    st_57 ← get st_57_loc ;;
    let st_57 := type_from_choice_type_elem (st_57) in
    let n_blocks_52 : uint_size :=
      ((seq_len (m_51)) / (blocksize_v)) in 
     temp_60 ←
      (foldi (usize 0) (n_blocks_52) (fun i_53 st_57 =>
          {code
           temp_55 ←
            (array_from_seq (16) (seq_get_exact_chunk (m_51) (blocksize_v) (
                  i_53))) ;;
          let temp_54 := type_from_choice_type_elem temp_55 in
          let block_56 : poly_block_t :=
            (temp_54) in 
           temp_59 ←
            (poly1305_update_block (block_56) (st_57)) ;;
          let temp_58 := type_from_choice_type_elem temp_59 in
          let st_57 :=
            (temp_58) in 
          pkg_core_definition.ret (choice_type_from_type_elem ((st_57)))
          } : code (fset.fset0) [interface] _)
        st_57) ;; let st_57 := type_from_choice_type_elem temp_60 in
    
    pkg_core_definition.ret (choice_type_from_type_elem (st_57))
    } : code ((fset [ st_57_loc])) [interface] _).

Definition st_64_loc : Location :=
  (choice_type_from_type (field_element_t '× field_element_t '× poly_key_t
    ) ; 74%nat).
Program Definition poly1305_update_last
  (pad_len_66 : uint_size)
  (b_65 : sub_block_t)
  (st_63 : poly_state_t)
  : code (fset [ st_64_loc]) [interface] (choice_type_from_type (
      poly_state_t)) :=
  ({code
    #put st_64_loc := choice_type_from_type_elem
      (st_63) ;;
    st_64 ← get st_64_loc ;;
    let st_64 := type_from_choice_type_elem (st_64) in
     temp_72 ←
      (if (seq_len (b_65)) !=.? (usize 0):bool then ({code
          let '(acc_69, r_70, k_71) :=
            (st_64) in 
           temp_68 ←
            (poly1305_encode_last (pad_len_66) (b_65)) ;;
          let temp_67 := type_from_choice_type_elem temp_68 in
          let st_64 :=
            ((((temp_67) +% (acc_69)) *% (r_70), r_70, k_71)) in 
          pkg_core_definition.ret (choice_type_from_type_elem ((st_64)))
          } : code (fset.fset0) [interface] _) else (
          pkg_core_definition.ret (choice_type_from_type_elem ((st_64))))) ;;
    let '(st_64) := type_from_choice_type_elem temp_72 in
    
    pkg_core_definition.ret (choice_type_from_type_elem (st_64))
    } : code ((fset [ st_64_loc])) [interface] _).


Program Definition poly1305_update
  (m_75 : byte_seq)
  (st_76 : poly_state_t)
  : code (fset [ st_57_loc ; st_64_loc]) [interface] (choice_type_from_type (
      poly_state_t)) :=
  ({code
     temp_78 ←
      (poly1305_update_blocks (m_75) (st_76)) ;;
    let temp_77 := type_from_choice_type_elem temp_78 in
    let st_80 : (field_element_t '× field_element_t '× poly_key_t) :=
      (temp_77) in 
    let last_79 : seq uint8 :=
      (seq_get_remainder_chunk (m_75) (blocksize_v)) in 
     temp_82 ←
      (poly1305_update_last (seq_len (last_79)) (last_79) (st_80)) ;;
    let temp_81 := type_from_choice_type_elem temp_82 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_81))
    } : code ((fset [ st_57_loc ; st_64_loc])) [interface] _).


Program Definition poly1305_finish
  (st_83 : poly_state_t)
  : code fset.fset0 [interface] (choice_type_from_type (poly1305_tag_t)) :=
  ({code
    let '(acc_89, _, k_84) :=
      (st_83) in 
     temp_86 ←
      (array_from_slice (default) (16) (k_84) (usize 16) (usize 16)) ;;
    let temp_85 := type_from_choice_type_elem temp_86 in
     temp_88 ←
      (uint128_from_le_bytes (temp_85)) ;;
    let temp_87 := type_from_choice_type_elem temp_88 in
    let n_96 : uint128 :=
      (temp_87) in 
    let aby_90 : seq uint8 :=
      (nat_mod_to_byte_seq_le (acc_89)) in 
     temp_92 ←
      (array_from_slice (default) (16) (aby_90) (usize 0) (usize 16)) ;;
    let temp_91 := type_from_choice_type_elem temp_92 in
     temp_94 ←
      (uint128_from_le_bytes (temp_91)) ;;
    let temp_93 := type_from_choice_type_elem temp_94 in
    let a_95 : uint128 :=
      (temp_93) in 
     temp_98 ←
      (uint128_to_le_bytes ((a_95) .+ (n_96))) ;;
    let temp_97 := type_from_choice_type_elem temp_98 in
     temp_100 ←
      (array_from_seq (16) (temp_97)) ;;
    let temp_99 := type_from_choice_type_elem temp_100 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_99))
    } : code (fset.fset0) [interface] _).

Definition st_105_loc : Location :=
  (choice_type_from_type (field_element_t '× field_element_t '× poly_key_t
    ) ; 111%nat).
Program Definition poly1305
  (m_104 : byte_seq)
  (key_101 : poly_key_t)
  : code (fset [ n_5_loc ; st_57_loc ; st_64_loc ; st_105_loc]) [interface] (
    choice_type_from_type (poly1305_tag_t)) :=
  ({code
     temp_103 ←
      (poly1305_init (key_101)) ;;
    let temp_102 := type_from_choice_type_elem temp_103 in
    #put st_105_loc := choice_type_from_type_elem
      (temp_102) ;;
    st_105 ← get st_105_loc ;;
    let st_105 := type_from_choice_type_elem (st_105) in
     temp_107 ←
      (poly1305_update (m_104) (st_105)) ;;
    let temp_106 := type_from_choice_type_elem temp_107 in
    let st_105 :=
      (temp_106) in 
     temp_109 ←
      (poly1305_finish (st_105)) ;;
    let temp_108 := type_from_choice_type_elem temp_109 in
    pkg_core_definition.ret (choice_type_from_type_elem (temp_108))
    } : code ((
        fset [ n_5_loc ; st_57_loc ; st_64_loc ; st_105_loc])) [interface] _).

