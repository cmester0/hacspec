(** This file was automatically generated using Hacspec **)

From mathcomp Require all_ssreflect. (* ssreflect *) (* seq tuple *)
Import (* -(coercions) *) all_ssreflect.

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
intros ; do 2 ssprove_valid_2.

Require Import Hacspec_Lib.

Definition poly_key_t := nseq' (uint8_choice) (usize 32).

Definition blocksize_v : uint_size :=
  (usize 16).

Definition poly_block_t := nseq (uint8_choice) (usize 16).

Definition poly1305_tag_t := nseq (uint8_choice) (usize 16).

Notation "'sub_block_t'" := (byte_seq) : hacspec_scope.

Notation "'block_index_t'" := (uint_size) : hacspec_scope.

Definition field_canvas_t := nseq (int8_choice) (17).
Definition field_element_t := nat_mod_choice 0x03fffffffffffffffffffffffffffffffb.

Check (field_element_t × field_element_t × poly_key_t).

Notation "'poly_state_t'" := ((
  field_element_t ×
  field_element_t ×
  poly_key_t
) : choice_type) : hacspec_scope.

Definition n_5_loc : Location :=
  ((*choice_type_from_type*) uint128_choice ; 11%nat).
Program Definition poly1305_encode_r
  (b_0 : poly_block_t)
  : code (fset [::  n_5_loc]) [interface] ((* choice_type_from_type *) (
      field_element_t)).
  refine ({code
     temp_2 ←
      (@array_from_seq _ int_default (16) (array_to_seq b_0)) ;;
    let temp_1 := (*type_from_choice_type_elem*) temp_2 in
     temp_4 ←
      (uint128_from_le_bytes (temp_1)) ;;
    let temp_3 := (*type_from_choice_type_elem*) temp_4 in
    #put n_5_loc := (* choice_type_from_type_elem *)
      (temp_3) ;;
    n_5 ← get n_5_loc ;;
    
     temp_7 ←
      (secret (@repr WORDSIZE128 21267647620597763993911028882763415551)) ;;
    let temp_6 := (*type_from_choice_type_elem*) temp_7 : int128 in
    n_5 ← get n_5_loc ;;
    
    #put n_5_loc := (* choice_type_from_type_elem *)
      ((n_5) .& (temp_6)) ;;
    n_5 ← get n_5_loc ;;
    
     temp_9 ←
      (nat_mod_from_secret_literal (n_5)) ;;
    let temp_8 := (*type_from_choice_type_elem*) temp_9 in
    pkg_core_definition.ret ((*choice_type_from_type_elem*) (temp_8))
    } : code ((fset [::  n_5_loc])) [interface] _).
  
  apply valid_bind.
  ssprove_valid_program.
  intros.
  
  apply valid_bind.
  ssprove_valid_program.
  intros.

  apply (@valid_putr (fset [:: n_5_loc]) [interface] field_element_t n_5_loc _).
  rewrite <- fset1E.
  rewrite in_fset1.
  apply eq_refl.

  apply (@valid_getr (fset [:: n_5_loc]) [interface] field_element_t n_5_loc).
  rewrite <- fset1E.
  rewrite in_fset1.
  apply eq_refl.
  intros.
  
  apply valid_bind.
  ssprove_valid_program.
  intros.

  apply (@valid_getr (fset [:: n_5_loc]) [interface] field_element_t n_5_loc).
  rewrite <- fset1E.
  rewrite in_fset1.
  apply eq_refl.
  intros.

  apply (@valid_putr (fset [:: n_5_loc]) [interface] field_element_t n_5_loc _).
  rewrite <- fset1E.
  rewrite in_fset1.
  apply eq_refl.

  apply (@valid_getr (fset [:: n_5_loc]) [interface] field_element_t n_5_loc).
  rewrite <- fset1E.
  rewrite in_fset1.
  apply eq_refl.
  intros.

  apply valid_bind.
  ssprove_valid_program.
  intros.

  ssprove_valid_2.
Defined.  
  
Program Definition poly1305_encode_block
  (b_12 : poly_block_t)
  : code fset.fset0 [interface] ((* choice_type_from_type *) (
      field_element_t)) :=
  ({code
     temp_14 ←
      (array_from_seq (16) (array_to_seq b_12)) ;;
    let temp_13 := (*type_from_choice_type_elem*) temp_14 in
     temp_16 ←
      (uint128_from_le_bytes (temp_13)) ;;
    let temp_15 := (*type_from_choice_type_elem*) temp_16 in
    let n_17 : uint128 :=
      (temp_15) in 
     temp_19 ←
      (nat_mod_from_secret_literal (n_17)) ;;
    let temp_18 := (*type_from_choice_type_elem*) temp_19 in
    let f_20 : field_element_t :=
      (temp_18) in 
     temp_22 ←
      (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (usize 128)) ;;
    let temp_21 := (*type_from_choice_type_elem*) temp_22 : field_element_t in
    pkg_core_definition.ret ((*choice_type_from_type_elem*) ((f_20) +% (
        temp_21)))
    } : code (fset.fset0) [interface] _).


Program Definition poly1305_encode_last
  (pad_len_32 : block_index_t)
  (b_23 : sub_block_t)
  : code fset.fset0 [interface] ((* choice_type_from_type *) (
      field_element_t)) :=
  ({code
     temp_25 ←
      (array_from_slice (default) (16) (b_23) (usize 0) (seq_len (b_23))) ;;
    let temp_24 := (*type_from_choice_type_elem*) temp_25 in
     temp_27 ←
      (uint128_from_le_bytes (temp_24)) ;;
    let temp_26 := (*type_from_choice_type_elem*) temp_27 in
    let n_28 : uint128 :=
      (temp_26) in 
     temp_30 ←
      (nat_mod_from_secret_literal (n_28)) ;;
    let temp_29 := (*type_from_choice_type_elem*) temp_30 in
    let f_31 : field_element_t :=
      (temp_29) in 
     temp_34 ←
      (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) * (
            pad_len_32))) ;;
    let temp_33 := (*type_from_choice_type_elem*) temp_34 : field_element_t in
    pkg_core_definition.ret ((*choice_type_from_type_elem*) ((f_31) +% (
        temp_33)))
    } : code (fset.fset0) [interface] _).


Program Definition poly1305_init
  (k_35 : poly_key_t)
  : code (fset [::  n_5_loc]) [interface] ((* choice_type_from_type *) (
                                             poly_state_t)).
  refine ({code
     temp_37 ←
      (array_from_slice (default) (16) (array_to_seq k_35) (usize 0) (usize 16)) ;;
    let temp_36 := (*type_from_choice_type_elem*) temp_37 in
     temp_39 ←
      (poly1305_encode_r (temp_36)) ;;
    let temp_38 := (*type_from_choice_type_elem*) temp_39 in
    let r_42 : field_element_t :=
      (temp_38) in 
     temp_41 ←
      (nat_mod_zero ) ;;
    let temp_40 := (*type_from_choice_type_elem*) temp_41 in
    pkg_core_definition.ret ((*choice_type_from_type_elem*) ((
        temp_40,
        r_42,
        k_35
      )))
           } : code ((fset [::  n_5_loc])) [interface] _).
  apply valid_bind.
  ssprove_valid_program.
  intros.

  apply valid_bind.
  ssprove_valid_program.
  intros.

  apply valid_bind.
  ssprove_valid_program.
  intros.

  ssprove_valid.
Qed.  


Program Definition poly1305_update_block
  (b_44 : poly_block_t)
  (st_43 : poly_state_t)
  : code fset.fset0 [interface] ((* choice_type_from_type *) (poly_state_t)) :=
  ({code
    let '(acc_47, r_48, k_49) :=
      (st_43) in 
     temp_46 ←
      (poly1305_encode_block (b_44)) ;;
    let temp_45 := (*type_from_choice_type_elem*) temp_46 in
    pkg_core_definition.ret ((*choice_type_from_type_elem*) ((
        ((temp_45) +% (acc_47)) *% (r_48),
        r_48,
        k_49
      )))
    } : code (fset.fset0) [interface] _).

Definition st_57_loc : Location :=
  ((*choice_type_from_type*) (field_element_t '× field_element_t '× poly_key_t
    ) ; 63%nat).
Program Definition poly1305_update_blocks
  (m_51 : byte_seq)
  (st_50 : poly_state_t)
  : code (fset [::  st_57_loc]) [interface] ((* choice_type_from_type *) (
      poly_state_t)) :=
  ({code
    #put st_57_loc := (* choice_type_from_type_elem *)
      (st_50) ;;
    st_57 ← get st_57_loc ;;
    
    let n_blocks_52 : uint_size :=
      ((seq_len (m_51)) / (blocksize_v)) in 
     temp_61 ←
      (foldi (usize 0) (n_blocks_52) (fun i_53 st_57 =>
          {code
           temp_55 ←
            (array_from_seq (16) (seq_get_exact_chunk (m_51) (blocksize_v) (
                  i_53))) ;;
          let temp_54 := (*type_from_choice_type_elem*) temp_55 in
          let block_56 : poly_block_t :=
            (temp_54) in 
           temp_59 ←
            (poly1305_update_block (block_56) (st_57)) ;;
          let temp_58 := (*type_from_choice_type_elem*) temp_59 in
          st_57 ← get st_57_loc ;;
          
          #put st_57_loc := (* choice_type_from_type_elem *)
            (temp_58) ;;
          st_57 ← get st_57_loc ;;
          
          pkg_core_definition.ret ((*choice_type_from_type_elem*) ((st_57)))
          } : code ((fset [::  st_57_loc])) [interface] _)
        st_57) ;; let st_57 := (*type_from_choice_type_elem*) temp_61 in
    
    pkg_core_definition.ret ((*choice_type_from_type_elem*) (st_57))
    } : code ((fset [::  st_57_loc])) [interface] _).

Definition st_65_loc : Location :=
  ((*choice_type_from_type*) (field_element_t '× field_element_t '× poly_key_t
    ) ; 76%nat).
Program Definition poly1305_update_last
  (pad_len_67 : uint_size)
  (b_66 : sub_block_t)
  (st_64 : poly_state_t)
  : code (fset [::  st_65_loc]) [interface] ((* choice_type_from_type *) (
      poly_state_t)) :=
  ({code
    #put st_65_loc := (* choice_type_from_type_elem *)
      (st_64) ;;
    st_65 ← get st_65_loc ;;
    
     temp_74 ←
      (if (seq_len (b_66)) !=.? (usize 0):bool then ({code
          let '(acc_70, r_71, k_72) :=
            (st_65) in 
           temp_69 ←
            (poly1305_encode_last (pad_len_67) (b_66)) ;;
          let temp_68 := (*type_from_choice_type_elem*) temp_69 in
          st_65 ← get st_65_loc ;;
          
          #put st_65_loc := (* choice_type_from_type_elem *)
            ((((temp_68) +% (acc_70)) *% (r_71), r_71, k_72)) ;;
          st_65 ← get st_65_loc ;;
          
          pkg_core_definition.ret ((*choice_type_from_type_elem*) ((st_65)))
          } : code ((fset [::  st_65_loc])) [interface] _) else (
          pkg_core_definition.ret ((*choice_type_from_type_elem*) ((st_65
            ))))) ;; let '(st_65) := (*type_from_choice_type_elem*) temp_74 in
    
    pkg_core_definition.ret ((*choice_type_from_type_elem*) (st_65))
    } : code ((fset [::  st_65_loc])) [interface] _).


Program Definition poly1305_update
  (m_77 : byte_seq)
  (st_78 : poly_state_t)
  : code (fset [::  st_65_loc ; st_57_loc]) [interface] (
    (* choice_type_from_type *) (poly_state_t)) :=
  ({code
     temp_80 ←
      (poly1305_update_blocks (m_77) (st_78)) ;;
    let temp_79 := (*type_from_choice_type_elem*) temp_80 in
    let st_82 : (field_element_t '× field_element_t '× poly_key_t) :=
      (temp_79) in 
    let last_81 : seq uint8 :=
      (seq_get_remainder_chunk (m_77) (blocksize_v)) in 
     temp_84 ←
      (poly1305_update_last (seq_len (last_81)) (last_81) (st_82)) ;;
    let temp_83 := (*type_from_choice_type_elem*) temp_84 in
    pkg_core_definition.ret ((*choice_type_from_type_elem*) (temp_83))
    } : code ((fset [::  st_65_loc ; st_57_loc])) [interface] _).


Program Definition poly1305_finish
  (st_85 : poly_state_t)
  : code fset.fset0 [interface] ((* choice_type_from_type *) (
      poly1305_tag_t)) :=
  ({code
    let '(acc_91, _, k_86) :=
      (st_85) in 
     temp_88 ←
      (array_from_slice (default) (16) (k_86) (usize 16) (usize 16)) ;;
    let temp_87 := (*type_from_choice_type_elem*) temp_88 in
     temp_90 ←
      (uint128_from_le_bytes (temp_87)) ;;
    let temp_89 := (*type_from_choice_type_elem*) temp_90 in
    let n_98 : uint128 :=
      (temp_89) in 
    let aby_92 : seq uint8 :=
      (nat_mod_to_byte_seq_le (acc_91)) in 
     temp_94 ←
      (array_from_slice (default) (16) (aby_92) (usize 0) (usize 16)) ;;
    let temp_93 := (*type_from_choice_type_elem*) temp_94 in
     temp_96 ←
      (uint128_from_le_bytes (temp_93)) ;;
    let temp_95 := (*type_from_choice_type_elem*) temp_96 in
    let a_97 : uint128 :=
      (temp_95) in 
     temp_100 ←
      (uint128_to_le_bytes ((a_97) .+ (n_98))) ;;
    let temp_99 := (*type_from_choice_type_elem*) temp_100 in
     temp_102 ←
      (array_from_seq (16) (temp_99)) ;;
    let temp_101 := (*type_from_choice_type_elem*) temp_102 in
    pkg_core_definition.ret ((*choice_type_from_type_elem*) (temp_101))
    } : code (fset.fset0) [interface] _).

Definition st_107_loc : Location :=
  ((*choice_type_from_type*) (field_element_t '× field_element_t '× poly_key_t
    ) ; 113%nat).
Program Definition poly1305
  (m_106 : byte_seq)
  (key_103 : poly_key_t)
  : code (fset [::  st_57_loc ; st_107_loc ; n_5_loc ; st_65_loc]) [interface] (
    (* choice_type_from_type *) (poly1305_tag_t)) :=
  ({code
     temp_105 ←
      (poly1305_init (key_103)) ;;
    let temp_104 := (*type_from_choice_type_elem*) temp_105 in
    #put st_107_loc := (* choice_type_from_type_elem *)
      (temp_104) ;;
    st_107 ← get st_107_loc ;;
    
     temp_109 ←
      (poly1305_update (m_106) (st_107)) ;;
    let temp_108 := (*type_from_choice_type_elem*) temp_109 in
    st_107 ← get st_107_loc ;;
    
    #put st_107_loc := (* choice_type_from_type_elem *)
      (temp_108) ;;
    st_107 ← get st_107_loc ;;
    
     temp_111 ←
      (poly1305_finish (st_107)) ;;
    let temp_110 := (*type_from_choice_type_elem*) temp_111 in
    pkg_core_definition.ret ((*choice_type_from_type_elem*) (temp_110))
    } : code ((
        fset [::  st_57_loc ; st_107_loc ; n_5_loc ; st_65_loc])) [interface] _).

