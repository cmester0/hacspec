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
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.


Obligation Tactic :=
(intros ; do 2 ssprove_valid'_2) ||
(try (Tactics.program_simpl; fail); simpl). (* Old Obligation Tactic *)

Require Import Hacspec_Lib.

Definition poly_key_t := nseq (uint8) (usize 32).

Definition blocksize_v : (uint_size) :=
  ((usize 16)).

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
  (uint128 : choice_type ; 7%nat).
Program Definition poly1305_encode_r
  (b_0 : poly_block_t)
  : code (fset (path.sort leb [ n_4_loc])) [interface] (@ct (
      field_element_t)) :=
  (({code  temp_1 ←
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
      let n_4 : uint128 :=
        (n_4) in
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
      @pkg_core_definition.ret field_element_t ( (temp_6)) } : code (fset (
          path.sort leb [ n_4_loc])) [interface] _)).
Fail Next Obligation.


Program Definition poly1305_encode_block
  (b_8 : poly_block_t)
  : code (fset.fset0) [interface] (@ct (field_element_t)) :=
  (({code  temp_9 ←
        (array_to_seq (b_8)) ;;
      let temp_9 : seq uint8 :=
        (temp_9) in
       temp_10 ←
        (array_from_seq (16) (temp_9)) ;;
       temp_11 ←
        (uint128_from_le_bytes (temp_10)) ;;
      let n_12 : uint128 :=
        (temp_11) in
       temp_13 ←
        (nat_mod_from_secret_literal (n_12)) ;;
      let f_14 : field_element_t :=
        (temp_13) in
       temp_15 ←
        (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (usize 128)) ;;
      let temp_15 : field_element_t :=
        (temp_15) in
      @pkg_core_definition.ret field_element_t ( ((f_14) +% (
          temp_15))) } : code (fset.fset0) [interface] _)).
Fail Next Obligation.


Program Definition poly1305_encode_last
  (pad_len_23 : block_index_t)
  (b_16 : sub_block_t)
  : code (fset.fset0) [interface] (@ct (field_element_t)) :=
  (({code  temp_17 ←
        (seq_len (b_16)) ;;
       temp_18 ←
        (array_from_slice (default) (16) (b_16) (usize 0) (temp_17)) ;;
       temp_19 ←
        (uint128_from_le_bytes (temp_18)) ;;
      let n_20 : uint128 :=
        (temp_19) in
       temp_21 ←
        (nat_mod_from_secret_literal (n_20)) ;;
      let f_22 : field_element_t :=
        (temp_21) in
       temp_24 ←
        (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) .* (
              pad_len_23))) ;;
      let temp_24 : field_element_t :=
        (temp_24) in
      @pkg_core_definition.ret field_element_t ( ((f_22) +% (
          temp_24))) } : code (fset.fset0) [interface] _)).
Fail Next Obligation.


Program Definition poly1305_init
  (k_25 : poly_key_t)
  : code (fset (path.sort leb [ n_4_loc])) [interface] (@ct (poly_state_t)) :=
  (({code  temp_26 ←
        (array_to_seq (k_25)) ;;
      let temp_26 : seq uint8 :=
        (temp_26) in
       temp_27 ←
        (array_from_slice (default) (16) (temp_26) (usize 0) (usize 16)) ;;
       temp_28 ←
        (poly1305_encode_r (temp_27)) ;;
      let r_30 : field_element_t :=
        (temp_28) in
       temp_29 ←
        (nat_mod_zero ) ;;
      @pkg_core_definition.ret (
        field_element_t '×
        field_element_t '×
        poly_key_t
      ) ( ((temp_29, r_30, k_25))) } : code (fset (
          path.sort leb [ n_4_loc])) [interface] _)).
Fail Next Obligation.


Program Definition poly1305_update_block
  (b_32 : poly_block_t)
  (st_31 : poly_state_t)
  : code (fset.fset0) [interface] (@ct (poly_state_t)) :=
  (({code let '(acc_34, r_35, k_36) :=
        (st_31) : (field_element_t '× field_element_t '× poly_key_t) in
       temp_33 ←
        (poly1305_encode_block (b_32)) ;;
      @pkg_core_definition.ret (
        field_element_t '×
        field_element_t '×
        poly_key_t
      ) ( ((((temp_33) +% (acc_34)) *% (r_35), r_35, k_36))) } : code (
        fset.fset0) [interface] _)).
Fail Next Obligation.

Definition st_45_loc : Location :=
  ((field_element_t '× field_element_t '× poly_key_t) : choice_type ; 47%nat).
Program Definition poly1305_update_blocks
  (m_38 : byte_seq)
  (st_37 : poly_state_t)
  : code (fset (path.sort leb [ st_45_loc])) [interface] (@ct (poly_state_t)) :=
  (({code #put st_45_loc := 
        (st_37) ;;
      st_45 ← get st_45_loc ;;
      let st_45 : (field_element_t '× field_element_t '× poly_key_t) :=
        (st_45) in
       temp_39 ←
        (seq_len (m_38)) ;;
      let n_blocks_40 : uint_size :=
        ((temp_39 : uint_size_type) ./ (blocksize_v)) in
       st_45 ←
        (foldi (usize 0) (n_blocks_40) (fun i_41 (st_45 : _) =>
            ({code  temp_42 ←
                (seq_get_exact_chunk (m_38) (blocksize_v) (i_41)) ;;
               temp_43 ←
                (array_from_seq (16) (temp_42 : seq int8)) ;;
              let block_44 : poly_block_t :=
                (temp_43) in
               temp_46 ←
                (poly1305_update_block (block_44) (st_45)) ;;
              st_45 ← get st_45_loc ;;
              
              #put st_45_loc := 
                (temp_46) ;;
              st_45 ← get st_45_loc ;;
              
              @pkg_core_definition.ret _ ( ((st_45))) } : code (fset (
                  path.sort leb [ st_45_loc])) [interface] _))
          st_45) ;;
      
      @pkg_core_definition.ret (
        field_element_t '×
        field_element_t '×
        poly_key_t
      ) ( (st_45)) } : code (fset (path.sort leb [ st_45_loc])) [interface] _)).
Fail Next Obligation.

Definition st_49_loc : Location :=
  ((field_element_t '× field_element_t '× poly_key_t) : choice_type ; 57%nat).
Program Definition poly1305_update_last
  (pad_len_52 : uint_size)
  (b_50 : sub_block_t)
  (st_48 : poly_state_t)
  : code (fset (path.sort leb [ st_49_loc])) [interface] (@ct (poly_state_t)) :=
  (({code #put st_49_loc := 
        (st_48) ;;
      st_49 ← get st_49_loc ;;
      let st_49 : (field_element_t '× field_element_t '× poly_key_t) :=
        (st_49) in
       temp_51 ←
        (seq_len (b_50)) ;;
       '(st_49) ←
        (if (temp_51) !=.? (usize 0 : uint_size_type):bool_ChoiceEquality then (({code let '(
                  acc_54,
                  r_55,
                  k_56
                ) :=
                (st_49) : (field_element_t '× field_element_t '× poly_key_t
              ) in
               temp_53 ←
                (poly1305_encode_last (pad_len_52) (b_50)) ;;
              st_49 ← get st_49_loc ;;
              
              #put st_49_loc := 
                ((((temp_53) +% (acc_54)) *% (r_55), r_55, k_56)) ;;
              st_49 ← get st_49_loc ;;
              
              @pkg_core_definition.ret _ ( ((st_49))) } : code (fset (
                  path.sort leb [ st_49_loc])) [interface] _)) else (
            @pkg_core_definition.ret _ ( ((st_49))))) ;;
      
      @pkg_core_definition.ret (
        field_element_t '×
        field_element_t '×
        poly_key_t
      ) ( (st_49)) } : code (fset (path.sort leb [ st_49_loc])) [interface] _)).
Fail Next Obligation.


Program Definition poly1305_update
  (m_58 : byte_seq)
  (st_59 : poly_state_t)
  : code (fset (path.sort leb [ st_45_loc ; st_49_loc])) [interface] (@ct (
      poly_state_t)) :=
  (({code  temp_60 ←
        (poly1305_update_blocks (m_58) (st_59)) ;;
      let st_64 : (field_element_t '× field_element_t '× poly_key_t) :=
        (temp_60) in
       temp_61 ←
        (seq_get_remainder_chunk (m_58) (blocksize_v)) ;;
      let last_62 : seq uint8 :=
        (temp_61) in
       temp_63 ←
        (seq_len (last_62)) ;;
       temp_65 ←
        (poly1305_update_last (temp_63 : uint_size_type) (last_62) (st_64)) ;;
      @pkg_core_definition.ret poly_state_t ( (temp_65)) } : code (fset (
          path.sort leb [ st_45_loc ; st_49_loc])) [interface] _)).
Fail Next Obligation.


Program Definition poly1305_finish
  (st_66 : poly_state_t)
  : code (fset.fset0) [interface] (@ct (poly1305_tag_t)) :=
  (({code let '(acc_71, _, k_67) :=
        (st_66) : (field_element_t '× field_element_t '× poly_key_t) in
       temp_68 ←
        (array_to_seq (k_67)) ;;
      let temp_68 : seq uint8 :=
        (temp_68) in
       temp_69 ←
        (array_from_slice (default) (16) (temp_68) (usize 16) (usize 16)) ;;
       temp_70 ←
        (uint128_from_le_bytes (temp_69)) ;;
      let n_77 : uint128 :=
        (temp_70) in
       temp_72 ←
        (nat_mod_to_byte_seq_le (acc_71)) ;;
      let aby_73 : seq uint8 :=
        (temp_72) in
       temp_74 ←
        (array_from_slice (default) (16) (aby_73) (usize 0) (usize 16)) ;;
       temp_75 ←
        (uint128_from_le_bytes (temp_74)) ;;
      let a_76 : uint128 :=
        (temp_75) in
       temp_78 ←
        (uint128_to_le_bytes ((a_76) .+ (n_77))) ;;
       temp_79 ←
        (array_to_seq (temp_78 : nseq int8 16)) ;;
      let temp_79 : seq uint8 :=
        (temp_79) in
       temp_80 ←
        (array_from_seq (16) (temp_79)) ;;
      @pkg_core_definition.ret poly1305_tag_t ( (temp_80)) } : code (
        fset.fset0) [interface] _)).
Fail Next Obligation.

Definition st_84_loc : Location :=
  ((field_element_t '× field_element_t '× poly_key_t) : choice_type ; 87%nat).
Program Definition poly1305
  (m_83 : byte_seq)
  (key_81 : poly_key_t)
  : code (fset (
      path.sort leb [ st_49_loc ; st_45_loc ; n_4_loc ; st_84_loc])) [interface] (
    @ct (poly1305_tag_t)) :=
  (({code  temp_82 ←
        (poly1305_init (key_81)) ;;
      #put st_84_loc := 
        (temp_82) ;;
      st_84 ← get st_84_loc ;;
      let st_84 : (field_element_t '× field_element_t '× poly_key_t) :=
        (st_84) in
       temp_85 ←
        (poly1305_update (m_83) (st_84)) ;;
      st_84 ← get st_84_loc ;;
      
      #put st_84_loc := 
        (temp_85) ;;
      st_84 ← get st_84_loc ;;
      
       temp_86 ←
        (poly1305_finish (st_84)) ;;
      @pkg_core_definition.ret poly1305_tag_t ( (temp_86)) } : code (fset (
          path.sort leb [ st_49_loc ; st_45_loc ; n_4_loc ; st_84_loc])) [interface] _)).
Fail Next Obligation.

