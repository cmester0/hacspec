(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp.word Require Import ssrZ word.
From Jasmin Require Import word.

From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.

Require Import ChoiceEquality.
Require Import LocationUtility.
Require Import Hacspec_Lib_Comparable.
Require Import Hacspec_Lib_Pre.
Require Import Hacspec_Lib.

Open Scope hacspec_scope.
Import choice.Choice.Exports.

Obligation Tactic := try timeout 8 solve_ssprove_obligations.


Definition state_t := nseq (uint32) (usize 16).

Definition state_idx_t :=
  nat_mod (usize 16).
Definition uint_size_in_state_idx_t(n : uint_size) : state_idx_t := int_in_nat_mod n.
Coercion uint_size_in_state_idx_t : uint_size >-> state_idx_t.

Definition constants_t := nseq (uint32) (usize 4).

Definition constants_idx_t :=
  nat_mod (usize 4).
Definition uint_size_in_constants_idx_t(n : uint_size) : constants_idx_t := int_in_nat_mod n.
Coercion uint_size_in_constants_idx_t : uint_size >-> constants_idx_t.

Definition block_t := nseq (uint8) (usize 64).

Definition cha_cha_iv_t := nseq (uint8) (usize 12).

Definition cha_cha_key_t := nseq (uint8) (usize 32).

Definition state_249_loc : ChoiceEqualityLocation :=
  (state_t ; 250%nat).
Notation "'chacha20_line_inp'" :=(
  state_idx_t × state_idx_t × state_idx_t × uint_size × state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_line_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_LINE : nat :=
  256.
Program Definition chacha20_line (a_252 : state_idx_t) (b_253 : state_idx_t) (
    d_254 : state_idx_t) (s_255 : uint_size) (m_251 : state_t)
  : both (CEfset ([state_249_loc])) [interface] (state_t) :=
  ((letbm state_249 : state_t loc( state_249_loc ) := lift_to_both0 m_251 in
      letb state_249 : state_t :=
        array_upd state_249 (lift_to_both0 a_252) (is_pure ((array_index (
                state_249) (lift_to_both0 a_252)) .+ (array_index (state_249) (
                lift_to_both0 b_253)))) in
      letb state_249 : state_t :=
        array_upd state_249 (lift_to_both0 d_254) (is_pure ((array_index (
                state_249) (lift_to_both0 d_254)) .^ (array_index (state_249) (
                lift_to_both0 a_252)))) in
      letb state_249 : state_t :=
        array_upd state_249 (lift_to_both0 d_254) (is_pure (uint32_rotate_left (
              array_index (state_249) (lift_to_both0 d_254)) (
              lift_to_both0 s_255))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 state_249)
      ) : both (CEfset ([state_249_loc])) [interface] (state_t)).
Fail Next Obligation.


Notation "'chacha20_quarter_round_inp'" :=(
  state_idx_t × state_idx_t × state_idx_t × state_idx_t × state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_quarter_round_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_QUARTER_ROUND : nat :=
  265.
Program Definition chacha20_quarter_round (a_257 : state_idx_t) (
    b_258 : state_idx_t) (c_262 : state_idx_t) (d_259 : state_idx_t) (
    state_260 : state_t)
  : both (CEfset ([state_249_loc])) [interface] (state_t) :=
  ((letb state_261 : state_t :=
        chacha20_line (lift_to_both0 a_257) (lift_to_both0 b_258) (
          lift_to_both0 d_259) (lift_to_both0 (usize 16)) (
          lift_to_both0 state_260) in
      letb state_263 : state_t :=
        chacha20_line (lift_to_both0 c_262) (lift_to_both0 d_259) (
          lift_to_both0 b_258) (lift_to_both0 (usize 12)) (
          lift_to_both0 state_261) in
      letb state_264 : state_t :=
        chacha20_line (lift_to_both0 a_257) (lift_to_both0 b_258) (
          lift_to_both0 d_259) (lift_to_both0 (usize 8)) (
          lift_to_both0 state_263) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (chacha20_line (
          lift_to_both0 c_262) (lift_to_both0 d_259) (lift_to_both0 b_258) (
          lift_to_both0 (usize 7)) (lift_to_both0 state_264))
      ) : both (CEfset ([state_249_loc])) [interface] (state_t)).
Fail Next Obligation.


Notation "'chacha20_double_round_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_double_round_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_DOUBLE_ROUND : nat :=
  274.
Program Definition chacha20_double_round (state_266 : state_t)
  : both (CEfset ([state_249_loc])) [interface] (state_t) :=
  ((letb state_267 : state_t :=
        chacha20_quarter_round (lift_to_both0 (usize 0)) (lift_to_both0 (
            usize 4)) (lift_to_both0 (usize 8)) (lift_to_both0 (usize 12)) (
          lift_to_both0 state_266) in
      letb state_268 : state_t :=
        chacha20_quarter_round (lift_to_both0 (usize 1)) (lift_to_both0 (
            usize 5)) (lift_to_both0 (usize 9)) (lift_to_both0 (usize 13)) (
          lift_to_both0 state_267) in
      letb state_269 : state_t :=
        chacha20_quarter_round (lift_to_both0 (usize 2)) (lift_to_both0 (
            usize 6)) (lift_to_both0 (usize 10)) (lift_to_both0 (usize 14)) (
          lift_to_both0 state_268) in
      letb state_270 : state_t :=
        chacha20_quarter_round (lift_to_both0 (usize 3)) (lift_to_both0 (
            usize 7)) (lift_to_both0 (usize 11)) (lift_to_both0 (usize 15)) (
          lift_to_both0 state_269) in
      letb state_271 : state_t :=
        chacha20_quarter_round (lift_to_both0 (usize 0)) (lift_to_both0 (
            usize 5)) (lift_to_both0 (usize 10)) (lift_to_both0 (usize 15)) (
          lift_to_both0 state_270) in
      letb state_272 : state_t :=
        chacha20_quarter_round (lift_to_both0 (usize 1)) (lift_to_both0 (
            usize 6)) (lift_to_both0 (usize 11)) (lift_to_both0 (usize 12)) (
          lift_to_both0 state_271) in
      letb state_273 : state_t :=
        chacha20_quarter_round (lift_to_both0 (usize 2)) (lift_to_both0 (
            usize 7)) (lift_to_both0 (usize 8)) (lift_to_both0 (usize 13)) (
          lift_to_both0 state_272) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (chacha20_quarter_round (
          lift_to_both0 (usize 3)) (lift_to_both0 (usize 4)) (lift_to_both0 (
            usize 9)) (lift_to_both0 (usize 14)) (lift_to_both0 state_273))
      ) : both (CEfset ([state_249_loc])) [interface] (state_t)).
Fail Next Obligation.

Definition st_275_loc : ChoiceEqualityLocation :=
  (state_t ; 276%nat).
Notation "'chacha20_rounds_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_rounds_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_ROUNDS : nat :=
  279.
Program Definition chacha20_rounds (state_277 : state_t)
  : both (CEfset ([state_249_loc ; st_275_loc])) [interface] (state_t) :=
  ((letbm st_275 : state_t loc( st_275_loc ) := lift_to_both0 state_277 in
      letb st_275 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 10)) st_275 (L := (CEfset ([state_249_loc ; st_275_loc]))) (
            I := [interface]) (fun i_278 st_275 =>
            letbm st_275 loc( st_275_loc ) :=
              chacha20_double_round (lift_to_both0 st_275) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 st_275)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 st_275)
      ) : both (CEfset ([state_249_loc ; st_275_loc])) [interface] (state_t)).
Fail Next Obligation.

Definition state_280_loc : ChoiceEqualityLocation :=
  (state_t ; 281%nat).
Notation "'chacha20_core_inp'" :=(
  uint32 × state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_core_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_CORE : nat :=
  285.
Program Definition chacha20_core (ctr_283 : uint32) (st0_282 : state_t)
  : both (CEfset ([state_249_loc ; st_275_loc ; state_280_loc])) [interface] (
    state_t) :=
  ((letbm state_280 : state_t loc( state_280_loc ) := lift_to_both0 st0_282 in
      letb state_280 : state_t :=
        array_upd state_280 (lift_to_both0 (usize 12)) (is_pure ((array_index (
                state_280) (lift_to_both0 (usize 12))) .+ (
              lift_to_both0 ctr_283))) in
      letb k_284 : state_t := chacha20_rounds (lift_to_both0 state_280) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 k_284) array_add (lift_to_both0 state_280))
      ) : both (CEfset (
        [state_249_loc ; st_275_loc ; state_280_loc])) [interface] (state_t)).
Fail Next Obligation.

Definition constants_286_loc : ChoiceEqualityLocation :=
  (constants_t ; 287%nat).
Notation "'chacha20_constants_init_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_constants_init_out'" :=(
  constants_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_CONSTANTS_INIT : nat :=
  288.
Program Definition chacha20_constants_init 
  : both (CEfset ([constants_286_loc])) [interface] (constants_t) :=
  ((letbm constants_286 : constants_t loc( constants_286_loc ) :=
        array_new_ (default : uint32) (4) in
      letb constants_286 : constants_t :=
        array_upd constants_286 (lift_to_both0 (usize 0)) (is_pure (secret (
              lift_to_both0 (@repr U32 1634760805)))) in
      letb constants_286 : constants_t :=
        array_upd constants_286 (lift_to_both0 (usize 1)) (is_pure (secret (
              lift_to_both0 (@repr U32 857760878)))) in
      letb constants_286 : constants_t :=
        array_upd constants_286 (lift_to_both0 (usize 2)) (is_pure (secret (
              lift_to_both0 (@repr U32 2036477234)))) in
      letb constants_286 : constants_t :=
        array_upd constants_286 (lift_to_both0 (usize 3)) (is_pure (secret (
              lift_to_both0 (@repr U32 1797285236)))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 constants_286)
      ) : both (CEfset ([constants_286_loc])) [interface] (constants_t)).
Fail Next Obligation.

Definition st_289_loc : ChoiceEqualityLocation :=
  (state_t ; 290%nat).
Notation "'chacha20_init_inp'" :=(
  cha_cha_key_t × cha_cha_iv_t × uint32 : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_init_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_INIT : nat :=
  294.
Program Definition chacha20_init (key_291 : cha_cha_key_t) (
    iv_293 : cha_cha_iv_t) (ctr_292 : uint32)
  : both (CEfset ([constants_286_loc ; st_289_loc])) [interface] (state_t) :=
  ((letbm st_289 : state_t loc( st_289_loc ) :=
        array_new_ (default : uint32) (16) in
      letbm st_289 loc( st_289_loc ) :=
        array_update (lift_to_both0 st_289) (lift_to_both0 (usize 0)) (
          array_to_seq (chacha20_constants_init )) in
      letbm st_289 loc( st_289_loc ) :=
        array_update (lift_to_both0 st_289) (lift_to_both0 (usize 4)) (
          array_to_le_uint32s (lift_to_both0 key_291)) in
      letb st_289 : state_t :=
        array_upd st_289 (lift_to_both0 (usize 12)) (is_pure (
            lift_to_both0 ctr_292)) in
      letbm st_289 loc( st_289_loc ) :=
        array_update (lift_to_both0 st_289) (lift_to_both0 (usize 13)) (
          array_to_le_uint32s (lift_to_both0 iv_293)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 st_289)
      ) : both (CEfset ([constants_286_loc ; st_289_loc])) [interface] (
      state_t)).
Fail Next Obligation.


Notation "'chacha20_key_block_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_key_block_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_KEY_BLOCK : nat :=
  297.
Program Definition chacha20_key_block (state_295 : state_t)
  : both (CEfset ([state_249_loc ; st_275_loc ; state_280_loc])) [interface] (
    block_t) :=
  ((letb state_296 : state_t :=
        chacha20_core (secret (lift_to_both0 (@repr U32 0))) (
          lift_to_both0 state_295) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (64) (
          array_to_le_bytes (lift_to_both0 state_296)))
      ) : both (CEfset (
        [state_249_loc ; st_275_loc ; state_280_loc])) [interface] (block_t)).
Fail Next Obligation.


Notation "'chacha20_key_block0_inp'" :=(
  cha_cha_key_t × cha_cha_iv_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_key_block0_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_KEY_BLOCK0 : nat :=
  301.
Program Definition chacha20_key_block0 (key_298 : cha_cha_key_t) (
    iv_299 : cha_cha_iv_t)
  : both (CEfset (
      [state_249_loc ; st_275_loc ; state_280_loc ; constants_286_loc ; st_289_loc])) [interface] (
    block_t) :=
  ((letb state_300 : state_t :=
        chacha20_init (lift_to_both0 key_298) (lift_to_both0 iv_299) (secret (
            lift_to_both0 (@repr U32 0))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (chacha20_key_block (
          lift_to_both0 state_300))
      ) : both (CEfset (
        [state_249_loc ; st_275_loc ; state_280_loc ; constants_286_loc ; st_289_loc])) [interface] (
      block_t)).
Fail Next Obligation.


Notation "'chacha20_encrypt_block_inp'" :=(
  state_t × uint32 × block_t : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_encrypt_block_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_ENCRYPT_BLOCK : nat :=
  308.
Program Definition chacha20_encrypt_block (st0_303 : state_t) (
    ctr_302 : uint32) (plain_305 : block_t)
  : both (CEfset ([state_249_loc ; st_275_loc ; state_280_loc])) [interface] (
    block_t) :=
  ((letb st_304 : state_t :=
        chacha20_core (lift_to_both0 ctr_302) (lift_to_both0 st0_303) in
      letb pl_306 : state_t :=
        array_from_seq (16) (array_to_le_uint32s (lift_to_both0 plain_305)) in
      letb st_307 : state_t :=
        (lift_to_both0 pl_306) array_xor (lift_to_both0 st_304) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (64) (
          array_to_le_bytes (lift_to_both0 st_307)))
      ) : both (CEfset (
        [state_249_loc ; st_275_loc ; state_280_loc])) [interface] (block_t)).
Fail Next Obligation.

Definition b_309_loc : ChoiceEqualityLocation :=
  (block_t ; 310%nat).
Notation "'chacha20_encrypt_last_inp'" :=(
  state_t × uint32 × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_encrypt_last_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_ENCRYPT_LAST : nat :=
  314.
Program Definition chacha20_encrypt_last (st0_312 : state_t) (
    ctr_313 : uint32) (plain_311 : byte_seq)
  : both (CEfset (
      [state_249_loc ; st_275_loc ; state_280_loc ; b_309_loc])) [interface] (
    byte_seq) :=
  ((letbm b_309 : block_t loc( b_309_loc ) :=
        array_new_ (default : uint8) (64) in
      letbm b_309 loc( b_309_loc ) :=
        array_update (lift_to_both0 b_309) (lift_to_both0 (usize 0)) (
          lift_to_both0 plain_311) in
      letbm b_309 loc( b_309_loc ) :=
        chacha20_encrypt_block (lift_to_both0 st0_312) (lift_to_both0 ctr_313) (
          lift_to_both0 b_309) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_slice (
          lift_to_both0 b_309) (lift_to_both0 (usize 0)) (seq_len (
            lift_to_both0 plain_311)))
      ) : both (CEfset (
        [state_249_loc ; st_275_loc ; state_280_loc ; b_309_loc])) [interface] (
      byte_seq)).
Fail Next Obligation.

Definition blocks_out_315_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 316%nat).
Notation "'chacha20_update_inp'" :=(
  state_t × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_update_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition CHACHA20_UPDATE : nat :=
  325.
Program Definition chacha20_update (st0_321 : state_t) (m_317 : byte_seq)
  : both (CEfset (
      [state_249_loc ; st_275_loc ; state_280_loc ; b_309_loc ; blocks_out_315_loc])) [interface] (
    byte_seq) :=
  ((letbm blocks_out_315 : seq uint8 loc( blocks_out_315_loc ) :=
        seq_new_ (default : uint8) (seq_len (lift_to_both0 m_317)) in
      letb n_blocks_318 : uint_size :=
        seq_num_exact_chunks (lift_to_both0 m_317) (lift_to_both0 (usize 64)) in
      letb blocks_out_315 :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 n_blocks_318) blocks_out_315 (L := (CEfset (
                [state_249_loc ; st_275_loc ; state_280_loc ; b_309_loc ; blocks_out_315_loc]))) (
            I := [interface]) (fun i_319 blocks_out_315 =>
            letb msg_block_320 : seq uint8 :=
              seq_get_exact_chunk (lift_to_both0 m_317) (lift_to_both0 (
                  usize 64)) (lift_to_both0 i_319) in
            letb b_322 : block_t :=
              chacha20_encrypt_block (lift_to_both0 st0_321) (secret (pub_u32 (
                    is_pure (lift_to_both0 i_319)))) (array_from_seq (64) (
                  lift_to_both0 msg_block_320)) in
            letbm blocks_out_315 loc( blocks_out_315_loc ) :=
              seq_set_exact_chunk (lift_to_both0 blocks_out_315) (
                lift_to_both0 (usize 64)) (lift_to_both0 i_319) (
                array_to_seq (lift_to_both0 b_322)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 blocks_out_315)
            ) in
      letb last_block_323 : seq uint8 :=
        seq_get_remainder_chunk (lift_to_both0 m_317) (lift_to_both0 (
            usize 64)) in
      letb '(blocks_out_315) :=
        if (seq_len (lift_to_both0 last_block_323)) !=.? (lift_to_both0 (
            usize 0)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [state_249_loc ; st_275_loc ; state_280_loc ; b_309_loc ; blocks_out_315_loc])) (
          L2 := CEfset (
            [state_249_loc ; st_275_loc ; state_280_loc ; b_309_loc ; blocks_out_315_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb b_324 : seq uint8 :=
            chacha20_encrypt_last (lift_to_both0 st0_321) (secret (pub_u32 (
                  is_pure (lift_to_both0 n_blocks_318)))) (
              lift_to_both0 last_block_323) in
          letbm blocks_out_315 loc( blocks_out_315_loc ) :=
            seq_set_chunk (lift_to_both0 blocks_out_315) (lift_to_both0 (
                usize 64)) (lift_to_both0 n_blocks_318) (lift_to_both0 b_324) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 blocks_out_315)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 blocks_out_315)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 blocks_out_315)
      ) : both (CEfset (
        [state_249_loc ; st_275_loc ; state_280_loc ; b_309_loc ; blocks_out_315_loc])) [interface] (
      byte_seq)).
Fail Next Obligation.


Notation "'chacha20_inp'" :=(
  cha_cha_key_t × cha_cha_iv_t × int32 × byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'chacha20_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition CHACHA20 : nat :=
  331.
Program Definition chacha20 (key_326 : cha_cha_key_t) (iv_327 : cha_cha_iv_t) (
    ctr_328 : int32) (m_330 : byte_seq)
  : both (CEfset (
      [state_249_loc ; st_275_loc ; state_280_loc ; constants_286_loc ; st_289_loc ; b_309_loc ; blocks_out_315_loc])) [interface] (
    byte_seq) :=
  ((letb state_329 : state_t :=
        chacha20_init (lift_to_both0 key_326) (lift_to_both0 iv_327) (secret (
            lift_to_both0 ctr_328)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (chacha20_update (
          lift_to_both0 state_329) (lift_to_both0 m_330))
      ) : both (CEfset (
        [state_249_loc ; st_275_loc ; state_280_loc ; constants_286_loc ; st_289_loc ; b_309_loc ; blocks_out_315_loc])) [interface] (
      byte_seq)).
Fail Next Obligation.

