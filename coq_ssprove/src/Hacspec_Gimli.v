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


Definition state_t := nseq (uint32) (usize 12).

Definition state_idx_t :=
  nat_mod (usize 12).
Definition uint_size_in_state_idx_t(n : uint_size) : state_idx_t := int_in_nat_mod n.
Coercion uint_size_in_state_idx_t : uint_size >-> state_idx_t.


Notation "'swap_inp'" :=(
  state_t × state_idx_t × state_idx_t : choice_type) (in custom pack_type at level 2).
Notation "'swap_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition SWAP : nat :=
  1268.
Program Definition swap (s_1265 : state_t) (i_1264 : state_idx_t) (
    j_1267 : state_idx_t)
  : both (fset.fset0) [interface] (state_t) :=
  ((letb tmp_1266 : uint32 := array_index (s_1265) (lift_to_both0 i_1264) in
      letb s_1265 : state_t :=
        array_upd s_1265 (lift_to_both0 i_1264) (is_pure (array_index (s_1265) (
              lift_to_both0 j_1267))) in
      letb s_1265 : state_t :=
        array_upd s_1265 (lift_to_both0 j_1267) (is_pure (
            lift_to_both0 tmp_1266)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1265)
      ) : both (fset.fset0) [interface] (state_t)).
Fail Next Obligation.


Notation "'gimli_round_inp'" :=(
  state_t × int32 : choice_type) (in custom pack_type at level 2).
Notation "'gimli_round_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition GIMLI_ROUND : nat :=
  1275.
Program Definition gimli_round (s_1269 : state_t) (r_1274 : int32)
  : both (fset.fset0) [interface] (state_t) :=
  ((letb s_1269 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (usize 4)) s_1269 (
            L := (fset.fset0)) (I := [interface]) (fun col_1270 s_1269 =>
            letb x_1271 : uint32 :=
              uint32_rotate_left (array_index (s_1269) (
                  lift_to_both0 col_1270)) (lift_to_both0 (usize 24)) in
            letb y_1272 : uint32 :=
              uint32_rotate_left (array_index (s_1269) ((
                    lift_to_both0 col_1270) .+ (lift_to_both0 (usize 4)))) (
                lift_to_both0 (usize 9)) in
            letb z_1273 : uint32 :=
              array_index (s_1269) ((lift_to_both0 col_1270) .+ (lift_to_both0 (
                    usize 8))) in
            letb s_1269 : state_t :=
              array_upd s_1269 ((lift_to_both0 col_1270) .+ (lift_to_both0 (
                    usize 8))) (is_pure (((lift_to_both0 x_1271) .^ ((
                        lift_to_both0 z_1273) shift_left (lift_to_both0 (
                          usize 1)))) .^ (((lift_to_both0 y_1272) .& (
                        lift_to_both0 z_1273)) shift_left (lift_to_both0 (
                        usize 2))))) in
            letb s_1269 : state_t :=
              array_upd s_1269 ((lift_to_both0 col_1270) .+ (lift_to_both0 (
                    usize 4))) (is_pure (((lift_to_both0 y_1272) .^ (
                      lift_to_both0 x_1271)) .^ (((lift_to_both0 x_1271) .| (
                        lift_to_both0 z_1273)) shift_left (lift_to_both0 (
                        usize 1))))) in
            letb s_1269 : state_t :=
              array_upd s_1269 (lift_to_both0 col_1270) (is_pure (((
                      lift_to_both0 z_1273) .^ (lift_to_both0 y_1272)) .^ (((
                        lift_to_both0 x_1271) .& (
                        lift_to_both0 y_1272)) shift_left (lift_to_both0 (
                        usize 3))))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1269)
            ) in
      letb '(s_1269) :=
        if ((lift_to_both0 r_1274) .& (lift_to_both0 (@repr U32 3))) =.? (
          lift_to_both0 (@repr U32 0)) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm s_1269 loc( s_1269_loc ) :=
            swap (lift_to_both0 s_1269) (lift_to_both0 (usize 0)) (
              lift_to_both0 (usize 1)) in
          letbm s_1269 loc( s_1269_loc ) :=
            swap (lift_to_both0 s_1269) (lift_to_both0 (usize 2)) (
              lift_to_both0 (usize 3)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 s_1269)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 s_1269)
         in
      letb '(s_1269) :=
        if ((lift_to_both0 r_1274) .& (lift_to_both0 (@repr U32 3))) =.? (
          lift_to_both0 (@repr U32 2)) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm s_1269 loc( s_1269_loc ) :=
            swap (lift_to_both0 s_1269) (lift_to_both0 (usize 0)) (
              lift_to_both0 (usize 2)) in
          letbm s_1269 loc( s_1269_loc ) :=
            swap (lift_to_both0 s_1269) (lift_to_both0 (usize 1)) (
              lift_to_both0 (usize 3)) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 s_1269)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 s_1269)
         in
      letb '(s_1269) :=
        if ((lift_to_both0 r_1274) .& (lift_to_both0 (@repr U32 3))) =.? (
          lift_to_both0 (@repr U32 0)) :bool_ChoiceEquality
        then lift_scope (L1 := fset.fset0) (L2 := fset.fset0) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb s_1269 : state_t :=
            array_upd s_1269 (lift_to_both0 (usize 0)) (is_pure ((array_index (
                    s_1269) (lift_to_both0 (usize 0))) .^ ((secret (
                      lift_to_both0 (@repr U32 2654435584))) .| (secret (
                      lift_to_both0 r_1274))))) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 s_1269)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 s_1269)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1269)
      ) : both (fset.fset0) [interface] (state_t)).
Fail Next Obligation.


Notation "'gimli_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition GIMLI : nat :=
  1279.
Program Definition gimli (s_1276 : state_t)
  : both (fset.fset0) [interface] (state_t) :=
  ((letb s_1276 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 24)) s_1276 (L := (fset.fset0)) (I := [interface]) (
            fun rnd_1277 s_1276 =>
            letb rnd_1278 : int32 :=
              pub_u32 (is_pure ((lift_to_both0 (usize 24)) .- (
                    lift_to_both0 rnd_1277))) in
            letbm s_1276 loc( s_1276_loc ) :=
              gimli_round (lift_to_both0 s_1276) (lift_to_both0 rnd_1278) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1276)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1276)
      ) : both (fset.fset0) [interface] (state_t)).
Fail Next Obligation.

Definition block_t := nseq (uint8) (usize 16).

Definition digest_t := nseq (uint8) (usize 32).


Notation "'absorb_block_inp'" :=(
  block_t × state_t : choice_type) (in custom pack_type at level 2).
Notation "'absorb_block_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition ABSORB_BLOCK : nat :=
  1283.
Program Definition absorb_block (input_block_1280 : block_t) (s_1282 : state_t)
  : both (fset.fset0) [interface] (state_t) :=
  ((letb input_bytes_1281 : seq uint32 :=
        array_to_le_uint32s (lift_to_both0 input_block_1280) in
      letb s_1282 : state_t :=
        array_upd s_1282 (lift_to_both0 (usize 0)) (is_pure ((array_index (
                s_1282) (lift_to_both0 (usize 0))) .^ (seq_index (
                input_bytes_1281) (lift_to_both0 (usize 0))))) in
      letb s_1282 : state_t :=
        array_upd s_1282 (lift_to_both0 (usize 1)) (is_pure ((array_index (
                s_1282) (lift_to_both0 (usize 1))) .^ (seq_index (
                input_bytes_1281) (lift_to_both0 (usize 1))))) in
      letb s_1282 : state_t :=
        array_upd s_1282 (lift_to_both0 (usize 2)) (is_pure ((array_index (
                s_1282) (lift_to_both0 (usize 2))) .^ (seq_index (
                input_bytes_1281) (lift_to_both0 (usize 2))))) in
      letb s_1282 : state_t :=
        array_upd s_1282 (lift_to_both0 (usize 3)) (is_pure ((array_index (
                s_1282) (lift_to_both0 (usize 3))) .^ (seq_index (
                input_bytes_1281) (lift_to_both0 (usize 3))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (gimli (
          lift_to_both0 s_1282))
      ) : both (fset.fset0) [interface] (state_t)).
Fail Next Obligation.

Definition block_1284_loc : ChoiceEqualityLocation :=
  (block_t ; 1285%nat).
Notation "'squeeze_block_inp'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Notation "'squeeze_block_out'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Definition SQUEEZE_BLOCK : nat :=
  1290.
Program Definition squeeze_block (s_1287 : state_t)
  : both (CEfset ([block_1284_loc])) [interface] (block_t) :=
  ((letbm block_1284 : block_t loc( block_1284_loc ) :=
        array_new_ (default : uint8) (16) in
      letb block_1284 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 4)) block_1284 (L := (CEfset ([block_1284_loc]))) (
            I := [interface]) (fun i_1286 block_1284 =>
            letb s_i_1288 : uint32 :=
              array_index (s_1287) (lift_to_both0 i_1286) in
            letb s_i_bytes_1289 : seq uint8 :=
              uint32_to_le_bytes (lift_to_both0 s_i_1288) in
            letb block_1284 : block_t :=
              array_upd block_1284 ((lift_to_both0 (usize 4)) .* (
                  lift_to_both0 i_1286)) (is_pure (seq_index (s_i_bytes_1289) (
                    lift_to_both0 (usize 0)))) in
            letb block_1284 : block_t :=
              array_upd block_1284 (((lift_to_both0 (usize 4)) .* (
                    lift_to_both0 i_1286)) .+ (lift_to_both0 (usize 1))) (
                is_pure (seq_index (s_i_bytes_1289) (lift_to_both0 (
                      usize 1)))) in
            letb block_1284 : block_t :=
              array_upd block_1284 (((lift_to_both0 (usize 4)) .* (
                    lift_to_both0 i_1286)) .+ (lift_to_both0 (usize 2))) (
                is_pure (seq_index (s_i_bytes_1289) (lift_to_both0 (
                      usize 2)))) in
            letb block_1284 : block_t :=
              array_upd block_1284 (((lift_to_both0 (usize 4)) .* (
                    lift_to_both0 i_1286)) .+ (lift_to_both0 (usize 3))) (
                is_pure (seq_index (s_i_bytes_1289) (lift_to_both0 (
                      usize 3)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 block_1284)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 block_1284)
      ) : both (CEfset ([block_1284_loc])) [interface] (block_t)).
Fail Next Obligation.

Definition input_block_padded_1291_loc : ChoiceEqualityLocation :=
  (block_t ; 1292%nat).
Notation "'gimli_hash_state_inp'" :=(
  byte_seq × state_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_hash_state_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition GIMLI_HASH_STATE : nat :=
  1302.
Program Definition gimli_hash_state (input_1294 : byte_seq) (s_1296 : state_t)
  : both (CEfset ([input_block_padded_1291_loc])) [interface] (state_t) :=
  ((letb rate_1293 : uint_size := array_length  in
      letb chunks_1295 : uint_size :=
        seq_num_exact_chunks (lift_to_both0 input_1294) (
          lift_to_both0 rate_1293) in
      letb s_1296 :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 chunks_1295) s_1296 (L := (CEfset (
                [input_block_padded_1291_loc]))) (I := [interface]) (
            fun i_1297 s_1296 =>
            letb input_block_1298 : seq uint8 :=
              seq_get_exact_chunk (lift_to_both0 input_1294) (
                lift_to_both0 rate_1293) (lift_to_both0 i_1297) in
            letb full_block_1299 : block_t :=
              array_from_seq (16) (lift_to_both0 input_block_1298) in
            letbm s_1296 loc( s_1296_loc ) :=
              absorb_block (lift_to_both0 full_block_1299) (
                lift_to_both0 s_1296) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_1296)
            ) in
      letb input_block_1300 : seq uint8 :=
        seq_get_remainder_chunk (lift_to_both0 input_1294) (
          lift_to_both0 rate_1293) in
      letb input_block_padded_1301 : block_t :=
        array_new_ (default : uint8) (16) in
      letbm input_block_padded_1291 : block_t loc( input_block_padded_1291_loc ) :=
        array_update_start (lift_to_both0 input_block_padded_1301) (
          lift_to_both0 input_block_1300) in
      letb input_block_padded_1291 : block_t :=
        array_upd input_block_padded_1291 (seq_len (
            lift_to_both0 input_block_1300)) (is_pure (secret (lift_to_both0 (
                @repr U8 1)))) in
      letb s_1296 : state_t :=
        array_upd s_1296 (lift_to_both0 (usize 11)) (is_pure ((array_index (
                s_1296) (lift_to_both0 (usize 11))) .^ (secret (lift_to_both0 (
                  @repr U32 16777216))))) in
      letbm s_1296 loc( s_1296_loc ) :=
        absorb_block (lift_to_both0 input_block_padded_1291) (
          lift_to_both0 s_1296) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_1296)
      ) : both (CEfset ([input_block_padded_1291_loc])) [interface] (state_t)).
Fail Next Obligation.


Notation "'gimli_hash_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'gimli_hash_out'" :=(
  digest_t : choice_type) (in custom pack_type at level 2).
Definition GIMLI_HASH : nat :=
  1309.
Program Definition gimli_hash (input_bytes_1304 : byte_seq)
  : both (CEfset ([block_1284_loc ; input_block_padded_1291_loc])) [interface] (
    digest_t) :=
  ((letb s_1303 : state_t := array_new_ (default : uint32) (12) in
      letb s_1305 : state_t :=
        gimli_hash_state (lift_to_both0 input_bytes_1304) (
          lift_to_both0 s_1303) in
      letb output_1306 : digest_t := array_new_ (default : uint8) (32) in
      letb output_1307 : digest_t :=
        array_update_start (lift_to_both0 output_1306) (
          array_to_seq (squeeze_block (lift_to_both0 s_1305))) in
      letb s_1308 : state_t := gimli (lift_to_both0 s_1305) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_update (
          lift_to_both0 output_1307) (array_length ) (
          array_to_seq (squeeze_block (lift_to_both0 s_1308))))
      ) : both (CEfset (
        [block_1284_loc ; input_block_padded_1291_loc])) [interface] (
      digest_t)).
Fail Next Obligation.

Definition nonce_t := nseq (uint8) (usize 16).

Definition key_t := nseq (uint8) (usize 32).

Definition tag_t := nseq (uint8) (usize 16).


Notation "'process_ad_inp'" :=(
  byte_seq × state_t : choice_type) (in custom pack_type at level 2).
Notation "'process_ad_out'" :=(
  state_t : choice_type) (in custom pack_type at level 2).
Definition PROCESS_AD : nat :=
  1312.
Program Definition process_ad (ad_1310 : byte_seq) (s_1311 : state_t)
  : both (CEfset ([input_block_padded_1291_loc])) [interface] (state_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (gimli_hash_state (
          lift_to_both0 ad_1310) (lift_to_both0 s_1311))
      ) : both (CEfset ([input_block_padded_1291_loc])) [interface] (state_t)).
Fail Next Obligation.

Definition msg_block_padded_1314_loc : ChoiceEqualityLocation :=
  (block_t ; 1315%nat).
Definition ciphertext_1313_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 1316%nat).
Notation "'process_msg_inp'" :=(
  byte_seq × state_t : choice_type) (in custom pack_type at level 2).
Notation "'process_msg_out'" :=((state_t '× byte_seq
  ) : choice_type) (in custom pack_type at level 2).
Definition PROCESS_MSG : nat :=
  1329.
Program Definition process_msg (message_1317 : byte_seq) (s_1320 : state_t)
  : both (CEfset (
      [block_1284_loc ; ciphertext_1313_loc ; msg_block_padded_1314_loc])) [interface] (
    (state_t '× byte_seq)) :=
  ((letbm ciphertext_1313 : seq uint8 loc( ciphertext_1313_loc ) :=
        seq_new_ (default : uint8) (seq_len (lift_to_both0 message_1317)) in
      letb rate_1318 : uint_size := array_length  in
      letb num_chunks_1319 : uint_size :=
        seq_num_exact_chunks (lift_to_both0 message_1317) (
          lift_to_both0 rate_1318) in
      letb '(s_1320, ciphertext_1313) :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 num_chunks_1319) prod_ce(s_1320, ciphertext_1313) (
            L := (CEfset (
                [block_1284_loc ; ciphertext_1313_loc ; msg_block_padded_1314_loc]))) (
            I := [interface]) (fun i_1321 '(s_1320, ciphertext_1313) =>
            letb key_block_1322 : block_t :=
              squeeze_block (lift_to_both0 s_1320) in
            letb msg_block_1323 : seq uint8 :=
              seq_get_exact_chunk (lift_to_both0 message_1317) (
                lift_to_both0 rate_1318) (lift_to_both0 i_1321) in
            letb msg_block_1324 : block_t :=
              array_from_seq (16) (lift_to_both0 msg_block_1323) in
            letbm ciphertext_1313 loc( ciphertext_1313_loc ) :=
              seq_set_exact_chunk (lift_to_both0 ciphertext_1313) (
                lift_to_both0 rate_1318) (lift_to_both0 i_1321) (array_to_seq ((
                  lift_to_both0 msg_block_1324) array_xor (
                  lift_to_both0 key_block_1322))) in
            letbm s_1320 loc( s_1320_loc ) :=
              absorb_block (lift_to_both0 msg_block_1324) (
                lift_to_both0 s_1320) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 s_1320,
                lift_to_both0 ciphertext_1313
              ))
            ) in
      letb key_block_1325 : block_t := squeeze_block (lift_to_both0 s_1320) in
      letb last_block_1326 : seq uint8 :=
        seq_get_remainder_chunk (lift_to_both0 message_1317) (
          lift_to_both0 rate_1318) in
      letb block_len_1327 : uint_size :=
        seq_len (lift_to_both0 last_block_1326) in
      letb msg_block_padded_1328 : block_t :=
        array_new_ (default : uint8) (16) in
      letbm msg_block_padded_1314 : block_t loc( msg_block_padded_1314_loc ) :=
        array_update_start (lift_to_both0 msg_block_padded_1328) (
          lift_to_both0 last_block_1326) in
      letbm ciphertext_1313 loc( ciphertext_1313_loc ) :=
        seq_set_chunk (lift_to_both0 ciphertext_1313) (
          lift_to_both0 rate_1318) (lift_to_both0 num_chunks_1319) (
          array_slice_range ((lift_to_both0 msg_block_padded_1314) array_xor (
              lift_to_both0 key_block_1325)) (prod_b(
              lift_to_both0 (usize 0),
              lift_to_both0 block_len_1327
            ))) in
      letb msg_block_padded_1314 : block_t :=
        array_upd msg_block_padded_1314 (lift_to_both0 block_len_1327) (
          is_pure ((array_index (msg_block_padded_1314) (
                lift_to_both0 block_len_1327)) .^ (secret (lift_to_both0 (
                  @repr U8 1))))) in
      letb s_1320 : state_t :=
        array_upd s_1320 (lift_to_both0 (usize 11)) (is_pure ((array_index (
                s_1320) (lift_to_both0 (usize 11))) .^ (secret (lift_to_both0 (
                  @repr U32 16777216))))) in
      letbm s_1320 loc( s_1320_loc ) :=
        absorb_block (lift_to_both0 msg_block_padded_1314) (
          lift_to_both0 s_1320) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 s_1320,
          lift_to_both0 ciphertext_1313
        ))
      ) : both (CEfset (
        [block_1284_loc ; ciphertext_1313_loc ; msg_block_padded_1314_loc])) [interface] (
      (state_t '× byte_seq))).
Fail Next Obligation.

Definition msg_block_1331_loc : ChoiceEqualityLocation :=
  (block_t ; 1332%nat).
Definition message_1330_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 1333%nat).
Notation "'process_ct_inp'" :=(
  byte_seq × state_t : choice_type) (in custom pack_type at level 2).
Notation "'process_ct_out'" :=((state_t '× byte_seq
  ) : choice_type) (in custom pack_type at level 2).
Definition PROCESS_CT : nat :=
  1349.
Program Definition process_ct (ciphertext_1334 : byte_seq) (s_1337 : state_t)
  : both (CEfset (
      [block_1284_loc ; message_1330_loc ; msg_block_1331_loc])) [interface] ((
      state_t '×
      byte_seq
    )) :=
  ((letbm message_1330 : seq uint8 loc( message_1330_loc ) :=
        seq_new_ (default : uint8) (seq_len (lift_to_both0 ciphertext_1334)) in
      letb rate_1335 : uint_size := array_length  in
      letb num_chunks_1336 : uint_size :=
        seq_num_exact_chunks (lift_to_both0 ciphertext_1334) (
          lift_to_both0 rate_1335) in
      letb '(s_1337, message_1330) :=
        foldi_both' (lift_to_both0 (usize 0)) (
            lift_to_both0 num_chunks_1336) prod_ce(s_1337, message_1330) (L := (
              CEfset (
                [block_1284_loc ; message_1330_loc ; msg_block_1331_loc]))) (
            I := [interface]) (fun i_1338 '(s_1337, message_1330) =>
            letb key_block_1339 : block_t :=
              squeeze_block (lift_to_both0 s_1337) in
            letb ct_block_1340 : seq uint8 :=
              seq_get_exact_chunk (lift_to_both0 ciphertext_1334) (
                lift_to_both0 rate_1335) (lift_to_both0 i_1338) in
            letb ct_block_1341 : block_t :=
              array_from_seq (16) (lift_to_both0 ct_block_1340) in
            letb msg_block_1342 : block_t :=
              (lift_to_both0 ct_block_1341) array_xor (
                lift_to_both0 key_block_1339) in
            letbm message_1330 loc( message_1330_loc ) :=
              seq_set_exact_chunk (lift_to_both0 message_1330) (
                lift_to_both0 rate_1335) (lift_to_both0 i_1338) (array_to_seq ((
                  lift_to_both0 ct_block_1341) array_xor (
                  lift_to_both0 key_block_1339))) in
            letbm s_1337 loc( s_1337_loc ) :=
              absorb_block (lift_to_both0 msg_block_1342) (
                lift_to_both0 s_1337) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 s_1337,
                lift_to_both0 message_1330
              ))
            ) in
      letb key_block_1343 : block_t := squeeze_block (lift_to_both0 s_1337) in
      letb ct_final_1344 : seq uint8 :=
        seq_get_remainder_chunk (lift_to_both0 ciphertext_1334) (
          lift_to_both0 rate_1335) in
      letb block_len_1345 : uint_size :=
        seq_len (lift_to_both0 ct_final_1344) in
      letb ct_block_padded_1346 : block_t :=
        array_new_ (default : uint8) (16) in
      letb ct_block_padded_1347 : block_t :=
        array_update_start (lift_to_both0 ct_block_padded_1346) (
          lift_to_both0 ct_final_1344) in
      letb msg_block_1348 : block_t :=
        (lift_to_both0 ct_block_padded_1347) array_xor (
          lift_to_both0 key_block_1343) in
      letbm message_1330 loc( message_1330_loc ) :=
        seq_set_chunk (lift_to_both0 message_1330) (lift_to_both0 rate_1335) (
          lift_to_both0 num_chunks_1336) (array_slice_range (
            lift_to_both0 msg_block_1348) (prod_b(
              lift_to_both0 (usize 0),
              lift_to_both0 block_len_1345
            ))) in
      letbm msg_block_1331 : block_t loc( msg_block_1331_loc ) :=
        array_from_slice_range (default : uint8) (16) (
          array_to_seq (lift_to_both0 msg_block_1348)) (prod_b(
            lift_to_both0 (usize 0),
            lift_to_both0 block_len_1345
          )) in
      letb msg_block_1331 : block_t :=
        array_upd msg_block_1331 (lift_to_both0 block_len_1345) (is_pure ((
              array_index (msg_block_1331) (lift_to_both0 block_len_1345)) .^ (
              secret (lift_to_both0 (@repr U8 1))))) in
      letb s_1337 : state_t :=
        array_upd s_1337 (lift_to_both0 (usize 11)) (is_pure ((array_index (
                s_1337) (lift_to_both0 (usize 11))) .^ (secret (lift_to_both0 (
                  @repr U32 16777216))))) in
      letbm s_1337 loc( s_1337_loc ) :=
        absorb_block (lift_to_both0 msg_block_1331) (lift_to_both0 s_1337) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 s_1337,
          lift_to_both0 message_1330
        ))
      ) : both (CEfset (
        [block_1284_loc ; message_1330_loc ; msg_block_1331_loc])) [interface] (
      (state_t '× byte_seq))).
Fail Next Obligation.

Definition uints_1350_loc : ChoiceEqualityLocation :=
  (seq uint32 ; 1351%nat).
Notation "'nonce_to_u32s_inp'" :=(
  nonce_t : choice_type) (in custom pack_type at level 2).
Notation "'nonce_to_u32s_out'" :=(
  seq uint32 : choice_type) (in custom pack_type at level 2).
Definition NONCE_TO_U32S : nat :=
  1353.
Program Definition nonce_to_u32s (nonce_1352 : nonce_t)
  : both (CEfset ([uints_1350_loc])) [interface] (seq uint32) :=
  ((letbm uints_1350 : seq uint32 loc( uints_1350_loc ) :=
        seq_new_ (default : uint32) (lift_to_both0 (usize 4)) in
      letb uints_1350 : seq uint32 :=
        seq_upd uints_1350 (lift_to_both0 (usize 0)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 nonce_1352)) (prod_b(
                  lift_to_both0 (usize 0),
                  lift_to_both0 (usize 4)
                ))))) in
      letb uints_1350 : seq uint32 :=
        seq_upd uints_1350 (lift_to_both0 (usize 1)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 nonce_1352)) (prod_b(
                  lift_to_both0 (usize 4),
                  lift_to_both0 (usize 8)
                ))))) in
      letb uints_1350 : seq uint32 :=
        seq_upd uints_1350 (lift_to_both0 (usize 2)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 nonce_1352)) (prod_b(
                  lift_to_both0 (usize 8),
                  lift_to_both0 (usize 12)
                ))))) in
      letb uints_1350 : seq uint32 :=
        seq_upd uints_1350 (lift_to_both0 (usize 3)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 nonce_1352)) (prod_b(
                  lift_to_both0 (usize 12),
                  lift_to_both0 (usize 16)
                ))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 uints_1350)
      ) : both (CEfset ([uints_1350_loc])) [interface] (seq uint32)).
Fail Next Obligation.

Definition uints_1354_loc : ChoiceEqualityLocation :=
  (seq uint32 ; 1355%nat).
Notation "'key_to_u32s_inp'" :=(
  key_t : choice_type) (in custom pack_type at level 2).
Notation "'key_to_u32s_out'" :=(
  seq uint32 : choice_type) (in custom pack_type at level 2).
Definition KEY_TO_U32S : nat :=
  1357.
Program Definition key_to_u32s (key_1356 : key_t)
  : both (CEfset ([uints_1354_loc])) [interface] (seq uint32) :=
  ((letbm uints_1354 : seq uint32 loc( uints_1354_loc ) :=
        seq_new_ (default : uint32) (lift_to_both0 (usize 8)) in
      letb uints_1354 : seq uint32 :=
        seq_upd uints_1354 (lift_to_both0 (usize 0)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 key_1356)) (prod_b(
                  lift_to_both0 (usize 0),
                  lift_to_both0 (usize 4)
                ))))) in
      letb uints_1354 : seq uint32 :=
        seq_upd uints_1354 (lift_to_both0 (usize 1)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 key_1356)) (prod_b(
                  lift_to_both0 (usize 4),
                  lift_to_both0 (usize 8)
                ))))) in
      letb uints_1354 : seq uint32 :=
        seq_upd uints_1354 (lift_to_both0 (usize 2)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 key_1356)) (prod_b(
                  lift_to_both0 (usize 8),
                  lift_to_both0 (usize 12)
                ))))) in
      letb uints_1354 : seq uint32 :=
        seq_upd uints_1354 (lift_to_both0 (usize 3)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 key_1356)) (prod_b(
                  lift_to_both0 (usize 12),
                  lift_to_both0 (usize 16)
                ))))) in
      letb uints_1354 : seq uint32 :=
        seq_upd uints_1354 (lift_to_both0 (usize 4)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 key_1356)) (prod_b(
                  lift_to_both0 (usize 16),
                  lift_to_both0 (usize 20)
                ))))) in
      letb uints_1354 : seq uint32 :=
        seq_upd uints_1354 (lift_to_both0 (usize 5)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 key_1356)) (prod_b(
                  lift_to_both0 (usize 20),
                  lift_to_both0 (usize 24)
                ))))) in
      letb uints_1354 : seq uint32 :=
        seq_upd uints_1354 (lift_to_both0 (usize 6)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 key_1356)) (prod_b(
                  lift_to_both0 (usize 24),
                  lift_to_both0 (usize 28)
                ))))) in
      letb uints_1354 : seq uint32 :=
        seq_upd uints_1354 (lift_to_both0 (usize 7)) (is_pure (
            uint32_from_le_bytes (array_from_slice_range (default : uint8) (4) (
                array_to_seq (lift_to_both0 key_1356)) (prod_b(
                  lift_to_both0 (usize 28),
                  lift_to_both0 (usize 32)
                ))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 uints_1354)
      ) : both (CEfset ([uints_1354_loc])) [interface] (seq uint32)).
Fail Next Obligation.


Notation "'gimli_aead_encrypt_inp'" :=(
  byte_seq × byte_seq × nonce_t × key_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_aead_encrypt_out'" :=((byte_seq '× tag_t
  ) : choice_type) (in custom pack_type at level 2).
Definition GIMLI_AEAD_ENCRYPT : nat :=
  1369.
Program Definition gimli_aead_encrypt (message_1364 : byte_seq) (
    ad_1362 : byte_seq) (nonce_1358 : nonce_t) (key_1359 : key_t)
  : both (CEfset (
      [block_1284_loc ; input_block_padded_1291_loc ; ciphertext_1313_loc ; msg_block_padded_1314_loc ; uints_1350_loc ; uints_1354_loc])) [interface] (
    (byte_seq '× tag_t)) :=
  ((letb s_1360 : state_t :=
        array_from_seq (12) (seq_concat (nonce_to_u32s (
              lift_to_both0 nonce_1358)) (key_to_u32s (
              lift_to_both0 key_1359))) in
      letb s_1361 : state_t := gimli (lift_to_both0 s_1360) in
      letb s_1363 : state_t :=
        process_ad (lift_to_both0 ad_1362) (lift_to_both0 s_1361) in
      letb '(s_1365, ciphertext_1366) : (state_t '× byte_seq) :=
        process_msg (lift_to_both0 message_1364) (lift_to_both0 s_1363) in
      letb tag_1367 : block_t := squeeze_block (lift_to_both0 s_1365) in
      letb tag_1368 : tag_t :=
        array_from_seq (16) (array_to_seq (lift_to_both0 tag_1367)) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 ciphertext_1366,
          lift_to_both0 tag_1368
        ))
      ) : both (CEfset (
        [block_1284_loc ; input_block_padded_1291_loc ; ciphertext_1313_loc ; msg_block_padded_1314_loc ; uints_1350_loc ; uints_1354_loc])) [interface] (
      (byte_seq '× tag_t))).
Fail Next Obligation.

Definition out_1370_loc : ChoiceEqualityLocation :=
  (seq uint8 ; 1371%nat).
Notation "'gimli_aead_decrypt_inp'" :=(
  byte_seq × byte_seq × tag_t × nonce_t × key_t : choice_type) (in custom pack_type at level 2).
Notation "'gimli_aead_decrypt_out'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Definition GIMLI_AEAD_DECRYPT : nat :=
  1384.
Program Definition gimli_aead_decrypt (ciphertext_1378 : byte_seq) (
    ad_1376 : byte_seq) (tag_1383 : tag_t) (nonce_1372 : nonce_t) (
    key_1373 : key_t)
  : both (CEfset (
      [block_1284_loc ; input_block_padded_1291_loc ; message_1330_loc ; msg_block_1331_loc ; uints_1350_loc ; uints_1354_loc ; out_1370_loc])) [interface] (
    byte_seq) :=
  ((letb s_1374 : state_t :=
        array_from_seq (12) (seq_concat (nonce_to_u32s (
              lift_to_both0 nonce_1372)) (key_to_u32s (
              lift_to_both0 key_1373))) in
      letb s_1375 : state_t := gimli (lift_to_both0 s_1374) in
      letb s_1377 : state_t :=
        process_ad (lift_to_both0 ad_1376) (lift_to_both0 s_1375) in
      letb '(s_1379, message_1380) : (state_t '× byte_seq) :=
        process_ct (lift_to_both0 ciphertext_1378) (lift_to_both0 s_1377) in
      letb my_tag_1381 : block_t := squeeze_block (lift_to_both0 s_1379) in
      letb my_tag_1382 : tag_t :=
        array_from_seq (16) (array_to_seq (lift_to_both0 my_tag_1381)) in
      letbm out_1370 : seq uint8 loc( out_1370_loc ) :=
        seq_new_ (default : uint8) (lift_to_both0 (usize 0)) in
      letb '(out_1370) :=
        if array_equal (lift_to_both0 my_tag_1382) (
          lift_to_both0 tag_1383) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [block_1284_loc ; input_block_padded_1291_loc ; message_1330_loc ; msg_block_1331_loc ; uints_1350_loc ; uints_1354_loc ; out_1370_loc])) (
          L2 := CEfset (
            [block_1284_loc ; input_block_padded_1291_loc ; message_1330_loc ; msg_block_1331_loc ; uints_1350_loc ; uints_1354_loc ; out_1370_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm out_1370 loc( out_1370_loc ) := lift_to_both0 message_1380 in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 out_1370)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 out_1370)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 out_1370)
      ) : both (CEfset (
        [block_1284_loc ; input_block_padded_1291_loc ; message_1330_loc ; msg_block_1331_loc ; uints_1350_loc ; uints_1354_loc ; out_1370_loc])) [interface] (
      byte_seq)).
Fail Next Obligation.

