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


Definition schedule_t := nseq (uint32) (usize 80).

Definition block_words_v : uint_size :=
  ((usize 512) ./ (usize 32)).

Definition hash_words_v : uint_size :=
  ((usize 160) ./ (usize 32)).

Definition block_t := nseq (uint32) (block_words_v).

Definition hash_t := nseq (uint32) (hash_words_v).

Definition block_bytes_v : uint_size :=
  ((usize 512) ./ (usize 8)).

Definition hash_bytes_v : uint_size :=
  ((usize 160) ./ (usize 8)).

Definition block_bytes_t := nseq (uint8) (block_bytes_v).

Definition sha1_digest_t := nseq (uint8) (hash_bytes_v).

Definition bitlength_bytes_v : uint_size :=
  ((usize 64) ./ (usize 8)).


Notation "'ch_inp'" :=(
  uint32 × uint32 × uint32 : choice_type) (in custom pack_type at level 2).
Notation "'ch_out'" :=(uint32 : choice_type) (in custom pack_type at level 2).
Definition CH : nat :=
  1388.
Program Definition ch (x_1385 : uint32) (y_1386 : uint32) (z_1387 : uint32)
  : both (fset.fset0) [interface] (uint32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 x_1385) .& (lift_to_both0 y_1386)) .^ ((not (
              lift_to_both0 x_1385)) .& (lift_to_both0 z_1387)))
      ) : both (fset.fset0) [interface] (uint32)).
Fail Next Obligation.


Notation "'parity_inp'" :=(
  uint32 × uint32 × uint32 : choice_type) (in custom pack_type at level 2).
Notation "'parity_out'" :=(
  uint32 : choice_type) (in custom pack_type at level 2).
Definition PARITY : nat :=
  1392.
Program Definition parity (x_1389 : uint32) (y_1390 : uint32) (z_1391 : uint32)
  : both (fset.fset0) [interface] (uint32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 x_1389) .^ (lift_to_both0 y_1390)) .^ (
          lift_to_both0 z_1391))
      ) : both (fset.fset0) [interface] (uint32)).
Fail Next Obligation.


Notation "'maj_inp'" :=(
  uint32 × uint32 × uint32 : choice_type) (in custom pack_type at level 2).
Notation "'maj_out'" :=(uint32 : choice_type) (in custom pack_type at level 2).
Definition MAJ : nat :=
  1396.
Program Definition maj (x_1393 : uint32) (y_1394 : uint32) (z_1395 : uint32)
  : both (fset.fset0) [interface] (uint32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((((
              lift_to_both0 x_1393) .& (lift_to_both0 y_1394)) .^ ((
              lift_to_both0 x_1393) .& (lift_to_both0 z_1395))) .^ ((
            lift_to_both0 y_1394) .& (lift_to_both0 z_1395)))
      ) : both (fset.fset0) [interface] (uint32)).
Fail Next Obligation.

Definition hash_init_v : hash_t :=
  @array_from_list uint32 [
    (secret (@repr U32 1732584193)) : uint32;
    (secret (@repr U32 4023233417)) : uint32;
    (secret (@repr U32 2562383102)) : uint32;
    (secret (@repr U32 271733878)) : uint32;
    (secret (@repr U32 3285377520)) : uint32
  ].

Definition e_1402_loc : ChoiceEqualityLocation :=
  (uint32 ; 1404%nat).
Definition w_1397_loc : ChoiceEqualityLocation :=
  (schedule_t ; 1405%nat).
Definition c_1400_loc : ChoiceEqualityLocation :=
  (uint32 ; 1406%nat).
Definition d_1401_loc : ChoiceEqualityLocation :=
  (uint32 ; 1407%nat).
Definition t_1403_loc : ChoiceEqualityLocation :=
  (uint32 ; 1408%nat).
Definition b_1399_loc : ChoiceEqualityLocation :=
  (uint32 ; 1409%nat).
Definition a_1398_loc : ChoiceEqualityLocation :=
  (uint32 ; 1410%nat).
Notation "'compress_inp'" :=(
  block_bytes_t × hash_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_out'" :=(
  hash_t : choice_type) (in custom pack_type at level 2).
Definition COMPRESS : nat :=
  1416.
Program Definition compress (m_bytes_1411 : block_bytes_t) (h_1414 : hash_t)
  : both (CEfset (
      [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc])) [interface] (
    hash_t) :=
  ((letb m_1412 : seq uint32 :=
        array_to_be_uint32s (lift_to_both0 m_bytes_1411) in
      letbm w_1397 : schedule_t loc( w_1397_loc ) :=
        array_new_ (default : uint32) (80) in
      letb w_1397 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 80)) w_1397 (L := (CEfset (
                [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc]))) (
            I := [interface]) (fun t_1413 w_1397 =>
            letb '(w_1397) :=
              if (lift_to_both0 t_1413) <.? (lift_to_both0 (
                  usize 16)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([w_1397_loc])) (L2 := CEfset (
                  [w_1397_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb w_1397 : schedule_t :=
                  array_upd w_1397 (lift_to_both0 t_1413) (is_pure (seq_index (
                        m_1412) (lift_to_both0 t_1413))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 w_1397)
                )
              else  lift_scope (L1 := CEfset ([w_1397_loc])) (L2 := CEfset (
                  [w_1397_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb w_1397 : schedule_t :=
                  array_upd w_1397 (lift_to_both0 t_1413) (is_pure (
                      uint32_rotate_left ((((array_index (w_1397) ((
                                  lift_to_both0 t_1413) .- (lift_to_both0 (
                                    usize 3)))) .^ (array_index (w_1397) ((
                                  lift_to_both0 t_1413) .- (lift_to_both0 (
                                    usize 8))))) .^ (array_index (w_1397) ((
                                lift_to_both0 t_1413) .- (lift_to_both0 (
                                  usize 14))))) .^ (array_index (w_1397) ((
                              lift_to_both0 t_1413) .- (lift_to_both0 (
                                usize 16))))) (lift_to_both0 (usize 1)))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 w_1397)
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 w_1397)
            ) in
      letbm a_1398 : uint32 loc( a_1398_loc ) :=
        array_index (h_1414) (lift_to_both0 (usize 0)) in
      letbm b_1399 : uint32 loc( b_1399_loc ) :=
        array_index (h_1414) (lift_to_both0 (usize 1)) in
      letbm c_1400 : uint32 loc( c_1400_loc ) :=
        array_index (h_1414) (lift_to_both0 (usize 2)) in
      letbm d_1401 : uint32 loc( d_1401_loc ) :=
        array_index (h_1414) (lift_to_both0 (usize 3)) in
      letbm e_1402 : uint32 loc( e_1402_loc ) :=
        array_index (h_1414) (lift_to_both0 (usize 4)) in
      letb '(a_1398, b_1399, c_1400, d_1401, e_1402) :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 80)) prod_ce(a_1398, b_1399, c_1400, d_1401, e_1402) (L := (
              CEfset (
                [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc]))) (
            I := [interface]) (fun t_1415 '(
              a_1398,
              b_1399,
              c_1400,
              d_1401,
              e_1402
            ) =>
            letbm t_1403 : uint32 loc( t_1403_loc ) := uint32_zero  in
            letb '(t_1403) :=
              if ((lift_to_both0 (usize 0)) <=.? (lift_to_both0 t_1415)) && ((
                  lift_to_both0 t_1415) <.? (lift_to_both0 (
                    usize 20))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc])) (
                L2 := CEfset (
                  [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm t_1403 loc( t_1403_loc ) :=
                  ((((uint32_rotate_left (lift_to_both0 a_1398) (lift_to_both0 (
                              usize 5))) .+ (ch (lift_to_both0 b_1399) (
                            lift_to_both0 c_1400) (lift_to_both0 d_1401))) .+ (
                        lift_to_both0 e_1402)) .+ (secret (lift_to_both0 (
                          @repr U32 1518500249)))) .+ (array_index (w_1397) (
                      lift_to_both0 t_1415)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 t_1403)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 t_1403)
               in
            letb '(t_1403) :=
              if ((lift_to_both0 (usize 20)) <=.? (lift_to_both0 t_1415)) && ((
                  lift_to_both0 t_1415) <.? (lift_to_both0 (
                    usize 40))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc])) (
                L2 := CEfset (
                  [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm t_1403 loc( t_1403_loc ) :=
                  ((((uint32_rotate_left (lift_to_both0 a_1398) (lift_to_both0 (
                              usize 5))) .+ (parity (lift_to_both0 b_1399) (
                            lift_to_both0 c_1400) (lift_to_both0 d_1401))) .+ (
                        lift_to_both0 e_1402)) .+ (secret (lift_to_both0 (
                          @repr U32 1859775393)))) .+ (array_index (w_1397) (
                      lift_to_both0 t_1415)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 t_1403)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 t_1403)
               in
            letb '(t_1403) :=
              if ((lift_to_both0 (usize 40)) <=.? (lift_to_both0 t_1415)) && ((
                  lift_to_both0 t_1415) <.? (lift_to_both0 (
                    usize 60))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc])) (
                L2 := CEfset (
                  [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm t_1403 loc( t_1403_loc ) :=
                  ((((uint32_rotate_left (lift_to_both0 a_1398) (lift_to_both0 (
                              usize 5))) .+ (maj (lift_to_both0 b_1399) (
                            lift_to_both0 c_1400) (lift_to_both0 d_1401))) .+ (
                        lift_to_both0 e_1402)) .+ (secret (lift_to_both0 (
                          @repr U32 2400959708)))) .+ (array_index (w_1397) (
                      lift_to_both0 t_1415)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 t_1403)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 t_1403)
               in
            letb '(t_1403) :=
              if ((lift_to_both0 (usize 60)) <=.? (lift_to_both0 t_1415)) && ((
                  lift_to_both0 t_1415) <.? (lift_to_both0 (
                    usize 80))) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc])) (
                L2 := CEfset (
                  [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm t_1403 loc( t_1403_loc ) :=
                  ((((uint32_rotate_left (lift_to_both0 a_1398) (lift_to_both0 (
                              usize 5))) .+ (parity (lift_to_both0 b_1399) (
                            lift_to_both0 c_1400) (lift_to_both0 d_1401))) .+ (
                        lift_to_both0 e_1402)) .+ (secret (lift_to_both0 (
                          @repr U32 3395469782)))) .+ (array_index (w_1397) (
                      lift_to_both0 t_1415)) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 t_1403)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 t_1403)
               in
            letbm e_1402 loc( e_1402_loc ) := lift_to_both0 d_1401 in
            letbm d_1401 loc( d_1401_loc ) := lift_to_both0 c_1400 in
            letbm c_1400 loc( c_1400_loc ) :=
              uint32_rotate_left (lift_to_both0 b_1399) (lift_to_both0 (
                  usize 30)) in
            letbm b_1399 loc( b_1399_loc ) := lift_to_both0 a_1398 in
            letbm a_1398 loc( a_1398_loc ) := lift_to_both0 t_1403 in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 a_1398,
                lift_to_both0 b_1399,
                lift_to_both0 c_1400,
                lift_to_both0 d_1401,
                lift_to_both0 e_1402
              ))
            ) in
      letb h_1414 : hash_t :=
        array_upd h_1414 (lift_to_both0 (usize 0)) (is_pure ((
              lift_to_both0 a_1398) .+ (array_index (h_1414) (lift_to_both0 (
                  usize 0))))) in
      letb h_1414 : hash_t :=
        array_upd h_1414 (lift_to_both0 (usize 1)) (is_pure ((
              lift_to_both0 b_1399) .+ (array_index (h_1414) (lift_to_both0 (
                  usize 1))))) in
      letb h_1414 : hash_t :=
        array_upd h_1414 (lift_to_both0 (usize 2)) (is_pure ((
              lift_to_both0 c_1400) .+ (array_index (h_1414) (lift_to_both0 (
                  usize 2))))) in
      letb h_1414 : hash_t :=
        array_upd h_1414 (lift_to_both0 (usize 3)) (is_pure ((
              lift_to_both0 d_1401) .+ (array_index (h_1414) (lift_to_both0 (
                  usize 3))))) in
      letb h_1414 : hash_t :=
        array_upd h_1414 (lift_to_both0 (usize 4)) (is_pure ((
              lift_to_both0 e_1402) .+ (array_index (h_1414) (lift_to_both0 (
                  usize 4))))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 h_1414)
      ) : both (CEfset (
        [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc])) [interface] (
      hash_t)).
Fail Next Obligation.

Definition h_1417_loc : ChoiceEqualityLocation :=
  (hash_t ; 1420%nat).
Definition pad_block_1419_loc : ChoiceEqualityLocation :=
  (block_bytes_t ; 1421%nat).
Definition block_bytes_1418_loc : ChoiceEqualityLocation :=
  (block_bytes_t ; 1422%nat).
Notation "'hash_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'hash_out'" :=(
  sha1_digest_t : choice_type) (in custom pack_type at level 2).
Definition HASH : nat :=
  1429.
Program Definition hash (msg_1423 : byte_seq)
  : both (CEfset (
      [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc ; h_1417_loc ; block_bytes_1418_loc ; pad_block_1419_loc])) [interface] (
    sha1_digest_t) :=
  ((letbm h_1417 : hash_t loc( h_1417_loc ) := lift_to_both0 hash_init_v in
      letb h_1417 :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_num_exact_chunks (
              lift_to_both0 msg_1423) (lift_to_both0 block_bytes_v)) h_1417 (
            L := (CEfset (
                [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc ; h_1417_loc ; block_bytes_1418_loc ; pad_block_1419_loc]))) (
            I := [interface]) (fun i_1424 h_1417 =>
            letb raw_bytes_1425 : seq uint8 :=
              seq_get_exact_chunk (lift_to_both0 msg_1423) (
                lift_to_both0 block_bytes_v) (lift_to_both0 i_1424) in
            letb block_bytes_1426 : block_bytes_t :=
              array_from_seq (block_bytes_v) (lift_to_both0 raw_bytes_1425) in
            letbm h_1417 loc( h_1417_loc ) :=
              compress (lift_to_both0 block_bytes_1426) (
                lift_to_both0 h_1417) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 h_1417)
            ) in
      letb raw_bytes_1427 : seq uint8 :=
        seq_get_remainder_chunk (lift_to_both0 msg_1423) (
          lift_to_both0 block_bytes_v) in
      letbm block_bytes_1418 : block_bytes_t loc( block_bytes_1418_loc ) :=
        array_update_start (array_new_ (default : uint8) (block_bytes_v)) (
          lift_to_both0 raw_bytes_1427) in
      letb block_bytes_1418 : block_bytes_t :=
        array_upd block_bytes_1418 (seq_len (lift_to_both0 raw_bytes_1427)) (
          is_pure (secret (lift_to_both0 (@repr U8 128)))) in
      letb message_bitlength_1428 : uint64 :=
        secret (pub_u64 (is_pure ((seq_len (lift_to_both0 msg_1423)) .* (
                lift_to_both0 (usize 8))))) in
      letb '(h_1417, block_bytes_1418) :=
        if (seq_len (lift_to_both0 raw_bytes_1427)) <.? ((
            lift_to_both0 block_bytes_v) .- (
            lift_to_both0 bitlength_bytes_v)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc ; h_1417_loc ; block_bytes_1418_loc])) (
          L2 := CEfset (
            [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc ; h_1417_loc ; block_bytes_1418_loc ; pad_block_1419_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm block_bytes_1418 loc( block_bytes_1418_loc ) :=
            array_update (lift_to_both0 block_bytes_1418) ((
                lift_to_both0 block_bytes_v) .- (
                lift_to_both0 bitlength_bytes_v)) (
              array_to_seq (uint64_to_be_bytes (
                lift_to_both0 message_bitlength_1428))) in
          letbm h_1417 loc( h_1417_loc ) :=
            compress (lift_to_both0 block_bytes_1418) (lift_to_both0 h_1417) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 h_1417,
              lift_to_both0 block_bytes_1418
            ))
          )
        else  lift_scope (L1 := CEfset (
            [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc ; h_1417_loc ; block_bytes_1418_loc ; pad_block_1419_loc])) (
          L2 := CEfset (
            [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc ; h_1417_loc ; block_bytes_1418_loc ; pad_block_1419_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm h_1417 loc( h_1417_loc ) :=
            compress (lift_to_both0 block_bytes_1418) (lift_to_both0 h_1417) in
          letbm pad_block_1419 : block_bytes_t loc( pad_block_1419_loc ) :=
            array_new_ (default : uint8) (block_bytes_v) in
          letbm pad_block_1419 loc( pad_block_1419_loc ) :=
            array_update (lift_to_both0 pad_block_1419) ((
                lift_to_both0 block_bytes_v) .- (
                lift_to_both0 bitlength_bytes_v)) (
              array_to_seq (uint64_to_be_bytes (
                lift_to_both0 message_bitlength_1428))) in
          letbm h_1417 loc( h_1417_loc ) :=
            compress (lift_to_both0 pad_block_1419) (lift_to_both0 h_1417) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 h_1417,
              lift_to_both0 block_bytes_1418
            ))
          ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (
          hash_bytes_v) (array_to_be_bytes (lift_to_both0 h_1417)))
      ) : both (CEfset (
        [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc ; h_1417_loc ; block_bytes_1418_loc ; pad_block_1419_loc])) [interface] (
      sha1_digest_t)).
Fail Next Obligation.


Notation "'sha1_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha1_out'" :=(
  sha1_digest_t : choice_type) (in custom pack_type at level 2).
Definition SHA1 : nat :=
  1431.
Program Definition sha1 (msg_1430 : byte_seq)
  : both (CEfset (
      [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc ; h_1417_loc ; block_bytes_1418_loc ; pad_block_1419_loc])) [interface] (
    sha1_digest_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (hash (
          lift_to_both0 msg_1430))
      ) : both (CEfset (
        [w_1397_loc ; a_1398_loc ; b_1399_loc ; c_1400_loc ; d_1401_loc ; e_1402_loc ; t_1403_loc ; h_1417_loc ; block_bytes_1418_loc ; pad_block_1419_loc])) [interface] (
      sha1_digest_t)).
Fail Next Obligation.

