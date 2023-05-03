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


Definition irr_1432_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1433%nat).
Notation "'build_irreducible_inp'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Notation "'build_irreducible_out'" :=(
  seq int128 : choice_type) (in custom pack_type at level 2).
Definition BUILD_IRREDUCIBLE : nat :=
  1435.
Program Definition build_irreducible (p_1434 : uint_size)
  : both (CEfset ([irr_1432_loc])) [interface] (seq int128) :=
  ((letbm irr_1432 : seq int128 loc( irr_1432_loc ) :=
        seq_new_ (default : int128) ((lift_to_both0 p_1434) .+ (lift_to_both0 (
              usize 1))) in
      letb irr_1432 : seq int128 :=
        seq_upd irr_1432 (lift_to_both0 (usize 0)) (is_pure (- (lift_to_both0 (
                @repr U128 1)))) in
      letb irr_1432 : seq int128 :=
        seq_upd irr_1432 (lift_to_both0 (usize 1)) (is_pure (- (lift_to_both0 (
                @repr U128 1)))) in
      letb irr_1432 : seq int128 :=
        seq_upd irr_1432 (lift_to_both0 p_1434) (is_pure (lift_to_both0 (
              @repr U128 1))) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 irr_1432)
      ) : both (CEfset ([irr_1432_loc])) [interface] (seq int128)).
Fail Next Obligation.

Definition result_1436_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1437%nat).
Notation "'round_to_3_inp'" :=(
  seq int128 × int128 : choice_type) (in custom pack_type at level 2).
Notation "'round_to_3_out'" :=(
  seq int128 : choice_type) (in custom pack_type at level 2).
Definition ROUND_TO_3 : nat :=
  1443.
Program Definition round_to_3 (poly_1438 : seq int128) (q_1439 : int128)
  : both (CEfset ([result_1436_loc])) [interface] (seq int128) :=
  ((letbm result_1436 : seq int128 loc( result_1436_loc ) :=
        (lift_to_both0 poly_1438) in
      letb q_12_1440 : int128 :=
        ((lift_to_both0 q_1439) .- (lift_to_both0 (@repr U128 1))) ./ (
          lift_to_both0 (@repr U128 2)) in
      letb result_1436 :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 poly_1438)) result_1436 (L := (CEfset (
                [result_1436_loc]))) (I := [interface]) (
            fun i_1441 result_1436 =>
            letb '(result_1436) :=
              if (seq_index (poly_1438) (lift_to_both0 i_1441)) >.? (
                lift_to_both0 q_12_1440) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([result_1436_loc])) (L2 := CEfset (
                  [result_1436_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb result_1436 : seq int128 :=
                  seq_upd result_1436 (lift_to_both0 i_1441) (is_pure ((
                        seq_index (poly_1438) (lift_to_both0 i_1441)) .- (
                        lift_to_both0 q_1439))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 result_1436)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 result_1436)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 result_1436)
            ) in
      letb result_1436 :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 result_1436)) result_1436 (L := (CEfset (
                [result_1436_loc]))) (I := [interface]) (
            fun i_1442 result_1436 =>
            letb '(result_1436) :=
              if ((seq_index (result_1436) (lift_to_both0 i_1442)) .% (
                  lift_to_both0 (@repr U128 3))) !=.? (lift_to_both0 (
                  @repr U128 0)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([result_1436_loc])) (L2 := CEfset (
                  [result_1436_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb result_1436 : seq int128 :=
                  seq_upd result_1436 (lift_to_both0 i_1442) (is_pure ((
                        seq_index (result_1436) (lift_to_both0 i_1442)) .- (
                        lift_to_both0 (@repr U128 1)))) in
                letb '(result_1436) :=
                  if ((seq_index (result_1436) (lift_to_both0 i_1442)) .% (
                      lift_to_both0 (@repr U128 3))) !=.? (lift_to_both0 (
                      @repr U128 0)) :bool_ChoiceEquality
                  then lift_scope (L1 := CEfset ([result_1436_loc])) (
                    L2 := CEfset ([result_1436_loc])) (I1 := [interface]) (
                    I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                    letb result_1436 : seq int128 :=
                      seq_upd result_1436 (lift_to_both0 i_1442) (is_pure ((
                            seq_index (result_1436) (lift_to_both0 i_1442)) .+ (
                            lift_to_both0 (@repr U128 2)))) in
                    lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                      lift_to_both0 result_1436)
                    )
                  else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                    lift_to_both0 result_1436)
                   in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 result_1436)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 result_1436)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 result_1436)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 result_1436)
      ) : both (CEfset ([result_1436_loc])) [interface] (seq int128)).
Fail Next Obligation.


Notation "'encrypt_inp'" :=(
  seq int128 × seq int128 × int128 × seq int128 : choice_type) (in custom pack_type at level 2).
Notation "'encrypt_out'" :=(
  seq int128 : choice_type) (in custom pack_type at level 2).
Definition ENCRYPT : nat :=
  1449.
Program Definition encrypt (r_1444 : seq int128) (h_1445 : seq int128) (
    q_1447 : int128) (irreducible_1446 : seq int128)
  : both (CEfset ([result_1436_loc])) [interface] (seq int128) :=
  ((letb pre_1448 : seq int128 :=
        mul_poly_irr (lift_to_both0 r_1444) (lift_to_both0 h_1445) (
          lift_to_both0 irreducible_1446) (lift_to_both0 q_1447) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (round_to_3 (
          lift_to_both0 pre_1448) (lift_to_both0 q_1447))
      ) : both (CEfset ([result_1436_loc])) [interface] (seq int128)).
Fail Next Obligation.


Notation "'ntru_prime_653_encrypt_inp'" :=(
  seq int128 × seq int128 : choice_type) (in custom pack_type at level 2).
Notation "'ntru_prime_653_encrypt_out'" :=(
  seq int128 : choice_type) (in custom pack_type at level 2).
Definition NTRU_PRIME_653_ENCRYPT : nat :=
  1456.
Program Definition ntru_prime_653_encrypt (r_1454 : seq int128) (
    h_1455 : seq int128)
  : both (CEfset ([irr_1432_loc ; result_1436_loc])) [interface] (seq int128) :=
  ((letb p_1450 : uint_size := lift_to_both0 (usize 653) in
      letb q_1451 : int128 := lift_to_both0 (@repr U128 4621) in
      letb w_1452 : uint_size := lift_to_both0 (usize 288) in
      letb irreducible_1453 : seq int128 :=
        build_irreducible (lift_to_both0 p_1450) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (encrypt (
          lift_to_both0 r_1454) (lift_to_both0 h_1455) (lift_to_both0 q_1451) (
          lift_to_both0 irreducible_1453))
      ) : both (CEfset ([irr_1432_loc ; result_1436_loc])) [interface] (
      seq int128)).
Fail Next Obligation.

Definition e_1458_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1460%nat).
Definition f_3_c_1457_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1461%nat).
Definition r_1459_loc : ChoiceEqualityLocation :=
  (seq int128 ; 1462%nat).
Notation "'ntru_prime_653_decrypt_inp'" :=(
  seq int128 × seq int128 × seq int128 : choice_type) (in custom pack_type at level 2).
Notation "'ntru_prime_653_decrypt_out'" :=((seq int128 '× bool_ChoiceEquality
  ) : choice_type) (in custom pack_type at level 2).
Definition NTRU_PRIME_653_DECRYPT : nat :=
  1478.
Program Definition ntru_prime_653_decrypt (c_1468 : seq int128) (
    key_f_1467 : seq int128) (key_v_1476 : seq int128)
  : both (CEfset (
      [irr_1432_loc ; f_3_c_1457_loc ; e_1458_loc ; r_1459_loc])) [interface] ((
      seq int128 '×
      bool_ChoiceEquality
    )) :=
  ((letb p_1463 : uint_size := lift_to_both0 (usize 653) in
      letb q_1464 : int128 := lift_to_both0 (@repr U128 4621) in
      letb w_1465 : uint_size := lift_to_both0 (usize 288) in
      letb irreducible_1466 : seq int128 :=
        build_irreducible (lift_to_both0 p_1463) in
      letb f_c_1469 : seq int128 :=
        mul_poly_irr (lift_to_both0 key_f_1467) (lift_to_both0 c_1468) (
          lift_to_both0 irreducible_1466) (lift_to_both0 q_1464) in
      letb f_3_c_and_decryption_ok_1470 : (seq int128 '× bool_ChoiceEquality
        ) :=
        poly_to_ring (lift_to_both0 irreducible_1466) (add_poly (
            lift_to_both0 f_c_1469) (add_poly (lift_to_both0 f_c_1469) (
              lift_to_both0 f_c_1469) (lift_to_both0 q_1464)) (
            lift_to_both0 q_1464)) (lift_to_both0 q_1464) in
      letb '(f_3_c_1471, ok_decrypt_1472) : (seq int128 '× bool_ChoiceEquality
        ) :=
        lift_to_both0 f_3_c_and_decryption_ok_1470 in
      letbm f_3_c_1457 : seq int128 loc( f_3_c_1457_loc ) :=
        lift_to_both0 f_3_c_1471 in
      letb q_12_1473 : int128 :=
        ((lift_to_both0 q_1464) .- (lift_to_both0 (@repr U128 1))) ./ (
          lift_to_both0 (@repr U128 2)) in
      letb f_3_c_1457 :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 f_3_c_1457)) f_3_c_1457 (L := (CEfset (
                [irr_1432_loc ; f_3_c_1457_loc ; e_1458_loc ; r_1459_loc]))) (
            I := [interface]) (fun i_1474 f_3_c_1457 =>
            letb '(f_3_c_1457) :=
              if (seq_index (f_3_c_1457) (lift_to_both0 i_1474)) >.? (
                lift_to_both0 q_12_1473) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([irr_1432_loc ; f_3_c_1457_loc])) (
                L2 := CEfset ([irr_1432_loc ; f_3_c_1457_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb f_3_c_1457 : seq int128 :=
                  seq_upd f_3_c_1457 (lift_to_both0 i_1474) (is_pure ((
                        seq_index (f_3_c_1457) (lift_to_both0 i_1474)) .- (
                        lift_to_both0 q_1464))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 f_3_c_1457)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 f_3_c_1457)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 f_3_c_1457)
            ) in
      letbm e_1458 : seq int128 loc( e_1458_loc ) :=
        seq_new_ (default : int128) (seq_len (lift_to_both0 f_3_c_1457)) in
      letb e_1458 :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 e_1458)) e_1458 (L := (CEfset (
                [irr_1432_loc ; f_3_c_1457_loc ; e_1458_loc ; r_1459_loc]))) (
            I := [interface]) (fun i_1475 e_1458 =>
            letb e_1458 : seq int128 :=
              seq_upd e_1458 (lift_to_both0 i_1475) (is_pure ((seq_index (
                      f_3_c_1457) (lift_to_both0 i_1475)) .% (lift_to_both0 (
                      @repr U128 3)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 e_1458)
            ) in
      letbm e_1458 loc( e_1458_loc ) :=
        make_positive (lift_to_both0 e_1458) (lift_to_both0 (@repr U128 3)) in
      letbm r_1459 : seq int128 loc( r_1459_loc ) :=
        mul_poly_irr (lift_to_both0 e_1458) (lift_to_both0 key_v_1476) (
          lift_to_both0 irreducible_1466) (lift_to_both0 (@repr U128 3)) in
      letb r_1459 :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 r_1459)) r_1459 (L := (CEfset (
                [irr_1432_loc ; f_3_c_1457_loc ; e_1458_loc ; r_1459_loc]))) (
            I := [interface]) (fun i_1477 r_1459 =>
            letb '(r_1459) :=
              if (seq_index (r_1459) (lift_to_both0 i_1477)) =.? (
                lift_to_both0 (@repr U128 2)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [irr_1432_loc ; f_3_c_1457_loc ; e_1458_loc ; r_1459_loc])) (
                L2 := CEfset (
                  [irr_1432_loc ; f_3_c_1457_loc ; e_1458_loc ; r_1459_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb r_1459 : seq int128 :=
                  seq_upd r_1459 (lift_to_both0 i_1477) (is_pure (- (
                        lift_to_both0 (@repr U128 1)))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 r_1459)
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                lift_to_both0 r_1459)
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 r_1459)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 r_1459,
          lift_to_both0 ok_decrypt_1472
        ))
      ) : both (CEfset (
        [irr_1432_loc ; f_3_c_1457_loc ; e_1458_loc ; r_1459_loc])) [interface] (
      (seq int128 '× bool_ChoiceEquality))).
Fail Next Obligation.

