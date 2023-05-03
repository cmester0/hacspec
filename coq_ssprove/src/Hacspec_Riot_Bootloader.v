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


Definition riotboot_magic_v : int32 :=
  @repr U32 1414482258.

Notation "'fletcher_t'" := ((int32 × int32)) : hacspec_scope.


Notation "'new_fletcher_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'new_fletcher_out'" :=(
  fletcher_t : choice_type) (in custom pack_type at level 2).
Definition NEW_FLETCHER : nat :=
  1479.
Program Definition new_fletcher  : both (fset.fset0) [interface] (fletcher_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 (@repr U32 65535),
          lift_to_both0 (@repr U32 65535)
        ))
      ) : both (fset.fset0) [interface] (fletcher_t)).
Fail Next Obligation.


Notation "'max_chunk_size_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'max_chunk_size_out'" :=(
  uint_size : choice_type) (in custom pack_type at level 2).
Definition MAX_CHUNK_SIZE : nat :=
  1480.
Program Definition max_chunk_size 
  : both (fset.fset0) [interface] (uint_size) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 (usize 360))
      ) : both (fset.fset0) [interface] (uint_size)).
Fail Next Obligation.


Notation "'reduce_u32_inp'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'reduce_u32_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Definition REDUCE_U32 : nat :=
  1482.
Program Definition reduce_u32 (x_1481 : int32)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 x_1481) .& (lift_to_both0 (@repr U32 65535))) .+ ((
            lift_to_both0 x_1481) shift_right (lift_to_both0 (@repr U32 16))))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.


Notation "'combine_inp'" :=(
  int32 × int32 : choice_type) (in custom pack_type at level 2).
Notation "'combine_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Definition COMBINE : nat :=
  1485.
Program Definition combine (lower_1483 : int32) (upper_1484 : int32)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((
          lift_to_both0 lower_1483) .| ((lift_to_both0 upper_1484) shift_left (
            lift_to_both0 (@repr U32 16))))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.

Definition intermediate_b_1489_loc : ChoiceEqualityLocation :=
  (int32 ; 1490%nat).
Definition b_1487_loc : ChoiceEqualityLocation :=
  (int32 ; 1491%nat).
Definition intermediate_a_1488_loc : ChoiceEqualityLocation :=
  (int32 ; 1492%nat).
Definition a_1486_loc : ChoiceEqualityLocation :=
  (int32 ; 1493%nat).
Notation "'update_fletcher_inp'" :=(
  fletcher_t × seq int16 : choice_type) (in custom pack_type at level 2).
Notation "'update_fletcher_out'" :=(
  fletcher_t : choice_type) (in custom pack_type at level 2).
Definition UPDATE_FLETCHER : nat :=
  1501.
Program Definition update_fletcher (f_1495 : fletcher_t) (data_1496 : seq int16)
  : both (CEfset (
      [a_1486_loc ; b_1487_loc ; intermediate_a_1488_loc ; intermediate_b_1489_loc])) [interface] (
    fletcher_t) :=
  ((letb max_chunk_size_1494 : uint_size := max_chunk_size  in
      letb '(a_1486, b_1487) : (int32 '× int32) := lift_to_both0 f_1495 in
      letb '(a_1486, b_1487) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_num_chunks (
              lift_to_both0 data_1496) (
              lift_to_both0 max_chunk_size_1494)) prod_ce(a_1486, b_1487) (
            L := (CEfset (
                [a_1486_loc ; b_1487_loc ; intermediate_a_1488_loc ; intermediate_b_1489_loc]))) (
            I := [interface]) (fun i_1497 '(a_1486, b_1487) =>
            letb '(chunk_len_1498, chunk_1499) : (uint_size '× seq int16) :=
              seq_get_chunk (lift_to_both0 data_1496) (
                lift_to_both0 max_chunk_size_1494) (lift_to_both0 i_1497) in
            letbm intermediate_a_1488 : int32 loc( intermediate_a_1488_loc ) :=
              lift_to_both0 a_1486 in
            letbm intermediate_b_1489 : int32 loc( intermediate_b_1489_loc ) :=
              lift_to_both0 b_1487 in
            letb '(intermediate_a_1488, intermediate_b_1489) :=
              foldi_both' (lift_to_both0 (usize 0)) (
                  lift_to_both0 chunk_len_1498) prod_ce(
                  intermediate_a_1488,
                  intermediate_b_1489
                ) (L := (CEfset (
                      [a_1486_loc ; b_1487_loc ; intermediate_a_1488_loc ; intermediate_b_1489_loc]))) (
                  I := [interface]) (fun j_1500 '(
                    intermediate_a_1488,
                    intermediate_b_1489
                  ) =>
                  letbm intermediate_a_1488 loc( intermediate_a_1488_loc ) :=
                    (lift_to_both0 intermediate_a_1488) .+ (
                      (fun x => lift_to_both0 (repr (unsigned x)))(seq_index (
                          chunk_1499) (lift_to_both0 j_1500))) in
                  letbm intermediate_b_1489 loc( intermediate_b_1489_loc ) :=
                    (lift_to_both0 intermediate_b_1489) .+ (
                      lift_to_both0 intermediate_a_1488) in
                  lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                      lift_to_both0 intermediate_a_1488,
                      lift_to_both0 intermediate_b_1489
                    ))
                  ) in
            letbm a_1486 loc( a_1486_loc ) :=
              reduce_u32 (lift_to_both0 intermediate_a_1488) in
            letbm b_1487 loc( b_1487_loc ) :=
              reduce_u32 (lift_to_both0 intermediate_b_1489) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 a_1486,
                lift_to_both0 b_1487
              ))
            ) in
      letbm a_1486 loc( a_1486_loc ) := reduce_u32 (lift_to_both0 a_1486) in
      letbm b_1487 loc( b_1487_loc ) := reduce_u32 (lift_to_both0 b_1487) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 a_1486,
          lift_to_both0 b_1487
        ))
      ) : both (CEfset (
        [a_1486_loc ; b_1487_loc ; intermediate_a_1488_loc ; intermediate_b_1489_loc])) [interface] (
      fletcher_t)).
Fail Next Obligation.


Notation "'value_inp'" :=(
  fletcher_t : choice_type) (in custom pack_type at level 2).
Notation "'value_out'" :=(int32 : choice_type) (in custom pack_type at level 2).
Definition VALUE : nat :=
  1505.
Program Definition value (x_1502 : fletcher_t)
  : both (fset.fset0) [interface] (int32) :=
  ((letb '(a_1503, b_1504) : (int32 '× int32) := lift_to_both0 x_1502 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (combine (
          lift_to_both0 a_1503) (lift_to_both0 b_1504))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.

Notation "'header_t'" := ((int32 × int32 × int32 × int32)) : hacspec_scope.

Definition u16_seq_1506_loc : ChoiceEqualityLocation :=
  (seq int16 ; 1507%nat).
Notation "'header_as_u16_slice_inp'" :=(
  header_t : choice_type) (in custom pack_type at level 2).
Notation "'header_as_u16_slice_out'" :=(
  seq int16 : choice_type) (in custom pack_type at level 2).
Definition HEADER_AS_U16_SLICE : nat :=
  1524.
Program Definition header_as_u16_slice (h_1508 : header_t)
  : both (CEfset ([u16_seq_1506_loc])) [interface] (seq int16) :=
  ((letb '(magic_1509, seq_number_1510, start_addr_1511, _) : (
          int32 '×
          int32 '×
          int32 '×
          int32
        ) :=
        lift_to_both0 h_1508 in
      letb magic_1512 : u32_word_t :=
        u32_to_be_bytes (lift_to_both0 magic_1509) in
      letb seq_number_1513 : u32_word_t :=
        u32_to_be_bytes (lift_to_both0 seq_number_1510) in
      letb start_addr_1514 : u32_word_t :=
        u32_to_be_bytes (lift_to_both0 start_addr_1511) in
      letb u8_seq_1515 : seq int8 :=
        seq_new_ (default : int8) (lift_to_both0 (usize 12)) in
      letb u8_seq_1516 : seq int8 :=
        seq_update_slice (lift_to_both0 u8_seq_1515) (lift_to_both0 (usize 0)) (
          array_to_seq (lift_to_both0 magic_1512)) (lift_to_both0 (usize 0)) (
          lift_to_both0 (usize 4)) in
      letb u8_seq_1517 : seq int8 :=
        seq_update_slice (lift_to_both0 u8_seq_1516) (lift_to_both0 (usize 4)) (
          array_to_seq (lift_to_both0 seq_number_1513)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 4)) in
      letb u8_seq_1518 : seq int8 :=
        seq_update_slice (lift_to_both0 u8_seq_1517) (lift_to_both0 (usize 8)) (
          array_to_seq (lift_to_both0 start_addr_1514)) (lift_to_both0 (
            usize 0)) (lift_to_both0 (usize 4)) in
      letbm u16_seq_1506 : seq int16 loc( u16_seq_1506_loc ) :=
        seq_new_ (default : int16) (lift_to_both0 (usize 6)) in
      letb u16_seq_1506 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (
              usize 3)) u16_seq_1506 (L := (CEfset ([u16_seq_1506_loc]))) (
            I := [interface]) (fun i_1519 u16_seq_1506 =>
            letb u16_word_1520 : u16_word_t :=
              array_from_seq (2) (seq_slice (lift_to_both0 u8_seq_1518) ((
                    lift_to_both0 i_1519) .* (lift_to_both0 (usize 4))) (
                  lift_to_both0 (usize 2))) in
            letb u16_value_1521 : int16 :=
              u16_from_be_bytes (lift_to_both0 u16_word_1520) in
            letb u16_seq_1506 : seq int16 :=
              seq_upd u16_seq_1506 (((lift_to_both0 (usize 2)) .* (
                    lift_to_both0 i_1519)) .+ (lift_to_both0 (usize 1))) (
                is_pure (lift_to_both0 u16_value_1521)) in
            letb u16_word_1522 : u16_word_t :=
              array_from_seq (2) (seq_slice (lift_to_both0 u8_seq_1518) (((
                      lift_to_both0 i_1519) .* (lift_to_both0 (usize 4))) .+ (
                    lift_to_both0 (usize 2))) (lift_to_both0 (usize 2))) in
            letb u16_value_1523 : int16 :=
              u16_from_be_bytes (lift_to_both0 u16_word_1522) in
            letb u16_seq_1506 : seq int16 :=
              seq_upd u16_seq_1506 ((lift_to_both0 (usize 2)) .* (
                  lift_to_both0 i_1519)) (is_pure (
                  lift_to_both0 u16_value_1523)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 u16_seq_1506)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 u16_seq_1506)
      ) : both (CEfset ([u16_seq_1506_loc])) [interface] (seq int16)).
Fail Next Obligation.

Definition result_1525_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 1526%nat).
Notation "'is_valid_header_inp'" :=(
  header_t : choice_type) (in custom pack_type at level 2).
Notation "'is_valid_header_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition IS_VALID_HEADER : nat :=
  1536.
Program Definition is_valid_header (h_1527 : header_t)
  : both (CEfset (
      [a_1486_loc ; b_1487_loc ; intermediate_a_1488_loc ; intermediate_b_1489_loc ; u16_seq_1506_loc ; result_1525_loc])) [interface] (
    bool_ChoiceEquality) :=
  ((letb '(magic_number_1528, seq_number_1529, start_addr_1530, checksum_1531
        ) : (int32 '× int32 '× int32 '× int32) :=
        lift_to_both0 h_1527 in
      letb slice_1532 : seq int16 :=
        header_as_u16_slice (prod_b(
            lift_to_both0 magic_number_1528,
            lift_to_both0 seq_number_1529,
            lift_to_both0 start_addr_1530,
            lift_to_both0 checksum_1531
          )) in
      letbm result_1525 : bool_ChoiceEquality loc( result_1525_loc ) :=
        lift_to_both0 ((false : bool_ChoiceEquality)) in
      letb '(result_1525) :=
        if (lift_to_both0 magic_number_1528) =.? (
          lift_to_both0 riotboot_magic_v) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [a_1486_loc ; b_1487_loc ; intermediate_a_1488_loc ; intermediate_b_1489_loc ; u16_seq_1506_loc ; result_1525_loc])) (
          L2 := CEfset (
            [a_1486_loc ; b_1487_loc ; intermediate_a_1488_loc ; intermediate_b_1489_loc ; u16_seq_1506_loc ; result_1525_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb fletcher_1533 : (int32 '× int32) := new_fletcher  in
          letb fletcher_1534 : (int32 '× int32) :=
            update_fletcher (lift_to_both0 fletcher_1533) (
              lift_to_both0 slice_1532) in
          letb sum_1535 : int32 := value (lift_to_both0 fletcher_1534) in
          letbm result_1525 loc( result_1525_loc ) :=
            (lift_to_both0 sum_1535) =.? (lift_to_both0 checksum_1531) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 result_1525)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 result_1525)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        lift_to_both0 result_1525)
      ) : both (CEfset (
        [a_1486_loc ; b_1487_loc ; intermediate_a_1488_loc ; intermediate_b_1489_loc ; u16_seq_1506_loc ; result_1525_loc])) [interface] (
      bool_ChoiceEquality)).
Fail Next Obligation.

Definition image_1537_loc : ChoiceEqualityLocation :=
  (int32 ; 1539%nat).
Definition image_found_1538_loc : ChoiceEqualityLocation :=
  (bool_ChoiceEquality ; 1540%nat).
Notation "'choose_image_inp'" :=(
  seq header_t : choice_type) (in custom pack_type at level 2).
Notation "'choose_image_out'" :=((bool_ChoiceEquality '× int32
  ) : choice_type) (in custom pack_type at level 2).
Definition CHOOSE_IMAGE : nat :=
  1549.
Program Definition choose_image (images_1541 : seq header_t)
  : both (CEfset (
      [a_1486_loc ; b_1487_loc ; intermediate_a_1488_loc ; intermediate_b_1489_loc ; u16_seq_1506_loc ; result_1525_loc ; image_1537_loc ; image_found_1538_loc])) [interface] (
    (bool_ChoiceEquality '× int32)) :=
  ((letbm image_1537 : int32 loc( image_1537_loc ) :=
        lift_to_both0 (@repr U32 0) in
      letbm image_found_1538 : bool_ChoiceEquality loc( image_found_1538_loc ) :=
        lift_to_both0 ((false : bool_ChoiceEquality)) in
      letb '(image_1537, image_found_1538) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_len (
              lift_to_both0 images_1541)) prod_ce(image_1537, image_found_1538
          ) (L := (CEfset (
                [a_1486_loc ; b_1487_loc ; intermediate_a_1488_loc ; intermediate_b_1489_loc ; u16_seq_1506_loc ; result_1525_loc ; image_1537_loc ; image_found_1538_loc]))) (
            I := [interface]) (fun i_1542 '(image_1537, image_found_1538) =>
            letb header_1543 : (int32 '× int32 '× int32 '× int32) :=
              seq_index (images_1541) (lift_to_both0 i_1542) in
            letb '(
                magic_number_1544,
                seq_number_1545,
                start_addr_1546,
                checksum_1547
              ) : (int32 '× int32 '× int32 '× int32) :=
              lift_to_both0 header_1543 in
            letb '(image_1537, image_found_1538) :=
              if is_valid_header (prod_b(
                  lift_to_both0 magic_number_1544,
                  lift_to_both0 seq_number_1545,
                  lift_to_both0 start_addr_1546,
                  lift_to_both0 checksum_1547
                )) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [a_1486_loc ; b_1487_loc ; intermediate_a_1488_loc ; intermediate_b_1489_loc ; u16_seq_1506_loc ; result_1525_loc ; image_1537_loc ; image_found_1538_loc])) (
                L2 := CEfset (
                  [a_1486_loc ; b_1487_loc ; intermediate_a_1488_loc ; intermediate_b_1489_loc ; u16_seq_1506_loc ; result_1525_loc ; image_1537_loc ; image_found_1538_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb change_image_1548 : bool_ChoiceEquality :=
                  negb ((lift_to_both0 image_found_1538) && ((
                        lift_to_both0 seq_number_1545) <=.? (
                        lift_to_both0 image_1537))) in
                letb '(image_1537, image_found_1538) :=
                  if lift_to_both0 change_image_1548 :bool_ChoiceEquality
                  then lift_scope (L1 := CEfset (
                      [a_1486_loc ; b_1487_loc ; intermediate_a_1488_loc ; intermediate_b_1489_loc ; u16_seq_1506_loc ; result_1525_loc ; image_1537_loc ; image_found_1538_loc])) (
                    L2 := CEfset (
                      [a_1486_loc ; b_1487_loc ; intermediate_a_1488_loc ; intermediate_b_1489_loc ; u16_seq_1506_loc ; result_1525_loc ; image_1537_loc ; image_found_1538_loc])) (
                    I1 := [interface]) (
                    I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                    letbm image_1537 loc( image_1537_loc ) :=
                      lift_to_both0 start_addr_1546 in
                    letbm image_found_1538 loc( image_found_1538_loc ) :=
                      lift_to_both0 ((true : bool_ChoiceEquality)) in
                    lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                        lift_to_both0 image_1537,
                        lift_to_both0 image_found_1538
                      ))
                    )
                  else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                      lift_to_both0 image_1537,
                      lift_to_both0 image_found_1538
                    ))
                   in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 image_1537,
                    lift_to_both0 image_found_1538
                  ))
                )
              else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                  lift_to_both0 image_1537,
                  lift_to_both0 image_found_1538
                ))
               in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 image_1537,
                lift_to_both0 image_found_1538
              ))
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          lift_to_both0 image_found_1538,
          lift_to_both0 image_1537
        ))
      ) : both (CEfset (
        [a_1486_loc ; b_1487_loc ; intermediate_a_1488_loc ; intermediate_b_1489_loc ; u16_seq_1506_loc ; result_1525_loc ; image_1537_loc ; image_found_1538_loc])) [interface] (
      (bool_ChoiceEquality '× int32))).
Fail Next Obligation.

