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


Definition uint32_bits_v : uint_size :=
  ((usize 4) .* (usize 8)).

Definition n_queues_v : uint_size :=
  usize 20.

Definition n_threads_v : uint_size :=
  usize 30.

Definition sentinel_v : int8 :=
  @repr U8 255.

Definition runqueue_id_t : ChoiceEquality :=
  int8.
Definition RunqueueId (x : int8) : runqueue_id_t :=
   x.

Definition thread_id_t : ChoiceEquality :=
  int8.
Definition ThreadId (x : int8) : thread_id_t :=
   x.

Definition tail_t := nseq (int8) (n_queues_v).

Definition next_ids_t := nseq (int8) (n_threads_v).

Definition clist_t : ChoiceEquality :=
  (tail_t '× next_ids_t).
Definition Clist (x : (tail_t '× next_ids_t)) : clist_t :=
   x.

Definition tail_1550_loc : ChoiceEqualityLocation :=
  (tail_t ; 1552%nat).
Definition next_idxs_1551_loc : ChoiceEqualityLocation :=
  (next_ids_t ; 1553%nat).
Notation "'clist_new_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'clist_new_out'" :=(
  clist_t : choice_type) (in custom pack_type at level 2).
Definition CLIST_NEW : nat :=
  1556.
Program Definition clist_new 
  : both (CEfset ([tail_1550_loc ; next_idxs_1551_loc])) [interface] (
    clist_t) :=
  ((letbm tail_1550 : tail_t loc( tail_1550_loc ) :=
        array_new_ (default : int8) (n_queues_v) in
      letb tail_1550 :=
        foldi_both' (lift_to_both0 (usize 0)) (array_len (
              lift_to_both0 tail_1550)) tail_1550 (L := (CEfset (
                [tail_1550_loc ; next_idxs_1551_loc]))) (I := [interface]) (
            fun i_1554 tail_1550 =>
            letb tail_1550 : tail_t :=
              array_upd tail_1550 (lift_to_both0 i_1554) (is_pure (
                  lift_to_both0 sentinel_v)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 tail_1550)
            ) in
      letbm next_idxs_1551 : next_ids_t loc( next_idxs_1551_loc ) :=
        array_new_ (default : int8) (n_threads_v) in
      letb next_idxs_1551 :=
        foldi_both' (lift_to_both0 (usize 0)) (array_len (
              lift_to_both0 next_idxs_1551)) next_idxs_1551 (L := (CEfset (
                [tail_1550_loc ; next_idxs_1551_loc]))) (I := [interface]) (
            fun i_1555 next_idxs_1551 =>
            letb next_idxs_1551 : next_ids_t :=
              array_upd next_idxs_1551 (lift_to_both0 i_1555) (is_pure (
                  lift_to_both0 sentinel_v)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 next_idxs_1551)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (Clist (prod_b(
            lift_to_both0 tail_1550,
            lift_to_both0 next_idxs_1551
          )))
      ) : both (CEfset ([tail_1550_loc ; next_idxs_1551_loc])) [interface] (
      clist_t)).
Fail Next Obligation.


Notation "'clist_is_empty_inp'" :=(
  clist_t × runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_is_empty_out'" :=(
  bool_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Definition CLIST_IS_EMPTY : nat :=
  1562.
Program Definition clist_is_empty (x_1559 : clist_t) (rq_1557 : runqueue_id_t)
  : both (fset.fset0) [interface] (bool_ChoiceEquality) :=
  ((letb RunqueueId (rq_1558) : runqueue_id_t := lift_to_both0 rq_1557 in
      letb Clist ((tail_1560, next_ids_1561)) : clist_t :=
        lift_to_both0 x_1559 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((array_index (
            tail_1560) ((fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 rq_1558))) =.? (lift_to_both0 sentinel_v))
      ) : both (fset.fset0) [interface] (bool_ChoiceEquality)).
Fail Next Obligation.

Definition next_idxs_1564_loc : ChoiceEqualityLocation :=
  (next_ids_t ; 1565%nat).
Definition tail_1563_loc : ChoiceEqualityLocation :=
  (tail_t ; 1566%nat).
Notation "'clist_push_inp'" :=(
  clist_t × thread_id_t × runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_push_out'" :=(
  clist_t : choice_type) (in custom pack_type at level 2).
Definition CLIST_PUSH : nat :=
  1572.
Program Definition clist_push (x_1571 : clist_t) (n_1569 : thread_id_t) (
    rq_1567 : runqueue_id_t)
  : both (CEfset ([tail_1563_loc ; next_idxs_1564_loc])) [interface] (
    clist_t) :=
  ((letb RunqueueId (rq_1568) : runqueue_id_t := lift_to_both0 rq_1567 in
      letb ThreadId (n_1570) : thread_id_t := lift_to_both0 n_1569 in
      letb Clist ((tail_1563, next_idxs_1564)) : clist_t :=
        lift_to_both0 x_1571 in
      letb '(tail_1563, next_idxs_1564) :=
        if (array_index (next_idxs_1564) (
            (fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 n_1570))) =.? (
          lift_to_both0 sentinel_v) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([tail_1563_loc ; next_idxs_1564_loc])) (
          L2 := CEfset ([tail_1563_loc ; next_idxs_1564_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (letb '(
              tail_1563,
              next_idxs_1564
            ) :=
            if (array_index (tail_1563) (
                (fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 rq_1568))) =.? (
              lift_to_both0 sentinel_v) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset (
                [tail_1563_loc ; next_idxs_1564_loc])) (L2 := CEfset (
                [tail_1563_loc ; next_idxs_1564_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letb tail_1563 : tail_t :=
                array_upd tail_1563 (
                  (fun x => lift_to_both0 (repr (unsigned x)))(
                    lift_to_both0 rq_1568)) (is_pure (lift_to_both0 n_1570)) in
              letb next_idxs_1564 : next_ids_t :=
                array_upd next_idxs_1564 (
                  (fun x => lift_to_both0 (repr (unsigned x)))(
                    lift_to_both0 n_1570)) (is_pure (lift_to_both0 n_1570)) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                  lift_to_both0 tail_1563,
                  lift_to_both0 next_idxs_1564
                ))
              )
            else  lift_scope (L1 := CEfset (
                [tail_1563_loc ; next_idxs_1564_loc])) (L2 := CEfset (
                [tail_1563_loc ; next_idxs_1564_loc])) (I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letb next_idxs_1564 : next_ids_t :=
                array_upd next_idxs_1564 (
                  (fun x => lift_to_both0 (repr (unsigned x)))(
                    lift_to_both0 n_1570)) (is_pure (array_index (
                      next_idxs_1564) (
                      (fun x => lift_to_both0 (repr (unsigned x)))(array_index (
                          tail_1563) (
                          (fun x => lift_to_both0 (repr (unsigned x)))(
                            lift_to_both0 rq_1568)))))) in
              letb next_idxs_1564 : next_ids_t :=
                array_upd next_idxs_1564 (
                  (fun x => lift_to_both0 (repr (unsigned x)))(array_index (
                      tail_1563) ((fun x => lift_to_both0 (repr (unsigned x)))(
                        lift_to_both0 rq_1568)))) (is_pure (
                    lift_to_both0 n_1570)) in
              letb tail_1563 : tail_t :=
                array_upd tail_1563 (
                  (fun x => lift_to_both0 (repr (unsigned x)))(
                    lift_to_both0 rq_1568)) (is_pure (lift_to_both0 n_1570)) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                  lift_to_both0 tail_1563,
                  lift_to_both0 next_idxs_1564
                ))
              ) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 tail_1563,
              lift_to_both0 next_idxs_1564
            ))
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
            lift_to_both0 tail_1563,
            lift_to_both0 next_idxs_1564
          ))
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (Clist (prod_b(
            lift_to_both0 tail_1563,
            lift_to_both0 next_idxs_1564
          )))
      ) : both (CEfset ([tail_1563_loc ; next_idxs_1564_loc])) [interface] (
      clist_t)).
Fail Next Obligation.

Definition out_1575_loc : ChoiceEqualityLocation :=
  ((option (int8)) ; 1576%nat).
Definition tail_1573_loc : ChoiceEqualityLocation :=
  (tail_t ; 1577%nat).
Definition next_idxs_1574_loc : ChoiceEqualityLocation :=
  (next_ids_t ; 1578%nat).
Notation "'clist_pop_head_inp'" :=(
  clist_t × runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_pop_head_out'" :=((clist_t '× (option (int8))
  ) : choice_type) (in custom pack_type at level 2).
Definition CLIST_POP_HEAD : nat :=
  1583.
Program Definition clist_pop_head (x_1581 : clist_t) (rq_1579 : runqueue_id_t)
  : both (CEfset (
      [tail_1573_loc ; next_idxs_1574_loc ; out_1575_loc])) [interface] ((
      clist_t '×
      (option (int8))
    )) :=
  ((letb RunqueueId (rq_1580) : runqueue_id_t := lift_to_both0 rq_1579 in
      letb Clist ((tail_1573, next_idxs_1574)) : clist_t :=
        lift_to_both0 x_1581 in
      letbm out_1575 : (option (int8)) loc( out_1575_loc ) := @None int8 in
      letb '(tail_1573, next_idxs_1574, out_1575) :=
        if (array_index (tail_1573) (
            (fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 rq_1580))) =.? (
          lift_to_both0 sentinel_v) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [tail_1573_loc ; next_idxs_1574_loc ; out_1575_loc])) (
          L2 := CEfset ([tail_1573_loc ; next_idxs_1574_loc ; out_1575_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 tail_1573,
              lift_to_both0 next_idxs_1574,
              lift_to_both0 out_1575
            ))
          )
        else  lift_scope (L1 := CEfset (
            [tail_1573_loc ; next_idxs_1574_loc ; out_1575_loc])) (
          L2 := CEfset ([tail_1573_loc ; next_idxs_1574_loc ; out_1575_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb head_1582 : int8 :=
            array_index (next_idxs_1574) (
              (fun x => lift_to_both0 (repr (unsigned x)))(array_index (
                  tail_1573) ((fun x => lift_to_both0 (repr (unsigned x)))(
                    lift_to_both0 rq_1580)))) in
          letb '(tail_1573, next_idxs_1574) :=
            if (lift_to_both0 head_1582) =.? (array_index (tail_1573) (
                (fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 rq_1580))) :bool_ChoiceEquality
            then lift_scope (L1 := CEfset (
                [tail_1573_loc ; next_idxs_1574_loc ; out_1575_loc])) (
              L2 := CEfset (
                [tail_1573_loc ; next_idxs_1574_loc ; out_1575_loc])) (
              I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letb tail_1573 : tail_t :=
                array_upd tail_1573 (
                  (fun x => lift_to_both0 (repr (unsigned x)))(
                    lift_to_both0 rq_1580)) (is_pure (
                    lift_to_both0 sentinel_v)) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                  lift_to_both0 tail_1573,
                  lift_to_both0 next_idxs_1574
                ))
              )
            else  lift_scope (L1 := CEfset (
                [tail_1573_loc ; next_idxs_1574_loc ; out_1575_loc])) (
              L2 := CEfset (
                [tail_1573_loc ; next_idxs_1574_loc ; out_1575_loc])) (
              I1 := [interface]) (
              I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
              letb next_idxs_1574 : next_ids_t :=
                array_upd next_idxs_1574 (
                  (fun x => lift_to_both0 (repr (unsigned x)))(array_index (
                      tail_1573) ((fun x => lift_to_both0 (repr (unsigned x)))(
                        lift_to_both0 rq_1580)))) (is_pure (array_index (
                      next_idxs_1574) (
                      (fun x => lift_to_both0 (repr (unsigned x)))(
                        lift_to_both0 head_1582)))) in
              lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                  lift_to_both0 tail_1573,
                  lift_to_both0 next_idxs_1574
                ))
              ) in
          letb next_idxs_1574 : next_ids_t :=
            array_upd next_idxs_1574 (
              (fun x => lift_to_both0 (repr (unsigned x)))(
                lift_to_both0 head_1582)) (is_pure (
                lift_to_both0 sentinel_v)) in
          letbm out_1575 loc( out_1575_loc ) :=
            @Some int8 (lift_to_both0 head_1582) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 tail_1573,
              lift_to_both0 next_idxs_1574,
              lift_to_both0 out_1575
            ))
          ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
          Clist (prod_b(lift_to_both0 tail_1573, lift_to_both0 next_idxs_1574)),
          lift_to_both0 out_1575
        ))
      ) : both (CEfset (
        [tail_1573_loc ; next_idxs_1574_loc ; out_1575_loc])) [interface] ((
        clist_t '×
        (option (int8))
      ))).
Fail Next Obligation.


Notation "'clist_peek_head_inp'" :=(
  clist_t × runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_peek_head_out'" :=((option (
      int8)) : choice_type) (in custom pack_type at level 2).
Definition CLIST_PEEK_HEAD : nat :=
  1589.
Program Definition clist_peek_head (x_1586 : clist_t) (rq_1584 : runqueue_id_t)
  : both (fset.fset0) [interface] ((option (int8))) :=
  ((letb RunqueueId (rq_1585) : runqueue_id_t := lift_to_both0 rq_1584 in
      letb Clist ((tail_1587, next_idxs_1588)) : clist_t :=
        lift_to_both0 x_1586 in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
        if is_pure (I := [interface]) ((array_index (tail_1587) (
              (fun x => lift_to_both0 (repr (unsigned x)))(
                lift_to_both0 rq_1585))) =.? (lift_to_both0 sentinel_v))
        then @None int8
        else @Some int8 (array_index (next_idxs_1588) (
            (fun x => lift_to_both0 (repr (unsigned x)))(array_index (
                tail_1587) ((fun x => lift_to_both0 (repr (unsigned x)))(
                  lift_to_both0 rq_1585))))))
      ) : both (fset.fset0) [interface] ((option (int8)))).
Fail Next Obligation.

Definition tail_1590_loc : ChoiceEqualityLocation :=
  (tail_t ; 1591%nat).
Notation "'clist_advance_inp'" :=(
  clist_t × runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'clist_advance_out'" :=(
  clist_t : choice_type) (in custom pack_type at level 2).
Definition CLIST_ADVANCE : nat :=
  1596.
Program Definition clist_advance (x_1594 : clist_t) (rq_1592 : runqueue_id_t)
  : both (CEfset ([tail_1590_loc])) [interface] (clist_t) :=
  ((letb RunqueueId (rq_1593) : runqueue_id_t := lift_to_both0 rq_1592 in
      letb Clist ((tail_1590, next_idxs_1595)) : clist_t :=
        lift_to_both0 x_1594 in
      letb '(tail_1590) :=
        if (array_index (tail_1590) (
            (fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 rq_1593))) !=.? (
          lift_to_both0 sentinel_v) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([tail_1590_loc])) (L2 := CEfset (
            [tail_1590_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb tail_1590 : tail_t :=
            array_upd tail_1590 ((fun x => lift_to_both0 (repr (unsigned x)))(
                lift_to_both0 rq_1593)) (is_pure (array_index (next_idxs_1595) (
                  (fun x => lift_to_both0 (repr (unsigned x)))(array_index (
                      tail_1590) ((fun x => lift_to_both0 (repr (unsigned x)))(
                        lift_to_both0 rq_1593)))))) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 tail_1590)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 tail_1590)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (Clist (prod_b(
            lift_to_both0 tail_1590,
            lift_to_both0 next_idxs_1595
          )))
      ) : both (CEfset ([tail_1590_loc])) [interface] (clist_t)).
Fail Next Obligation.

Definition run_queue_t : ChoiceEquality :=
  (int32 '× clist_t).
Definition RunQueue (x : (int32 '× clist_t)) : run_queue_t :=
   x.


Notation "'runqueue_new_inp'" :=(
  unit_ChoiceEquality : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_new_out'" :=(
  run_queue_t : choice_type) (in custom pack_type at level 2).
Definition RUNQUEUE_NEW : nat :=
  1597.
Program Definition runqueue_new 
  : both (CEfset ([tail_1550_loc ; next_idxs_1551_loc])) [interface] (
    run_queue_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (RunQueue (prod_b(
            lift_to_both0 (@repr U32 0),
            clist_new 
          )))
      ) : both (CEfset ([tail_1550_loc ; next_idxs_1551_loc])) [interface] (
      run_queue_t)).
Fail Next Obligation.

Definition queues_1599_loc : ChoiceEqualityLocation :=
  (clist_t ; 1600%nat).
Definition bitcache_1598_loc : ChoiceEqualityLocation :=
  (int32 ; 1601%nat).
Notation "'runqueue_add_inp'" :=(
  run_queue_t × thread_id_t × runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_add_out'" :=(
  run_queue_t : choice_type) (in custom pack_type at level 2).
Definition RUNQUEUE_ADD : nat :=
  1606.
Program Definition runqueue_add (y_1604 : run_queue_t) (n_1605 : thread_id_t) (
    rq_1602 : runqueue_id_t)
  : both (CEfset (
      [tail_1563_loc ; next_idxs_1564_loc ; bitcache_1598_loc ; queues_1599_loc])) [interface] (
    run_queue_t) :=
  ((letb RunqueueId (rq_u8_1603) : runqueue_id_t := lift_to_both0 rq_1602 in
      letb RunQueue ((bitcache_1598, queues_1599)) : run_queue_t :=
        lift_to_both0 y_1604 in
      letbm bitcache_1598 loc( bitcache_1598_loc ) :=
        (lift_to_both0 bitcache_1598) .| ((lift_to_both0 (
              @repr U32 1)) shift_left (
            (fun x => lift_to_both0 (repr (unsigned x)))(
              lift_to_both0 rq_u8_1603))) in
      letbm queues_1599 loc( queues_1599_loc ) :=
        clist_push (lift_to_both0 queues_1599) (lift_to_both0 n_1605) (
          lift_to_both0 rq_1602) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (RunQueue (prod_b(
            lift_to_both0 bitcache_1598,
            lift_to_both0 queues_1599
          )))
      ) : both (CEfset (
        [tail_1563_loc ; next_idxs_1564_loc ; bitcache_1598_loc ; queues_1599_loc])) [interface] (
      run_queue_t)).
Fail Next Obligation.

Definition bitcache_1607_loc : ChoiceEqualityLocation :=
  (int32 ; 1608%nat).
Notation "'runqueue_del_inp'" :=(
  run_queue_t × thread_id_t × runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_del_out'" :=(
  run_queue_t : choice_type) (in custom pack_type at level 2).
Definition RUNQUEUE_DEL : nat :=
  1615.
Program Definition runqueue_del (y_1611 : run_queue_t) (n_1616 : thread_id_t) (
    rq_1609 : runqueue_id_t)
  : both (CEfset (
      [tail_1573_loc ; next_idxs_1574_loc ; out_1575_loc ; bitcache_1607_loc])) [interface] (
    run_queue_t) :=
  ((letb RunqueueId (rq_u8_1610) : runqueue_id_t := lift_to_both0 rq_1609 in
      letb RunQueue ((bitcache_1607, queues_1612)) : run_queue_t :=
        lift_to_both0 y_1611 in
      letb '(queues_1613, popped_1614) : (clist_t '× (option (int8))) :=
        clist_pop_head (lift_to_both0 queues_1612) (lift_to_both0 rq_1609) in
      letb '(bitcache_1607) :=
        if clist_is_empty (lift_to_both0 queues_1613) (
          lift_to_both0 rq_1609) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [tail_1573_loc ; next_idxs_1574_loc ; out_1575_loc ; bitcache_1607_loc])) (
          L2 := CEfset (
            [tail_1573_loc ; next_idxs_1574_loc ; out_1575_loc ; bitcache_1607_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm bitcache_1607 loc( bitcache_1607_loc ) :=
            (lift_to_both0 bitcache_1607) .& (not ((lift_to_both0 (
                    @repr U32 1)) shift_left (
                  (fun x => lift_to_both0 (repr (unsigned x)))(
                    lift_to_both0 rq_u8_1610)))) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 bitcache_1607)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 bitcache_1607)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (RunQueue (prod_b(
            lift_to_both0 bitcache_1607,
            lift_to_both0 queues_1613
          )))
      ) : both (CEfset (
        [tail_1573_loc ; next_idxs_1574_loc ; out_1575_loc ; bitcache_1607_loc])) [interface] (
      run_queue_t)).
Fail Next Obligation.


Notation "'runqueue_ffs_inp'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_ffs_out'" :=(
  int32 : choice_type) (in custom pack_type at level 2).
Definition RUNQUEUE_FFS : nat :=
  1618.
Program Definition runqueue_ffs (val_1617 : int32)
  : both (fset.fset0) [interface] (int32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) ((pub_u32 (is_pure (
              lift_to_both0 uint32_bits_v))) .- (pub_uint32_leading_zeros (
            lift_to_both0 val_1617)))
      ) : both (fset.fset0) [interface] (int32)).
Fail Next Obligation.

Definition out_1619_loc : ChoiceEqualityLocation :=
  ((option (int8)) ; 1620%nat).
Notation "'runqueue_get_next_inp'" :=(
  run_queue_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_get_next_out'" :=((option (
      int8)) : choice_type) (in custom pack_type at level 2).
Definition RUNQUEUE_GET_NEXT : nat :=
  1626.
Program Definition runqueue_get_next (y_1621 : run_queue_t)
  : both (CEfset ([out_1619_loc])) [interface] ((option (int8))) :=
  ((letb RunQueue ((bitcache_1622, queues_1623)) : run_queue_t :=
        lift_to_both0 y_1621 in
      letb rq_ffs_1624 : int32 :=
        runqueue_ffs ((lift_to_both0 bitcache_1622)) in
      letbm out_1619 : (option (int8)) loc( out_1619_loc ) := @None int8 in
      letb '(out_1619) :=
        if (lift_to_both0 rq_ffs_1624) >.? (lift_to_both0 (
            @repr U32 0)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([out_1619_loc])) (L2 := CEfset (
            [out_1619_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letb rq_1625 : runqueue_id_t :=
            RunqueueId ((fun x => lift_to_both0 (repr (unsigned x)))((
                  lift_to_both0 rq_ffs_1624) .- (lift_to_both0 (
                    @repr U32 1)))) in
          letbm out_1619 loc( out_1619_loc ) :=
            clist_peek_head (lift_to_both0 queues_1623) (
              lift_to_both0 rq_1625) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 out_1619)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 out_1619)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 out_1619)
      ) : both (CEfset ([out_1619_loc])) [interface] ((option (int8)))).
Fail Next Obligation.

Definition queues_1627_loc : ChoiceEqualityLocation :=
  (clist_t ; 1628%nat).
Notation "'runqueue_advance_inp'" :=(
  run_queue_t × runqueue_id_t : choice_type) (in custom pack_type at level 2).
Notation "'runqueue_advance_out'" :=(
  run_queue_t : choice_type) (in custom pack_type at level 2).
Definition RUNQUEUE_ADVANCE : nat :=
  1632.
Program Definition runqueue_advance (y_1629 : run_queue_t) (
    rq_1631 : runqueue_id_t)
  : both (CEfset ([tail_1590_loc ; queues_1627_loc])) [interface] (
    run_queue_t) :=
  ((letb RunQueue ((bitcache_1630, queues_1627)) : run_queue_t :=
        lift_to_both0 y_1629 in
      letbm queues_1627 loc( queues_1627_loc ) :=
        clist_advance (lift_to_both0 queues_1627) (lift_to_both0 rq_1631) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (RunQueue (prod_b(
            lift_to_both0 bitcache_1630,
            lift_to_both0 queues_1627
          )))
      ) : both (CEfset ([tail_1590_loc ; queues_1627_loc])) [interface] (
      run_queue_t)).
Fail Next Obligation.

