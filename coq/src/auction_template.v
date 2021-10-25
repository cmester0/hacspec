(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Definition user_address := nseq (int8) (usize 32).

Inductive auction_state :=
| NotSoldYet : auction_state
| Sold : user_address -> auction_state.

Definition eqb_auction_state (x y : auction_state) : bool := match x with
   | NotSoldYet => match y with | NotSoldYet=> true | _ => false end
   | Sold a => match y with | Sold b => a =.? b | _ => false end
   end.

Definition eqb_leibniz_auction_state (x y : auction_state) : eqb_auction_state x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Instance eq_dec_auction_state : EqDec (auction_state) :=
Build_EqDec (auction_state) (eqb_auction_state) (eqb_leibniz_auction_state).


Inductive seq_map :=
| SeqMap : (public_byte_seq × public_byte_seq) -> seq_map.

Definition eqb_seq_map (x y : seq_map) : bool := match x with
   | SeqMap a => match y with | SeqMap b => a =.? b end
   end.

Definition eqb_leibniz_seq_map (x y : seq_map) : eqb_seq_map x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Instance eq_dec_seq_map : EqDec (seq_map) :=
Build_EqDec (seq_map) (eqb_seq_map) (eqb_leibniz_seq_map).


Notation "'amount'" := (int64) : hacspec_scope.

Notation "'timestamp'" := (int64) : hacspec_scope.

Inductive state :=
| State : (auction_state × int64 × seq int8 × int64 × seq_map) -> state.

Definition eqb_state (x y : state) : bool := match x with
   | State a => match y with | State b => a =.? b end
   end.

Definition eqb_leibniz_state (x y : state) : eqb_state x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Instance eq_dec_state : EqDec (state) :=
Build_EqDec (state) (eqb_state) (eqb_leibniz_state).


Definition fresh_state (itm_0 : seq int8) (exp_1 : int64) : state :=
  State (
    (
      NotSoldYet,
      repr 0,
      itm_0,
      exp_1,
      SeqMap ((seq_new_ (repr 0) (usize 0), seq_new_ (repr 0) (usize 0)))
    )).

Inductive map_entry :=
| Entry : (int64 × seq_map) -> map_entry.

Definition eqb_map_entry (x y : map_entry) : bool := match x with
   | Entry a => match y with | Entry b => a =.? b end
   end.

Definition eqb_leibniz_map_entry (x y : map_entry) : eqb_map_entry x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Instance eq_dec_map_entry : EqDec (map_entry) :=
Build_EqDec (map_entry) (eqb_map_entry) (eqb_leibniz_map_entry).


Definition seq_map_entry
  (m_2 : seq_map)
  (sender_address_3 : user_address)
  : map_entry :=
  match  (m_2) with SeqMap ((m0_4, m1_5)) => 
  match 
    Entry (
      (
        repr 0,
        SeqMap (
          (
            seq_concat ((m0_4)) (sender_address_3),
            seq_concat ((m1_5)) (u64_to_be_bytes (repr 0))
          ))
      )) with res_6 => 
  let res_6 :=
    foldi (usize 0) ((seq_len ((m0_4))) / (usize 32)) (fun x_7 res_6 =>
      let '(res_6) :=
        if (
          array_from_seq (32) (
            seq_slice ((m0_4)) ((x_7) * (usize 32)) (usize 32))) array_eq (
          sender_address_3):bool then (
          let res_6 :=
            Entry (
              (
                u64_from_be_bytes (
                  array_from_seq (8) (
                    seq_slice (m1_5) ((x_7) * (usize 8)) (usize 8))),
                (m_2)
              )) in 
          (res_6)
        ) else ( (res_6)
        ) in 
      (res_6))
    res_6 in 
  res_6 end end.

Inductive map_update :=
| Update : (int64 × seq_map) -> map_update.

Definition eqb_map_update (x y : map_update) : bool := match x with
   | Update a => match y with | Update b => a =.? b end
   end.

Definition eqb_leibniz_map_update (x y : map_update) : eqb_map_update x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Instance eq_dec_map_update : EqDec (map_update) :=
Build_EqDec (map_update) (eqb_map_update) (eqb_leibniz_map_update).


Definition seq_map_update_entry
  (m_8 : seq_map)
  (sender_address_9 : user_address)
  (amount_10 : int64)
  : map_update :=
  match  (m_8) with SeqMap ((m0_11, m1_12)) => 
  match 
    Update (
      (
        amount_10,
        SeqMap (
          (
            seq_concat (m0_11) (sender_address_9),
            seq_concat (m1_12) (u64_to_be_bytes (amount_10))
          ))
      )) with res_13 => 
  let res_13 :=
    foldi (usize 0) ((seq_len ((m0_11))) / (usize 32)) (fun x_14 res_13 =>
      let '(res_13) :=
        if (
          array_from_seq (32) (
            seq_slice ((m0_11)) ((x_14) * (usize 32)) (usize 32))) array_eq (
          sender_address_9):bool then (
          let res_13 :=
            Update (
              (
                amount_10,
                SeqMap (
                  (
                    seq_update ((m0_11)) ((x_14) * (usize 32)) (
                      sender_address_9),
                    seq_update ((m1_12)) ((x_14) * (usize 8)) (
                      u64_to_be_bytes (amount_10))
                  ))
              )) in 
          (res_13)
        ) else ( (res_13)
        ) in 
      (res_13))
    res_13 in 
  res_13 end end.

Inductive bid_error :=
| ContractSender : bid_error
| BidTooLow : bid_error
| BidsOverWaitingForAuctionFinalization : bid_error
| AuctionIsFinalized : bid_error.

Definition eqb_bid_error (x y : bid_error) : bool := match x with
   | ContractSender => match y with | ContractSender=> true | _ => false end
   | BidTooLow => match y with | BidTooLow=> true | _ => false end
   | BidsOverWaitingForAuctionFinalization =>
       match y with
       | BidsOverWaitingForAuctionFinalization=> true
       | _ => false
       end
   | AuctionIsFinalized =>
       match y with
       | AuctionIsFinalized=> true
       | _ => false
       end
   end.

Definition eqb_leibniz_bid_error (x y : bid_error) : eqb_bid_error x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Instance eq_dec_bid_error : EqDec (bid_error) :=
Build_EqDec (bid_error) (eqb_bid_error) (eqb_leibniz_bid_error).


Inductive user_address_set :=
| UserAddressSome : (user_address × unit) -> user_address_set
| UserAddressNone : user_address_set.

Definition eqb_user_address_set (x y : user_address_set) : bool := match x with
   | UserAddressSome a =>
       match y with
       | UserAddressSome b => a =.? b
       | _ => false
       end
   | UserAddressNone => match y with | UserAddressNone=> true | _ => false end
   end.

Definition eqb_leibniz_user_address_set (x y : user_address_set) : eqb_user_address_set x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Instance eq_dec_user_address_set : EqDec (user_address_set) :=
Build_EqDec (user_address_set) (eqb_user_address_set) (eqb_leibniz_user_address_set).


Notation "'context'" := ((int64 × user_address_set)) : hacspec_scope.

Notation "'auction_bid_result'" := ((result unit bid_error)) : hacspec_scope.

Inductive boolean :=
| True : boolean
| False : boolean.

Definition eqb_boolean (x y : boolean) : bool := match x with
   | True => match y with | True=> true | _ => false end
   | False => match y with | False=> true | _ => false end
   end.

Definition eqb_leibniz_boolean (x y : boolean) : eqb_boolean x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Instance eq_dec_boolean : EqDec (boolean) :=
Build_EqDec (boolean) (eqb_boolean) (eqb_leibniz_boolean).


Definition auction_bid
  (ctx_15 : context)
  (amount_16 : int64)
  (state_17 : state)
  : (state × auction_bid_result) :=
  let '(slot_time_18, sender_19) :=
    ctx_15 in 
  match  (state_17) with State ((st0_20, st1_21, st2_22, st3_23, st4_24)) => 
  let '(new_state_25, rese_26) :=
    match st0_20 with
    | NotSoldYet => match (if ((slot_time_18) <=.? (st3_23)):bool then (
      True) else (False)) with
    | True => match sender_19 with
    | UserAddressNone => (state_17, Err (ContractSender))
    | UserAddressSome (sender_address_27, _) => match seq_map_entry ((st4_24)) (
      sender_address_27) with
    | Entry (bid_to_update_28, new_map_29) => match seq_map_update_entry (
      (new_map_29)) (sender_address_27) ((bid_to_update_28) .+ (amount_16)) with
    | Update (updated_bid_30, updated_map_31) => match (if (
      (updated_bid_30) >.? (st1_21)):bool then (True) else (False)) with
    | True => (
      State ((st0_20, updated_bid_30, st2_22, st3_23, updated_map_31)),
      Ok (tt)
    )
    | False => (
      State ((st0_20, st1_21, st2_22, st3_23, updated_map_31)),
      Err (BidTooLow)
    ) end end end end
    | False => (state_17, Err (BidsOverWaitingForAuctionFinalization)) end
    | Sold _ => (state_17, Err (AuctionIsFinalized)) end in 
  (new_state_25, rese_26) end.

Notation "'finalize_context'" := ((int64 × user_address × int64
)) : hacspec_scope.

Inductive finalize_error :=
| BidMapError : finalize_error
| AuctionStillActive : finalize_error
| AuctionFinalized : finalize_error.

Definition eqb_finalize_error (x y : finalize_error) : bool := match x with
   | BidMapError => match y with | BidMapError=> true | _ => false end
   | AuctionStillActive =>
       match y with
       | AuctionStillActive=> true
       | _ => false
       end
   | AuctionFinalized => match y with | AuctionFinalized=> true | _ => false end
   end.

Definition eqb_leibniz_finalize_error (x y : finalize_error) : eqb_finalize_error x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Instance eq_dec_finalize_error : EqDec (finalize_error) :=
Build_EqDec (finalize_error) (eqb_finalize_error) (eqb_leibniz_finalize_error).


Inductive finalize_action :=
| Accept : finalize_action
| SimpleTransfer : (user_address × int64 × public_byte_seq
) -> finalize_action.

Definition eqb_finalize_action (x y : finalize_action) : bool := match x with
   | Accept => match y with | Accept=> true | _ => false end
   | SimpleTransfer a =>
       match y with
       | SimpleTransfer b => a =.? b
       | _ => false
       end
   end.

Definition eqb_leibniz_finalize_action (x y : finalize_action) : eqb_finalize_action x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Instance eq_dec_finalize_action : EqDec (finalize_action) :=
Build_EqDec (finalize_action) (eqb_finalize_action) (eqb_leibniz_finalize_action).


Inductive bid_remain :=
| None : bid_remain
| Some : (int64 × unit) -> bid_remain.

Definition eqb_bid_remain (x y : bid_remain) : bool := match x with
   | None => match y with | None=> true | _ => false end
   | Some a => match y with | Some b => a =.? b | _ => false end
   end.

Definition eqb_leibniz_bid_remain (x y : bid_remain) : eqb_bid_remain x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Instance eq_dec_bid_remain : EqDec (bid_remain) :=
Build_EqDec (bid_remain) (eqb_bid_remain) (eqb_leibniz_bid_remain).


Notation "'auction_finalize_result'" := ((
  result finalize_action finalize_error)) : hacspec_scope.

Definition auction_finalize
  (ctx_32 : finalize_context)
  (state_33 : state)
  : (state × auction_finalize_result) :=
  match  (state_33) with State ((st0_34, st1_35, st2_36, st3_37, st4_38)) => 
  let '(slot_time_39, owner_40, balance_41) :=
    ctx_32 in 
  let '(continues_42, return_action_43) :=
    match st0_34 with
    | NotSoldYet => (if ((slot_time_39) >.? (st3_37)):bool then (
      (if ((balance_41) =.? (repr 0)):bool then ((false, Ok (Accept))) else (
        (
          true,
          Ok (SimpleTransfer ((owner_40, st1_35, seq_new_ (repr 0) (usize 0))))
        )))) else ((false, Err (AuctionStillActive))))
    | Sold _ => (false, Err (AuctionFinalized)) end in 
  match  None with remaining_bid_44 => 
  match  (st4_38) with SeqMap ((m0_45, m1_46)) => 
  let '(st0_34, return_action_43, remaining_bid_44) :=
    if continues_42:bool then (
      let '(st0_34, return_action_43, remaining_bid_44) :=
        foldi (usize 0) ((seq_len ((m0_45))) / (usize 32)) (fun x_47 '(
            st0_34,
            return_action_43,
            remaining_bid_44
          ) =>
          match 
            u64_from_be_bytes (
              array_from_seq (8) (
                seq_slice (m1_46) ((x_47) * (usize 8)) (
                  usize 8))) with amnt_48 => 
          match 
            array_from_seq (32) (
              seq_slice ((m0_45)) ((x_47) * (usize 32)) (
                usize 32)) with addr_49 => 
          let '(st0_34, return_action_43, remaining_bid_44) :=
            if (amnt_48) <.? (st1_35):bool then (
              let return_action_43 :=
                match return_action_43 with
                | Ok a_50 => match a_50 with
                | SimpleTransfer (o_51, b_52, a_53) => Ok (
                  SimpleTransfer (
                    (
                      o_51,
                      b_52,
                      seq_concat (seq_concat (a_53) (addr_49)) (
                        u64_to_be_bytes (amnt_48))
                    )))
                | Accept => Ok (Accept) end
                | Err e_54 => Err (e_54) end in 
              (st0_34, return_action_43, remaining_bid_44)
            ) else (
              let '(st0_34, return_action_43, remaining_bid_44) :=
                if match remaining_bid_44 with
                | None => true
                | Some (_, _) => false end:bool then (
                  let st0_34 :=
                    Sold (addr_49) in 
                  let remaining_bid_44 :=
                    Some ((amnt_48, tt)) in 
                  (st0_34, return_action_43, remaining_bid_44)
                ) else (
                  let return_action_43 :=
                    Err (BidMapError) in 
                  (st0_34, return_action_43, remaining_bid_44)
                ) in 
              (st0_34, return_action_43, remaining_bid_44)
            ) in 
          (st0_34, return_action_43, remaining_bid_44) end end)
        (st0_34, return_action_43, remaining_bid_44) in 
      (st0_34, return_action_43, remaining_bid_44)
    ) else ( (st0_34, return_action_43, remaining_bid_44)
    ) in 
  let '(return_action_43) :=
    if continues_42:bool then (
      let return_action_43 :=
        match remaining_bid_44 with
        | Some (amount_55, _) => match (if (
          (amount_55) =.? (st1_35)):bool then (True) else (False)) with
        | True => return_action_43
        | False => Err (BidMapError) end
        | None => Err (BidMapError) end in 
      (return_action_43)
    ) else ( (return_action_43)
    ) in 
  (State ((st0_34, st1_35, st2_36, st3_37, st4_38)), return_action_43
  ) end end end.

Definition auction_test_init  : bool :=
  match  seq_new_ (repr 0) (usize 0) with item_56 => 
  match  repr 100 with time_57 => 
  (fresh_state ((item_56)) (time_57)) =.? (
    State (
      (
        NotSoldYet,
        repr 0,
        (item_56),
        time_57,
        SeqMap ((seq_new_ (repr 0) (usize 0), seq_new_ (repr 0) (usize 0)))
      ))) end end.

Theorem auction_test_init_correct : auction_test_init = true.
Proof. Admitted.


Definition verify_bid
  (state_58 : state)
  (account_59 : user_address)
  (ctx_60 : context)
  (amount_61 : int64)
  (bid_map_62 : seq_map)
  (highest_bid_63 : int64)
  : (state × bool) :=
  match  seq_new_ (repr 0) (usize 0) with item_64 => 
  match  repr 100 with time_65 => 
  let '(State ((auc_st_66, hb_67, its_68, tm_69, bm_70)), res_71) :=
    auction_bid (ctx_60) (amount_61) (state_58) in 
  match 
    match seq_map_update_entry ((bid_map_62)) (account_59) (highest_bid_63) with
    | Update (_, updated_map_73) => updated_map_73 end with bid_map_72 => 
  (
    State ((auc_st_66, hb_67, (its_68), tm_69, (bm_70))),
    (State ((auc_st_66, hb_67, (its_68), tm_69, (bm_70)))) =.? (
      State ((NotSoldYet, highest_bid_63, (item_64), time_65, (bid_map_72))))
  ) end end end.

Definition test_auction_bid_and_finalize  : bool :=
  match  seq_new_ (repr 0) (usize 0) with item_74 => 
  match  repr 100 with time_75 => 
  match  repr 100 with amount_76 => 
  match 
    SeqMap (
      (seq_new_ (repr 0) (usize 0), seq_new_ (repr 0) (usize 0)
      )) with bid_map_77 => 
  match  fresh_state ((item_74)) (time_75) with state_78 => 
  match 
    array_from_list int8 (
      let l :=
        [
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0;
          repr 0
        ] in  l) with alice_79 => 
  match  (repr 1, UserAddressSome ((alice_79, tt))) with alice_ctx_80 => 
  let '(state_81, result_0_82) :=
    verify_bid (state_78) (alice_79) (alice_ctx_80) (amount_76) ((bid_map_77)) (
      amount_76) in 
  result_0_82 end end end end end end end.

Theorem test_auction_bid_and_finalize_correct : test_auction_bid_and_finalize = true.
Proof. Admitted.


