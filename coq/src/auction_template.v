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
| Sold : (user_address) -> auction_state.

Notation "'seq_map'" := ((public_byte_seq × public_byte_seq)) : hacspec_scope.

Notation "'state'" := ((auction_state × int64 × seq int8 × int64 × seq_map
)) : hacspec_scope.

Definition fresh_state (itm_0 : seq int8) (exp_1 : int64) : state :=
  (
    NotSoldYet,
    repr 0,
    itm_0,
    exp_1,
    (seq_new_ (repr 0) (usize 0), seq_new_ (repr 0) (usize 0))
  ).

Inductive bid_error :=
| ContractSender : bid_error
| BidTooLow : bid_error
| BidsOverWaitingForAuctionFinalization : bid_error
| AuctionFinalized : bid_error.

Notation "'user_address_set'" := ((option user_address)) : hacspec_scope.

Notation "'context'" := ((int64 × user_address_set)) : hacspec_scope.

Notation "'finalize_context'" := ((int64 × user_address × int64
)) : hacspec_scope.

Inductive map_entry := | Entry : (int64 × seq_map) -> map_entry.

Definition seq_map_entry
  (m_2 : seq_map)
  (sender_address_3 : user_address)
  : map_entry :=
  let '(m1_4, m2_5) :=
    tuple_clone (m_2) in 
  let res_6 :=
    Entry (
      (
        repr 0,
        (
          seq_concat (seq_clone (m1_4)) (sender_address_3),
          seq_concat (seq_clone (m2_5)) (u64_to_be_bytes (repr 0))
        )
      )) in 
  let res_6 :=
    foldi (usize 0) (
        (seq_len (seq_clone (m1_4))) / (usize 32)) (fun x_7 res_6 =>
      let '(res_6) :=
        if (
          array_from_seq (32) (
            seq_slice (seq_clone (m1_4)) ((x_7) * (usize 32)) (
              usize 32))) array_eq (sender_address_3):bool then (
          let res_6 :=
            Entry (
              (
                u64_from_be_bytes (
                  array_from_seq (8) (
                    seq_slice (m2_5) ((x_7) * (usize 8)) (usize 8))),
                tuple_clone (m_2)
              )) in 
          (res_6)
        ) else ( (res_6)
        ) in 
      (res_6))
    res_6 in 
  res_6.

Inductive map_update := | Update : (int64 × seq_map) -> map_update.

Definition seq_map_update_entry
  (m_8 : seq_map)
  (sender_address_9 : user_address)
  (amount_10 : int64)
  : map_update :=
  let '(m1_11, m2_12) :=
    m_8 in 
  let res_13 :=
    Update (
      (
        amount_10,
        (
          seq_concat (m1_11) (sender_address_9),
          seq_concat (m2_12) (u64_to_be_bytes (amount_10))
        )
      )) in 
  let res_13 :=
    foldi (usize 0) (
        (seq_len (seq_clone (m1_11))) / (usize 32)) (fun x_14 res_13 =>
      let '(res_13) :=
        if (
          array_from_seq (32) (
            seq_slice (seq_clone (m1_11)) ((x_14) * (usize 32)) (
              usize 32))) array_eq (sender_address_9):bool then (
          let res_13 :=
            Update (
              (
                amount_10,
                (
                  seq_update (seq_clone (m1_11)) ((x_14) * (usize 32)) (
                    sender_address_9),
                  seq_update (seq_clone (m2_12)) ((x_14) * (usize 8)) (
                    u64_to_be_bytes (amount_10))
                )
              )) in 
          (res_13)
        ) else ( (res_13)
        ) in 
      (res_13))
    res_13 in 
  res_13.

Notation "'auction_bid_result'" := ((result () bid_error)) : hacspec_scope.

Inductive bool := | True : bool | False : bool.

Definition auction_bid
  (ctx_15 : context)
  (amount_16 : int64)
  (state_17 : state)
  : (state × auction_bid_result) :=
  let '(auction_state_18, b_19, c_20, expiry_21, e_22) :=
    state_17 in 
  let '(slot_time_23, sender_24) :=
    ctx_15 in 
  let '(
      (acs_25, upb_26, ce_27, expirye_28, (updated1_mape_29, updated2_mape_30)),
      rese_31
    ) :=
    match auction_state_18 with
    | NotSoldYet => match if ((slot_time_23) <=.? (expiry_21)):bool then (
      True) else (False) with
    | True => match sender_24 with
    | None(option) => (
      (auction_state_18, b_19, c_20, expiry_21, e_22),
      Err(result) ((ContractSender))
    )
    | Some(option) sender_address_32 => match seq_map_entry (
      tuple_clone (e_22)) (sender_address_32) with
    | Entry (bid_to_update_33, new_map_34) => match seq_map_update_entry (
      tuple_clone (new_map_34)) (sender_address_32) (
      (bid_to_update_33) .+ (amount_16)) with
    | Update (updated_bid_35, updated_map_36) => match if (
      (updated_bid_35) >.? (b_19)):bool then (True) else (False) with
    | True => (
      (auction_state_18, updated_bid_35, c_20, expiry_21, updated_map_36),
      Ok(result) ((()))
    )
    | False => (
      (auction_state_18, b_19, c_20, expiry_21, updated_map_36),
      Err(result) ((BidTooLow))
    ) end end end end
    | False => (
      (auction_state_18, b_19, c_20, expiry_21, e_22),
      Err(result) ((BidsOverWaitingForAuctionFinalization))
    ) end
    | Sold _ => (
      (auction_state_18, b_19, c_20, expiry_21, e_22),
      Err(result) ((AuctionFinalized))
    ) end in 
  (
    (acs_25, upb_26, ce_27, expirye_28, (updated1_mape_29, updated2_mape_30)),
    rese_31
  ).

Inductive finalize_error :=
| BidMapError : finalize_error
| AuctionStillActive : finalize_error
| AuctionFinalized : finalize_error.

Inductive finalize_action :=
| Accept : finalize_action
| SimpleTransfer : (user_address × int64 × public_byte_seq
) -> finalize_action.

Inductive bid_remain :=
| None : bid_remain
| Some : (int64 × ()) -> bid_remain.

Notation "'auction_finalize_result'" := ((
  result finalize_action finalize_error)) : hacspec_scope.

Definition auction_finalize
  (ctx_37 : finalize_context)
  (state_38 : state)
  : (state × auction_finalize_result) :=
  let '(auction_state_39, b_40, c_41, expiry_42, (m1_43, m2_44)) :=
    state_38 in 
  let '(slot_time_45, owner_46, balance_47) :=
    ctx_37 in 
  let '(continues_48, return_action_49) :=
    match auction_state_39 with
    | NotSoldYet => if ((slot_time_45) >.? (expiry_42)):bool then (
      if ((balance_47) =.? (repr 0)):bool then (
        (false, Ok(result) ((Accept)))) else (
        (
          true,
          Ok(result) (
            (SimpleTransfer ((owner_46, b_40, seq_new_ (repr 0) (usize 0)))))
        ))) else ((false, Err(result) ((AuctionStillActive))))
    | Sold _ => (false, Err(result) ((AuctionFinalized))) end in 
  let remaining_bid_50 :=
    None in 
  let '(auction_state_39, return_action_49, remaining_bid_50) :=
    if continues_48:bool then (
      let '(auction_state_39, return_action_49, remaining_bid_50) :=
        foldi (usize 0) (
            (seq_len (seq_clone (m1_43))) / (usize 32)) (fun x_51 '(
            auction_state_39,
            return_action_49,
            remaining_bid_50
          ) =>
          let amnt_52 :=
            u64_from_be_bytes (
              array_from_seq (8) (
                seq_slice (m2_44) ((x_51) * (usize 8)) (usize 8))) in 
          let addr_53 :=
            array_from_seq (32) (
              seq_slice (seq_clone (m1_43)) ((x_51) * (usize 32)) (
                usize 32)) in 
          let '(auction_state_39, return_action_49, remaining_bid_50) :=
            if (amnt_52) <.? (b_40):bool then (
              let return_action_49 :=
                match return_action_49 with
                | Ok(result) a_54 => match a_54 with
                | SimpleTransfer (o_55, b_56, a_57) => Ok(result) (
                  (
                    SimpleTransfer (
                      (
                        o_55,
                        b_56,
                        seq_concat (seq_concat (a_57) (addr_53)) (
                          u64_to_be_bytes (amnt_52))
                      ))
                  ))
                | Accept => Ok(result) ((Accept)) end
                | Err(result) e_58 => Err(result) ((e_58)) end in 
              (auction_state_39, return_action_49, remaining_bid_50)
            ) else (
              let '(auction_state_39, return_action_49, remaining_bid_50) :=
                if match remaining_bid_50 with
                | None => true
                | Some (_, _) => false end:bool then (
                  let auction_state_39 :=
                    Sold ((addr_53)) in 
                  let remaining_bid_50 :=
                    Some ((amnt_52, ())) in 
                  (auction_state_39, return_action_49, remaining_bid_50)
                ) else (
                  let return_action_49 :=
                    Err(result) ((BidMapError)) in 
                  (auction_state_39, return_action_49, remaining_bid_50)
                ) in 
              (auction_state_39, return_action_49, remaining_bid_50)
            ) in 
          (auction_state_39, return_action_49, remaining_bid_50))
        (auction_state_39, return_action_49, remaining_bid_50) in 
      (auction_state_39, return_action_49, remaining_bid_50)
    ) else ( (auction_state_39, return_action_49, remaining_bid_50)
    ) in 
  let '(return_action_49) :=
    if continues_48:bool then (
      let return_action_49 :=
        match remaining_bid_50 with
        | Some (amount_59, _) => match if ((amount_59) =.? (b_40)):bool then (
          True) else (False) with
        | True => return_action_49
        | False => Err(result) ((BidMapError)) end
        | None => Err(result) ((BidMapError)) end in 
      (return_action_49)
    ) else ( (return_action_49)
    ) in 
  ((auction_state_39, b_40, c_41, expiry_42, (m1_43, m2_44)), return_action_49).

