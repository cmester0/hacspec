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

Definition eqb_auction_state (x y : auction_state) : bool := match x with
   | NotSoldYet => match y with | NotSoldYet=> true | _ => false end
   | Sold a => match y with | Sold b => a =.? b | _ => false end
   end.

Definition eqb_leibniz_auction_state (x y : auction_state) : eqb_auction_state x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Instance eq_dec_auction_state : EqDec (auction_state) :=
Build_EqDec (auction_state) (eqb_auction_state) (eqb_leibniz_auction_state).


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

Notation "'finalize_context'" := ((int64 × user_address × int64
)) : hacspec_scope.

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
  let '(auction_state_18, b_19, c_20, expiry_21, e_22) :=
    state_17 in 
  let '(slot_time_23, sender_24) :=
    ctx_15 in 
  let '(
      (acs_25, upb_26, ce_27, expirye_28, (updated1_mape_29, updated2_mape_30)),
      rese_31
    ) :=
    match auction_state_18 with
    | NotSoldYet => match (if ((slot_time_23) <=.? (expiry_21)):bool then (
      True) else (False)) with
    | True => match sender_24 with
    | UserAddressNone => (
      (auction_state_18, b_19, c_20, expiry_21, e_22),
      Err ((ContractSender))
    )
    | UserAddressSome (sender_address_32, _) => match seq_map_entry (
      tuple_clone (e_22)) (sender_address_32) with
    | Entry (bid_to_update_33, new_map_34) => match seq_map_update_entry (
      tuple_clone (new_map_34)) (sender_address_32) (
      (bid_to_update_33) .+ (amount_16)) with
    | Update (updated_bid_35, updated_map_36) => match (if (
      (updated_bid_35) >.? (b_19)):bool then (True) else (False)) with
    | True => (
      (auction_state_18, updated_bid_35, c_20, expiry_21, updated_map_36),
      Ok ((tt))
    )
    | False => (
      (auction_state_18, b_19, c_20, expiry_21, updated_map_36),
      Err ((BidTooLow))
    ) end end end end
    | False => (
      (auction_state_18, b_19, c_20, expiry_21, e_22),
      Err ((BidsOverWaitingForAuctionFinalization))
    ) end
    | Sold _ => (
      (auction_state_18, b_19, c_20, expiry_21, e_22),
      Err ((AuctionIsFinalized))
    ) end in 
  (
    (acs_25, upb_26, ce_27, expirye_28, (updated1_mape_29, updated2_mape_30)),
    rese_31
  ).

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
  (ctx_37 : finalize_context)
  (state_38 : state)
  : (state × auction_finalize_result) :=
  let '(auction_state_39, b_40, c_41, expiry_42, (m1_43, m2_44)) :=
    state_38 in 
  let '(slot_time_45, owner_46, balance_47) :=
    ctx_37 in 
  let '(continues_48, return_action_49) :=
    match auction_state_39 with
    | NotSoldYet => (if ((slot_time_45) >.? (expiry_42)):bool then (
      (if ((balance_47) =.? (repr 0)):bool then ((false, Ok ((Accept)))) else (
        (
          true,
          Ok ((SimpleTransfer ((owner_46, b_40, seq_new_ (repr 0) (usize 0)))))
        )))) else ((false, Err ((AuctionStillActive)))))
    | Sold _ => (false, Err ((AuctionFinalized))) end in 
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
                | Ok a_54 => match a_54 with
                | SimpleTransfer (o_55, b_56, a_57) => Ok (
                  (
                    SimpleTransfer (
                      (
                        o_55,
                        b_56,
                        seq_concat (seq_concat (a_57) (addr_53)) (
                          u64_to_be_bytes (amnt_52))
                      ))
                  ))
                | Accept => Ok ((Accept)) end
                | Err e_58 => Err ((e_58)) end in 
              (auction_state_39, return_action_49, remaining_bid_50)
            ) else (
              let '(auction_state_39, return_action_49, remaining_bid_50) :=
                if match remaining_bid_50 with
                | None => true
                | Some (_, _) => false end:bool then (
                  let auction_state_39 :=
                    Sold ((addr_53)) in 
                  let remaining_bid_50 :=
                    Some ((amnt_52, tt)) in 
                  (auction_state_39, return_action_49, remaining_bid_50)
                ) else (
                  let return_action_49 :=
                    Err ((BidMapError)) in 
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
        | Some (amount_59, _) => match (if ((amount_59) =.? (b_40)):bool then (
          True) else (False)) with
        | True => return_action_49
        | False => Err ((BidMapError)) end
        | None => Err ((BidMapError)) end in 
      (return_action_49)
    ) else ( (return_action_49)
    ) in 
  ((auction_state_39, b_40, c_41, expiry_42, (m1_43, m2_44)), return_action_49).

Definition auction_test_init  : bool :=
  let item_60 :=
    seq_new_ (repr 0) (usize 0) in 
  let time_61 :=
    repr 100 in 
  (fresh_state (seq_clone (item_60)) (time_61)) =.? (
    (
      NotSoldYet,
      repr 0,
      seq_clone (item_60),
      time_61,
      (seq_new_ (repr 0) (usize 0), seq_new_ (repr 0) (usize 0))
    )).

Theorem auction_test_init_correct : auction_test_init = true.
Proof. reflexivity. Qed.


Definition verify_bid
  (state_62 : state)
  (account_63 : user_address)
  (ctx_64 : context)
  (amount_65 : int64)
  (bid_map_66 : seq_map)
  (highest_bid_67 : int64)
  : bool :=
  let item_68 :=
    seq_new_ (repr 0) (usize 0) in 
  let time_69 :=
    repr 100 in 
  let '(state_70, res_71) :=
    auction_bid (ctx_64) (amount_65) (state_62) in 
  let bid_map_72 :=
    match seq_map_update_entry (bid_map_66) (account_63) (highest_bid_67) with
    | Update (_, updated_map_73) => updated_map_73 end in 
  (state_70) =.? (
    (NotSoldYet, highest_bid_67, seq_clone (item_68), time_69, bid_map_72)).

Definition test_auction_bid_and_finalize  : bool :=
  let item_74 :=
    seq_new_ (repr 0) (usize 0) in 
  let time_75 :=
    repr 100 in 
  let amount_76 :=
    repr 100 in 
  let bid_map_77 :=
    (seq_new_ (repr 0) (usize 0), seq_new_ (repr 0) (usize 0)) in 
  let state_78 :=
    fresh_state (seq_clone (item_74)) (time_75) in 
  let alice_79 :=
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
        ] in  l) in 
  let alice_ctx_80 :=
    (repr 1, UserAddressSome ((alice_79, tt))) in 
  verify_bid (state_78) (alice_79) (alice_ctx_80) (amount_76) (bid_map_77) (
    amount_76).

Compute test_auction_bid_and_finalize.

Axiom HK : (forall k, (u64_to_be_bytes (@repr WORDSIZE64 k)) = array_from_list (int8) [@repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 k]).

Theorem test_auction_bid_and_finalize_correct : test_auction_bid_and_finalize = true.
Proof.
  unfold test_auction_bid_and_finalize.
  unfold fresh_state.
  unfold verify_bid.
  unfold seq_map_update_entry.

  assert (
      (@seq_len int8
                (@seq_clone public_byte_seq
                            (@seq_new_
                               (@int WORDSIZE8)
                               (@repr WORDSIZE8 Z0)
                               (uint_size_to_nat
                                  (@usize Z Z_uint_sizable Z0)))))  / usize 32
      = (usize 0)) by reflexivity.
  rewrite H. clear H.
  unfold foldi.

  assert (Z.sub
                   (@unsigned WORDSIZE32
                      (Z_to_uint_size
                         (Z.of_N
                            (N.of_nat
                               (uint_size_to_nat (@usize Z Z_uint_sizable Z0))))))
                   (@unsigned WORDSIZE32 (@usize Z Z_uint_sizable Z0)) = 0) by reflexivity.
  rewrite H. clear H.

  (* Set Printing All. *)
  (* Set Printing Depth 400. *)

  assert ((
                (@Vector.to_list int8
                   (@length int8
                      (@List.rev_append int8
                         (@seq_new_ (@int WORDSIZE8) 
                            (@repr WORDSIZE8 Z0)
                            (uint_size_to_nat (@usize Z Z_uint_sizable Z0)))
                         (@Vector.to_list int8
                            (uint_size_to_nat
                               (@usize Z Z_uint_sizable
                                  (Zpos (xO (xO (xO (xO (xO xH))))))))
                            (array_from_list int8
                               (@cons (@int WORDSIZE8) 
                                  (@repr WORDSIZE8 Z0)
                                  (@cons (@int WORDSIZE8)
                                     (@repr WORDSIZE8 Z0)
                                     (@cons (@int WORDSIZE8)
                                        (@repr WORDSIZE8 Z0)
                                        (@cons (@int WORDSIZE8)
                                           (@repr WORDSIZE8 Z0)
                                           (@cons 
                                              (@int WORDSIZE8)
                                              (@repr WORDSIZE8 Z0)
                                              (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@nil (@int WORDSIZE8))))))))))))))))))))))))))))))))))))))
                   (@seq_concat int8
                      (@seq_new_ (@int WORDSIZE8) 
                         (@repr WORDSIZE8 Z0)
                         (uint_size_to_nat (@usize Z Z_uint_sizable Z0)))
                      (@Vector.to_list int8
                         (uint_size_to_nat
                            (@usize Z Z_uint_sizable
                               (Zpos (xO (xO (xO (xO (xO xH))))))))
                         (array_from_list int8
                            (@cons (@int WORDSIZE8) 
                               (@repr WORDSIZE8 Z0)
                               (@cons (@int WORDSIZE8) 
                                  (@repr WORDSIZE8 Z0)
                                  (@cons (@int WORDSIZE8)
                                     (@repr WORDSIZE8 Z0)
                                     (@cons (@int WORDSIZE8)
                                        (@repr WORDSIZE8 Z0)
                                        (@cons (@int WORDSIZE8)
                                           (@repr WORDSIZE8 Z0)
                                           (@cons 
                                              (@int WORDSIZE8)
                                              (@repr WORDSIZE8 Z0)
                                              (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@nil (@int WORDSIZE8))))))))))))))))))))))))))))))))))))))
                ) = ([@repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
       @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
       @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
       @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
       @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
       @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
       @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
       @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0])) by reflexivity.
  rewrite H. clear H.

  (* assert (seq_concat (seq_new_ (@repr WORDSIZE8 0) (usize 0)) *)
  (*                    (u64_to_be_bytes (@repr WORDSIZE64 100)) = (u64_to_be_bytes (@repr WORDSIZE64 100))). *)
  (* reflexivity. *)
  
  assert ((@Vector.to_list int8
                   (@length int8
                      (@List.rev_append int8
                         (@seq_new_ (@int WORDSIZE8) 
                            (@repr WORDSIZE8 Z0)
                            (uint_size_to_nat (@usize Z Z_uint_sizable Z0)))
                         (@Vector.to_list int8
                            (S (S (S (S (S (S (S (S O))))))))
                            (u64_to_be_bytes
                               (@repr WORDSIZE64
                                  (Zpos (xO (xO (xI (xO (xO (xI xH))))))))))))
                   (@seq_concat int8
                      (@seq_new_ (@int WORDSIZE8) 
                         (@repr WORDSIZE8 Z0)
                         (uint_size_to_nat (@usize Z Z_uint_sizable Z0)))
                      (@Vector.to_list int8 (S (S (S (S (S (S (S (S O))))))))
                         (u64_to_be_bytes
                            (@repr WORDSIZE64
                               (Zpos (xO (xO (xI (xO (xO (xI xH)))))))))))) =
          (u64_to_be_bytes (@repr WORDSIZE64 100))).
  cbn.

  rewrite HK.
  simpl.
  reflexivity.

  rewrite H. clear H.
  
  unfold auction_bid.
  
  assert (@leb int64 (@int_comparable WORDSIZE64)
              (@repr WORDSIZE64 (Zpos xH))
              (@repr WORDSIZE64 (Zpos (xO (xO (xI (xO (xO (xI xH)))))))) = true) by reflexivity.
  rewrite H. clear H.
  
  assert (seq_map_entry
            (@tuple_clone (prod public_byte_seq public_byte_seq)
               (@pair public_byte_seq public_byte_seq
                  (@seq_new_ (@int WORDSIZE8) (@repr WORDSIZE8 Z0)
                     (uint_size_to_nat (@usize Z Z_uint_sizable Z0)))
                  (@seq_new_ (@int WORDSIZE8) (@repr WORDSIZE8 Z0)
                     (uint_size_to_nat (@usize Z Z_uint_sizable Z0)))))
            (array_from_list int8 [@repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
         @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
         @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
         @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
         @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
         @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
         @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
         @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0]) = Entry (@repr WORDSIZE64 0, ([@repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
         @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
         @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
         @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
         @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
         @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
         @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
         @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0], (u64_to_be_bytes (@repr WORDSIZE64 0))))).
  cbn. rewrite HK. reflexivity.

  rewrite H. clear H.

  unfold tuple_clone.

  unfold seq_map_entry.
  unfold tuple_clone.
  
  unfold seq_map_update_entry.
  unfold seq_clone.
  
  assert (((Z_to_uint_size
               (Z.div
                  (Z.of_N
                     (@seq_len int8
                        [@repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
            @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
            @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
            @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
            @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
            @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
            @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
            @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
            @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
            @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
            @repr WORDSIZE8 0; @repr WORDSIZE8 0]))
                  (Z.of_N
                     (N.of_nat
                        (uint_size_to_nat
                           (@usize Z Z_uint_sizable
                              (Zpos (xO (xO (xO (xO (xO xH))))))))))))) = 1) by reflexivity.
  rewrite H. clear H.

  unfold foldi.

  assert  (Z.sub (@unsigned WORDSIZE32 (Z_to_uint_size (Zpos xH)))
                 (@unsigned WORDSIZE32 (@usize Z Z_uint_sizable Z0)) = 1) by reflexivity.
  rewrite H. clear H.

  unfold "array_eq".
  unfold int_default.
  
  (* Set Printing All. *)
  (* Set Printing Depth 400. *)
  
  assert (@foldi_ map_update (Pos.to_nat xH) (@usize Z Z_uint_sizable Z0)
            (fun (x_14 : uint_size) (res_13 : map_update) =>
             match
               @Vector.eqb (@int WORDSIZE8) (@eq WORDSIZE8)
                 32%nat
                 32%nat
                 (@array_from_seq int8
                    (Build_Default (@int WORDSIZE8) (@repr WORDSIZE8 Z0))
                    32%nat
                    (@Vector.to_list int8
                       (uint_size_to_nat
                          (@usize Z Z_uint_sizable
                             (Zpos (xO (xO (xO (xO (xO xH))))))))
                       (@seq_slice int8
                          (Build_Default (@int WORDSIZE8)
                             (@repr WORDSIZE8 Z0))
                          (@cons (@int WORDSIZE8) 
                             (@repr WORDSIZE8 Z0)
                             (@cons (@int WORDSIZE8) 
                                (@repr WORDSIZE8 Z0)
                                (@cons (@int WORDSIZE8) 
                                   (@repr WORDSIZE8 Z0)
                                   (@cons (@int WORDSIZE8)
                                      (@repr WORDSIZE8 Z0)
                                      (@cons (@int WORDSIZE8)
                                         (@repr WORDSIZE8 Z0)
                                         (@cons (@int WORDSIZE8)
                                            (@repr WORDSIZE8 Z0)
                                            (@cons 
                                               (@int WORDSIZE8)
                                               (@repr WORDSIZE8 Z0)
                                               (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@nil (@int WORDSIZE8))))))))))))))))))))))))))))))))))
                          (Init.Nat.mul (uint_size_to_nat x_14)
                             (uint_size_to_nat
                                (@usize Z Z_uint_sizable
                                   (Zpos (xO (xO (xO (xO (xO xH)))))))))
                          (uint_size_to_nat
                             (@usize Z Z_uint_sizable
                                (Zpos (xO (xO (xO (xO (xO xH)))))))))))
                 (array_from_list int8
                    (@cons (@int WORDSIZE8) (@repr WORDSIZE8 Z0)
                       (@cons (@int WORDSIZE8) (@repr WORDSIZE8 Z0)
                          (@cons (@int WORDSIZE8) 
                             (@repr WORDSIZE8 Z0)
                             (@cons (@int WORDSIZE8) 
                                (@repr WORDSIZE8 Z0)
                                (@cons (@int WORDSIZE8) 
                                   (@repr WORDSIZE8 Z0)
                                   (@cons (@int WORDSIZE8)
                                      (@repr WORDSIZE8 Z0)
                                      (@cons (@int WORDSIZE8)
                                         (@repr WORDSIZE8 Z0)
                                         (@cons (@int WORDSIZE8)
                                            (@repr WORDSIZE8 Z0)
                                            (@cons 
                                               (@int WORDSIZE8)
                                               (@repr WORDSIZE8 Z0)
                                               (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@nil (@int WORDSIZE8)))))))))))))))))))))))))))))))))))
               return map_update
             with
             | true =>
                 Update
                   (@pair int64 (prod public_byte_seq public_byte_seq)
                      (@add WORDSIZE64 (@repr WORDSIZE64 Z0)
                         (@repr WORDSIZE64
                            (Zpos (xO (xO (xI (xO (xO (xI xH)))))))))
                      (@pair public_byte_seq public_byte_seq
                         (@seq_update int8
                            (Build_Default (@int WORDSIZE8)
                               (@repr WORDSIZE8 Z0))
                            (@cons (@int WORDSIZE8) 
                               (@repr WORDSIZE8 Z0)
                               (@cons (@int WORDSIZE8) 
                                  (@repr WORDSIZE8 Z0)
                                  (@cons (@int WORDSIZE8)
                                     (@repr WORDSIZE8 Z0)
                                     (@cons (@int WORDSIZE8)
                                        (@repr WORDSIZE8 Z0)
                                        (@cons (@int WORDSIZE8)
                                           (@repr WORDSIZE8 Z0)
                                           (@cons 
                                              (@int WORDSIZE8)
                                              (@repr WORDSIZE8 Z0)
                                              (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@nil (@int WORDSIZE8))))))))))))))))))))))))))))))))))
                            (Init.Nat.mul (uint_size_to_nat x_14)
                               (uint_size_to_nat
                                  (@usize Z Z_uint_sizable
                                     (Zpos (xO (xO (xO (xO (xO xH)))))))))
                            (@Vector.to_list int8
                               (uint_size_to_nat
                                  (@usize Z Z_uint_sizable
                                     (Zpos (xO (xO (xO (xO (xO xH))))))))
                               (array_from_list int8
                                  (@cons (@int WORDSIZE8)
                                     (@repr WORDSIZE8 Z0)
                                     (@cons (@int WORDSIZE8)
                                        (@repr WORDSIZE8 Z0)
                                        (@cons (@int WORDSIZE8)
                                           (@repr WORDSIZE8 Z0)
                                           (@cons 
                                              (@int WORDSIZE8)
                                              (@repr WORDSIZE8 Z0)
                                              (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@nil (@int WORDSIZE8)))))))))))))))))))))))))))))))))))))
                         (@seq_update int8
                            (Build_Default (@int WORDSIZE8)
                               (@repr WORDSIZE8 Z0))
                            (@Vector.to_list int8
                               (S (S (S (S (S (S (S (S O))))))))
                               (u64_to_be_bytes (@repr WORDSIZE64 Z0)))
                            (Init.Nat.mul (uint_size_to_nat x_14)
                               (uint_size_to_nat
                                  (@usize Z Z_uint_sizable
                                     (Zpos (xO (xO (xO xH)))))))
                            (@Vector.to_list int8
                               (S (S (S (S (S (S (S (S O))))))))
                               (u64_to_be_bytes
                                  (@add WORDSIZE64 
                                     (@repr WORDSIZE64 Z0)
                                     (@repr WORDSIZE64
                                        (Zpos
                                           (xO (xO (xI (xO (xO (xI xH))))))))))))))
             | false => res_13
             end)
            (Update
               (@pair int64 (prod public_byte_seq public_byte_seq)
                  (@add WORDSIZE64 (@repr WORDSIZE64 Z0)
                     (@repr WORDSIZE64
                        (Zpos (xO (xO (xI (xO (xO (xI xH)))))))))
                  (@pair public_byte_seq public_byte_seq
                     (@Vector.to_list int8
                        (@length int8
                           (@List.rev_append int8
                              (@cons (@int WORDSIZE8) 
                                 (@repr WORDSIZE8 Z0)
                                 (@cons (@int WORDSIZE8) 
                                    (@repr WORDSIZE8 Z0)
                                    (@cons (@int WORDSIZE8)
                                       (@repr WORDSIZE8 Z0)
                                       (@cons (@int WORDSIZE8)
                                          (@repr WORDSIZE8 Z0)
                                          (@cons (@int WORDSIZE8)
                                             (@repr WORDSIZE8 Z0)
                                             (@cons 
                                                (@int WORDSIZE8)
                                                (@repr WORDSIZE8 Z0)
                                                (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@nil (@int WORDSIZE8))))))))))))))))))))))))))))))))))
                              (@Vector.to_list int8
                                 (uint_size_to_nat
                                    (@usize Z Z_uint_sizable
                                       (Zpos (xO (xO (xO (xO (xO xH))))))))
                                 (array_from_list int8
                                    (@cons (@int WORDSIZE8)
                                       (@repr WORDSIZE8 Z0)
                                       (@cons (@int WORDSIZE8)
                                          (@repr WORDSIZE8 Z0)
                                          (@cons (@int WORDSIZE8)
                                             (@repr WORDSIZE8 Z0)
                                             (@cons 
                                                (@int WORDSIZE8)
                                                (@repr WORDSIZE8 Z0)
                                                (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@nil (@int WORDSIZE8))))))))))))))))))))))))))))))))))))))
                        (@seq_concat int8
                           (@cons (@int WORDSIZE8) 
                              (@repr WORDSIZE8 Z0)
                              (@cons (@int WORDSIZE8) 
                                 (@repr WORDSIZE8 Z0)
                                 (@cons (@int WORDSIZE8) 
                                    (@repr WORDSIZE8 Z0)
                                    (@cons (@int WORDSIZE8)
                                       (@repr WORDSIZE8 Z0)
                                       (@cons (@int WORDSIZE8)
                                          (@repr WORDSIZE8 Z0)
                                          (@cons (@int WORDSIZE8)
                                             (@repr WORDSIZE8 Z0)
                                             (@cons 
                                                (@int WORDSIZE8)
                                                (@repr WORDSIZE8 Z0)
                                                (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@nil (@int WORDSIZE8))))))))))))))))))))))))))))))))))
                           (@Vector.to_list int8
                              (uint_size_to_nat
                                 (@usize Z Z_uint_sizable
                                    (Zpos (xO (xO (xO (xO (xO xH))))))))
                              (array_from_list int8
                                 (@cons (@int WORDSIZE8) 
                                    (@repr WORDSIZE8 Z0)
                                    (@cons (@int WORDSIZE8)
                                       (@repr WORDSIZE8 Z0)
                                       (@cons (@int WORDSIZE8)
                                          (@repr WORDSIZE8 Z0)
                                          (@cons (@int WORDSIZE8)
                                             (@repr WORDSIZE8 Z0)
                                             (@cons 
                                                (@int WORDSIZE8)
                                                (@repr WORDSIZE8 Z0)
                                                (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@cons 
                                                 (@int WORDSIZE8)
                                                 (@repr WORDSIZE8 Z0)
                                                 (@nil (@int WORDSIZE8))))))))))))))))))))))))))))))))))))))
                     (@Vector.to_list int8
                        (@length int8
                           (@List.rev_append int8
                              (@Vector.to_list int8
                                 (S (S (S (S (S (S (S (S O))))))))
                                 (u64_to_be_bytes (@repr WORDSIZE64 Z0)))
                              (@Vector.to_list int8
                                 (S (S (S (S (S (S (S (S O))))))))
                                 (u64_to_be_bytes
                                    (@add WORDSIZE64 
                                       (@repr WORDSIZE64 Z0)
                                       (@repr WORDSIZE64
                                          (Zpos
                                             (xO (xO (xI (xO (xO (xI xH)))))))))))))
                        (@seq_concat int8
                           (@Vector.to_list int8
                              (S (S (S (S (S (S (S (S O))))))))
                              (u64_to_be_bytes (@repr WORDSIZE64 Z0)))
                           (@Vector.to_list int8
                              (S (S (S (S (S (S (S (S O))))))))
                              (u64_to_be_bytes
                                 (@add WORDSIZE64 
                                    (@repr WORDSIZE64 Z0)
                                    (@repr WORDSIZE64
                                           (Zpos (xO (xO (xI (xO (xO (xI xH)))))))))))))))) =
                       Update (@repr WORDSIZE64 0 .+ @repr WORDSIZE64 100,
            ([@repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
               @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
               @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
               @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
               @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
               @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
               @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
               @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
               @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
               @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
               @repr WORDSIZE8 0; @repr WORDSIZE8 0],
             (u64_to_be_bytes (@repr WORDSIZE64 0 .+ @repr WORDSIZE64 100))))). {
    assert ((Pos.to_nat 1) = 1%nat) by reflexivity. rewrite H. clear H. cbn.

    rewrite HK.
    cbn.

    assert ((@repr WORDSIZE64 0 .+ @repr WORDSIZE64 100) = @repr WORDSIZE64 100) by reflexivity.
    rewrite H. 
    rewrite HK.
    cbn.

    clear H.
    assert ((Z.to_nat
                                                 (Zbits.P_mod_two_p
                                                 (xO (xO (xO (xO (xO xH)))))
                                                 (@wordsize WORDSIZE32))) = 32) by reflexivity.


    rewrite H. clear H.

    assert ((32%Z - 1 - 0 + 1)%nat = 32%nat) by reflexivity.
    rewrite H. clear H.

    cbn.
    assert (Z.to_nat (Zbits.P_mod_two_p 32 (@wordsize WORDSIZE32)) = 32%nat) by reflexivity.
    rewrite H.
    cbn.

    apply eqb_leibniz_map_update.
    cbn.
    rewrite eq_true.
    cbn.
    
    assert (list_eq_refl : forall (a : list int8), list_eqdec a a = true). {
      intros.
      induction a.
      - reflexivity.
      - simpl.
        rewrite eq_true.
        (* rewrite bid_remain_eq_true. *)
        assumption.
    }

    rewrite eq_true.
    reflexivity.
  }
  
  rewrite H. clear H.
  
  assert (@gtb int64 (@int_comparable WORDSIZE64)
              (@add WORDSIZE64 (@repr WORDSIZE64 Z0)
                 (@repr WORDSIZE64 (Zpos (xO (xO (xI (xO (xO (xI xH)))))))))
              (@repr WORDSIZE64 Z0) = true) by reflexivity.
  rewrite H. clear H.

  cbn.

  assert ((@repr WORDSIZE64 0 .+ @repr WORDSIZE64 100) = @repr WORDSIZE64 100) by reflexivity.
  rewrite H.
  rewrite eq_true.

  cbn.

  assert (bid_remain_eq_true : forall a, eqb_bid_remain a a = true). {
    destruct a. reflexivity.
    destruct p.
    cbn.
    rewrite eq_true.
    easy.
  }
  
  assert (list_eq_refl : forall (a : list int8), list_eqdec a a = true). {
    intros.
    induction a.
    - reflexivity.
    - simpl.
      rewrite eq_true.
      (* rewrite bid_remain_eq_true. *)
      assumption.
  }

  apply (list_eq_refl).  
Qed.
