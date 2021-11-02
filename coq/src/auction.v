(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
From QuickChick Require Import QuickChick.
Require Import QuickChickLib.
Require Import Hacspec.Lib.

Definition user_address := nseq (int8) (usize 32).

Inductive auction_state :=
| NotSoldYet : auction_state
| Sold : user_address -> auction_state.

Definition eqb_auction_state (x y : auction_state) : bool :=
match x with
   | NotSoldYet => match y with | NotSoldYet=> true | _ => false end
   | Sold a => match y with | Sold b => a =.? b | _ => false end
   end.

Definition eqb_leibniz_auction_state (x y : auction_state) : eqb_auction_state x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Definition eqb_leibniz'_auction_state (x y : auction_state) : x = y -> eqb_auction_state x y = true.
Proof. intros. subst. destruct y ; try reflexivity ; try (apply eqdec_refl). Qed.

Instance eq_dec_auction_state : EqDec (auction_state) :=
Build_EqDec (auction_state) (eqb_auction_state) (eqb_leibniz_auction_state) (eqb_leibniz'_auction_state).

 Instance show_auction_state : Show (auction_state) :=
  @Build_Show (auction_state) (fun x =>
 match x with
 NotSoldYet => "NotSoldYet"%string
 | Sold a => append "Sold"%string (show a)
 end).
Definition g_auction_state : G (auction_state) := oneOf_ (returnGen NotSoldYet) [returnGen NotSoldYet;bindGen arbitrary (fun a => returnGen (Sold a))].
Instance gen_auction_state : Gen (auction_state) := Build_Gen auction_state g_auction_state.


Inductive seq_map :=
| SeqMap : (public_byte_seq × public_byte_seq) -> seq_map.

Definition eqb_seq_map (x y : seq_map) : bool :=
match x with
   | SeqMap a => match y with | SeqMap b => a =.? b end
   end.

Definition eqb_leibniz_seq_map (x y : seq_map) : eqb_seq_map x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Definition eqb_leibniz'_seq_map (x y : seq_map) : x = y -> eqb_seq_map x y = true.
Proof. intros. subst. destruct y ; try reflexivity ; try (apply eqdec_refl). Qed.

Instance eq_dec_seq_map : EqDec (seq_map) :=
Build_EqDec (seq_map) (eqb_seq_map) (eqb_leibniz_seq_map) (eqb_leibniz'_seq_map).

 Instance show_seq_map : Show (seq_map) :=
  @Build_Show (seq_map) (fun x =>
 match x with
 SeqMap a => append "SeqMap"%string (show a)
 end).
Definition g_seq_map : G (seq_map) := oneOf_ (bindGen arbitrary (fun a => returnGen (SeqMap a))) [bindGen arbitrary (fun a => returnGen (SeqMap a))].
Instance gen_seq_map : Gen (seq_map) := Build_Gen seq_map g_seq_map.


Notation "'amount'" := (int64) : hacspec_scope.

Notation "'timestamp'" := (int64) : hacspec_scope.

Notation "'itemtyp'" := (public_byte_seq) : hacspec_scope.

Inductive state :=
| State : (auction_state × amount × itemtyp × timestamp × seq_map) -> state.

Definition eqb_state (x y : state) : bool :=
match x with
   | State a => match y with | State b => a =.? b end
   end.

Definition eqb_leibniz_state (x y : state) : eqb_state x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Definition eqb_leibniz'_state (x y : state) : x = y -> eqb_state x y = true.
Proof. intros. subst. destruct y ; try reflexivity ; try (apply eqdec_refl). Qed.

Instance eq_dec_state : EqDec (state) :=
Build_EqDec (state) (eqb_state) (eqb_leibniz_state) (eqb_leibniz'_state).

 Instance show_state : Show (state) :=
  @Build_Show (state) (fun x =>
 match x with
 State a => append "State"%string (show a)
 end).
Definition g_state : G (state) := oneOf_ (bindGen arbitrary (fun a => returnGen (State a))) [bindGen arbitrary (fun a => returnGen (State a))].
Instance gen_state : Gen (state) := Build_Gen state g_state.


Definition fresh_state (itm_0 : itemtyp) (exp_1 : int64) : state :=
  State ((
      NotSoldYet,
      @repr WORDSIZE64 0,
      itm_0,
      exp_1,
      SeqMap ((
          seq_new_ (@repr WORDSIZE8 0) (usize 0),
          seq_new_ (@repr WORDSIZE8 0) (usize 0)
        ))
    )).

Inductive map_entry :=
| Entry : (int64 × seq_map) -> map_entry.

Definition eqb_map_entry (x y : map_entry) : bool :=
match x with
   | Entry a => match y with | Entry b => a =.? b end
   end.

Definition eqb_leibniz_map_entry (x y : map_entry) : eqb_map_entry x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Definition eqb_leibniz'_map_entry (x y : map_entry) : x = y -> eqb_map_entry x y = true.
Proof. intros. subst. destruct y ; try reflexivity ; try (apply eqdec_refl). Qed.

Instance eq_dec_map_entry : EqDec (map_entry) :=
Build_EqDec (map_entry) (eqb_map_entry) (eqb_leibniz_map_entry) (eqb_leibniz'_map_entry).

 Instance show_map_entry : Show (map_entry) :=
  @Build_Show (map_entry) (fun x =>
 match x with
 Entry a => append "Entry"%string (show a)
 end).
Definition g_map_entry : G (map_entry) := oneOf_ (bindGen arbitrary (fun a => returnGen (Entry a))) [bindGen arbitrary (fun a => returnGen (Entry a))].
Instance gen_map_entry : Gen (map_entry) := Build_Gen map_entry g_map_entry.


Definition seq_map_entry
  (m_2 : seq_map)
  (sender_address_3 : user_address)
  : map_entry :=
  let 'SeqMap ((m0_4, m1_5)) :=
    m_2 in 
  let res_6 :=
    Entry ((
        @repr WORDSIZE64 0,
        SeqMap ((
            seq_concat ((m0_4)) (sender_address_3),
            seq_concat ((m1_5)) (u64_to_be_bytes (@repr WORDSIZE64 0))
          ))
      )) in 
  let res_6 :=
    foldi (usize 0) ((seq_len ((m0_4))) / (usize 32)) (fun x_7 res_6 =>
      let '(res_6) :=
        if (array_from_seq (32) (seq_slice ((m0_4)) ((x_7) * (usize 32)) (usize 32))) array_eq (sender_address_3):bool then (
          let res_6 :=
            Entry ((
                u64_from_be_bytes (array_from_seq (8) (seq_slice (m1_5) ((x_7) * (usize 8)) (usize 8))),
                SeqMap (((m0_4), (m1_5)))
              )) in 
          (res_6)
        ) else ( (res_6)
        ) in 
      (res_6))
    res_6 in 
  res_6.

Inductive map_update :=
| Update : (int64 × seq_map) -> map_update.

Definition eqb_map_update (x y : map_update) : bool :=
match x with
   | Update a => match y with | Update b => a =.? b end
   end.

Definition eqb_leibniz_map_update (x y : map_update) : eqb_map_update x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Definition eqb_leibniz'_map_update (x y : map_update) : x = y -> eqb_map_update x y = true.
Proof. intros. subst. destruct y ; try reflexivity ; try (apply eqdec_refl). Qed.

Instance eq_dec_map_update : EqDec (map_update) :=
Build_EqDec (map_update) (eqb_map_update) (eqb_leibniz_map_update) (eqb_leibniz'_map_update).

 Instance show_map_update : Show (map_update) :=
  @Build_Show (map_update) (fun x =>
 match x with
 Update a => append "Update"%string (show a)
 end).
Definition g_map_update : G (map_update) := oneOf_ (bindGen arbitrary (fun a => returnGen (Update a))) [bindGen arbitrary (fun a => returnGen (Update a))].
Instance gen_map_update : Gen (map_update) := Build_Gen map_update g_map_update.


Definition seq_map_update_entry
  (m_8 : seq_map)
  (sender_address_9 : user_address)
  (amount_10 : int64)
  : map_update :=
  let 'SeqMap ((m0_11, m1_12)) :=
    m_8 in 
  let res_13 :=
    Update ((
        amount_10,
        SeqMap ((
            seq_concat (m0_11) (sender_address_9),
            seq_concat (m1_12) (u64_to_be_bytes (amount_10))
          ))
      )) in 
  let res_13 :=
    foldi (usize 0) ((seq_len ((m0_11))) / (usize 32)) (fun x_14 res_13 =>
      let '(res_13) :=
        if (array_from_seq (32) (seq_slice ((m0_11)) ((x_14) * (usize 32)) (usize 32))) array_eq (sender_address_9):bool then (
          let res_13 :=
            Update ((
                amount_10,
                SeqMap ((
                    seq_update ((m0_11)) ((x_14) * (usize 32)) (sender_address_9),
                    seq_update ((m1_12)) ((x_14) * (usize 8)) (u64_to_be_bytes (amount_10))
                  ))
              )) in 
          (res_13)
        ) else ( (res_13)
        ) in 
      (res_13))
    res_13 in 
  res_13.

Inductive bid_error :=
| ContractSender : bid_error
| BidTooLow : bid_error
| BidsOverWaitingForAuctionFinalization : bid_error
| AuctionIsFinalized : bid_error.

Definition eqb_bid_error (x y : bid_error) : bool :=
match x with
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

Definition eqb_leibniz'_bid_error (x y : bid_error) : x = y -> eqb_bid_error x y = true.
Proof. intros. subst. destruct y ; try reflexivity ; try (apply eqdec_refl). Qed.

Instance eq_dec_bid_error : EqDec (bid_error) :=
Build_EqDec (bid_error) (eqb_bid_error) (eqb_leibniz_bid_error) (eqb_leibniz'_bid_error).

 Instance show_bid_error : Show (bid_error) :=
  @Build_Show (bid_error) (fun x =>
 match x with
 ContractSender => "ContractSender"%string
 | BidTooLow => "BidTooLow"%string
 | BidsOverWaitingForAuctionFinalization => "BidsOverWaitingForAuctionFinalization"%string
 | AuctionIsFinalized => "AuctionIsFinalized"%string
 end).
Definition g_bid_error : G (bid_error) := oneOf_ (returnGen ContractSender) [returnGen ContractSender;returnGen BidTooLow;returnGen BidsOverWaitingForAuctionFinalization;returnGen AuctionIsFinalized].
Instance gen_bid_error : Gen (bid_error) := Build_Gen bid_error g_bid_error.


Inductive user_address_set :=
| UserAddressSome : (user_address × unit) -> user_address_set
| UserAddressNone : user_address_set.

Definition eqb_user_address_set (x y : user_address_set) : bool :=
match x with
   | UserAddressSome a =>
       match y with
       | UserAddressSome b => a =.? b
       | _ => false
       end
   | UserAddressNone => match y with | UserAddressNone=> true | _ => false end
   end.

Definition eqb_leibniz_user_address_set (x y : user_address_set) : eqb_user_address_set x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Definition eqb_leibniz'_user_address_set (x y : user_address_set) : x = y -> eqb_user_address_set x y = true.
Proof. intros. subst. destruct y ; try reflexivity ; try (apply eqdec_refl). Qed.

Instance eq_dec_user_address_set : EqDec (user_address_set) :=
Build_EqDec (user_address_set) (eqb_user_address_set) (eqb_leibniz_user_address_set) (eqb_leibniz'_user_address_set).

 Instance show_user_address_set : Show (user_address_set) :=
  @Build_Show (user_address_set) (fun x =>
 match x with
 UserAddressSome a => append "UserAddressSome"%string (show a)
 | UserAddressNone => "UserAddressNone"%string
 end).
Definition g_user_address_set : G (user_address_set) := oneOf_ (bindGen arbitrary (fun a => returnGen (UserAddressSome a))) [bindGen arbitrary (fun a => returnGen (UserAddressSome a));returnGen UserAddressNone].
Instance gen_user_address_set : Gen (user_address_set) := Build_Gen user_address_set g_user_address_set.


Notation "'context'" := ((int64 × user_address_set)) : hacspec_scope.
Instance show_context : Show (context) :=
Build_Show context (fun x =>
  let (x, x0) := x in
  append ("("%string) (append (show x) (append (","%string) (append (show x0) (")"%string))))).
Definition g_context : G (context) :=
bindGen arbitrary (fun x0 : int64 =>
  bindGen arbitrary (fun x1 : user_address_set =>
  returnGen (x0,x1))).
Instance gen_context : Gen (context) := Build_Gen context g_context.


Notation "'auction_bid_result'" := ((result unit bid_error)) : hacspec_scope.

Definition auction_bid
  (ctx_15 : context)
  (amount_16 : int64)
  (state_17 : state)
  : (state × auction_bid_result) :=
  let '(slot_time_18, sender_19) :=
    ctx_15 in 
  let 'State ((st0_20, st1_21, st2_22, st3_23, st4_24)) :=
    (state_17) in 
  let '(new_state_25, rese_26) :=
    match st0_20 with
    | NotSoldYet => (if ((slot_time_18) <=.? (st3_23)):bool then (match sender_19 with
        | UserAddressNone => (state_17, Err (ContractSender))
        | UserAddressSome (sender_address_27, _
        ) => match seq_map_entry ((st4_24)) (sender_address_27) with
        | Entry (bid_to_update_28, new_map_29
        ) => match seq_map_update_entry ((new_map_29)) (sender_address_27) ((bid_to_update_28) .+ (amount_16)) with
        | Update (updated_bid_30, updated_map_31
        ) => (if ((updated_bid_30) >.? (st1_21)):bool then ((
              State ((st0_20, updated_bid_30, st2_22, st3_23, updated_map_31)),
              Ok (tt)
            )) else ((
              State ((st0_20, st1_21, st2_22, st3_23, updated_map_31)),
              Err (BidTooLow)
            ))) end end end) else ((
          state_17,
          Err (BidsOverWaitingForAuctionFinalization)
        )))
    | Sold _ => (state_17, Err (AuctionIsFinalized)) end in 
  (new_state_25, rese_26).

Notation "'finalize_context'" := ((int64 × user_address × int64
)) : hacspec_scope.
Instance show_finalize_context : Show (finalize_context) :=
Build_Show finalize_context (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  append ("("%string) (append (show x) (append (","%string) (append (show x0) (append (","%string) (append (show x1) (")"%string))))))).
Definition g_finalize_context : G (finalize_context) :=
bindGen arbitrary (fun x0 : int64 =>
  bindGen arbitrary (fun x1 : user_address =>
  bindGen arbitrary (fun x2 : int64 =>
  returnGen (x0,x1,x2)))).
Instance gen_finalize_context : Gen (finalize_context) := Build_Gen finalize_context g_finalize_context.


Inductive finalize_error :=
| BidMapError : finalize_error
| AuctionStillActive : finalize_error
| AuctionFinalized : finalize_error.

Definition eqb_finalize_error (x y : finalize_error) : bool :=
match x with
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

Definition eqb_leibniz'_finalize_error (x y : finalize_error) : x = y -> eqb_finalize_error x y = true.
Proof. intros. subst. destruct y ; try reflexivity ; try (apply eqdec_refl). Qed.

Instance eq_dec_finalize_error : EqDec (finalize_error) :=
Build_EqDec (finalize_error) (eqb_finalize_error) (eqb_leibniz_finalize_error) (eqb_leibniz'_finalize_error).

 Instance show_finalize_error : Show (finalize_error) :=
  @Build_Show (finalize_error) (fun x =>
 match x with
 BidMapError => "BidMapError"%string
 | AuctionStillActive => "AuctionStillActive"%string
 | AuctionFinalized => "AuctionFinalized"%string
 end).
Definition g_finalize_error : G (finalize_error) := oneOf_ (returnGen BidMapError) [returnGen BidMapError;returnGen AuctionStillActive;returnGen AuctionFinalized].
Instance gen_finalize_error : Gen (finalize_error) := Build_Gen finalize_error g_finalize_error.


Inductive finalize_action :=
| Accept : finalize_action
| SimpleTransfer : (user_address × int64 × public_byte_seq
) -> finalize_action.

Definition eqb_finalize_action (x y : finalize_action) : bool :=
match x with
   | Accept => match y with | Accept=> true | _ => false end
   | SimpleTransfer a =>
       match y with
       | SimpleTransfer b => a =.? b
       | _ => false
       end
   end.

Definition eqb_leibniz_finalize_action (x y : finalize_action) : eqb_finalize_action x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Definition eqb_leibniz'_finalize_action (x y : finalize_action) : x = y -> eqb_finalize_action x y = true.
Proof. intros. subst. destruct y ; try reflexivity ; try (apply eqdec_refl). Qed.

Instance eq_dec_finalize_action : EqDec (finalize_action) :=
Build_EqDec (finalize_action) (eqb_finalize_action) (eqb_leibniz_finalize_action) (eqb_leibniz'_finalize_action).

 Instance show_finalize_action : Show (finalize_action) :=
  @Build_Show (finalize_action) (fun x =>
 match x with
 Accept => "Accept"%string
 | SimpleTransfer a => append "SimpleTransfer"%string (show a)
 end).
Definition g_finalize_action : G (finalize_action) := oneOf_ (returnGen Accept) [returnGen Accept;bindGen arbitrary (fun a => returnGen (SimpleTransfer a))].
Instance gen_finalize_action : Gen (finalize_action) := Build_Gen finalize_action g_finalize_action.


Inductive bid_remain :=
| None : bid_remain
| Some : (int64 × unit) -> bid_remain.

Definition eqb_bid_remain (x y : bid_remain) : bool :=
match x with
   | None => match y with | None=> true | _ => false end
   | Some a => match y with | Some b => a =.? b | _ => false end
   end.

Definition eqb_leibniz_bid_remain (x y : bid_remain) : eqb_bid_remain x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Definition eqb_leibniz'_bid_remain (x y : bid_remain) : x = y -> eqb_bid_remain x y = true.
Proof. intros. subst. destruct y ; try reflexivity ; try (apply eqdec_refl). Qed.

Instance eq_dec_bid_remain : EqDec (bid_remain) :=
Build_EqDec (bid_remain) (eqb_bid_remain) (eqb_leibniz_bid_remain) (eqb_leibniz'_bid_remain).

 Instance show_bid_remain : Show (bid_remain) :=
  @Build_Show (bid_remain) (fun x =>
 match x with
 None => "None"%string
 | Some a => append "Some"%string (show a)
 end).
Definition g_bid_remain : G (bid_remain) := oneOf_ (returnGen None) [returnGen None;bindGen arbitrary (fun a => returnGen (Some a))].
Instance gen_bid_remain : Gen (bid_remain) := Build_Gen bid_remain g_bid_remain.


Notation "'auction_finalize_result'" := ((result finalize_action finalize_error)) : hacspec_scope.

Definition auction_finalize
  (ctx_32 : finalize_context)
  (state_33 : state)
  : (state × auction_finalize_result) :=
  let 'State ((st0_34, st1_35, st2_36, st3_37, st4_38)) :=
    (state_33) in 
  let '(slot_time_39, owner_40, balance_41) :=
    ctx_32 in 
  let '(continues_42, return_action_43) :=
    match st0_34 with
    | NotSoldYet => (if ((slot_time_39) >.? (st3_37)):bool then ((if ((balance_41) =.? (@repr WORDSIZE64 0)):bool then ((
              false,
              Ok (Accept)
            )) else ((
              true,
              Ok (SimpleTransfer ((
                    owner_40,
                    st1_35,
                    seq_new_ (@repr WORDSIZE8 0) (usize 0)
                  )))
            )))) else ((false, Err (AuctionStillActive))))
    | Sold _ => (false, Err (AuctionFinalized)) end in 
  let remaining_bid_44 :=
    None in 
  let 'SeqMap ((m0_45, m1_46)) :=
    (st4_38) in 
  let '(st0_34, return_action_43, remaining_bid_44) :=
    if continues_42:bool then (
      let '(st0_34, return_action_43, remaining_bid_44) :=
        foldi (usize 0) ((seq_len ((m0_45))) / (usize 32)) (fun x_47 '(
            st0_34,
            return_action_43,
            remaining_bid_44
          ) =>
          let amnt_48 :=
            u64_from_be_bytes (array_from_seq (8) (seq_slice (m1_46) ((x_47) * (usize 8)) (usize 8))) in 
          let addr_49 :=
            array_from_seq (32) (seq_slice ((m0_45)) ((x_47) * (usize 32)) (usize 32)) in 
          let '(st0_34, return_action_43, remaining_bid_44) :=
            if (amnt_48) <.? (st1_35):bool then (
              let return_action_43 :=
                match return_action_43 with
                | Ok a_50 => match a_50 with
                | SimpleTransfer (o_51, b_52, a_53) => Ok (SimpleTransfer ((
                      o_51,
                      b_52,
                      seq_concat (seq_concat (a_53) (addr_49)) (u64_to_be_bytes (amnt_48))
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
          (st0_34, return_action_43, remaining_bid_44))
        (st0_34, return_action_43, remaining_bid_44) in 
      (st0_34, return_action_43, remaining_bid_44)
    ) else ( (st0_34, return_action_43, remaining_bid_44)
    ) in 
  let '(return_action_43) :=
    if continues_42:bool then (
      let return_action_43 :=
        match remaining_bid_44 with
        | Some (amount_55, _
        ) => (if ((amount_55) =.? (st1_35)):bool then (return_action_43) else (Err (BidMapError)))
        | None => Err (BidMapError) end in 
      (return_action_43)
    ) else ( (return_action_43)
    ) in 
  (State ((st0_34, st1_35, st2_36, st3_37, st4_38)), return_action_43).

Definition auction_test_init
  (item_56 : public_byte_seq)
  (time_57 : int64)
  : bool :=
  (fresh_state ((item_56)) (time_57)) =.? (State ((
        NotSoldYet,
        @repr WORDSIZE64 0,
        (item_56),
        time_57,
        SeqMap ((
            seq_new_ (@repr WORDSIZE8 0) (usize 0),
            seq_new_ (@repr WORDSIZE8 0) (usize 0)
          ))
      ))).
Theorem ensures_auction_test_init : forall result (item : public_byte_seq) (time : int64),
auction_test_init item time = result ->
 (result) = (true).
Proof. Admitted.
(* QuickChick (forAll g_public_byte_seq (fun item_56 : public_byte_seq => *)
(*   forAll g_int64 (fun time_57 : int64 => *)
(*   auction_test_init item_56 time_57))). *)


Theorem auction_test_init_correct : forall item_56 : public_byte_seq ,forall time_57 : int64 ,auction_test_init item_56 time_57 = true.
Proof. Admitted.


Definition verify_bid
  (state_58 : state)
  (account_59 : user_address)
  (ctx_60 : context)
  (amount_61 : int64)
  (highest_bid_62 : int64)
  : (state × bool) :=
  let item_63 :=
    seq_new_ (@repr WORDSIZE8 0) (usize 0) in 
  let time_64 :=
    @repr WORDSIZE64 100 in 
  let '(State ((auc_st_65, hb_66, its_67, tm_68, bm_69)), res_70) :=
    auction_bid (ctx_60) (amount_61) (state_58) in 
  let bm_71 :=
    match seq_map_update_entry ((bm_69)) (account_59) (highest_bid_62) with
    | Update (_, updated_map_72) => updated_map_72 end in 
  (
    State ((auc_st_65, hb_66, (its_67), tm_68, (bm_71))),
    (State ((auc_st_65, hb_66, (its_67), tm_68, (bm_71)))) =.? (State ((
          NotSoldYet,
          highest_bid_62,
          (item_63),
          time_64,
          (bm_71)
        )))
  ).

Definition test_auction_bid_and_finalize  : bool :=
  let item_73 :=
    seq_new_ (@repr WORDSIZE8 0) (usize 0) in 
  let time_74 :=
    @repr WORDSIZE64 100 in 
  let amount_75 :=
    @repr WORDSIZE64 100 in 
  let winning_amount_76 :=
    @repr WORDSIZE64 300 in 
  let state_77 :=
    fresh_state ((item_73)) (time_74) in 
  let alice_78 :=
    array_from_list int8 (let l :=
        [
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0;
          @repr WORDSIZE8 0
        ] in  l) in 
  let alice_ctx_79 :=
    (@repr WORDSIZE64 1, UserAddressSome ((alice_78, tt))) in 
  let '(state_80, result_0_81) :=
    verify_bid (state_77) (alice_78) (alice_ctx_79) (amount_75) (amount_75) in 
  result_0_81.
Theorem ensures_test_auction_bid_and_finalize : forall result ,
test_auction_bid_and_finalize  = result ->
 (result) = (true).
Proof. Admitted.

Theorem test_auction_bid_and_finalize_correct : test_auction_bid_and_finalize = true.
Proof.
  unfold test_auction_bid_and_finalize.
  unfold fresh_state.
  unfold seq_new_.
  unfold verify_bid.

  Print user_address.
  Compute (nseq int8 (usize 32)).
  
  assert (auction_bid
            (@repr WORDSIZE64 1,
              UserAddressSome
                (Vector.of_list [@repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
                  @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
                  @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
                  @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
                  @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
                  @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
                  @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; 
                  @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0; @repr WORDSIZE8 0], tt)) 
            (@repr WORDSIZE64 100)
            (State
               (NotSoldYet, @repr WORDSIZE64 0, Vector.const (@repr WORDSIZE8 0) (usize 0), 
                 @repr WORDSIZE64 100,
                 SeqMap
                   (Vector.const (@repr WORDSIZE8 0) (usize 0), Vector.const (@repr WORDSIZE8 0) (usize 0))))
 =
   ((State (NotSoldYet, @repr WORDSIZE64 0, Vector.const (@repr WORDSIZE8 0) (usize 0), @repr WORDSIZE64 100, SeqMap (Vector.const (@repr WORDSIZE8 0) (usize 0), Vector.const (@repr WORDSIZE8 0) (usize 0)))), Ok (tt))).

  
  
  2 : {
    cbn.
  }
  
  unfold auction_bid.
  cbn.
  replace (@repr WORDSIZE64 1 == @repr WORDSIZE64 100) with false by reflexivity.
  replace (lt (@repr WORDSIZE64 1) (@repr WORDSIZE64 100)) with true by reflexivity.
  replace (Z.to_nat (Zbits.P_mod_two_p 32 wordsize)) with 32%nat by reflexivity.
  replace ((@repr WORDSIZE64 100 .+ @repr WORDSIZE64 100)) with ((@repr WORDSIZE64 200)) by reflexivity.  
  
  cbn.
  replace (Z.to_nat (Zbits.P_mod_two_p 32 wordsize)) with 32.
