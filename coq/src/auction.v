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
  let 'SeqMap ((m0_4, m1_5)) := m_2 in 
  let res_6 : map_entry := Entry ((
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
          let res_6 := Entry ((
                u64_from_be_bytes (array_from_seq (8) (seq_slice ((m1_5)) ((x_7) * (usize 8)) (usize 8))),
                SeqMap (((m0_4), (m1_5)))
              )) in 
          (res_6) ) else ( (res_6) ) in 
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
  let 'SeqMap ((m0_11, m1_12)) := m_8 in 
  let res_13 : map_update := Update ((
        amount_10,
        SeqMap ((
            seq_concat ((m0_11)) (sender_address_9),
            seq_concat ((m1_12)) (u64_to_be_bytes (amount_10))
          ))
      )) in 
  let res_13 :=
    foldi (usize 0) ((seq_len ((m0_11))) / (usize 32)) (fun x_14 res_13 =>
      let '(res_13) :=
        if (array_from_seq (32) (seq_slice ((m0_11)) ((x_14) * (usize 32)) (usize 32))) array_eq (sender_address_9):bool then (
          let res_13 := Update ((
                amount_10,
                SeqMap ((
                    seq_update ((m0_11)) ((x_14) * (usize 32)) (sender_address_9),
                    seq_update ((m1_12)) ((x_14) * (usize 8)) (u64_to_be_bytes (amount_10))
                  ))
              )) in 
          (res_13) ) else ( (res_13) ) in 
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
| UserAddressSome : user_address -> user_address_set
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


Notation "'auction_bid_result'" := ((result state bid_error)) : hacspec_scope.

Definition auction_bid
  (ctx_15 : context)
  (amount_16 : int64)
  (state_17 : state)
  : auction_bid_result :=
  let 'State ((auction_state_18, highest_bid_19, st2_20, expiry_21, st4_22)) :=
    (state_17) in 
  let f a :=
  let '(slot_time_23, sender_24) := ctx_15 in 
  let f a :=
  let f a :=
  let sender_address_25 : user_address := match sender_24 with
    | UserAddressNone => array_from_list int8 (let l := [
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5;
          @repr WORDSIZE8 5
        ] in  l)
    | UserAddressSome account_address_26 => account_address_26
    end in 
  let '(bid_to_update_27, new_map_28) :=
    match seq_map_entry ((st4_22)) (sender_address_25) with
    | Entry (bid_to_update_29, new_map_30) => (bid_to_update_29, new_map_30)
    end in 
  let '(updated_bid_31, updated_map_32) :=
    match seq_map_update_entry ((st4_22)) (sender_address_25) ((bid_to_update_27) .+ (amount_16)) with
    | Update (updated_bid_33, updated_map_34) => (updated_bid_33, updated_map_34
    )
    end in 
  let f a :=
  Ok (State ((
        auction_state_18,
        updated_bid_31,
        st2_20,
        expiry_21,
        updated_map_32
      )))
  in
  if negb ((updated_bid_31) >.? (highest_bid_19)) : bool
  then bind (match Err (BidTooLow)  : result state _ with
     | Err a => Err a
     | Ok _ => Ok (tt)
    end) f
   else f (tt)
  in
  if (sender_24) =.? (UserAddressNone) : bool
  then bind (match Err (ContractSender)  : result state _ with
     | Err a => Err a
     | Ok _ => Ok (tt)
    end) f
   else f (tt)
  in
  if negb ((slot_time_23) <=.? (expiry_21)) : bool
  then bind (match Err (BidsOverWaitingForAuctionFinalization)  : result state _ with
     | Err a => Err a
     | Ok _ => Ok (tt)
    end) f
   else f (tt)
  in
  if negb ((auction_state_18) =.? (NotSoldYet)) : bool
  then bind (match Err (AuctionIsFinalized)  : result state _ with
     | Err a => Err a
     | Ok _ => Ok (tt)
    end) f
   else f (tt).

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
| BidMapError0 : finalize_error
| BidMapError1 : finalize_error
| BidMapError2 : finalize_error
| AuctionStillActive : finalize_error
| AuctionFinalized : finalize_error.

Definition eqb_finalize_error (x y : finalize_error) : bool :=
match x with
   | BidMapError0 => match y with | BidMapError0=> true | _ => false end
   | BidMapError1 => match y with | BidMapError1=> true | _ => false end
   | BidMapError2 => match y with | BidMapError2=> true | _ => false end
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
 BidMapError0 => "BidMapError0"%string
 | BidMapError1 => "BidMapError1"%string
 | BidMapError2 => "BidMapError2"%string
 | AuctionStillActive => "AuctionStillActive"%string
 | AuctionFinalized => "AuctionFinalized"%string
 end).
Definition g_finalize_error : G (finalize_error) := oneOf_ (returnGen BidMapError0) [returnGen BidMapError0;returnGen BidMapError1;returnGen BidMapError2;returnGen AuctionStillActive;returnGen AuctionFinalized].
Instance gen_finalize_error : Gen (finalize_error) := Build_Gen finalize_error g_finalize_error.


Inductive finalize_action :=
| Accept : finalize_action
| SimpleTransfer : public_byte_seq -> finalize_action.

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
| BidNone : bid_remain
| BidSome : int64 -> bid_remain.

Definition eqb_bid_remain (x y : bid_remain) : bool :=
match x with
   | BidNone => match y with | BidNone=> true | _ => false end
   | BidSome a => match y with | BidSome b => a =.? b | _ => false end
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
 BidNone => "BidNone"%string
 | BidSome a => append "BidSome"%string (show a)
 end).
Definition g_bid_remain : G (bid_remain) := oneOf_ (returnGen BidNone) [returnGen BidNone;bindGen arbitrary (fun a => returnGen (BidSome a))].
Instance gen_bid_remain : Gen (bid_remain) := Build_Gen bid_remain g_bid_remain.


Notation "'auction_finalize_result'" := ((result (state × finalize_action
  ) finalize_error)) : hacspec_scope.

Definition auction_finalize
  (ctx_35 : finalize_context)
  (state_36 : state)
  : auction_finalize_result :=
  let 'State ((
        auction_state_37,
        highest_bid_38,
        st2_39,
        expiry_40,
        SeqMap ((m0_41, m1_42))
      )) := (state_36) in 
  let result_43 : (result (state × finalize_action) finalize_error) := Ok ((
        (state_36),
        Accept
      )) in 
  let f a :=
  let '(slot_time_44, owner_45, balance_46) := ctx_35 in 
  let f a :=
  let f a :=
  result_43
  in
  if (balance_46) !=.? (@repr WORDSIZE64 0) : bool
  then bind (let return_action_47 : finalize_action :=
      SimpleTransfer (seq_concat (seq_concat (seq_new_ (@repr WORDSIZE8 0) (usize 0)) (owner_45)) (u64_to_be_bytes (highest_bid_38))) in 
    (* let remaining_bid_48 : bid_remain := BidNone in  *)
    match (let f  x_49 '(auction_state_37, return_action_47, remaining_bid_48
      ) :=
      let addr_50 : user_address :=
        array_from_seq (32) (seq_slice ((m0_41)) ((x_49) * (usize 32)) (usize 32)) in 
      let amnt_51 : int64 :=
        u64_from_be_bytes (array_from_seq (8) (seq_slice ((m1_42)) ((x_49) * (usize 8)) (usize 8))) in 
      let f a :=
      Ok ((auction_state_37, return_action_47, remaining_bid_48))
      in
      if (amnt_51) <.? (highest_bid_38) : bool
      then f ((let return_action_47 := match return_action_47 with
            | Accept => Accept
            | SimpleTransfer m_52 => SimpleTransfer (seq_concat (seq_concat (m_52) (addr_50)) (u64_to_be_bytes (amnt_51)))
            end in 
          (auction_state_37, return_action_47, remaining_bid_48)))
       else bind (let f a :=
        let auction_state_37 := Sold (addr_50) in 
        let remaining_bid_48 := BidSome (amnt_51) in 
        Ok ((auction_state_37, return_action_47, remaining_bid_48))
        in
        if  (match remaining_bid_48 with
          | BidNone => true
          | BidSome _ => false
          end) : bool
        then bind (match Err (BidMapError0)  : result (state × finalize_action
          ) _ with
           | Err a => Err a
           | Ok _ => Ok (tt)
          end) f
         else f (tt)) f in
      foldi (usize 0) ((seq_len ((m0_41))) / (usize 32)) (fun x y => result_bind y (f x))
      (Ok (auction_state_37, return_action_47, BidNone))) with
    | Err e => Err e
    | Ok (auction_state_37, return_action_47, remaining_bid_48) => 
    let result_43 := match remaining_bid_48 with
      | BidSome amount_53 => (if (negb ((amount_53) =.? (highest_bid_38))):bool then (Err (BidMapError1)) else (Ok ((
              State ((
                  auction_state_37,
                  highest_bid_38,
                  st2_39,
                  expiry_40,
                  SeqMap (((m0_41), (m1_42)))
                )),
              return_action_47
            ))))
      | BidNone => Err (BidMapError2)
      end in 
    match (result_43)  : result (state × finalize_action) _ with
     | Err a => Err a
     | Ok _ => Ok ((auction_state_37, result_43))
    end end) f
   else f ((auction_state_37, result_43))
  in
  if negb ((slot_time_44) >.? (expiry_40)) : bool
  then bind (match Err (AuctionStillActive)  : result (state × finalize_action
    ) _ with
     | Err a => Err a
     | Ok _ => Ok (tt)
    end) f
   else f (tt)
  in
  if negb ((auction_state_37) =.? (NotSoldYet)) : bool
  then bind (match Err (AuctionFinalized)  : result (state × finalize_action
    ) _ with
     | Err a => Err a
     | Ok _ => Ok (tt)
    end) f
   else f (tt).

Definition auction_test_init
  (item_54 : public_byte_seq)
  (time_55 : int64)
  : bool :=
  (fresh_state ((item_54)) (time_55)) =.? (State ((
        NotSoldYet,
        @repr WORDSIZE64 0,
        (item_54),
        time_55,
        SeqMap ((
            seq_new_ (@repr WORDSIZE8 0) (usize 0),
            seq_new_ (@repr WORDSIZE8 0) (usize 0)
          ))
      ))).
Theorem ensures_auction_test_init : forall result (item : public_byte_seq) (time : int64),
auction_test_init item time = result ->
 (result) = (true).
Proof. Admitted.
(* QuickChick (forAll g_public_byte_seq (fun item_54 : public_byte_seq => *)
(*   forAll g_int64 (fun time_55 : int64 => *)
(*   auction_test_init item_54 time_55))). *)


Theorem auction_test_init_correct : forall item_54 : public_byte_seq ,forall time_55 : int64 ,auction_test_init item_54 time_55 = true.
Proof. Admitted.


Definition verify_bid
  (item_56 : public_byte_seq)
  (state_57 : state)
  (account_58 : user_address)
  (ctx_59 : context)
  (amount_60 : int64)
  (bid_map_61 : seq_map)
  (highest_bid_62 : int64)
  (time_63 : int64)
  : (state × seq_map × bool × bool) :=
  let t_64 : (result state bid_error) :=
    auction_bid (ctx_59) (amount_60) ((state_57)) in 
  let '(state_65, res_66) := match t_64 with
    | Err e_67 => (state_57, false)
    | Ok s_68 => (s_68, true)
    end in 
  let bid_map_69 : seq_map :=
    match seq_map_update_entry ((bid_map_61)) (account_58) (highest_bid_62) with
    | Update (_, updated_map_70) => updated_map_70
    end in 
  (
    (state_65),
    (bid_map_69),
    res_66,
    ((state_65)) =.? (State ((
          NotSoldYet,
          highest_bid_62,
          (item_56),
          time_63,
          (bid_map_69)
        )))
  ).

(* Theorem verify_bid_correct : forall item_56 : public_byte_seq ,forall state_57 : state ,forall account_58 : user_address ,forall ctx_59 : context ,forall amount_60 : int64 ,forall bid_map_61 : seq_map ,forall highest_bid_62 : int64 ,forall time_63 : int64 ,verify_bid item_56 state_57 account_58 ctx_59 amount_60 bid_map_61 highest_bid_62 time_63 = true. *)
(* Proof. Admitted. *)


Definition test_auction_bid_and_finalize (item_71 : public_byte_seq) :=
  let time_72 : int64 := @repr WORDSIZE64 1 in 
  let amount_73 : int64 := @repr WORDSIZE64 100 in 
  let winning_amount_74 : int64 := @repr WORDSIZE64 300 in 
  let big_amount_75 : int64 := @repr WORDSIZE64 500 in 
  let bid_map_76 : seq_map := SeqMap ((
        seq_new_ (@repr WORDSIZE8 0) (usize 0),
        seq_new_ (@repr WORDSIZE8 0) (usize 0)
      )) in 
  let state_77 : state := fresh_state ((item_71)) (time_72) in 
  let alice_78 : user_address := array_from_list int8 (let l := [
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
  let alice_ctx_79 : (int64 × user_address_set) := (
      time_72,
      UserAddressSome (alice_78)
    ) in 
  let '(state_80, bid_map_81, res_0_82, result_0_83) :=
    verify_bid ((item_71)) (state_77) (alice_78) (alice_ctx_79) (amount_73) (bid_map_76) (amount_73) (time_72) in 
  let '(state_84, bid_map_85, res_1_86, result_1_87) :=
    verify_bid ((item_71)) (state_80) (alice_78) (alice_ctx_79) (amount_73) (bid_map_81) ((amount_73) .+ (amount_73)) (time_72) in 
  let bob_88 : user_address := array_from_list int8 (let l := [
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1
        ] in  l) in 
  let bob_ctx_89 : (int64 × user_address_set) := (
      time_72,
      UserAddressSome (bob_88)
    ) in 
  let '(state_90, bid_map_91, res_2_92, result_2_93) :=
    verify_bid ((item_71)) (state_84) (bob_88) (bob_ctx_89) (winning_amount_74) (bid_map_85) (winning_amount_74) (time_72) in 
  let owner_94 : user_address := array_from_list int8 (let l := [
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
  let balance_95 : int64 := @repr WORDSIZE64 100 in 
  let ctx4_96 : (int64 × user_address × int64) := (
      @repr WORDSIZE64 1,
      owner_94,
      balance_95
    ) in 
  let finres_97 : (result (state × finalize_action) finalize_error) :=
    auction_finalize (ctx4_96) ((state_90)) in 
  let '(state_98, result_3_99) := match finres_97 with
    | Err err_100 => ((state_90), (err_100) =.? (AuctionStillActive))
    | Ok (state_101, _) => (state_101, false)
    end in 
  let carol_102 : user_address := array_from_list int8 (let l := [
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 2
        ] in  l) in 
  let carol_ctx_103 : (int64 × user_address_set) := (
      time_72,
      UserAddressSome (carol_102)
    ) in 
  let ctx5_104 : (int64 × user_address × int64) := (
      (time_72) .+ (@repr WORDSIZE64 1),
      carol_102,
      winning_amount_74
    ) in 
  let finres2_105 : (result (state × finalize_action) finalize_error) :=
    auction_finalize (ctx5_104) ((state_98)) in 
  let '(state_106, result_4_107) := match finres2_105 with
    | Err _ => ((state_98), false)
    | Ok (state_108, action_109) => (
      state_108,
      (action_109) =.? (SimpleTransfer (seq_concat (seq_concat (seq_concat (seq_concat (seq_new_ (@repr WORDSIZE8 0) (usize 0)) (carol_102)) (u64_to_be_bytes (winning_amount_74))) (alice_78)) (u64_to_be_bytes ((amount_73) .+ (amount_73)))))
    )
    end in 
  let result_5_110 : bool := ((state_106)) =.? (State ((
          Sold (bob_88),
          winning_amount_74,
          (item_71),
          @repr WORDSIZE64 1,
          (bid_map_91)
        ))) in 
  let finres3_111 : (result (state × finalize_action) finalize_error) :=
    auction_finalize (ctx5_104) ((state_106)) in 
  let '(state_112, result_6_113) := match finres3_111 with
    | Err err_114 => (state_106, (err_114) =.? (AuctionFinalized))
    | Ok (state_115, action_116) => (state_115, false)
    end in 
  (result_4_107, finres2_105, (ctx5_104), (state_98)).


Compute test_auction_bid_and_finalize [] .
Compute auction_finalize (repr 2, array_from_list int8 [
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1;
          @repr WORDSIZE8 1
        ], repr 3)
       (State
         (NotSoldYet, repr 30000000000000000, [],
         repr 1,
         SeqMap ([repr 10 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0], [repr 40 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 0 ;repr 20 ;repr 10]))).

Theorem ensures_test_auction_bid_and_finalize : forall result (item : public_byte_seq),
test_auction_bid_and_finalize item = result ->
 (result) = (true).
Proof. Admitted.

Theorem test_auction_bid_and_finalize_correct : forall item_71 : public_byte_seq ,test_auction_bid_and_finalize item_71 = true.
Proof. Admitted.


