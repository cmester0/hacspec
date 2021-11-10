(** This file was automatically generated using Hacspec **)
From QuickChick Require Import QuickChick.
QuickChick true.
  
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

#[global] Instance eq_dec_auction_state : EqDec (auction_state) :=
Build_EqDec (auction_state) (eqb_auction_state) (eqb_leibniz_auction_state) (eqb_leibniz'_auction_state).

 #[global] Instance show_auction_state : Show (auction_state) :=
  @Build_Show (auction_state) (fun x =>
 match x with
 NotSoldYet => "NotSoldYet"%string
 | Sold a => append "Sold"%string (show a)
 end).
Definition g_auction_state : G (auction_state) := oneOf_ (returnGen NotSoldYet) [returnGen NotSoldYet;bindGen arbitrary (fun a => returnGen (Sold a))].
#[global] Instance gen_auction_state : Gen (auction_state) := Build_Gen auction_state g_auction_state.


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

#[global] Instance eq_dec_seq_map : EqDec (seq_map) :=
Build_EqDec (seq_map) (eqb_seq_map) (eqb_leibniz_seq_map) (eqb_leibniz'_seq_map).

 #[global] Instance show_seq_map : Show (seq_map) :=
  @Build_Show (seq_map) (fun x =>
 match x with
 SeqMap a => append "SeqMap"%string (show a)
 end).
Definition g_seq_map : G (seq_map) := oneOf_ (bindGen arbitrary (fun a => returnGen (SeqMap a))) [bindGen arbitrary (fun a => returnGen (SeqMap a))].
#[global] Instance gen_seq_map : Gen (seq_map) := Build_Gen seq_map g_seq_map.


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

#[global] Instance eq_dec_state : EqDec (state) :=
Build_EqDec (state) (eqb_state) (eqb_leibniz_state) (eqb_leibniz'_state).

 #[global] Instance show_state : Show (state) :=
  @Build_Show (state) (fun x =>
 match x with
 State a => append "State"%string (show a)
 end).
Definition g_state : G (state) := oneOf_ (bindGen arbitrary (fun a => returnGen (State a))) [bindGen arbitrary (fun a => returnGen (State a))].
#[global] Instance gen_state : Gen (state) := Build_Gen state g_state.


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

#[global] Instance eq_dec_map_entry : EqDec (map_entry) :=
Build_EqDec (map_entry) (eqb_map_entry) (eqb_leibniz_map_entry) (eqb_leibniz'_map_entry).

 #[global] Instance show_map_entry : Show (map_entry) :=
  @Build_Show (map_entry) (fun x =>
 match x with
 Entry a => append "Entry"%string (show a)
 end).
Definition g_map_entry : G (map_entry) := oneOf_ (bindGen arbitrary (fun a => returnGen (Entry a))) [bindGen arbitrary (fun a => returnGen (Entry a))].
#[global] Instance gen_map_entry : Gen (map_entry) := Build_Gen map_entry g_map_entry.


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

#[global] Instance eq_dec_map_update : EqDec (map_update) :=
Build_EqDec (map_update) (eqb_map_update) (eqb_leibniz_map_update) (eqb_leibniz'_map_update).

 #[global] Instance show_map_update : Show (map_update) :=
  @Build_Show (map_update) (fun x =>
 match x with
 Update a => append "Update"%string (show a)
 end).
Definition g_map_update : G (map_update) := oneOf_ (bindGen arbitrary (fun a => returnGen (Update a))) [bindGen arbitrary (fun a => returnGen (Update a))].
#[global] Instance gen_map_update : Gen (map_update) := Build_Gen map_update g_map_update.


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

#[global] Instance eq_dec_bid_error : EqDec (bid_error) :=
Build_EqDec (bid_error) (eqb_bid_error) (eqb_leibniz_bid_error) (eqb_leibniz'_bid_error).

 #[global] Instance show_bid_error : Show (bid_error) :=
  @Build_Show (bid_error) (fun x =>
 match x with
 ContractSender => "ContractSender"%string
 | BidTooLow => "BidTooLow"%string
 | BidsOverWaitingForAuctionFinalization => "BidsOverWaitingForAuctionFinalization"%string
 | AuctionIsFinalized => "AuctionIsFinalized"%string
 end).
Definition g_bid_error : G (bid_error) := oneOf_ (returnGen ContractSender) [returnGen ContractSender;returnGen BidTooLow;returnGen BidsOverWaitingForAuctionFinalization;returnGen AuctionIsFinalized].
#[global] Instance gen_bid_error : Gen (bid_error) := Build_Gen bid_error g_bid_error.


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

#[global] Instance eq_dec_user_address_set : EqDec (user_address_set) :=
Build_EqDec (user_address_set) (eqb_user_address_set) (eqb_leibniz_user_address_set) (eqb_leibniz'_user_address_set).

 #[global] Instance show_user_address_set : Show (user_address_set) :=
  @Build_Show (user_address_set) (fun x =>
 match x with
 UserAddressSome a => append "UserAddressSome"%string (show a)
 | UserAddressNone => "UserAddressNone"%string
 end).
Definition g_user_address_set : G (user_address_set) := oneOf_ (bindGen arbitrary (fun a => returnGen (UserAddressSome a))) [bindGen arbitrary (fun a => returnGen (UserAddressSome a));returnGen UserAddressNone].
#[global] Instance gen_user_address_set : Gen (user_address_set) := Build_Gen user_address_set g_user_address_set.


Notation "'context'" := ((int64 × user_address_set)) : hacspec_scope.
#[global] Instance show_context : Show (context) :=
Build_Show context (fun x =>
  let (x, x0) := x in
  append ("("%string) (append (show x) (append (","%string) (append (show x0) (")"%string))))).
Definition g_context : G (context) :=
bindGen arbitrary (fun x0 : int64 =>
  bindGen arbitrary (fun x1 : user_address_set =>
  returnGen (x0,x1))).
#[global] Instance gen_context : Gen (context) := Build_Gen context g_context.


Notation "'auction_bid_result'" := ((result state bid_error)) : hacspec_scope.

Definition auction_bid
  (ctx_15 : context)
  (amount_16 : int64)
  (state_17 : state)
  : auction_bid_result :=
  let 'State ((auction_state_18, highest_bid_19, st2_20, expiry_21, st4_22)) :=
    (state_17) in 
  ifbnd negb ((auction_state_18) =.? (NotSoldYet)) : bool
  thenbnd (match Err (AuctionIsFinalized)  : result state _ with
     | Err a => Err a
     | Ok _ => Ok (tt)
    end)
  else (tt) >> (fun 'tt =>
  let '(slot_time_23, sender_24) := ctx_15 in 
  ifbnd negb ((slot_time_23) <=.? (expiry_21)) : bool
  thenbnd (match Err (BidsOverWaitingForAuctionFinalization)  : result state _ with
     | Err a => Err a
     | Ok _ => Ok (tt)
    end)
  else (tt) >> (fun 'tt =>
  ifbnd (sender_24) =.? (UserAddressNone) : bool
  thenbnd (match Err (ContractSender)  : result state _ with
     | Err a => Err a
     | Ok _ => Ok (tt)
    end)
  else (tt) >> (fun 'tt =>
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
  ifbnd negb ((updated_bid_31) >.? (highest_bid_19)) : bool
  thenbnd (match Err (BidTooLow)  : result state _ with
     | Err a => Err a
     | Ok _ => Ok (tt)
    end)
  else (tt) >> (fun 'tt =>
  Ok (State ((
        auction_state_18,
        updated_bid_31,
        st2_20,
        expiry_21,
        updated_map_32
      ))))))).

Notation "'finalize_context'" := ((int64 × user_address × int64
)) : hacspec_scope.
#[global] Instance show_finalize_context : Show (finalize_context) :=
Build_Show finalize_context (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  append ("("%string) (append (show x) (append (","%string) (append (show x0) (append (","%string) (append (show x1) (")"%string))))))).
Definition g_finalize_context : G (finalize_context) :=
bindGen arbitrary (fun x0 : int64 =>
  bindGen arbitrary (fun x1 : user_address =>
  bindGen arbitrary (fun x2 : int64 =>
  returnGen (x0,x1,x2)))).
#[global] Instance gen_finalize_context : Gen (finalize_context) := Build_Gen finalize_context g_finalize_context.


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

#[global] Instance eq_dec_finalize_error : EqDec (finalize_error) :=
Build_EqDec (finalize_error) (eqb_finalize_error) (eqb_leibniz_finalize_error) (eqb_leibniz'_finalize_error).

 #[global] Instance show_finalize_error : Show (finalize_error) :=
  @Build_Show (finalize_error) (fun x =>
 match x with
 BidMapError => "BidMapError"%string
 | AuctionStillActive => "AuctionStillActive"%string
 | AuctionFinalized => "AuctionFinalized"%string
 end).
Definition g_finalize_error : G (finalize_error) := oneOf_ (returnGen BidMapError) [returnGen BidMapError;returnGen AuctionStillActive;returnGen AuctionFinalized].
#[global] Instance gen_finalize_error : Gen (finalize_error) := Build_Gen finalize_error g_finalize_error.


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

#[global] Instance eq_dec_finalize_action : EqDec (finalize_action) :=
Build_EqDec (finalize_action) (eqb_finalize_action) (eqb_leibniz_finalize_action) (eqb_leibniz'_finalize_action).

 #[global] Instance show_finalize_action : Show (finalize_action) :=
  @Build_Show (finalize_action) (fun x =>
 match x with
 Accept => "Accept"%string
 | SimpleTransfer a => append "SimpleTransfer"%string (show a)
 end).
Definition g_finalize_action : G (finalize_action) := oneOf_ (returnGen Accept) [returnGen Accept;bindGen arbitrary (fun a => returnGen (SimpleTransfer a))].
#[global] Instance gen_finalize_action : Gen (finalize_action) := Build_Gen finalize_action g_finalize_action.


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

#[global] Instance eq_dec_bid_remain : EqDec (bid_remain) :=
Build_EqDec (bid_remain) (eqb_bid_remain) (eqb_leibniz_bid_remain) (eqb_leibniz'_bid_remain).

 #[global] Instance show_bid_remain : Show (bid_remain) :=
  @Build_Show (bid_remain) (fun x =>
 match x with
 BidNone => "BidNone"%string
 | BidSome a => append "BidSome"%string (show a)
 end).
Definition g_bid_remain : G (bid_remain) := oneOf_ (returnGen BidNone) [returnGen BidNone;bindGen arbitrary (fun a => returnGen (BidSome a))].
#[global] Instance gen_bid_remain : Gen (bid_remain) := Build_Gen bid_remain g_bid_remain.


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
  ifbnd negb ((auction_state_37) =.? (NotSoldYet)) : bool
  thenbnd (match Err (AuctionFinalized)  : result (state × finalize_action
    ) _ with
     | Err a => Err a
     | Ok _ => Ok (tt)
    end)
  else (tt) >> (fun 'tt =>
  let '(slot_time_44, owner_45, balance_46) := ctx_35 in 
  ifbnd negb ((slot_time_44) >.? (expiry_40)) : bool
  thenbnd (match Err (AuctionStillActive)  : result (state × finalize_action
    ) _ with
     | Err a => Err a
     | Ok _ => Ok (tt)
    end)
  else (tt) >> (fun 'tt =>
  ifbnd (balance_46) !=.? (@repr WORDSIZE64 0) : bool
  thenbnd (let return_action_47 : finalize_action :=
      SimpleTransfer (seq_concat (seq_concat (seq_new_ (@repr WORDSIZE8 0) (usize 0)) (owner_45)) (u64_to_be_bytes (highest_bid_38))) in 
    let remaining_bid_48 : bid_remain := BidNone in 
    match (foldibnd (usize 0) to ((seq_len ((m0_41))) / (usize 32)) for (
        auction_state_37,
        return_action_47,
        remaining_bid_48
      )>> (fun x_49 '(auction_state_37, return_action_47, remaining_bid_48) =>
      let addr_50 : user_address :=
        array_from_seq (32) (seq_slice ((m0_41)) ((x_49) * (usize 32)) (usize 32)) in 
      let amnt_51 : int64 :=
        u64_from_be_bytes (array_from_seq (8) (seq_slice ((m1_42)) ((x_49) * (usize 8)) (usize 8))) in 
      ifbnd (amnt_51) <.? (highest_bid_38) : bool
      then (let return_action_47 := match return_action_47 with
          | Accept => Accept
          | SimpleTransfer m_52 => SimpleTransfer (seq_concat (seq_concat (m_52) (addr_50)) (u64_to_be_bytes (amnt_51)))
          end in 
        (auction_state_37, return_action_47, remaining_bid_48))
      elsebnd(ifbnd negb ((remaining_bid_48) =.? (BidNone)) : bool
        thenbnd (match Err (BidMapError)  : result (state × finalize_action
          ) _ with
           | Err a => Err a
           | Ok _ => Ok (tt)
          end)
        else (tt) >> (fun 'tt =>
        let auction_state_37 := Sold (addr_50) in 
        let remaining_bid_48 := BidSome (amnt_51) in 
        Ok ((auction_state_37, return_action_47, remaining_bid_48)))) >> (fun '(
        auction_state_37,
        return_action_47,
        remaining_bid_48
      ) =>
      Ok ((auction_state_37, return_action_47, remaining_bid_48))))) with
    | Err e => Err e
    | Ok (auction_state_37, return_action_47, remaining_bid_48) => 
    let result_43 := match remaining_bid_48 with
      | BidSome amount_53 => (if (negb ((amount_53) =.? (highest_bid_38))):bool then (Err (BidMapError)) else (Ok ((
              State ((
                  auction_state_37,
                  highest_bid_38,
                  st2_39,
                  expiry_40,
                  SeqMap (((m0_41), (m1_42)))
                )),
              return_action_47
            ))))
      | BidNone => Err (BidMapError)
      end in 
    match (result_43)  : result (state × finalize_action) _ with
     | Err a => Err a
     | Ok _ => Ok ((auction_state_37, result_43))
    end end)
  else ((auction_state_37, result_43)) >> (fun '(auction_state_37, result_43) =>
  result_43))).

Definition auction_item
  (a_54 : int64)
  (b_55 : int64)
  (c_56 : int64)
  : public_byte_seq :=
  seq_new_ (@repr WORDSIZE8 0) (usize 0).

Definition auction_test_init (item_57 : public_byte_seq) : bool :=
  let time_58 : int64 := @repr WORDSIZE64 1 in 
  (fresh_state ((item_57)) (time_58)) =.? (State ((
        NotSoldYet,
        @repr WORDSIZE64 0,
        (item_57),
        time_58,
        SeqMap ((
            seq_new_ (@repr WORDSIZE8 0) (usize 0),
            seq_new_ (@repr WORDSIZE8 0) (usize 0)
          ))
      ))).
Theorem ensures_auction_test_init : forall result (item : public_byte_seq),
auction_test_init item = result ->
(item) = (auction_item (repr 0) (repr 1) (repr 2))->(result) = (true).
Proof. Admitted.
QuickChick (forAll g_public_byte_seq (fun item_57 : public_byte_seq =>
  auction_test_init item_57)).


Definition verify_bid
  (item_59 : public_byte_seq)
  (state_60 : state)
  (account_61 : user_address)
  (ctx_62 : context)
  (amount_63 : int64)
  (bid_map_64 : seq_map)
  (highest_bid_65 : int64)
  (time_66 : int64)
  : (state × seq_map × bool × bool) :=
  let t_67 : (result state bid_error) :=
    auction_bid (ctx_62) (amount_63) ((state_60)) in 
  let '(state_68, res_69) := match t_67 with
    | Err e_70 => (state_60, false)
    | Ok s_71 => (s_71, true)
    end in 
  let bid_map_72 : seq_map :=
    match seq_map_update_entry ((bid_map_64)) (account_61) (highest_bid_65) with
    | Update (_, updated_map_73) => updated_map_73
    end in 
  (
    (state_68),
    (bid_map_72),
    res_69,
    ((state_68)) =.? (State ((
          NotSoldYet,
          highest_bid_65,
          (item_59),
          time_66,
          (bid_map_72)
        )))
  ).

Definition test_auction_bid_and_finalize  : bool :=
  let item_74 : seq int8 := seq_new_ (@repr WORDSIZE8 0) (usize 0) in 
  let time_75 : int64 := @repr WORDSIZE64 1 in 
  let amount_76 : int64 := @repr WORDSIZE64 100 in 
  let winning_amount_77 : int64 := @repr WORDSIZE64 300 in 
  let big_amount_78 : int64 := @repr WORDSIZE64 500 in 
  let bid_map_79 : seq_map := SeqMap ((
        seq_new_ (@repr WORDSIZE8 0) (usize 0),
        seq_new_ (@repr WORDSIZE8 0) (usize 0)
      )) in 
  let state_80 : state := fresh_state ((item_74)) (time_75) in 
  let alice_81 : user_address := array_from_list int8 (let l := [
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
  let alice_ctx_82 : (int64 × user_address_set) := (
      time_75,
      UserAddressSome (alice_81)
    ) in 
  let '(state_83, bid_map_84, res_0_85, result_0_86) :=
    verify_bid ((item_74)) (state_80) (alice_81) (alice_ctx_82) (amount_76) (bid_map_79) (amount_76) (time_75) in 
  let '(state_87, bid_map_88, res_1_89, result_1_90) :=
    verify_bid ((item_74)) (state_83) (alice_81) (alice_ctx_82) (amount_76) (bid_map_84) ((amount_76) .+ (amount_76)) (time_75) in 
  let bob_91 : user_address := array_from_list int8 (let l := [
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
  let bob_ctx_92 : (int64 × user_address_set) := (
      time_75,
      UserAddressSome (bob_91)
    ) in 
  let '(state_93, bid_map_94, res_2_95, result_2_96) :=
    verify_bid ((item_74)) (state_87) (bob_91) (bob_ctx_92) (winning_amount_77) (bid_map_88) (winning_amount_77) (time_75) in 
  let owner_97 : user_address := array_from_list int8 (let l := [
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
  let balance_98 : int64 := @repr WORDSIZE64 100 in 
  let ctx4_99 : (int64 × user_address × int64) := (
      @repr WORDSIZE64 1,
      owner_97,
      balance_98
    ) in 
  let finres_100 : (result (state × finalize_action) finalize_error) :=
    auction_finalize (ctx4_99) ((state_93)) in 
  let '(state_101, result_3_102) := match finres_100 with
    | Err err_103 => ((state_93), (err_103) =.? (AuctionStillActive))
    | Ok (state_104, _) => (state_104, false)
    end in 
  let carol_105 : user_address := array_from_list int8 (let l := [
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
  let carol_ctx_106 : (int64 × user_address_set) := (
      time_75,
      UserAddressSome (carol_105)
    ) in 
  let ctx5_107 : (int64 × user_address × int64) := (
      (time_75) .+ (@repr WORDSIZE64 1),
      carol_105,
      winning_amount_77
    ) in 
  let finres2_108 : (result (state × finalize_action) finalize_error) :=
    auction_finalize (ctx5_107) ((state_101)) in 
  let '(state_109, result_4_110) := match finres2_108 with
    | Err _ => ((state_101), false)
    | Ok (state_111, action_112) => (
      state_111,
      (action_112) =.? (SimpleTransfer (seq_concat (seq_concat (seq_concat (seq_concat (seq_new_ (@repr WORDSIZE8 0) (usize 0)) (carol_105)) (u64_to_be_bytes (winning_amount_77))) (alice_81)) (u64_to_be_bytes ((amount_76) .+ (amount_76)))))
    )
    end in 
  let result_5_113 : bool := ((state_109)) =.? (State ((
          Sold (bob_91),
          winning_amount_77,
          (item_74),
          @repr WORDSIZE64 1,
          (bid_map_94)
        ))) in 
  let finres3_114 : (result (state × finalize_action) finalize_error) :=
    auction_finalize (ctx5_107) ((state_109)) in 
  let '(state_115, result_6_116) := match finres3_114 with
    | Err err_117 => (state_109, (err_117) =.? (AuctionFinalized))
    | Ok (state_118, action_119) => (state_118, false)
    end in 
  let t_120 : (result state bid_error) :=
    auction_bid (bob_ctx_92) (big_amount_78) ((state_115)) in 
  let result_7_121 : bool := match t_120 with
    | Err e_122 => (e_122) =.? (AuctionIsFinalized)
    | Ok _ => false
    end in 
  (((((((result_0_86) && (result_1_90)) && (result_2_96)) && (result_3_102)) && (result_4_110)) && (result_5_113)) && (result_6_116)) && (result_7_121).
Theorem ensures_test_auction_bid_and_finalize : forall result ,
test_auction_bid_and_finalize  = result ->
(result) = (true).
Proof. Admitted.

