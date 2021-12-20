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

Definition eqb_leibniz_auction_state (x y : auction_state) : eqb_auction_state x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_auction_state : EqDec (auction_state) :=
Build_EqDec (auction_state) (eqb_auction_state) (eqb_leibniz_auction_state).

Global Instance show_auction_state : Show (auction_state) :=
 @Build_Show (auction_state) (fun x =>
 match x with
 NotSoldYet => ("NotSoldYet")%string
 | Sold a => ("Sold" ++ show a)%string
 end).
Definition g_auction_state : G (auction_state) := oneOf_ (returnGen NotSoldYet) [returnGen NotSoldYet;bindGen arbitrary (fun a => returnGen (Sold a))].
Global Instance gen_auction_state : Gen (auction_state) := Build_Gen auction_state g_auction_state.

Inductive seq_map :=
| SeqMap : (public_byte_seq × public_byte_seq) -> seq_map.

Definition eqb_seq_map (x y : seq_map) : bool :=
match x with
   | SeqMap a => match y with | SeqMap b => a =.? b end
   end.

Definition eqb_leibniz_seq_map (x y : seq_map) : eqb_seq_map x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_seq_map : EqDec (seq_map) :=
Build_EqDec (seq_map) (eqb_seq_map) (eqb_leibniz_seq_map).

Global Instance show_seq_map : Show (seq_map) :=
 @Build_Show (seq_map) (fun x =>
 match x with
 SeqMap a => ("SeqMap" ++ show a)%string
 end).
Definition g_seq_map : G (seq_map) := oneOf_ (bindGen arbitrary (fun a => returnGen (SeqMap a))) [bindGen arbitrary (fun a => returnGen (SeqMap a))].
Global Instance gen_seq_map : Gen (seq_map) := Build_Gen seq_map g_seq_map.

Notation "'amount'" := (int64) : hacspec_scope.

Notation "'timestamp'" := (int64) : hacspec_scope.

Notation "'itemtyp'" := (public_byte_seq) : hacspec_scope.

Inductive state :=
| State : (auction_state × amount × itemtyp × timestamp × seq_map) -> state.

Definition eqb_state (x y : state) : bool :=
match x with
   | State a => match y with | State b => a =.? b end
   end.

Definition eqb_leibniz_state (x y : state) : eqb_state x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_state : EqDec (state) :=
Build_EqDec (state) (eqb_state) (eqb_leibniz_state).

Global Instance show_state : Show (state) :=
 @Build_Show (state) (fun x =>
 match x with
 State a => ("State" ++ show a)%string
 end).
Definition g_state : G (state) := oneOf_ (bindGen arbitrary (fun a => returnGen (State a))) [bindGen arbitrary (fun a => returnGen (State a))].
Global Instance gen_state : Gen (state) := Build_Gen state g_state.

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

Theorem ensures_fresh_state : forall result_2 (itm_0 : itemtyp) (exp_1 : int64),
@fresh_state itm_0 exp_1 = result_2 ->
true.
Proof. Admitted.

Definition seq_map_entry
  (m_3 : seq_map)
  (sender_address_4 : user_address)
  : (int64 × seq_map) :=
  let 'SeqMap ((m0_5, m1_6)) :=
    m_3 in 
  let res_7 : (int64 × seq_map) :=
    (
      @repr WORDSIZE64 0,
      SeqMap ((
          seq_concat ((m0_5)) (sender_address_4),
          seq_concat ((m1_6)) (u64_to_be_bytes (@repr WORDSIZE64 0))
        ))
    ) in 
  let res_7 :=
    foldi (usize 0) ((seq_len ((m0_5))) / (usize 32)) (fun x_8 res_7 =>
      let '(res_7) :=
        if (array_from_seq (32) (seq_slice ((m0_5)) ((x_8) * (usize 32)) (
              usize 32))) array_eq (sender_address_4):bool then (let res_7 :=
            (
              u64_from_be_bytes (array_from_seq (8) (seq_slice ((m1_6)) ((
                      x_8) * (usize 8)) (usize 8))),
              SeqMap (((m0_5), (m1_6)))
            ) in 
          (res_7)) else ((res_7)) in 
      (res_7))
    res_7 in 
  res_7.

Inductive map_update :=
| Update : (int64 × seq_map) -> map_update.

Definition eqb_map_update (x y : map_update) : bool :=
match x with
   | Update a => match y with | Update b => a =.? b end
   end.

Definition eqb_leibniz_map_update (x y : map_update) : eqb_map_update x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_map_update : EqDec (map_update) :=
Build_EqDec (map_update) (eqb_map_update) (eqb_leibniz_map_update).

Global Instance show_map_update : Show (map_update) :=
 @Build_Show (map_update) (fun x =>
 match x with
 Update a => ("Update" ++ show a)%string
 end).
Definition g_map_update : G (map_update) := oneOf_ (bindGen arbitrary (fun a => returnGen (Update a))) [bindGen arbitrary (fun a => returnGen (Update a))].
Global Instance gen_map_update : Gen (map_update) := Build_Gen map_update g_map_update.

Definition seq_map_update_entry
  (m_9 : seq_map)
  (sender_address_10 : user_address)
  (amount_11 : int64)
  : map_update :=
  let 'SeqMap ((m0_12, m1_13)) :=
    m_9 in 
  let res_14 : map_update :=
    Update ((
        amount_11,
        SeqMap ((
            seq_concat ((m0_12)) (sender_address_10),
            seq_concat ((m1_13)) (u64_to_be_bytes (amount_11))
          ))
      )) in 
  let res_14 :=
    foldi (usize 0) ((seq_len ((m0_12))) / (usize 32)) (fun x_15 res_14 =>
      let '(res_14) :=
        if (array_from_seq (32) (seq_slice ((m0_12)) ((x_15) * (usize 32)) (
              usize 32))) array_eq (sender_address_10):bool then (let res_14 :=
            Update ((
                amount_11,
                SeqMap ((
                    seq_update ((m0_12)) ((x_15) * (usize 32)) (
                      sender_address_10),
                    seq_update ((m1_13)) ((x_15) * (usize 8)) (u64_to_be_bytes (
                        amount_11))
                  ))
              )) in 
          (res_14)) else ((res_14)) in 
      (res_14))
    res_14 in 
  res_14.

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

Definition eqb_leibniz_bid_error (x y : bid_error) : eqb_bid_error x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_bid_error : EqDec (bid_error) :=
Build_EqDec (bid_error) (eqb_bid_error) (eqb_leibniz_bid_error).

Global Instance show_bid_error : Show (bid_error) :=
 @Build_Show (bid_error) (fun x =>
 match x with
 ContractSender => ("ContractSender")%string
 | BidTooLow => ("BidTooLow")%string
 | BidsOverWaitingForAuctionFinalization => (
   "BidsOverWaitingForAuctionFinalization")%string
 | AuctionIsFinalized => ("AuctionIsFinalized")%string
 end).
Definition g_bid_error : G (bid_error) := oneOf_ (returnGen ContractSender) [returnGen ContractSender;returnGen BidTooLow;returnGen BidsOverWaitingForAuctionFinalization;returnGen AuctionIsFinalized].
Global Instance gen_bid_error : Gen (bid_error) := Build_Gen bid_error g_bid_error.

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

Definition eqb_leibniz_user_address_set (x y : user_address_set) : eqb_user_address_set x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_user_address_set : EqDec (user_address_set) :=
Build_EqDec (user_address_set) (eqb_user_address_set) (eqb_leibniz_user_address_set).

Global Instance show_user_address_set : Show (user_address_set) :=
 @Build_Show (user_address_set) (fun x =>
 match x with
 UserAddressSome a => ("UserAddressSome" ++ show a)%string
 | UserAddressNone => ("UserAddressNone")%string
 end).
Definition g_user_address_set : G (user_address_set) := oneOf_ (bindGen arbitrary (fun a => returnGen (UserAddressSome a))) [bindGen arbitrary (fun a => returnGen (UserAddressSome a));returnGen UserAddressNone].
Global Instance gen_user_address_set : Gen (user_address_set) := Build_Gen user_address_set g_user_address_set.

Notation "'context'" := ((int64 × user_address_set)) : hacspec_scope.
Instance show_context : Show (context) :=
Build_Show context (fun x =>
  let (x, x0) := x in
  (("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ (")"))))))%string.
Definition g_context : G (context) :=
bindGen arbitrary (fun x0 : int64 =>
  bindGen arbitrary (fun x1 : user_address_set =>
  returnGen (x0,x1))).
Instance gen_context : Gen (context) := Build_Gen context g_context.

Notation "'auction_bid_result'" := ((result state bid_error)) : hacspec_scope.

Definition auction_bid
  (ctx_16 : context)
  (amount_17 : int64)
  (state_18 : state)
  : auction_bid_result :=
  let 'State ((auction_state_19, highest_bid_20, st2_21, expiry_22, st4_23)) :=
    (state_18) in 
  ifbnd negb ((auction_state_19) =.? (NotSoldYet)) : bool
  thenbnd (bind (@Err state bid_error (AuctionIsFinalized)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let '(slot_time_24, sender_25) :=
    ctx_16 in 
  ifbnd negb ((slot_time_24) <=.? (expiry_22)) : bool
  thenbnd (bind (@Err state bid_error (BidsOverWaitingForAuctionFinalization)) (
      fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  ifbnd (sender_25) =.? (UserAddressNone) : bool
  thenbnd (bind (@Err state bid_error (ContractSender)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let sender_address_26 : user_address :=
    match sender_25 with
    | UserAddressNone => array_from_list int8 (let l :=
        [
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
    | UserAddressSome account_address_27 => account_address_27
    end in 
  let '(bid_to_update_28, new_map_29) :=
    seq_map_entry ((st4_23)) (sender_address_26) in 
  let '(updated_bid_30, updated_map_31) :=
    match seq_map_update_entry ((st4_23)) (sender_address_26) ((
        bid_to_update_28) .+ (amount_17)) with
    | Update (updated_bid_32, updated_map_33) => (updated_bid_32, updated_map_33
    )
    end in 
  ifbnd negb ((updated_bid_30) >.? (highest_bid_20)) : bool
  thenbnd (bind (@Err state bid_error (BidTooLow)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  @Ok state bid_error (State ((
        auction_state_19,
        updated_bid_30,
        st2_21,
        expiry_22,
        updated_map_31
      ))))))).

Notation "'finalize_context'" := ((int64 × user_address × int64
)) : hacspec_scope.
Instance show_finalize_context : Show (finalize_context) :=
Build_Show finalize_context (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
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

Definition eqb_leibniz_finalize_error (x y : finalize_error) : eqb_finalize_error x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_finalize_error : EqDec (finalize_error) :=
Build_EqDec (finalize_error) (eqb_finalize_error) (eqb_leibniz_finalize_error).

Global Instance show_finalize_error : Show (finalize_error) :=
 @Build_Show (finalize_error) (fun x =>
 match x with
 BidMapError => ("BidMapError")%string
 | AuctionStillActive => ("AuctionStillActive")%string
 | AuctionFinalized => ("AuctionFinalized")%string
 end).
Definition g_finalize_error : G (finalize_error) := oneOf_ (returnGen BidMapError) [returnGen BidMapError;returnGen AuctionStillActive;returnGen AuctionFinalized].
Global Instance gen_finalize_error : Gen (finalize_error) := Build_Gen finalize_error g_finalize_error.

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

Definition eqb_leibniz_finalize_action (x y : finalize_action) : eqb_finalize_action x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_finalize_action : EqDec (finalize_action) :=
Build_EqDec (finalize_action) (eqb_finalize_action) (eqb_leibniz_finalize_action).

Global Instance show_finalize_action : Show (finalize_action) :=
 @Build_Show (finalize_action) (fun x =>
 match x with
 Accept => ("Accept")%string
 | SimpleTransfer a => ("SimpleTransfer" ++ show a)%string
 end).
Definition g_finalize_action : G (finalize_action) := oneOf_ (returnGen Accept) [returnGen Accept;bindGen arbitrary (fun a => returnGen (SimpleTransfer a))].
Global Instance gen_finalize_action : Gen (finalize_action) := Build_Gen finalize_action g_finalize_action.

Inductive bid_remain :=
| BidNone : bid_remain
| BidSome : int64 -> bid_remain.

Definition eqb_bid_remain (x y : bid_remain) : bool :=
match x with
   | BidNone => match y with | BidNone=> true | _ => false end
   | BidSome a => match y with | BidSome b => a =.? b | _ => false end
   end.

Definition eqb_leibniz_bid_remain (x y : bid_remain) : eqb_bid_remain x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_bid_remain : EqDec (bid_remain) :=
Build_EqDec (bid_remain) (eqb_bid_remain) (eqb_leibniz_bid_remain).

Global Instance show_bid_remain : Show (bid_remain) :=
 @Build_Show (bid_remain) (fun x =>
 match x with
 BidNone => ("BidNone")%string
 | BidSome a => ("BidSome" ++ show a)%string
 end).
Definition g_bid_remain : G (bid_remain) := oneOf_ (returnGen BidNone) [returnGen BidNone;bindGen arbitrary (fun a => returnGen (BidSome a))].
Global Instance gen_bid_remain : Gen (bid_remain) := Build_Gen bid_remain g_bid_remain.

Notation "'auction_finalize_result'" := ((result (state × finalize_action
  ) finalize_error)) : hacspec_scope.

Definition auction_finalize
  (ctx_34 : finalize_context)
  (state_35 : state)
  : auction_finalize_result :=
  let 'State ((
	auction_state_36,
	highest_bid_37,
	st2_38,
	expiry_39,
	SeqMap ((m0_40, m1_41))
      )) :=
    (state_35) in 
  let result_42 : (result (state × finalize_action) finalize_error) :=
    @Ok (state × finalize_action) finalize_error (((state_35), Accept)) in 
  ifbnd negb ((auction_state_36) =.? (NotSoldYet)) : bool
  thenbnd (bind (@Err (state × finalize_action) finalize_error (
	AuctionFinalized)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let '(slot_time_43, owner_44, balance_45) :=
    ctx_34 in 
  ifbnd negb ((slot_time_43) >.? (expiry_39)) : bool
  thenbnd (bind (@Err (state × finalize_action) finalize_error (
	AuctionStillActive)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  ifbnd (balance_45) !=.? (@repr WORDSIZE64 0) : bool
  thenbnd (let return_action_46 : finalize_action :=
      SimpleTransfer (seq_concat (seq_concat (seq_new_ (@repr WORDSIZE8 0) (
	      usize 0)) (owner_44)) (u64_to_be_bytes (highest_bid_37))) in 
    let remaining_bid_47 : bid_remain :=
      BidNone in 
    bind (foldibnd (usize 0) to ((seq_len ((m0_40))) / (usize 32)) for (
	auction_state_36,
	return_action_46,
	remaining_bid_47
      )>> (fun x_48 '(auction_state_36, return_action_46, remaining_bid_47) =>
      let addr_49 : user_address :=
	array_from_seq (32) (seq_slice ((m0_40)) ((x_48) * (usize 32)) (
	    usize 32)) in 
      let amnt_50 : int64 :=
	u64_from_be_bytes (array_from_seq (8) (seq_slice ((m1_41)) ((x_48) * (
		usize 8)) (usize 8))) in 
      ifbnd (amnt_50) <.? (highest_bid_37) : bool
      then (let return_action_46 :=
	  match return_action_46 with
	  | Accept => Accept
	  | SimpleTransfer m_51 => SimpleTransfer (seq_concat (seq_concat (
		m_51) (addr_49)) (u64_to_be_bytes (amnt_50)))
	  end in 
	(auction_state_36, return_action_46, remaining_bid_47))
      elsebnd(ifbnd negb ((remaining_bid_47) =.? (BidNone)) : bool
	thenbnd (bind (@Err (state × finalize_action) finalize_error (
	      BidMapError)) (fun _ => Ok (tt)))
	else (tt) >> (fun 'tt =>
	let auction_state_36 :=
	  Sold (addr_49) in 
	let remaining_bid_47 :=
	  BidSome (amnt_50) in 
	Ok ((auction_state_36, return_action_46, remaining_bid_47)))) >> (fun '(
	auction_state_36,
	return_action_46,
	remaining_bid_47
      ) =>
      Ok ((auction_state_36, return_action_46, remaining_bid_47))))) (fun '(
	auction_state_36,
	return_action_46,
	remaining_bid_47
      ) => let result_42 :=
	match remaining_bid_47 with
	| BidSome amount_52 => (if (negb ((amount_52) =.? (
		highest_bid_37))):bool then (@Err (state × finalize_action
	    ) finalize_error (BidMapError)) else (@Ok (state × finalize_action
	    ) finalize_error ((
		State ((
		    auction_state_36,
		    highest_bid_37,
		    st2_38,
		    expiry_39,
		    SeqMap (((m0_40), (m1_41)))
		  )),
		return_action_46
	      ))))
	| BidNone => @Err (state × finalize_action) finalize_error (
	  BidMapError)
	end in 
      bind ((result_42)) (fun _ => Ok ((auction_state_36, result_42)))))
  else ((auction_state_36, result_42)) >> (fun '(auction_state_36, result_42) =>
  result_42))).

Definition auction_test_init
  (item_53 : public_byte_seq)
  (time_54 : int64)
  : bool :=
  (fresh_state ((item_53)) (time_54)) =.? (State ((
        NotSoldYet,
        @repr WORDSIZE64 0,
        (item_53),
        time_54,
        SeqMap ((
            seq_new_ (@repr WORDSIZE8 0) (usize 0),
            seq_new_ (@repr WORDSIZE8 0) (usize 0)
          ))
      ))).

Theorem ensures_auction_test_init : forall result_2 (
  item_53 : public_byte_seq) (time_54 : int64),
@auction_test_init item_53 time_54 = result_2 ->
result_2 = true.
Proof. Admitted.

QuickChick (
  forAll g_public_byte_seq (fun item_53 : public_byte_seq =>forAll g_int64 (fun time_54 : int64 =>auction_test_init item_53 time_54))).

Definition verify_bid
  (item_55 : public_byte_seq)
  (state_56 : state)
  (account_57 : user_address)
  (ctx_58 : context)
  (amount_59 : int64)
  (bid_map_60 : seq_map)
  (highest_bid_61 : int64)
  (time_62 : int64)
  : (state × seq_map × bool × bool) :=
  let t_63 : (result state bid_error) :=
    auction_bid (ctx_58) (amount_59) ((state_56)) in 
  let '(state_64, res_65) :=
    match t_63 with
    | Err e_66 => (state_56, false)
    | Ok s_67 => (s_67, true)
    end in 
  let bid_map_68 : seq_map :=
    match seq_map_update_entry ((bid_map_60)) (account_57) (highest_bid_61) with
    | Update (_, updated_map_69) => updated_map_69
    end in 
  (
    (state_64),
    (bid_map_68),
    res_65,
    ((state_64)) =.? (State ((
          NotSoldYet,
          highest_bid_61,
          (item_55),
          time_62,
          (bid_map_68)
        )))
  ).

Definition useraddress_from_u8 (i_70 : int8) : user_address :=
  array_from_list int8 (let l :=
      [
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70
      ] in  l).

Definition new_account
  (time_71 : int64)
  (i_72 : int8)
  : (user_address × context) :=
  let addr_73 : user_address :=
    useraddress_from_u8 (i_72) in 
  let ctx_74 : (int64 × user_address_set) :=
    (time_71, UserAddressSome (addr_73)) in 
  (addr_73, ctx_74).

Definition test_auction_bid_and_finalize
  (item_75 : public_byte_seq)
  (time_76 : int64)
  (input_amount_77 : int64)
  : bool :=
  let amount_78 : int64 :=
    (input_amount_77) .+ (@repr WORDSIZE64 1) in 
  let winning_amount_79 : int64 :=
    (amount_78) .* (@repr WORDSIZE64 3) in 
  let big_amount_80 : int64 :=
    (amount_78) .* (@repr WORDSIZE64 5) in 
  let bid_map_81 : seq_map :=
    SeqMap ((
        seq_new_ (@repr WORDSIZE8 0) (usize 0),
        seq_new_ (@repr WORDSIZE8 0) (usize 0)
      )) in 
  let state_82 : state :=
    fresh_state ((item_75)) (time_76) in 
  let '(alice_83, alice_ctx_84) :=
    new_account (time_76) (@repr WORDSIZE8 0) in 
  let '(state_85, bid_map_86, res_0_87, result_0_88) :=
    verify_bid ((item_75)) (state_82) (alice_83) (alice_ctx_84) (amount_78) (
      bid_map_81) (amount_78) (time_76) in 
  let '(state_89, bid_map_90, res_1_91, result_1_92) :=
    verify_bid ((item_75)) (state_85) (alice_83) (alice_ctx_84) (amount_78) (
      bid_map_86) ((amount_78) .+ (amount_78)) (time_76) in 
  let '(bob_93, bob_ctx_94) :=
    new_account (time_76) (@repr WORDSIZE8 1) in 
  let '(state_95, bid_map_96, res_2_97, result_2_98) :=
    verify_bid ((item_75)) (state_89) (bob_93) (bob_ctx_94) (
      winning_amount_79) (bid_map_90) (winning_amount_79) (time_76) in 
  let owner_99 : user_address :=
    useraddress_from_u8 (@repr WORDSIZE8 0) in 
  let balance_100 : int64 :=
    @repr WORDSIZE64 100 in 
  let ctx4_101 : (int64 × user_address × int64) :=
    (time_76, owner_99, balance_100) in 
  let finres_102 : (result (state × finalize_action) finalize_error) :=
    auction_finalize (ctx4_101) ((state_95)) in 
  let '(state_103, result_3_104) :=
    match finres_102 with
    | Err err_105 => ((state_95), (err_105) =.? (AuctionStillActive))
    | Ok (state_106, _) => (state_106, false)
    end in 
  let '(carol_107, carol_ctx_108) :=
    new_account (time_76) (@repr WORDSIZE8 2) in 
  let ctx5_109 : (int64 × user_address × int64) :=
    ((time_76) .+ (@repr WORDSIZE64 1), carol_107, winning_amount_79) in 
  let finres2_110 : (result (state × finalize_action) finalize_error) :=
    auction_finalize (ctx5_109) ((state_103)) in 
  let '(state_111, result_4_112) :=
    match finres2_110 with
    | Err _ => ((state_103), false)
    | Ok (state_113, action_114) => (
      state_113,
      (action_114) =.? (SimpleTransfer (seq_concat (seq_concat (seq_concat (
                seq_concat (seq_new_ (@repr WORDSIZE8 0) (usize 0)) (
                  carol_107)) (u64_to_be_bytes (winning_amount_79))) (
              alice_83)) (u64_to_be_bytes ((amount_78) .+ (amount_78)))))
    )
    end in 
  let result_5_115 : bool :=
    ((state_111)) =.? (State ((
          Sold (bob_93),
          winning_amount_79,
          (item_75),
          time_76,
          (bid_map_96)
        ))) in 
  let finres3_116 : (result (state × finalize_action) finalize_error) :=
    auction_finalize (ctx5_109) ((state_111)) in 
  let '(state_117, result_6_118) :=
    match finres3_116 with
    | Err err_119 => (state_111, (err_119) =.? (AuctionFinalized))
    | Ok (state_120, action_121) => (state_120, false)
    end in 
  let t_122 : (result state bid_error) :=
    auction_bid (bob_ctx_94) (big_amount_80) ((state_117)) in 
  let result_7_123 : bool :=
    match t_122 with
    | Err e_124 => (e_124) =.? (AuctionIsFinalized)
    | Ok _ => false
    end in 
  (((((((result_0_88) && (result_1_92)) && (result_2_98)) && (
            result_3_104)) && (result_4_112)) && (result_5_115)) && (
      result_6_118)) && (result_7_123).

Theorem ensures_test_auction_bid_and_finalize : forall result_2 (
  item_75 : public_byte_seq) (time_76 : int64) (input_amount_77 : int64),
@test_auction_bid_and_finalize item_75 time_76 input_amount_77 = result_2 ->
result_2 = true.
Proof. Admitted.

QuickChick (
  forAll g_public_byte_seq (fun item_75 : public_byte_seq =>forAll g_int64 (fun time_76 : int64 =>forAll g_int64 (fun input_amount_77 : int64 =>test_auction_bid_and_finalize item_75 time_76 input_amount_77)))).

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

Definition eqb_leibniz_auction_state (x y : auction_state) : eqb_auction_state x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_auction_state : EqDec (auction_state) :=
Build_EqDec (auction_state) (eqb_auction_state) (eqb_leibniz_auction_state).

Global Instance show_auction_state : Show (auction_state) :=
 @Build_Show (auction_state) (fun x =>
 match x with
 NotSoldYet => ("NotSoldYet")%string
 | Sold a => ("Sold" ++ show a)%string
 end).
Definition g_auction_state : G (auction_state) := oneOf_ (returnGen NotSoldYet) [returnGen NotSoldYet;bindGen arbitrary (fun a => returnGen (Sold a))].
Global Instance gen_auction_state : Gen (auction_state) := Build_Gen auction_state g_auction_state.

Inductive seq_map :=
| SeqMap : (public_byte_seq × public_byte_seq) -> seq_map.

Definition eqb_seq_map (x y : seq_map) : bool :=
match x with
   | SeqMap a => match y with | SeqMap b => a =.? b end
   end.

Definition eqb_leibniz_seq_map (x y : seq_map) : eqb_seq_map x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_seq_map : EqDec (seq_map) :=
Build_EqDec (seq_map) (eqb_seq_map) (eqb_leibniz_seq_map).

Global Instance show_seq_map : Show (seq_map) :=
 @Build_Show (seq_map) (fun x =>
 match x with
 SeqMap a => ("SeqMap" ++ show a)%string
 end).
Definition g_seq_map : G (seq_map) := oneOf_ (bindGen arbitrary (fun a => returnGen (SeqMap a))) [bindGen arbitrary (fun a => returnGen (SeqMap a))].
Global Instance gen_seq_map : Gen (seq_map) := Build_Gen seq_map g_seq_map.

Notation "'amount'" := (int64) : hacspec_scope.

Notation "'timestamp'" := (int64) : hacspec_scope.

Notation "'itemtyp'" := (public_byte_seq) : hacspec_scope.

Inductive state :=
| State : (auction_state × amount × itemtyp × timestamp × seq_map) -> state.

Definition eqb_state (x y : state) : bool :=
match x with
   | State a => match y with | State b => a =.? b end
   end.

Definition eqb_leibniz_state (x y : state) : eqb_state x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_state : EqDec (state) :=
Build_EqDec (state) (eqb_state) (eqb_leibniz_state).

Global Instance show_state : Show (state) :=
 @Build_Show (state) (fun x =>
 match x with
 State a => ("State" ++ show a)%string
 end).
Definition g_state : G (state) := oneOf_ (bindGen arbitrary (fun a => returnGen (State a))) [bindGen arbitrary (fun a => returnGen (State a))].
Global Instance gen_state : Gen (state) := Build_Gen state g_state.

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

Theorem ensures_fresh_state : forall result_2 (itm_0 : itemtyp) (exp_1 : int64),
@fresh_state itm_0 exp_1 = result_2 ->
true.
Proof. Admitted.

Definition seq_map_entry
  (m_3 : seq_map)
  (sender_address_4 : user_address)
  : (int64 × seq_map) :=
  let 'SeqMap ((m0_5, m1_6)) :=
    m_3 in 
  let res_7 : (int64 × seq_map) :=
    (
      @repr WORDSIZE64 0,
      SeqMap ((
          seq_concat ((m0_5)) (sender_address_4),
          seq_concat ((m1_6)) (u64_to_be_bytes (@repr WORDSIZE64 0))
        ))
    ) in 
  let res_7 :=
    foldi (usize 0) ((seq_len ((m0_5))) / (usize 32)) (fun x_8 res_7 =>
      let '(res_7) :=
        if (array_from_seq (32) (seq_slice ((m0_5)) ((x_8) * (usize 32)) (
              usize 32))) array_eq (sender_address_4):bool then (let res_7 :=
            (
              u64_from_be_bytes (array_from_seq (8) (seq_slice ((m1_6)) ((
                      x_8) * (usize 8)) (usize 8))),
              SeqMap (((m0_5), (m1_6)))
            ) in 
          (res_7)) else ((res_7)) in 
      (res_7))
    res_7 in 
  res_7.

Inductive map_update :=
| Update : (int64 × seq_map) -> map_update.

Definition eqb_map_update (x y : map_update) : bool :=
match x with
   | Update a => match y with | Update b => a =.? b end
   end.

Definition eqb_leibniz_map_update (x y : map_update) : eqb_map_update x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_map_update : EqDec (map_update) :=
Build_EqDec (map_update) (eqb_map_update) (eqb_leibniz_map_update).

Global Instance show_map_update : Show (map_update) :=
 @Build_Show (map_update) (fun x =>
 match x with
 Update a => ("Update" ++ show a)%string
 end).
Definition g_map_update : G (map_update) := oneOf_ (bindGen arbitrary (fun a => returnGen (Update a))) [bindGen arbitrary (fun a => returnGen (Update a))].
Global Instance gen_map_update : Gen (map_update) := Build_Gen map_update g_map_update.

Definition seq_map_update_entry
  (m_9 : seq_map)
  (sender_address_10 : user_address)
  (amount_11 : int64)
  : map_update :=
  let 'SeqMap ((m0_12, m1_13)) :=
    m_9 in 
  let res_14 : map_update :=
    Update ((
        amount_11,
        SeqMap ((
            seq_concat ((m0_12)) (sender_address_10),
            seq_concat ((m1_13)) (u64_to_be_bytes (amount_11))
          ))
      )) in 
  let res_14 :=
    foldi (usize 0) ((seq_len ((m0_12))) / (usize 32)) (fun x_15 res_14 =>
      let '(res_14) :=
        if (array_from_seq (32) (seq_slice ((m0_12)) ((x_15) * (usize 32)) (
              usize 32))) array_eq (sender_address_10):bool then (let res_14 :=
            Update ((
                amount_11,
                SeqMap ((
                    seq_update ((m0_12)) ((x_15) * (usize 32)) (
                      sender_address_10),
                    seq_update ((m1_13)) ((x_15) * (usize 8)) (u64_to_be_bytes (
                        amount_11))
                  ))
              )) in 
          (res_14)) else ((res_14)) in 
      (res_14))
    res_14 in 
  res_14.

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

Definition eqb_leibniz_bid_error (x y : bid_error) : eqb_bid_error x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_bid_error : EqDec (bid_error) :=
Build_EqDec (bid_error) (eqb_bid_error) (eqb_leibniz_bid_error).

Global Instance show_bid_error : Show (bid_error) :=
 @Build_Show (bid_error) (fun x =>
 match x with
 ContractSender => ("ContractSender")%string
 | BidTooLow => ("BidTooLow")%string
 | BidsOverWaitingForAuctionFinalization => (
   "BidsOverWaitingForAuctionFinalization")%string
 | AuctionIsFinalized => ("AuctionIsFinalized")%string
 end).
Definition g_bid_error : G (bid_error) := oneOf_ (returnGen ContractSender) [returnGen ContractSender;returnGen BidTooLow;returnGen BidsOverWaitingForAuctionFinalization;returnGen AuctionIsFinalized].
Global Instance gen_bid_error : Gen (bid_error) := Build_Gen bid_error g_bid_error.

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

Definition eqb_leibniz_user_address_set (x y : user_address_set) : eqb_user_address_set x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_user_address_set : EqDec (user_address_set) :=
Build_EqDec (user_address_set) (eqb_user_address_set) (eqb_leibniz_user_address_set).

Global Instance show_user_address_set : Show (user_address_set) :=
 @Build_Show (user_address_set) (fun x =>
 match x with
 UserAddressSome a => ("UserAddressSome" ++ show a)%string
 | UserAddressNone => ("UserAddressNone")%string
 end).
Definition g_user_address_set : G (user_address_set) := oneOf_ (bindGen arbitrary (fun a => returnGen (UserAddressSome a))) [bindGen arbitrary (fun a => returnGen (UserAddressSome a));returnGen UserAddressNone].
Global Instance gen_user_address_set : Gen (user_address_set) := Build_Gen user_address_set g_user_address_set.

Notation "'context'" := ((int64 × user_address_set)) : hacspec_scope.
Instance show_context : Show (context) :=
Build_Show context (fun x =>
  let (x, x0) := x in
  (("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ (")"))))))%string.
Definition g_context : G (context) :=
bindGen arbitrary (fun x0 : int64 =>
  bindGen arbitrary (fun x1 : user_address_set =>
  returnGen (x0,x1))).
Instance gen_context : Gen (context) := Build_Gen context g_context.

Notation "'auction_bid_result'" := ((result state bid_error)) : hacspec_scope.

Definition auction_bid
  (ctx_16 : context)
  (amount_17 : int64)
  (state_18 : state)
  : auction_bid_result :=
  let 'State ((auction_state_19, highest_bid_20, st2_21, expiry_22, st4_23)) :=
    (state_18) in 
  ifbnd negb ((auction_state_19) =.? (NotSoldYet)) : bool
  thenbnd (bind (@Err state bid_error (AuctionIsFinalized)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let '(slot_time_24, sender_25) :=
    ctx_16 in 
  ifbnd negb ((slot_time_24) <=.? (expiry_22)) : bool
  thenbnd (bind (@Err state bid_error (BidsOverWaitingForAuctionFinalization)) (
      fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  ifbnd (sender_25) =.? (UserAddressNone) : bool
  thenbnd (bind (@Err state bid_error (ContractSender)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let sender_address_26 : user_address :=
    match sender_25 with
    | UserAddressNone => array_from_list int8 (let l :=
        [
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
    | UserAddressSome account_address_27 => account_address_27
    end in 
  let '(bid_to_update_28, new_map_29) :=
    seq_map_entry ((st4_23)) (sender_address_26) in 
  let '(updated_bid_30, updated_map_31) :=
    match seq_map_update_entry ((st4_23)) (sender_address_26) ((
        bid_to_update_28) .+ (amount_17)) with
    | Update (updated_bid_32, updated_map_33) => (updated_bid_32, updated_map_33
    )
    end in 
  ifbnd negb ((updated_bid_30) >.? (highest_bid_20)) : bool
  thenbnd (bind (@Err state bid_error (BidTooLow)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  @Ok state bid_error (State ((
        auction_state_19,
        updated_bid_30,
        st2_21,
        expiry_22,
        updated_map_31
      ))))))).

Notation "'finalize_context'" := ((int64 × user_address × int64
)) : hacspec_scope.
Instance show_finalize_context : Show (finalize_context) :=
Build_Show finalize_context (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
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

Definition eqb_leibniz_finalize_error (x y : finalize_error) : eqb_finalize_error x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_finalize_error : EqDec (finalize_error) :=
Build_EqDec (finalize_error) (eqb_finalize_error) (eqb_leibniz_finalize_error).

Global Instance show_finalize_error : Show (finalize_error) :=
 @Build_Show (finalize_error) (fun x =>
 match x with
 BidMapError => ("BidMapError")%string
 | AuctionStillActive => ("AuctionStillActive")%string
 | AuctionFinalized => ("AuctionFinalized")%string
 end).
Definition g_finalize_error : G (finalize_error) := oneOf_ (returnGen BidMapError) [returnGen BidMapError;returnGen AuctionStillActive;returnGen AuctionFinalized].
Global Instance gen_finalize_error : Gen (finalize_error) := Build_Gen finalize_error g_finalize_error.

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

Definition eqb_leibniz_finalize_action (x y : finalize_action) : eqb_finalize_action x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_finalize_action : EqDec (finalize_action) :=
Build_EqDec (finalize_action) (eqb_finalize_action) (eqb_leibniz_finalize_action).

Global Instance show_finalize_action : Show (finalize_action) :=
 @Build_Show (finalize_action) (fun x =>
 match x with
 Accept => ("Accept")%string
 | SimpleTransfer a => ("SimpleTransfer" ++ show a)%string
 end).
Definition g_finalize_action : G (finalize_action) := oneOf_ (returnGen Accept) [returnGen Accept;bindGen arbitrary (fun a => returnGen (SimpleTransfer a))].
Global Instance gen_finalize_action : Gen (finalize_action) := Build_Gen finalize_action g_finalize_action.

Inductive bid_remain :=
| BidNone : bid_remain
| BidSome : int64 -> bid_remain.

Definition eqb_bid_remain (x y : bid_remain) : bool :=
match x with
   | BidNone => match y with | BidNone=> true | _ => false end
   | BidSome a => match y with | BidSome b => a =.? b | _ => false end
   end.

Definition eqb_leibniz_bid_remain (x y : bid_remain) : eqb_bid_remain x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_bid_remain : EqDec (bid_remain) :=
Build_EqDec (bid_remain) (eqb_bid_remain) (eqb_leibniz_bid_remain).

Global Instance show_bid_remain : Show (bid_remain) :=
 @Build_Show (bid_remain) (fun x =>
 match x with
 BidNone => ("BidNone")%string
 | BidSome a => ("BidSome" ++ show a)%string
 end).
Definition g_bid_remain : G (bid_remain) := oneOf_ (returnGen BidNone) [returnGen BidNone;bindGen arbitrary (fun a => returnGen (BidSome a))].
Global Instance gen_bid_remain : Gen (bid_remain) := Build_Gen bid_remain g_bid_remain.

Notation "'auction_finalize_result'" := ((result (state × finalize_action
  ) finalize_error)) : hacspec_scope.

Definition auction_finalize
  (ctx_34 : finalize_context)
  (state_35 : state)
  : auction_finalize_result :=
  let 'State ((
	auction_state_36,
	highest_bid_37,
	st2_38,
	expiry_39,
	SeqMap ((m0_40, m1_41))
      )) :=
    (state_35) in 
  let result_42 : (result (state × finalize_action) finalize_error) :=
    @Ok (state × finalize_action) finalize_error (((state_35), Accept)) in 
  ifbnd negb ((auction_state_36) =.? (NotSoldYet)) : bool
  thenbnd (bind (@Err (state × finalize_action) finalize_error (
	AuctionFinalized)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let '(slot_time_43, owner_44, balance_45) :=
    ctx_34 in 
  ifbnd negb ((slot_time_43) >.? (expiry_39)) : bool
  thenbnd (bind (@Err (state × finalize_action) finalize_error (
	AuctionStillActive)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  ifbnd (balance_45) !=.? (@repr WORDSIZE64 0) : bool
  thenbnd (let return_action_46 : finalize_action :=
      SimpleTransfer (seq_concat (seq_concat (seq_new_ (@repr WORDSIZE8 0) (
	      usize 0)) (owner_44)) (u64_to_be_bytes (highest_bid_37))) in 
    let remaining_bid_47 : bid_remain :=
      BidNone in 
    bind (foldibnd (usize 0) to ((seq_len ((m0_40))) / (usize 32)) for (
	auction_state_36,
	return_action_46,
	remaining_bid_47
      )>> (fun x_48 '(auction_state_36, return_action_46, remaining_bid_47) =>
      let addr_49 : user_address :=
	array_from_seq (32) (seq_slice ((m0_40)) ((x_48) * (usize 32)) (
	    usize 32)) in 
      let amnt_50 : int64 :=
	u64_from_be_bytes (array_from_seq (8) (seq_slice ((m1_41)) ((x_48) * (
		usize 8)) (usize 8))) in 
      ifbnd (amnt_50) <.? (highest_bid_37) : bool
      then (let return_action_46 :=
	  match return_action_46 with
	  | Accept => Accept
	  | SimpleTransfer m_51 => SimpleTransfer (seq_concat (seq_concat (
		m_51) (addr_49)) (u64_to_be_bytes (amnt_50)))
	  end in 
	(auction_state_36, return_action_46, remaining_bid_47))
      elsebnd(ifbnd negb ((remaining_bid_47) =.? (BidNone)) : bool
	thenbnd (bind (@Err (state × finalize_action) finalize_error (
	      BidMapError)) (fun _ => Ok (tt)))
	else (tt) >> (fun 'tt =>
	let auction_state_36 :=
	  Sold (addr_49) in 
	let remaining_bid_47 :=
	  BidSome (amnt_50) in 
	Ok ((auction_state_36, return_action_46, remaining_bid_47)))) >> (fun '(
	auction_state_36,
	return_action_46,
	remaining_bid_47
      ) =>
      Ok ((auction_state_36, return_action_46, remaining_bid_47))))) (fun '(
	auction_state_36,
	return_action_46,
	remaining_bid_47
      ) => let result_42 :=
	match remaining_bid_47 with
	| BidSome amount_52 => (if (negb ((amount_52) =.? (
		highest_bid_37))):bool then (@Err (state × finalize_action
	    ) finalize_error (BidMapError)) else (@Ok (state × finalize_action
	    ) finalize_error ((
		State ((
		    auction_state_36,
		    highest_bid_37,
		    st2_38,
		    expiry_39,
		    SeqMap (((m0_40), (m1_41)))
		  )),
		return_action_46
	      ))))
	| BidNone => @Err (state × finalize_action) finalize_error (
	  BidMapError)
	end in 
      bind ((result_42)) (fun _ => Ok ((auction_state_36, result_42)))))
  else ((auction_state_36, result_42)) >> (fun '(auction_state_36, result_42) =>
  result_42))).

Definition auction_test_init
  (item_53 : public_byte_seq)
  (time_54 : int64)
  : bool :=
  (fresh_state ((item_53)) (time_54)) =.? (State ((
        NotSoldYet,
        @repr WORDSIZE64 0,
        (item_53),
        time_54,
        SeqMap ((
            seq_new_ (@repr WORDSIZE8 0) (usize 0),
            seq_new_ (@repr WORDSIZE8 0) (usize 0)
          ))
      ))).

Theorem ensures_auction_test_init : forall result_2 (
  item_53 : public_byte_seq) (time_54 : int64),
@auction_test_init item_53 time_54 = result_2 ->
result_2 = true.
Proof. Admitted.

QuickChick (
  forAll g_public_byte_seq (fun item_53 : public_byte_seq =>forAll g_int64 (fun time_54 : int64 =>auction_test_init item_53 time_54))).

Definition verify_bid
  (item_55 : public_byte_seq)
  (state_56 : state)
  (account_57 : user_address)
  (ctx_58 : context)
  (amount_59 : int64)
  (bid_map_60 : seq_map)
  (highest_bid_61 : int64)
  (time_62 : int64)
  : (state × seq_map × bool × bool) :=
  let t_63 : (result state bid_error) :=
    auction_bid (ctx_58) (amount_59) ((state_56)) in 
  let '(state_64, res_65) :=
    match t_63 with
    | Err e_66 => (state_56, false)
    | Ok s_67 => (s_67, true)
    end in 
  let bid_map_68 : seq_map :=
    match seq_map_update_entry ((bid_map_60)) (account_57) (highest_bid_61) with
    | Update (_, updated_map_69) => updated_map_69
    end in 
  (
    (state_64),
    (bid_map_68),
    res_65,
    ((state_64)) =.? (State ((
          NotSoldYet,
          highest_bid_61,
          (item_55),
          time_62,
          (bid_map_68)
        )))
  ).

Definition useraddress_from_u8 (i_70 : int8) : user_address :=
  array_from_list int8 (let l :=
      [
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70;
        i_70
      ] in  l).

Definition new_account
  (time_71 : int64)
  (i_72 : int8)
  : (user_address × context) :=
  let addr_73 : user_address :=
    useraddress_from_u8 (i_72) in 
  let ctx_74 : (int64 × user_address_set) :=
    (time_71, UserAddressSome (addr_73)) in 
  (addr_73, ctx_74).

Definition test_auction_bid_and_finalize
  (item_75 : public_byte_seq)
  (time_76 : int64)
  (input_amount_77 : int64)
  : bool :=
  let amount_78 : int64 :=
    (input_amount_77) .+ (@repr WORDSIZE64 1) in 
  let winning_amount_79 : int64 :=
    (amount_78) .* (@repr WORDSIZE64 3) in 
  let big_amount_80 : int64 :=
    (amount_78) .* (@repr WORDSIZE64 5) in 
  let bid_map_81 : seq_map :=
    SeqMap ((
        seq_new_ (@repr WORDSIZE8 0) (usize 0),
        seq_new_ (@repr WORDSIZE8 0) (usize 0)
      )) in 
  let state_82 : state :=
    fresh_state ((item_75)) (time_76) in 
  let '(alice_83, alice_ctx_84) :=
    new_account (time_76) (@repr WORDSIZE8 0) in 
  let '(state_85, bid_map_86, res_0_87, result_0_88) :=
    verify_bid ((item_75)) (state_82) (alice_83) (alice_ctx_84) (amount_78) (
      bid_map_81) (amount_78) (time_76) in 
  let '(state_89, bid_map_90, res_1_91, result_1_92) :=
    verify_bid ((item_75)) (state_85) (alice_83) (alice_ctx_84) (amount_78) (
      bid_map_86) ((amount_78) .+ (amount_78)) (time_76) in 
  let '(bob_93, bob_ctx_94) :=
    new_account (time_76) (@repr WORDSIZE8 1) in 
  let '(state_95, bid_map_96, res_2_97, result_2_98) :=
    verify_bid ((item_75)) (state_89) (bob_93) (bob_ctx_94) (
      winning_amount_79) (bid_map_90) (winning_amount_79) (time_76) in 
  let owner_99 : user_address :=
    useraddress_from_u8 (@repr WORDSIZE8 0) in 
  let balance_100 : int64 :=
    @repr WORDSIZE64 100 in 
  let ctx4_101 : (int64 × user_address × int64) :=
    (time_76, owner_99, balance_100) in 
  let finres_102 : (result (state × finalize_action) finalize_error) :=
    auction_finalize (ctx4_101) ((state_95)) in 
  let '(state_103, result_3_104) :=
    match finres_102 with
    | Err err_105 => ((state_95), (err_105) =.? (AuctionStillActive))
    | Ok (state_106, _) => (state_106, false)
    end in 
  let '(carol_107, carol_ctx_108) :=
    new_account (time_76) (@repr WORDSIZE8 2) in 
  let ctx5_109 : (int64 × user_address × int64) :=
    ((time_76) .+ (@repr WORDSIZE64 1), carol_107, winning_amount_79) in 
  let finres2_110 : (result (state × finalize_action) finalize_error) :=
    auction_finalize (ctx5_109) ((state_103)) in 
  let '(state_111, result_4_112) :=
    match finres2_110 with
    | Err _ => ((state_103), false)
    | Ok (state_113, action_114) => (
      state_113,
      (action_114) =.? (SimpleTransfer (seq_concat (seq_concat (seq_concat (
                seq_concat (seq_new_ (@repr WORDSIZE8 0) (usize 0)) (
                  carol_107)) (u64_to_be_bytes (winning_amount_79))) (
              alice_83)) (u64_to_be_bytes ((amount_78) .+ (amount_78)))))
    )
    end in 
  let result_5_115 : bool :=
    ((state_111)) =.? (State ((
          Sold (bob_93),
          winning_amount_79,
          (item_75),
          time_76,
          (bid_map_96)
        ))) in 
  let finres3_116 : (result (state × finalize_action) finalize_error) :=
    auction_finalize (ctx5_109) ((state_111)) in 
  let '(state_117, result_6_118) :=
    match finres3_116 with
    | Err err_119 => (state_111, (err_119) =.? (AuctionFinalized))
    | Ok (state_120, action_121) => (state_120, false)
    end in 
  let t_122 : (result state bid_error) :=
    auction_bid (bob_ctx_94) (big_amount_80) ((state_117)) in 
  let result_7_123 : bool :=
    match t_122 with
    | Err e_124 => (e_124) =.? (AuctionIsFinalized)
    | Ok _ => false
    end in 
  (((((((result_0_88) && (result_1_92)) && (result_2_98)) && (
            result_3_104)) && (result_4_112)) && (result_5_115)) && (
      result_6_118)) && (result_7_123).

Theorem ensures_test_auction_bid_and_finalize : forall result_2 (
  item_75 : public_byte_seq) (time_76 : int64) (input_amount_77 : int64),
@test_auction_bid_and_finalize item_75 time_76 input_amount_77 = result_2 ->
result_2 = true.
Proof. Admitted.

QuickChick (
  forAll g_public_byte_seq (fun item_75 : public_byte_seq =>forAll g_int64 (fun time_76 : int64 =>forAll g_int64 (fun input_amount_77 : int64 =>test_auction_bid_and_finalize item_75 time_76 input_amount_77)))).
