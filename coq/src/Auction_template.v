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

Definition user_address_t := nseq (int8) (usize 32).

Inductive auction_state_hacspec_t :=
| NotSoldYet : auction_state_hacspec_t
| Sold : user_address_t -> auction_state_hacspec_t.

Definition eqb_auction_state_hacspec_t (x y : auction_state_hacspec_t) : bool :=
match x with
   | NotSoldYet => match y with | NotSoldYet=> true | _ => false end
   | Sold a => match y with | Sold b => a =.? b | _ => false end
   end.

Definition eqb_leibniz_auction_state_hacspec_t (x y : auction_state_hacspec_t) : eqb_auction_state_hacspec_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_auction_state_hacspec_t : EqDec (auction_state_hacspec_t) :=
Build_EqDec (auction_state_hacspec_t) (eqb_auction_state_hacspec_t) (eqb_leibniz_auction_state_hacspec_t).

Global Instance show_auction_state_hacspec_t : Show (auction_state_hacspec_t) :=
 @Build_Show (auction_state_hacspec_t) (fun x =>
 match x with
 NotSoldYet => ("NotSoldYet")%string
 | Sold a => ("Sold" ++ show a)%string
 end).
Definition g_auction_state_hacspec_t : G (auction_state_hacspec_t) := oneOf_ (returnGen NotSoldYet) [returnGen NotSoldYet;bindGen arbitrary (fun a => returnGen (Sold a))].
Global Instance gen_auction_state_hacspec_t : Gen (auction_state_hacspec_t) := Build_Gen auction_state_hacspec_t g_auction_state_hacspec_t.


Inductive seq_map_t :=
| SeqMap : (public_byte_seq × public_byte_seq) -> seq_map_t.

Definition eqb_seq_map_t (x y : seq_map_t) : bool :=
match x with
   | SeqMap a => match y with | SeqMap b => a =.? b end
   end.

Definition eqb_leibniz_seq_map_t (x y : seq_map_t) : eqb_seq_map_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_seq_map_t : EqDec (seq_map_t) :=
Build_EqDec (seq_map_t) (eqb_seq_map_t) (eqb_leibniz_seq_map_t).

Global Instance show_seq_map_t : Show (seq_map_t) :=
 @Build_Show (seq_map_t) (fun x =>
 match x with
 SeqMap a => ("SeqMap" ++ show a)%string
 end).
Definition g_seq_map_t : G (seq_map_t) := oneOf_ (bindGen arbitrary (fun a => returnGen (SeqMap a))) [bindGen arbitrary (fun a => returnGen (SeqMap a))].
Global Instance gen_seq_map_t : Gen (seq_map_t) := Build_Gen seq_map_t g_seq_map_t.


Inductive state_hacspec_t :=
| StateHacspec : (
  auction_state_hacspec_t ×
  int64 ×
  public_byte_seq ×
  int64 ×
  seq_map_t
) -> state_hacspec_t.

Definition eqb_state_hacspec_t (x y : state_hacspec_t) : bool :=
match x with
   | StateHacspec a => match y with | StateHacspec b => a =.? b end
   end.

Definition eqb_leibniz_state_hacspec_t (x y : state_hacspec_t) : eqb_state_hacspec_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_state_hacspec_t : EqDec (state_hacspec_t) :=
Build_EqDec (state_hacspec_t) (eqb_state_hacspec_t) (eqb_leibniz_state_hacspec_t).

Global Instance show_state_hacspec_t : Show (state_hacspec_t) :=
 @Build_Show (state_hacspec_t) (fun x =>
 match x with
 StateHacspec a => ("StateHacspec" ++ show a)%string
 end).
Definition g_state_hacspec_t : G (state_hacspec_t) := oneOf_ (bindGen arbitrary (fun a => returnGen (StateHacspec a))) [bindGen arbitrary (fun a => returnGen (StateHacspec a))].
Global Instance gen_state_hacspec_t : Gen (state_hacspec_t) := Build_Gen state_hacspec_t g_state_hacspec_t.


Definition fresh_state_hacspec
  (itm_0 : public_byte_seq)
  (exp_1 : int64)
  : state_hacspec_t :=
  StateHacspec ((
      NotSoldYet,
      @repr WORDSIZE64 0,
      itm_0,
      exp_1,
      SeqMap ((seq_new_ (default) (usize 0), seq_new_ (default) (usize 0)))
    )).

Definition seq_map_entry
  (m_2 : seq_map_t)
  (sender_address_3 : user_address_t)
  : (int64 × seq_map_t) :=
  let 'SeqMap ((m0_4, m1_5)) :=
    m_2 in 
  let res_6 : (int64 × seq_map_t) :=
    (
      @repr WORDSIZE64 0,
      SeqMap ((
          seq_concat ((m0_4)) (sender_address_3),
          seq_concat ((m1_5)) (u64_to_be_bytes (@repr WORDSIZE64 0))
        ))
    ) in 
  let res_6 :=
    foldi (usize 0) ((seq_len ((m0_4))) / (usize 32)) (fun x_7 res_6 =>
      let '(res_6) :=
        if (array_from_seq (32) (seq_slice ((m0_4)) ((x_7) * (usize 32)) (
              usize 32))) array_eq (sender_address_3):bool then (let res_6 :=
            (
              u64_from_be_bytes (array_from_seq (8) (seq_slice ((m1_5)) ((
                      x_7) * (usize 8)) (usize 8))),
              SeqMap (((m0_4), (m1_5)))
            ) in 
          (res_6)) else ((res_6)) in 
      (res_6))
    res_6 in 
  res_6.

Inductive map_update_t :=
| Update : (int64 × seq_map_t) -> map_update_t.

Definition eqb_map_update_t (x y : map_update_t) : bool :=
match x with
   | Update a => match y with | Update b => a =.? b end
   end.

Definition eqb_leibniz_map_update_t (x y : map_update_t) : eqb_map_update_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_map_update_t : EqDec (map_update_t) :=
Build_EqDec (map_update_t) (eqb_map_update_t) (eqb_leibniz_map_update_t).

Global Instance show_map_update_t : Show (map_update_t) :=
 @Build_Show (map_update_t) (fun x =>
 match x with
 Update a => ("Update" ++ show a)%string
 end).
Definition g_map_update_t : G (map_update_t) := oneOf_ (bindGen arbitrary (fun a => returnGen (Update a))) [bindGen arbitrary (fun a => returnGen (Update a))].
Global Instance gen_map_update_t : Gen (map_update_t) := Build_Gen map_update_t g_map_update_t.


Definition seq_map_update_entry
  (m_8 : seq_map_t)
  (sender_address_9 : user_address_t)
  (amount_10 : int64)
  : map_update_t :=
  let 'SeqMap ((m0_11, m1_12)) :=
    m_8 in 
  let res_13 : map_update_t :=
    Update ((
        amount_10,
        SeqMap ((
            seq_concat ((m0_11)) (sender_address_9),
            seq_concat ((m1_12)) (u64_to_be_bytes (amount_10))
          ))
      )) in 
  let res_13 :=
    foldi (usize 0) ((seq_len ((m0_11))) / (usize 32)) (fun x_14 res_13 =>
      let '(res_13) :=
        if (array_from_seq (32) (seq_slice ((m0_11)) ((x_14) * (usize 32)) (
              usize 32))) array_eq (sender_address_9):bool then (let res_13 :=
            Update ((
                amount_10,
                SeqMap ((
                    seq_update ((m0_11)) ((x_14) * (usize 32)) (
                      sender_address_9),
                    seq_update ((m1_12)) ((x_14) * (usize 8)) (u64_to_be_bytes (
                        amount_10))
                  ))
              )) in 
          (res_13)) else ((res_13)) in 
      (res_13))
    res_13 in 
  res_13.

Inductive bid_error_hacspec_t :=
| ContractSender : bid_error_hacspec_t
| BidTooLow : bid_error_hacspec_t
| BidsOverWaitingForAuctionFinalization : bid_error_hacspec_t
| AuctionIsFinalized : bid_error_hacspec_t.

Definition eqb_bid_error_hacspec_t (x y : bid_error_hacspec_t) : bool :=
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

Definition eqb_leibniz_bid_error_hacspec_t (x y : bid_error_hacspec_t) : eqb_bid_error_hacspec_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_bid_error_hacspec_t : EqDec (bid_error_hacspec_t) :=
Build_EqDec (bid_error_hacspec_t) (eqb_bid_error_hacspec_t) (eqb_leibniz_bid_error_hacspec_t).

Global Instance show_bid_error_hacspec_t : Show (bid_error_hacspec_t) :=
 @Build_Show (bid_error_hacspec_t) (fun x =>
 match x with
 ContractSender => ("ContractSender")%string
 | BidTooLow => ("BidTooLow")%string
 | BidsOverWaitingForAuctionFinalization => (
   "BidsOverWaitingForAuctionFinalization")%string
 | AuctionIsFinalized => ("AuctionIsFinalized")%string
 end).
Definition g_bid_error_hacspec_t : G (bid_error_hacspec_t) := oneOf_ (returnGen ContractSender) [returnGen ContractSender;returnGen BidTooLow;returnGen BidsOverWaitingForAuctionFinalization;returnGen AuctionIsFinalized].
Global Instance gen_bid_error_hacspec_t : Gen (bid_error_hacspec_t) := Build_Gen bid_error_hacspec_t g_bid_error_hacspec_t.


Inductive user_address_set_t :=
| UserAddressSome : user_address_t -> user_address_set_t
| UserAddressNone : user_address_set_t.

Definition eqb_user_address_set_t (x y : user_address_set_t) : bool :=
match x with
   | UserAddressSome a =>
       match y with
       | UserAddressSome b => a =.? b
       | _ => false
       end
   | UserAddressNone => match y with | UserAddressNone=> true | _ => false end
   end.

Definition eqb_leibniz_user_address_set_t (x y : user_address_set_t) : eqb_user_address_set_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_user_address_set_t : EqDec (user_address_set_t) :=
Build_EqDec (user_address_set_t) (eqb_user_address_set_t) (eqb_leibniz_user_address_set_t).

Global Instance show_user_address_set_t : Show (user_address_set_t) :=
 @Build_Show (user_address_set_t) (fun x =>
 match x with
 UserAddressSome a => ("UserAddressSome" ++ show a)%string
 | UserAddressNone => ("UserAddressNone")%string
 end).
Definition g_user_address_set_t : G (user_address_set_t) := oneOf_ (bindGen arbitrary (fun a => returnGen (UserAddressSome a))) [bindGen arbitrary (fun a => returnGen (UserAddressSome a));returnGen UserAddressNone].
Global Instance gen_user_address_set_t : Gen (user_address_set_t) := Build_Gen user_address_set_t g_user_address_set_t.


Notation "'context_t'" := ((int64 × user_address_set_t)) : hacspec_scope.
Instance show_context_t : Show (context_t) :=
Build_Show context_t (fun x =>
  let (x, x0) := x in
  (("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ (")"))))))%string.
Definition g_context_t : G (context_t) :=
bindGen arbitrary (fun x0 : int64 =>
  bindGen arbitrary (fun x1 : user_address_set_t =>
  returnGen (x0,x1))).
Instance gen_context_t : Gen (context_t) := Build_Gen context_t g_context_t.


Notation "'auction_bid_result_t'" := ((
  result state_hacspec_t bid_error_hacspec_t)) : hacspec_scope.

Definition auction_bid_hacspec
  (ctx_15 : context_t)
  (amount_16 : int64)
  (state_17 : state_hacspec_t)
  : auction_bid_result_t :=
  let 'StateHacspec ((
        auction_state_18,
        highest_bid_19,
        st2_20,
        expiry_21,
        st4_22
      )) :=
    (state_17) in 
  ifbnd negb ((auction_state_18) =.? (NotSoldYet)) : bool
  thenbnd (bind (@Err state_hacspec_t bid_error_hacspec_t (
        AuctionIsFinalized)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let '(slot_time_23, sender_24) :=
    ctx_15 in 
  ifbnd negb ((slot_time_23) <=.? (expiry_21)) : bool
  thenbnd (bind (@Err state_hacspec_t bid_error_hacspec_t (
        BidsOverWaitingForAuctionFinalization)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  ifbnd (sender_24) =.? (UserAddressNone) : bool
  thenbnd (bind (@Err state_hacspec_t bid_error_hacspec_t (ContractSender)) (
      fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let sender_address_25 : user_address_t :=
    match sender_24 with
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
    | UserAddressSome account_address_26 => account_address_26
    end in 
  let '(bid_to_update_27, new_map_28) :=
    seq_map_entry ((st4_22)) (sender_address_25) in 
  let '(updated_bid_29, updated_map_30) :=
    match seq_map_update_entry ((st4_22)) (sender_address_25) ((
        bid_to_update_27) .+ (amount_16)) with
    | Update (updated_bid_31, updated_map_32) => (updated_bid_31, updated_map_32
    )
    end in 
  ifbnd negb ((updated_bid_29) >.? (highest_bid_19)) : bool
  thenbnd (bind (@Err state_hacspec_t bid_error_hacspec_t (BidTooLow)) (fun _ =>
      Ok (tt)))
  else (tt) >> (fun 'tt =>
  @Ok state_hacspec_t bid_error_hacspec_t (StateHacspec ((
        auction_state_18,
        updated_bid_29,
        st2_20,
        expiry_21,
        updated_map_30
      ))))))).

Inductive finalize_error_hacspec_t :=
| BidMapError : finalize_error_hacspec_t
| AuctionStillActive : finalize_error_hacspec_t
| AuctionFinalized : finalize_error_hacspec_t.

Definition eqb_finalize_error_hacspec_t (x y : finalize_error_hacspec_t) : bool :=
match x with
   | BidMapError => match y with | BidMapError=> true | _ => false end
   | AuctionStillActive =>
       match y with
       | AuctionStillActive=> true
       | _ => false
       end
   | AuctionFinalized => match y with | AuctionFinalized=> true | _ => false end
   end.

Definition eqb_leibniz_finalize_error_hacspec_t (x y : finalize_error_hacspec_t) : eqb_finalize_error_hacspec_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_finalize_error_hacspec_t : EqDec (finalize_error_hacspec_t) :=
Build_EqDec (finalize_error_hacspec_t) (eqb_finalize_error_hacspec_t) (eqb_leibniz_finalize_error_hacspec_t).

Global Instance show_finalize_error_hacspec_t : Show (finalize_error_hacspec_t) :=
 @Build_Show (finalize_error_hacspec_t) (fun x =>
 match x with
 BidMapError => ("BidMapError")%string
 | AuctionStillActive => ("AuctionStillActive")%string
 | AuctionFinalized => ("AuctionFinalized")%string
 end).
Definition g_finalize_error_hacspec_t : G (finalize_error_hacspec_t) := oneOf_ (returnGen BidMapError) [returnGen BidMapError;returnGen AuctionStillActive;returnGen AuctionFinalized].
Global Instance gen_finalize_error_hacspec_t : Gen (finalize_error_hacspec_t) := Build_Gen finalize_error_hacspec_t g_finalize_error_hacspec_t.


Notation "'finalize_context_t'" := ((int64 × user_address_t × int64
)) : hacspec_scope.
Instance show_finalize_context_t : Show (finalize_context_t) :=
Build_Show finalize_context_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_finalize_context_t : G (finalize_context_t) :=
bindGen arbitrary (fun x0 : int64 =>
  bindGen arbitrary (fun x1 : user_address_t =>
  bindGen arbitrary (fun x2 : int64 =>
  returnGen (x0,x1,x2)))).
Instance gen_finalize_context_t : Gen (finalize_context_t) := Build_Gen finalize_context_t g_finalize_context_t.


Inductive finalize_action_t :=
| Accept : finalize_action_t
| SimpleTransfer : public_byte_seq -> finalize_action_t.

Definition eqb_finalize_action_t (x y : finalize_action_t) : bool :=
match x with
   | Accept => match y with | Accept=> true | _ => false end
   | SimpleTransfer a =>
       match y with
       | SimpleTransfer b => a =.? b
       | _ => false
       end
   end.

Definition eqb_leibniz_finalize_action_t (x y : finalize_action_t) : eqb_finalize_action_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_finalize_action_t : EqDec (finalize_action_t) :=
Build_EqDec (finalize_action_t) (eqb_finalize_action_t) (eqb_leibniz_finalize_action_t).

Global Instance show_finalize_action_t : Show (finalize_action_t) :=
 @Build_Show (finalize_action_t) (fun x =>
 match x with
 Accept => ("Accept")%string
 | SimpleTransfer a => ("SimpleTransfer" ++ show a)%string
 end).
Definition g_finalize_action_t : G (finalize_action_t) := oneOf_ (returnGen Accept) [returnGen Accept;bindGen arbitrary (fun a => returnGen (SimpleTransfer a))].
Global Instance gen_finalize_action_t : Gen (finalize_action_t) := Build_Gen finalize_action_t g_finalize_action_t.


Inductive bid_remain_t :=
| BidNone : bid_remain_t
| BidSome : int64 -> bid_remain_t.

Definition eqb_bid_remain_t (x y : bid_remain_t) : bool :=
match x with
   | BidNone => match y with | BidNone=> true | _ => false end
   | BidSome a => match y with | BidSome b => a =.? b | _ => false end
   end.

Definition eqb_leibniz_bid_remain_t (x y : bid_remain_t) : eqb_bid_remain_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_bid_remain_t : EqDec (bid_remain_t) :=
Build_EqDec (bid_remain_t) (eqb_bid_remain_t) (eqb_leibniz_bid_remain_t).

Global Instance show_bid_remain_t : Show (bid_remain_t) :=
 @Build_Show (bid_remain_t) (fun x =>
 match x with
 BidNone => ("BidNone")%string
 | BidSome a => ("BidSome" ++ show a)%string
 end).
Definition g_bid_remain_t : G (bid_remain_t) := oneOf_ (returnGen BidNone) [returnGen BidNone;bindGen arbitrary (fun a => returnGen (BidSome a))].
Global Instance gen_bid_remain_t : Gen (bid_remain_t) := Build_Gen bid_remain_t g_bid_remain_t.


Notation "'auction_finalize_result_t'" := ((result (
    state_hacspec_t ×
    finalize_action_t
  ) finalize_error_hacspec_t)) : hacspec_scope.

Definition auction_finalize_hacspec
  (ctx_33 : finalize_context_t)
  (state_34 : state_hacspec_t)
  : auction_finalize_result_t :=
  let 'StateHacspec ((
        auction_state_35,
        highest_bid_36,
        st2_37,
        expiry_38,
        SeqMap ((m0_39, m1_40))
      )) :=
    (state_34) in 
  let result_41 : (result (state_hacspec_t × finalize_action_t
      ) finalize_error_hacspec_t) :=
    @Ok (state_hacspec_t × finalize_action_t) finalize_error_hacspec_t ((
        (state_34),
        Accept
      )) in 
  ifbnd negb ((auction_state_35) =.? (NotSoldYet)) : bool
  thenbnd (bind (@Err (state_hacspec_t × finalize_action_t
      ) finalize_error_hacspec_t (AuctionFinalized)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let '(slot_time_42, owner_43, balance_44) :=
    ctx_33 in 
  ifbnd negb ((slot_time_42) >.? (expiry_38)) : bool
  thenbnd (bind (@Err (state_hacspec_t × finalize_action_t
      ) finalize_error_hacspec_t (AuctionStillActive)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  ifbnd (balance_44) !=.? (@repr WORDSIZE64 0) : bool
  thenbnd (let return_action_45 : finalize_action_t :=
      SimpleTransfer (seq_concat (seq_concat (seq_new_ (default) (usize 0)) (
            owner_43)) (u64_to_be_bytes (highest_bid_36))) in 
    let remaining_bid_46 : bid_remain_t :=
      BidNone in 
    bind (foldibnd (usize 0) to ((seq_len ((m0_39))) / (usize 32)) for (
        auction_state_35,
        return_action_45,
        remaining_bid_46
      ) >> (fun x_47 '(auction_state_35, return_action_45, remaining_bid_46) =>
      let addr_48 : user_address_t :=
        array_from_seq (32) (seq_slice ((m0_39)) ((x_47) * (usize 32)) (
            usize 32)) in 
      let amnt_49 : int64 :=
        u64_from_be_bytes (array_from_seq (8) (seq_slice ((m1_40)) ((x_47) * (
                usize 8)) (usize 8))) in 
      ifbnd (amnt_49) <.? (highest_bid_36) : bool
      then (let return_action_45 :=
          match return_action_45 with
          | Accept => Accept
          | SimpleTransfer m_50 => SimpleTransfer (seq_concat (seq_concat (
                m_50) (addr_48)) (u64_to_be_bytes (amnt_49)))
          end in 
        (auction_state_35, return_action_45, remaining_bid_46))
      elsebnd(ifbnd negb ((remaining_bid_46) =.? (BidNone)) : bool
        thenbnd (bind (@Err (state_hacspec_t × finalize_action_t
            ) finalize_error_hacspec_t (BidMapError)) (fun _ => Ok (tt)))
        else (tt) >> (fun 'tt =>
        let auction_state_35 :=
          Sold (addr_48) in 
        let remaining_bid_46 :=
          BidSome (amnt_49) in 
        Ok ((auction_state_35, return_action_45, remaining_bid_46)))) >> (fun '(
        auction_state_35,
        return_action_45,
        remaining_bid_46
      ) =>
      Ok ((auction_state_35, return_action_45, remaining_bid_46))))) (fun '(
        auction_state_35,
        return_action_45,
        remaining_bid_46
      ) => let result_41 :=
        match remaining_bid_46 with
        | BidSome amount_51 => (if (negb ((amount_51) =.? (
                highest_bid_36))):bool then (@Err (
              state_hacspec_t ×
              finalize_action_t
            ) finalize_error_hacspec_t (BidMapError)) else (@Ok (
              state_hacspec_t ×
              finalize_action_t
            ) finalize_error_hacspec_t ((
                StateHacspec ((
                    auction_state_35,
                    highest_bid_36,
                    st2_37,
                    expiry_38,
                    SeqMap (((m0_39), (m1_40)))
                  )),
                return_action_45
              ))))
        | BidNone => @Err (state_hacspec_t × finalize_action_t
        ) finalize_error_hacspec_t (BidMapError)
        end in 
      bind ((result_41)) (fun _ => Ok ((auction_state_35, result_41)))))
  else ((auction_state_35, result_41)) >> (fun '(auction_state_35, result_41) =>
  result_41))).

Definition auction_test_init
  (item_52 : public_byte_seq)
  (time_53 : int64)
  : bool :=
  (fresh_state_hacspec ((item_52)) (time_53)) =.? (StateHacspec ((
        NotSoldYet,
        @repr WORDSIZE64 0,
        (item_52),
        time_53,
        SeqMap ((seq_new_ (default) (usize 0), seq_new_ (default) (usize 0)))
      ))).

Theorem ensures_auction_test_init : forall result_54 (
  item_52 : public_byte_seq) (time_53 : int64),
@auction_test_init item_52 time_53 = result_54 ->
result_54 = true.
Proof. Admitted.
QuickChick (
  forAll g_public_byte_seq (fun item_52 : public_byte_seq =>forAll g_int64 (fun time_53 : int64 =>auction_test_init item_52 time_53))).


Definition verify_bid
  (item_55 : public_byte_seq)
  (state_56 : state_hacspec_t)
  (account_57 : user_address_t)
  (ctx_58 : context_t)
  (amount_59 : int64)
  (bid_map_60 : seq_map_t)
  (highest_bid_61 : int64)
  (time_62 : int64)
  : (state_hacspec_t × seq_map_t × bool × bool) :=
  let t_63 : (result state_hacspec_t bid_error_hacspec_t) :=
    auction_bid_hacspec (ctx_58) (amount_59) ((state_56)) in 
  let '(state_64, res_65) :=
    match t_63 with
    | Err e_66 => (state_56, false)
    | Ok s_67 => (s_67, true)
    end in 
  let bid_map_68 : seq_map_t :=
    match seq_map_update_entry ((bid_map_60)) (account_57) (highest_bid_61) with
    | Update (_, updated_map_69) => updated_map_69
    end in 
  (
    (state_64),
    (bid_map_68),
    res_65,
    ((state_64)) =.? (StateHacspec ((
          NotSoldYet,
          highest_bid_61,
          (item_55),
          time_62,
          (bid_map_68)
        )))
  ).

Definition useraddress_from_u8 (i_70 : int8) : user_address_t :=
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
  : (user_address_t × context_t) :=
  let addr_73 : user_address_t :=
    useraddress_from_u8 (i_72) in 
  let ctx_74 : (int64 × user_address_set_t) :=
    (time_71, UserAddressSome (addr_73)) in 
  (addr_73, ctx_74).

Definition test_auction_bid_and_finalize
  (item_75 : public_byte_seq)
  (time_76 : int64)
  (input_amount_77 : int64)
  `{(@repr WORDSIZE64 18446744073709551615) >.? (time_76)}
  `{(((@repr WORDSIZE64 18446744073709551615) ./ (@repr WORDSIZE64 5)) .- (
      @repr WORDSIZE64 1)) >.? (input_amount_77)}
  : bool :=
  let time_78 : int64 :=
    (if ((time_76) =.? (@repr WORDSIZE64 18446744073709551615)):bool then (
        @repr WORDSIZE64 18446744073709551614) else (time_76)) in 
  let input_amount_79 : int64 :=
    (if ((input_amount_77) >.? (((@repr WORDSIZE64 18446744073709551615) ./ (
              @repr WORDSIZE64 5)) .- (@repr WORDSIZE64 1))):bool then (
        @repr WORDSIZE64 100) else (input_amount_77)) in 
  let amount_80 : int64 :=
    (input_amount_79) .+ (@repr WORDSIZE64 1) in 
  let winning_amount_81 : int64 :=
    (amount_80) .* (@repr WORDSIZE64 3) in 
  let big_amount_82 : int64 :=
    (amount_80) .* (@repr WORDSIZE64 5) in 
  let bid_map_83 : seq_map_t :=
    SeqMap ((seq_new_ (default) (usize 0), seq_new_ (default) (usize 0))) in 
  let state_84 : state_hacspec_t :=
    fresh_state_hacspec ((item_75)) (time_78) in 
  let '(alice_85, alice_ctx_86) :=
    new_account (time_78) (@repr WORDSIZE8 0) in 
  let '(ac0_87, ac1_88) :=
    alice_ctx_86 in 
  let '(state_89, bid_map_90, res_0_91, result_0_92) :=
    verify_bid ((item_75)) (state_84) (alice_85) (((ac0_87), (ac1_88))) (
      amount_80) (bid_map_83) (amount_80) (time_78) in 
  let '(state_93, bid_map_94, res_1_95, result_1_96) :=
    verify_bid ((item_75)) (state_89) (alice_85) (((ac0_87), (ac1_88))) (
      amount_80) (bid_map_90) ((amount_80) .+ (amount_80)) (time_78) in 
  let '(bob_97, bob_ctx_98) :=
    new_account (time_78) (@repr WORDSIZE8 1) in 
  let '(bc1_99, bc2_100) :=
    bob_ctx_98 in 
  let '(state_101, bid_map_102, res_2_103, result_2_104) :=
    verify_bid ((item_75)) (state_93) (bob_97) (((bc1_99), (bc2_100))) (
      winning_amount_81) (bid_map_94) (winning_amount_81) (time_78) in 
  let owner_105 : user_address_t :=
    useraddress_from_u8 (@repr WORDSIZE8 0) in 
  let balance_106 : int64 :=
    @repr WORDSIZE64 100 in 
  let ctx4_107 : (int64 × user_address_t × int64) :=
    (time_78, owner_105, balance_106) in 
  let finres_108 : (result (state_hacspec_t × finalize_action_t
      ) finalize_error_hacspec_t) :=
    auction_finalize_hacspec (ctx4_107) ((state_101)) in 
  let '(state_109, result_3_110) :=
    match finres_108 with
    | Err err_111 => ((state_101), (err_111) =.? (AuctionStillActive))
    | Ok (state_112, _) => (state_112, false)
    end in 
  let '(carol_113, carol_ctx_114) :=
    new_account (time_78) (@repr WORDSIZE8 2) in 
  let ctx5_115 : (int64 × user_address_t × int64) :=
    ((time_78) .+ (@repr WORDSIZE64 1), carol_113, winning_amount_81) in 
  let finres2_116 : (result (state_hacspec_t × finalize_action_t
      ) finalize_error_hacspec_t) :=
    auction_finalize_hacspec (ctx5_115) ((state_109)) in 
  let '(state_117, result_4_118) :=
    match finres2_116 with
    | Err _ => ((state_109), false)
    | Ok (state_119, action_120) => (
      state_119,
      (action_120) =.? (SimpleTransfer (seq_concat (seq_concat (seq_concat (
                seq_concat (seq_new_ (default) (usize 0)) (carol_113)) (
                u64_to_be_bytes (winning_amount_81))) (alice_85)) (
            u64_to_be_bytes ((amount_80) .+ (amount_80)))))
    )
    end in 
  let result_5_121 : bool :=
    ((state_117)) =.? (StateHacspec ((
          Sold (bob_97),
          winning_amount_81,
          (item_75),
          time_78,
          (bid_map_102)
        ))) in 
  let finres3_122 : (result (state_hacspec_t × finalize_action_t
      ) finalize_error_hacspec_t) :=
    auction_finalize_hacspec (ctx5_115) ((state_117)) in 
  let '(state_123, result_6_124) :=
    match finres3_122 with
    | Err err_125 => (state_117, (err_125) =.? (AuctionFinalized))
    | Ok (state_126, action_127) => (state_126, false)
    end in 
  let t_128 : (result state_hacspec_t bid_error_hacspec_t) :=
    auction_bid_hacspec (((bc1_99), (bc2_100))) (big_amount_82) ((
        state_123)) in 
  let result_7_129 : bool :=
    match t_128 with
    | Err e_130 => (e_130) =.? (AuctionIsFinalized)
    | Ok _ => false
    end in 
  (((((((result_0_92) && (result_1_96)) && (result_2_104)) && (
            result_3_110)) && (result_4_118)) && (result_5_121)) && (
      result_6_124)) && (result_7_129).

Theorem ensures_test_auction_bid_and_finalize : forall result_54 (
  item_75 : public_byte_seq) (time_76 : int64) (input_amount_77 : int64),
forall {H_0 : (@repr WORDSIZE64 18446744073709551615) >.? (time_76)},
forall {H_1 : (((@repr WORDSIZE64 18446744073709551615) ./ (
      @repr WORDSIZE64 5)) .- (@repr WORDSIZE64 1)) >.? (input_amount_77)},
@test_auction_bid_and_finalize item_75 time_76 input_amount_77 H_0 H_1 = result_54 ->
result_54 = true.
Proof. Admitted.
QuickChick (
  forAll g_public_byte_seq (fun item_75 : public_byte_seq =>forAll g_int64 (fun time_76 : int64 =>forAll g_int64 (fun input_amount_77 : int64 =>test_auction_bid_and_finalize item_75 time_76 input_amount_77)))).


