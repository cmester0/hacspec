(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
From QuickChick Require Import QuickChick.
Require Import QuickChickLib.
Require Import Hacspec_Lib.

Require Import Hacspec_Concordium.

Require Import Concert_Lib.

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
#[global] Instance gen_auction_state_hacspec_t : Gen (auction_state_hacspec_t) := Build_Gen auction_state_hacspec_t g_auction_state_hacspec_t.


Inductive seq_map_t :=
| SeqMap : (public_byte_seq '× public_byte_seq) -> seq_map_t.

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
#[global] Instance gen_seq_map_t : Gen (seq_map_t) := Build_Gen seq_map_t g_seq_map_t.


Inductive state_hacspec_t :=
| StateHacspec : (
  auction_state_hacspec_t '×
  int64 '×
  public_byte_seq '×
  int64 '×
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
#[global] Instance gen_state_hacspec_t : Gen (state_hacspec_t) := Build_Gen state_hacspec_t g_state_hacspec_t.
Definition State := context_t ∏ state_hacspec_t.


Definition fresh_state_hacspec
  (itm_0 : public_byte_seq)
  (exp_1 : int64)
  
  : state_hacspec_t :=
  StateHacspec ((
      NotSoldYet,
      @repr WORDSIZE64 0,
      itm_0,
      exp_1,
      SeqMap ((
          seq_new_ (default : int8) (usize 0),
          seq_new_ (default : int8) (usize 0)
        ))
    )).

Inductive init_parameter_t :=
| InitParameter : (public_byte_seq '× int64) -> init_parameter_t.
 Global Instance show_init_parameter_t : Show (init_parameter_t) :=
  @Build_Show (init_parameter_t) (fun x =>
 match x with
 InitParameter a => ("InitParameter" ++ show a)%string
 end).
Definition g_init_parameter_t : G (init_parameter_t) := oneOf_ (bindGen arbitrary (fun a => returnGen (InitParameter a))) [bindGen arbitrary (fun a => returnGen (InitParameter a))].
#[global] Instance gen_init_parameter_t : Gen (init_parameter_t) := Build_Gen init_parameter_t g_init_parameter_t.


Notation "'context_state_hacspec_t'" := ((context_t '× state_hacspec_t
)) : hacspec_scope.
Instance show_context_state_hacspec_t : Show (context_state_hacspec_t) :=
Build_Show context_state_hacspec_t (fun x =>
  let (x, x0) := x in
  (("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ (")"))))))%string.
Definition g_context_state_hacspec_t : G (context_state_hacspec_t) :=
bindGen arbitrary (fun x0 : context_t =>
  bindGen arbitrary (fun x1 : state_hacspec_t =>
  returnGen (x0,x1))).
Instance gen_context_state_hacspec_t : Gen (context_state_hacspec_t) := Build_Gen context_state_hacspec_t g_context_state_hacspec_t.


Definition auction_init
  (ctx_2 : context_t)
  (init_parameter_3 : init_parameter_t)
  
  : context_state_hacspec_t :=
  (
    ctx_2,
    fresh_state_hacspec (seq_new_ (default : int8) (usize 0)) (
      @repr WORDSIZE64 0)
  ).

Definition seq_map_entry
  (m_4 : seq_map_t)
  (sender_address_5 : user_address_t)
  
  : (int64 '× seq_map_t) :=
  let 'SeqMap ((m0_6, m1_7)) :=
    m_4 in 
  let res_8 : (int64 '× seq_map_t) :=
    (
      @repr WORDSIZE64 0,
      SeqMap ((
          seq_concat ((m0_6)) (array_to_seq (sender_address_5)),
          seq_concat ((m1_7)) (array_to_seq (u64_to_be_bytes (
              @repr WORDSIZE64 0)))
        ))
    ) in 
  let res_8 :=
    foldi (usize 0) ((seq_len ((m0_6))) / (usize 32)) (fun x_9 res_8 =>
      let '(res_8) :=
        if (array_from_seq (32) (seq_slice ((m0_6)) ((x_9) * (usize 32)) (
              usize 32))) array_eq (sender_address_5):bool then (let res_8 :=
            (
              u64_from_be_bytes (array_from_seq (8) (seq_slice ((m1_7)) ((
                      x_9) * (usize 8)) (usize 8))),
              SeqMap (((m0_6), (m1_7)))
            ) in 
          (res_8)) else ((res_8)) in 
      (res_8))
    res_8 in 
  res_8.

Inductive map_update_t :=
| Update : (int64 '× seq_map_t) -> map_update_t.

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
#[global] Instance gen_map_update_t : Gen (map_update_t) := Build_Gen map_update_t g_map_update_t.


Definition seq_map_update_entry
  (m_10 : seq_map_t)
  (sender_address_11 : user_address_t)
  (amount_12 : int64)
  
  : map_update_t :=
  let 'SeqMap ((m0_13, m1_14)) :=
    m_10 in 
  let res_15 : map_update_t :=
    Update ((
        amount_12,
        SeqMap ((
            seq_concat ((m0_13)) (array_to_seq (sender_address_11)),
            seq_concat ((m1_14)) (array_to_seq (u64_to_be_bytes (amount_12)))
          ))
      )) in 
  let res_15 :=
    foldi (usize 0) ((seq_len ((m0_13))) / (usize 32)) (fun x_16 res_15 =>
      let '(res_15) :=
        if (array_from_seq (32) (seq_slice ((m0_13)) ((x_16) * (usize 32)) (
              usize 32))) array_eq (sender_address_11):bool then (let res_15 :=
            Update ((
                amount_12,
                SeqMap ((
                    seq_update ((m0_13)) ((x_16) * (usize 32)) (
                      array_to_seq (sender_address_11)),
                    seq_update ((m1_14)) ((x_16) * (usize 8)) (
                      array_to_seq (u64_to_be_bytes (amount_12)))
                  ))
              )) in 
          (res_15)) else ((res_15)) in 
      (res_15))
    res_15 in 
  res_15.

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
#[global] Instance gen_bid_error_hacspec_t : Gen (bid_error_hacspec_t) := Build_Gen bid_error_hacspec_t g_bid_error_hacspec_t.


Notation "'auction_bid_result_t'" := ((
  result state_hacspec_t bid_error_hacspec_t)) : hacspec_scope.

Definition auction_bid_hacspec
  (ctx_17 : context_t)
  (amount_18 : int64)
  (state_19 : state_hacspec_t)
  
  : auction_bid_result_t :=
  let 'StateHacspec ((
        auction_state_20,
        highest_bid_21,
        st2_22,
        expiry_23,
        st4_24
      )) :=
    (state_19) in 
  ifbnd negb ((auction_state_20) =.? (NotSoldYet)) : bool
  thenbnd (bind (@Err state_hacspec_t bid_error_hacspec_t (
        AuctionIsFinalized)) (fun _ => @Ok unit bid_error_hacspec_t (tt)))
  else (tt) >> (fun 'tt =>
  let 'Context ((owner_25, sender_26, balance_27, slot_time_28)) :=
    ctx_17 in 
  ifbnd negb ((slot_time_28) <=.? (expiry_23)) : bool
  thenbnd (bind (@Err state_hacspec_t bid_error_hacspec_t (
        BidsOverWaitingForAuctionFinalization)) (fun _ =>
      @Ok unit bid_error_hacspec_t (tt)))
  else (tt) >> (fun 'tt =>
  let '(bid_to_update_29, new_map_30) :=
    seq_map_entry ((st4_24)) (sender_26) in 
  let '(updated_bid_31, updated_map_32) :=
    match seq_map_update_entry ((st4_24)) (sender_26) ((bid_to_update_29) .+ (
        amount_18)) with
    | Update ((updated_bid_33, updated_map_34)) => (
      updated_bid_33,
      updated_map_34
    )
    end in 
  ifbnd negb ((updated_bid_31) >.? (highest_bid_21)) : bool
  thenbnd (bind (@Err state_hacspec_t bid_error_hacspec_t (BidTooLow)) (fun _ =>
      @Ok unit bid_error_hacspec_t (tt)))
  else (tt) >> (fun 'tt =>
  @Ok state_hacspec_t bid_error_hacspec_t (StateHacspec ((
        auction_state_20,
        updated_bid_31,
        st2_22,
        expiry_23,
        updated_map_32
      )))))).

Definition auction_bid
  (ctx_35 : context_state_hacspec_t)
  (amount_36 : int64)
  
  : (option (context_state_hacspec_t '× list_action_t)) :=
  let s_37 : seq has_action_t :=
    seq_new_ (default : has_action_t) (usize 0) in 
  @Some (context_state_hacspec_t '× list_action_t) ((ctx_35, s_37)).

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
#[global] Instance gen_finalize_error_hacspec_t : Gen (finalize_error_hacspec_t) := Build_Gen finalize_error_hacspec_t g_finalize_error_hacspec_t.


Notation "'finalize_context_t'" := ((int64 '× user_address_t '× int64
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
#[global] Instance gen_finalize_action_t : Gen (finalize_action_t) := Build_Gen finalize_action_t g_finalize_action_t.


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
#[global] Instance gen_bid_remain_t : Gen (bid_remain_t) := Build_Gen bid_remain_t g_bid_remain_t.


Notation "'auction_finalize_result_t'" := ((result (
    state_hacspec_t '×
    finalize_action_t
  ) finalize_error_hacspec_t)) : hacspec_scope.

Definition auction_finalize_hacspec
  (ctx_38 : finalize_context_t)
  (state_39 : state_hacspec_t)
  
  : auction_finalize_result_t :=
  let 'StateHacspec ((
        auction_state_40,
        highest_bid_41,
        st2_42,
        expiry_43,
        SeqMap ((m0_44, m1_45))
      )) :=
    (state_39) in 
  let result_46 : (result (state_hacspec_t '× finalize_action_t
      ) finalize_error_hacspec_t) :=
    @Ok (state_hacspec_t '× finalize_action_t) finalize_error_hacspec_t ((
        (state_39),
        Accept
      )) in 
  ifbnd negb ((auction_state_40) =.? (NotSoldYet)) : bool
  thenbnd (bind (@Err (state_hacspec_t '× finalize_action_t
      ) finalize_error_hacspec_t (AuctionFinalized)) (fun _ =>
      @Ok unit finalize_error_hacspec_t (tt)))
  else (tt) >> (fun 'tt =>
  let '(slot_time_47, owner_48, balance_49) :=
    ctx_38 in 
  ifbnd negb ((slot_time_47) >.? (expiry_43)) : bool
  thenbnd (bind (@Err (state_hacspec_t '× finalize_action_t
      ) finalize_error_hacspec_t (AuctionStillActive)) (fun _ =>
      @Ok unit finalize_error_hacspec_t (tt)))
  else (tt) >> (fun 'tt =>
  ifbnd (balance_49) !=.? (@repr WORDSIZE64 0) : bool
  thenbnd (let return_action_50 : finalize_action_t :=
      SimpleTransfer (seq_concat (seq_concat (seq_new_ (default : int8) (
              usize 0)) (array_to_seq (owner_48))) (
          array_to_seq (u64_to_be_bytes (highest_bid_41)))) in 
    let remaining_bid_51 : bid_remain_t :=
      BidNone in 
    bind (foldibnd (usize 0) to ((seq_len ((m0_44))) / (usize 32)) for (
        auction_state_40,
        return_action_50,
        remaining_bid_51
      ) >> (fun x_52 '(auction_state_40, return_action_50, remaining_bid_51) =>
      let addr_53 : user_address_t :=
        array_from_seq (32) (seq_slice ((m0_44)) ((x_52) * (usize 32)) (
            usize 32)) in 
      let amnt_54 : int64 :=
        u64_from_be_bytes (array_from_seq (8) (seq_slice ((m1_45)) ((x_52) * (
                usize 8)) (usize 8))) in 
      ifbnd (amnt_54) <.? (highest_bid_41) : bool
      then (let return_action_50 :=
          match return_action_50 with
          | Accept => Accept
          | SimpleTransfer (m_55) => SimpleTransfer (seq_concat (seq_concat (
                m_55) (array_to_seq (addr_53))) (array_to_seq (u64_to_be_bytes (
                amnt_54))))
          end in 
        (auction_state_40, return_action_50, remaining_bid_51))
      elsebnd(ifbnd negb ((remaining_bid_51) =.? (BidNone)) : bool
        thenbnd (bind (@Err (state_hacspec_t '× finalize_action_t
            ) finalize_error_hacspec_t (BidMapError)) (fun _ =>
            @Ok unit finalize_error_hacspec_t (tt)))
        else (tt) >> (fun 'tt =>
        let auction_state_40 :=
          Sold (addr_53) in 
        let remaining_bid_51 :=
          BidSome (amnt_54) in 
        @Ok (auction_state_hacspec_t '× finalize_action_t '× bid_remain_t
        ) finalize_error_hacspec_t ((
            auction_state_40,
            return_action_50,
            remaining_bid_51
          )))) >> (fun '(auction_state_40, return_action_50, remaining_bid_51
      ) =>
      @Ok (auction_state_hacspec_t '× finalize_action_t '× bid_remain_t
      ) finalize_error_hacspec_t ((
          auction_state_40,
          return_action_50,
          remaining_bid_51
        ))))) (fun '(auction_state_40, return_action_50, remaining_bid_51) =>
      let result_46 :=
        match remaining_bid_51 with
        | BidSome (amount_56) => (if (negb ((amount_56) =.? (
                highest_bid_41))):bool then (@Err (
              state_hacspec_t '×
              finalize_action_t
            ) finalize_error_hacspec_t (BidMapError)) else (@Ok (
              state_hacspec_t '×
              finalize_action_t
            ) finalize_error_hacspec_t ((
                StateHacspec ((
                    auction_state_40,
                    highest_bid_41,
                    st2_42,
                    expiry_43,
                    SeqMap (((m0_44), (m1_45)))
                  )),
                return_action_50
              ))))
        | BidNone => @Err (state_hacspec_t '× finalize_action_t
        ) finalize_error_hacspec_t (BidMapError)
        end in 
      bind ((result_46)) (fun _ => @Ok (
          auction_state_hacspec_t '×
          (result (state_hacspec_t '× finalize_action_t
            ) finalize_error_hacspec_t)
        ) finalize_error_hacspec_t ((auction_state_40, result_46)))))
  else ((auction_state_40, result_46)) >> (fun '(auction_state_40, result_46) =>
  result_46))).

Definition auction_finalize
  (ctx_57 : context_state_hacspec_t)
  
  : (option (context_state_hacspec_t '× list_action_t)) :=
  let s_58 : seq has_action_t :=
    seq_new_ (default : has_action_t) (usize 0) in 
  @Some (context_state_hacspec_t '× list_action_t) ((ctx_57, s_58)).

Definition auction_test_init
  (item_59 : public_byte_seq)
  (time_60 : int64)
  
  : bool :=
  (fresh_state_hacspec ((item_59)) (time_60)) =.? (StateHacspec ((
        NotSoldYet,
        @repr WORDSIZE64 0,
        (item_59),
        time_60,
        SeqMap ((
            seq_new_ (default : int8) (usize 0),
            seq_new_ (default : int8) (usize 0)
          ))
      ))).

Theorem ensures_auction_test_init : forall result_61 (
  item_59 : public_byte_seq) (time_60 : int64),
 @auction_test_init item_59 time_60 = result_61 ->
 result_61 = true.
 Proof. Admitted.
(*QuickChick (
  forAll g_public_byte_seq (fun item_59 : public_byte_seq =>forAll g_int64 (fun time_60 : int64 =>auction_test_init item_59 time_60))).*)


Definition verify_bid
  (item_62 : public_byte_seq)
  (state_63 : state_hacspec_t)
  (account_64 : user_address_t)
  (ctx_65 : context_t)
  (amount_66 : int64)
  (bid_map_67 : seq_map_t)
  (highest_bid_68 : int64)
  (time_69 : int64)
  
  : (state_hacspec_t '× seq_map_t '× bool '× bool) :=
  let t_70 : (result state_hacspec_t bid_error_hacspec_t) :=
    auction_bid_hacspec (ctx_65) (amount_66) ((state_63)) in 
  let '(state_71, res_72) :=
    match t_70 with
    | Err (e_73) => (state_63, false)
    | Ok (s_74) => (s_74, true)
    end in 
  let bid_map_75 : seq_map_t :=
    match seq_map_update_entry ((bid_map_67)) (account_64) (highest_bid_68) with
    | Update ((_, updated_map_76)) => updated_map_76
    end in 
  (
    (state_71),
    (bid_map_75),
    res_72,
    ((state_71)) =.? (StateHacspec ((
          NotSoldYet,
          highest_bid_68,
          (item_62),
          time_69,
          (bid_map_75)
        )))
  ).
