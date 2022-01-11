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

Notation "'reject_hacspec_t'" := (int32) : hacspec_scope.

Definition reject_impl_deafult  : reject_hacspec_t :=
  min_v.

Definition new_reject_impl (x_0 : int32) : (option reject_hacspec_t) :=
  (if ((x_0) <.? (@repr WORDSIZE32 0)):bool then (@Some int32 (x_0)) else (
      @None int32)).

Definition reject_impl_convert_from_unit  : reject_hacspec_t :=
  (min_v) .+ (@repr WORDSIZE32 1).

Theorem ensures_reject_impl_convert_from_unit : forall result_1 ,
@reject_impl_convert_from_unit  = result_1 ->
~ (result_1 = @repr WORDSIZE32 0).
Proof. Admitted.

Definition reject_impl_convert_from_parse_error  : reject_hacspec_t :=
  (min_v) .+ (@repr WORDSIZE32 2).

Theorem ensures_reject_impl_convert_from_parse_error : forall result_1 ,
@reject_impl_convert_from_parse_error  = result_1 ->
~ (result_1 = @repr WORDSIZE32 0).
Proof. Admitted.

Inductive log_error_t :=
| Full : log_error_t
| Malformed : log_error_t.
Global Instance show_log_error_t : Show (log_error_t) :=
 @Build_Show (log_error_t) (fun x =>
 match x with
 Full => ("Full")%string
 | Malformed => ("Malformed")%string
 end).
Definition g_log_error_t : G (log_error_t) := oneOf_ (returnGen Full) [returnGen Full;returnGen Malformed].
Global Instance gen_log_error_t : Gen (log_error_t) := Build_Gen log_error_t g_log_error_t.


Definition reject_impl_from_log_error (le_2 : log_error_t) : reject_hacspec_t :=
  match le_2 with
  | Full => (min_v) .+ (@repr WORDSIZE32 3)
  | Malformed => (min_v) .+ (@repr WORDSIZE32 4)
  end.

Theorem ensures_reject_impl_from_log_error : forall result_1 (
  le_2 : log_error_t),
@reject_impl_from_log_error le_2 = result_1 ->
~ (result_1 = @repr WORDSIZE32 0).
Proof. Admitted.

Inductive new_contract_name_error_t :=
| NewContractNameErrorMissingInitPrefix : new_contract_name_error_t
| NewContractNameErrorTooLong : new_contract_name_error_t
| NewContractNameErrorContainsDot : new_contract_name_error_t
| NewContractNameErrorInvalidCharacters : new_contract_name_error_t.
Global Instance show_new_contract_name_error_t : Show (new_contract_name_error_t) :=
 @Build_Show (new_contract_name_error_t) (fun x =>
 match x with
 NewContractNameErrorMissingInitPrefix => (
   "NewContractNameErrorMissingInitPrefix")%string
 | NewContractNameErrorTooLong => ("NewContractNameErrorTooLong")%string
 | NewContractNameErrorContainsDot => ("NewContractNameErrorContainsDot")%string
 | NewContractNameErrorInvalidCharacters => (
   "NewContractNameErrorInvalidCharacters")%string
 end).
Definition g_new_contract_name_error_t : G (new_contract_name_error_t) := oneOf_ (returnGen NewContractNameErrorMissingInitPrefix) [returnGen NewContractNameErrorMissingInitPrefix;returnGen NewContractNameErrorTooLong;returnGen NewContractNameErrorContainsDot;returnGen NewContractNameErrorInvalidCharacters].
Global Instance gen_new_contract_name_error_t : Gen (new_contract_name_error_t) := Build_Gen new_contract_name_error_t g_new_contract_name_error_t.


Definition reject_impl_from_new_contract_name_error
  (nre_3 : new_contract_name_error_t)
  : reject_hacspec_t :=
  match nre_3 with
  | NewContractNameErrorMissingInitPrefix => (min_v) .+ (@repr WORDSIZE32 5)
  | NewContractNameErrorTooLong => (min_v) .+ (@repr WORDSIZE32 6)
  | NewContractNameErrorContainsDot => (min_v) .+ (@repr WORDSIZE32 9)
  | NewContractNameErrorInvalidCharacters => (min_v) .+ (@repr WORDSIZE32 10)
  end.

Theorem ensures_reject_impl_from_new_contract_name_error : forall result_1 (
  nre_3 : new_contract_name_error_t),
@reject_impl_from_new_contract_name_error nre_3 = result_1 ->
~ (result_1 = @repr WORDSIZE32 0).
Proof. Admitted.

Inductive new_receive_name_error_t :=
| NewReceiveNameErrorMissingDotSeparator : new_receive_name_error_t
| NewReceiveNameErrorTooLong : new_receive_name_error_t
| NewReceiveNameErrorInvalidCharacters : new_receive_name_error_t.
Global Instance show_new_receive_name_error_t : Show (new_receive_name_error_t) :=
 @Build_Show (new_receive_name_error_t) (fun x =>
 match x with
 NewReceiveNameErrorMissingDotSeparator => (
   "NewReceiveNameErrorMissingDotSeparator")%string
 | NewReceiveNameErrorTooLong => ("NewReceiveNameErrorTooLong")%string
 | NewReceiveNameErrorInvalidCharacters => (
   "NewReceiveNameErrorInvalidCharacters")%string
 end).
Definition g_new_receive_name_error_t : G (new_receive_name_error_t) := oneOf_ (returnGen NewReceiveNameErrorMissingDotSeparator) [returnGen NewReceiveNameErrorMissingDotSeparator;returnGen NewReceiveNameErrorTooLong;returnGen NewReceiveNameErrorInvalidCharacters].
Global Instance gen_new_receive_name_error_t : Gen (new_receive_name_error_t) := Build_Gen new_receive_name_error_t g_new_receive_name_error_t.


Definition reject_impl_from_new_receive_name_error
  (nre_4 : new_receive_name_error_t)
  : reject_hacspec_t :=
  match nre_4 with
  | NewReceiveNameErrorMissingDotSeparator => (min_v) .+ (@repr WORDSIZE32 7)
  | NewReceiveNameErrorTooLong => (min_v) .+ (@repr WORDSIZE32 8)
  | NewReceiveNameErrorInvalidCharacters => (min_v) .+ (@repr WORDSIZE32 11)
  end.

Theorem ensures_reject_impl_from_new_receive_name_error : forall result_1 (
  nre_4 : new_receive_name_error_t),
@reject_impl_from_new_receive_name_error nre_4 = result_1 ->
~ (result_1 = @repr WORDSIZE32 0).
Proof. Admitted.

Notation "'contract_state_hacspec_t'" := (int32) : hacspec_scope.

Inductive seek_from_t :=
| Start : int64 -> seek_from_t
| End : int64 -> seek_from_t
| Current : int64 -> seek_from_t.
Global Instance show_seek_from_t : Show (seek_from_t) :=
 @Build_Show (seek_from_t) (fun x =>
 match x with
 Start a => ("Start" ++ show a)%string
 | End a => ("End" ++ show a)%string
 | Current a => ("Current" ++ show a)%string
 end).
Definition g_seek_from_t : G (seek_from_t) := oneOf_ (bindGen arbitrary (fun a => returnGen (Start a))) [bindGen arbitrary (fun a => returnGen (Start a));bindGen arbitrary (fun a => returnGen (End a));bindGen arbitrary (fun a => returnGen (Current a))].
Global Instance gen_seek_from_t : Gen (seek_from_t) := Build_Gen seek_from_t g_seek_from_t.


Notation "'uint32_option_t'" := ((option int32)) : hacspec_scope.

Notation "'iint64_option_t'" := ((option int64)) : hacspec_scope.

Definition contract_state_impl_seek
  (current_position_5 : contract_state_hacspec_t)
  (pos_6 : seek_from_t)
  : (result (contract_state_hacspec_t × int64) unit) :=
  match pos_6 with
  | Start offset_7 => @Ok (contract_state_hacspec_t × int64) unit ((
      @cast _ uint32 _ (offset_7),
      offset_7
    ))
  | End delta_8 => (if ((delta_8) >=.? (@repr WORDSIZE64 0)):bool then (
      match pub_uint32_checked_add (current_position_5) (@cast _ uint32 _ (
          delta_8)) with
      | Some b_9 => @Ok (contract_state_hacspec_t × int64) unit ((
          b_9,
          @cast _ uint64 _ (delta_8)
        ))
      | None => @Err (contract_state_hacspec_t × int64) unit (tt)
      end) else (match pub_int64_checked_abs (delta_8) with
      | Some b_10 => @Ok (contract_state_hacspec_t × int64) unit ((
          (@repr WORDSIZE32 4) .- (@cast _ uint32 _ (b_10)),
          @cast _ uint64 _ ((@repr WORDSIZE32 4) .- (@cast _ uint32 _ (b_10)))
        ))
      | None => @Err (contract_state_hacspec_t × int64) unit (tt)
      end))
  | Current delta_11 => (if ((delta_11) >=.? (@repr WORDSIZE64 0)):bool then (
      match pub_uint32_checked_add (current_position_5) (@cast _ uint32 _ (
          delta_11)) with
      | Some offset_12 => @Ok (contract_state_hacspec_t × int64) unit ((
          offset_12,
          @cast _ uint64 _ (offset_12)
        ))
      | None => @Err (contract_state_hacspec_t × int64) unit (tt)
      end) else (match pub_int64_checked_abs (delta_11) with
      | Some b_13 => match pub_uint32_checked_sub (current_position_5) (
        @cast _ uint32 _ (b_13)) with
      | Some offset_14 => @Ok (contract_state_hacspec_t × int64) unit ((
          offset_14,
          @cast _ uint64 _ (offset_14)
        ))
      | None => @Err (contract_state_hacspec_t × int64) unit (tt)
      end
      | None => @Err (contract_state_hacspec_t × int64) unit (tt)
      end))
  end.

Definition load_state_hacspec
  (buf_15 : public_byte_seq)
  (offset_16 : int32)
  : (public_byte_seq × int32) :=
  (buf_15, @repr WORDSIZE32 1).

Definition contract_state_impl_read_read
  (current_position_17 : contract_state_hacspec_t)
  (buf_18 : public_byte_seq)
  : (contract_state_hacspec_t × uint_size) :=
  let '(buf_19, num_read_20) :=
    load_state_hacspec (buf_18) (current_position_17) in 
  ((current_position_17) .+ (num_read_20), @cast _ uint32 _ (num_read_20)).

Definition contract_state_impl_read_read_u64
  (current_position_21 : contract_state_hacspec_t)
  : (contract_state_hacspec_t × int64) :=
  let buf_22 : seq int8 :=
    seq_new_ (default) (usize 8) in 
  let '(buf_23, num_read_24) :=
    load_state_hacspec (buf_22) (current_position_21) in 
  (
    (current_position_21) .+ (num_read_24),
    u64_from_le_bytes (array_from_seq (8) (buf_23))
  ).

Definition contract_state_impl_read_read_u32
  (current_position_25 : contract_state_hacspec_t)
  : (contract_state_hacspec_t × int32) :=
  let buf_26 : seq int8 :=
    seq_new_ (default) (usize 4) in 
  let '(buf_27, num_read_28) :=
    load_state_hacspec (buf_26) (current_position_25) in 
  (
    (current_position_25) .+ (num_read_28),
    u32_from_le_bytes (array_from_seq (4) (buf_27))
  ).

Definition contract_state_impl_read_read_u8
  (current_position_29 : contract_state_hacspec_t)
  : (contract_state_hacspec_t × int8) :=
  let buf_30 : seq int8 :=
    seq_new_ (default) (usize 1) in 
  let '(buf_31, num_read_32) :=
    load_state_hacspec (buf_30) (current_position_29) in 
  ((current_position_29) .+ (num_read_32), seq_index (buf_31) (usize 0)).

Definition write_state_hacspec
  (buf_33 : public_byte_seq)
  (offset_34 : int32)
  : (public_byte_seq × int32) :=
  (buf_33, @repr WORDSIZE32 1).

Definition contract_state_impl_write
  (current_position_35 : contract_state_hacspec_t)
  (buf_36 : public_byte_seq)
  : (result (contract_state_hacspec_t × uint_size) unit) :=
  ifbnd option_is_none (pub_uint32_checked_add (current_position_35) (pub_u32 (
        seq_len (buf_36)))) : bool
  thenbnd (bind (@Err (contract_state_hacspec_t × uint_size) unit (tt)) (
      fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_37, num_bytes_38) :=
    write_state_hacspec (buf_36) (current_position_35) in 
  @Ok (contract_state_hacspec_t × uint_size) unit ((
      (current_position_35) .+ (num_bytes_38),
      @cast _ uint32 _ (num_bytes_38)
    ))).

Definition state_size_hacspec  : int32 :=
  @repr WORDSIZE32 1.

Definition resize_state_hacspec (new_size_39 : int32) : int32 :=
  @repr WORDSIZE32 1.

Definition has_contract_state_impl_for_contract_state_open
  
  : contract_state_hacspec_t :=
  @repr WORDSIZE32 0.

Definition has_contract_state_impl_for_contract_state_reserve
  (contract_state_40 : contract_state_hacspec_t)
  (len_41 : int32)
  : bool :=
  let cur_size_42 : int32 :=
    state_size_hacspec  in 
  (if ((cur_size_42) <.? (len_41)):bool then ((resize_state_hacspec (
          len_41)) =.? (@repr WORDSIZE32 1)) else (true)).

Definition has_contract_state_impl_for_contract_state_truncate
  (current_position_43 : contract_state_hacspec_t)
  (cur_size_44 : int32)
  (new_size_45 : int32)
  : contract_state_hacspec_t :=
  let 'tt :=
    if (cur_size_44) >.? (new_size_45):bool then (let _ : int32 :=
        resize_state_hacspec (new_size_45) in 
      tt) else (tt) in 
  (if ((new_size_45) <.? (current_position_43)):bool then (new_size_45) else (
      current_position_43)).

Definition get_parameter_section_hacspec
  (buf_46 : public_byte_seq)
  (offset_47 : int32)
  : (public_byte_seq × int32) :=
  (buf_46, @repr WORDSIZE32 1).

Notation "'parameter_hacspec_t'" := (int32) : hacspec_scope.

Definition read_impl_for_parameter_read
  (current_position_48 : parameter_hacspec_t)
  (buf_49 : public_byte_seq)
  : (parameter_hacspec_t × uint_size) :=
  let '(buf_50, num_read_51) :=
    get_parameter_section_hacspec (buf_49) (current_position_48) in 
  ((current_position_48) .+ (num_read_51), @cast _ uint32 _ (num_read_51)).

Definition get_parameter_size_hacspec  : int32 :=
  @repr WORDSIZE32 1.

Definition get_slot_time_hacspec  : int64 :=
  @repr WORDSIZE64 1.

Definition get_policy_section_hacspec
  (policy_bytes_52 : public_byte_seq)
  (offset_53 : int32)
  : (public_byte_seq × int32) :=
  (policy_bytes_52, @repr WORDSIZE32 1).

Notation "'attributes_cursor_hacspec_t'" := ((int32 × int16)) : hacspec_scope.
Instance show_attributes_cursor_hacspec_t : Show (attributes_cursor_hacspec_t) :=
Build_Show attributes_cursor_hacspec_t (fun x =>
  let (x, x0) := x in
  (("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ (")"))))))%string.
Definition g_attributes_cursor_hacspec_t : G (attributes_cursor_hacspec_t) :=
bindGen arbitrary (fun x0 : int32 =>
  bindGen arbitrary (fun x1 : int16 =>
  returnGen (x0,x1))).
Instance gen_attributes_cursor_hacspec_t : Gen (attributes_cursor_hacspec_t) := Build_Gen attributes_cursor_hacspec_t g_attributes_cursor_hacspec_t.


Definition has_policy_impl_for_policy_attributes_cursor_next_item
  (policy_attribute_items_54 : attributes_cursor_hacspec_t)
  (buf_55 : public_byte_seq)
  : (option (attributes_cursor_hacspec_t × (int8 × int8))) :=
  let '(current_position_56, remaining_items_57) :=
    policy_attribute_items_54 in 
  ifbnd (remaining_items_57) =.? (@repr WORDSIZE16 0) : bool
  thenbnd (bind (@None (attributes_cursor_hacspec_t × (int8 × int8))) (
      fun _ => Some (tt)))
  else (tt) >> (fun 'tt =>
  let '(tag_value_len_58, num_read_59) :=
    get_policy_section_hacspec (seq_new_ (default) (usize 2)) (
      current_position_56) in 
  let current_position_56 :=
    (current_position_56) .+ (num_read_59) in 
  ifbnd (seq_index (tag_value_len_58) (usize 1)) >.? (@repr WORDSIZE8 31) : bool
  thenbnd (bind (@None (attributes_cursor_hacspec_t × (int8 × int8))) (
      fun _ => Some (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_60, num_read_61) :=
    get_policy_section_hacspec (buf_55) (current_position_56) in 
  let current_position_56 :=
    (current_position_56) .+ (num_read_61) in 
  let remaining_items_57 :=
    (remaining_items_57) .- (@repr WORDSIZE16 1) in 
  @Some (attributes_cursor_hacspec_t × (int8 × int8)) ((
      (current_position_56, remaining_items_57),
      (
        seq_index (tag_value_len_58) (usize 0),
        seq_index (tag_value_len_58) (usize 1)
      )
    )))).

Notation "'policies_iterator_hacspec_t'" := ((int32 × int16)) : hacspec_scope.
Instance show_policies_iterator_hacspec_t : Show (policies_iterator_hacspec_t) :=
Build_Show policies_iterator_hacspec_t (fun x =>
  let (x, x0) := x in
  (("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ (")"))))))%string.
Definition g_policies_iterator_hacspec_t : G (policies_iterator_hacspec_t) :=
bindGen arbitrary (fun x0 : int32 =>
  bindGen arbitrary (fun x1 : int16 =>
  returnGen (x0,x1))).
Instance gen_policies_iterator_hacspec_t : Gen (policies_iterator_hacspec_t) := Build_Gen policies_iterator_hacspec_t g_policies_iterator_hacspec_t.


Notation "'policy_attributes_cursor_hacspec_t'" := ((
  int32 ×
  int64 ×
  int64 ×
  attributes_cursor_hacspec_t
)) : hacspec_scope.
Instance show_policy_attributes_cursor_hacspec_t : Show (policy_attributes_cursor_hacspec_t) :=
Build_Show policy_attributes_cursor_hacspec_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  let (x, x2) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ ((",") ++ ((show x2) ++ (")"))))))))))%string.
Definition g_policy_attributes_cursor_hacspec_t : G (policy_attributes_cursor_hacspec_t) :=
bindGen arbitrary (fun x0 : int32 =>
  bindGen arbitrary (fun x1 : int64 =>
  bindGen arbitrary (fun x2 : int64 =>
  bindGen arbitrary (fun x3 : attributes_cursor_hacspec_t =>
  returnGen (x0,x1,x2,x3))))).
Instance gen_policy_attributes_cursor_hacspec_t : Gen (policy_attributes_cursor_hacspec_t) := Build_Gen policy_attributes_cursor_hacspec_t g_policy_attributes_cursor_hacspec_t.


Definition iterator_impl_for_policies_iterator_next
  (policies_iterator_62 : policies_iterator_hacspec_t)
  : (option (policies_iterator_hacspec_t × policy_attributes_cursor_hacspec_t
    )) :=
  let '(pos_63, remaining_items_64) :=
    policies_iterator_62 in 
  ifbnd (remaining_items_64) =.? (@repr WORDSIZE16 0) : bool
  thenbnd (bind (@None (
        policies_iterator_hacspec_t ×
        policy_attributes_cursor_hacspec_t
      )) (fun _ => Some (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_65, _) :=
    get_policy_section_hacspec (seq_new_ (default) (((((usize 2) + (
                usize 4)) + (usize 8)) + (usize 8)) + (usize 2))) (pos_63) in 
  let skip_part_66 : public_byte_seq :=
    seq_slice_range (buf_65) ((usize 0, usize 2)) in 
  let ip_part_67 : public_byte_seq :=
    seq_slice_range (buf_65) ((usize 2, (usize 2) + (usize 4))) in 
  let created_at_part_68 : public_byte_seq :=
    seq_slice_range (buf_65) ((
        (usize 2) + (usize 4),
        ((usize 2) + (usize 4)) + (usize 8)
      )) in 
  let valid_to_part_69 : public_byte_seq :=
    seq_slice_range (buf_65) ((
        ((usize 2) + (usize 4)) + (usize 8),
        (((usize 2) + (usize 4)) + (usize 8)) + (usize 8)
      )) in 
  let len_part_70 : public_byte_seq :=
    seq_slice_range (buf_65) ((
        (((usize 2) + (usize 4)) + (usize 8)) + (usize 8),
        ((((usize 2) + (usize 4)) + (usize 8)) + (usize 8)) + (usize 2)
      )) in 
  let identity_provider_71 : int32 :=
    u32_from_le_bytes (array_from_seq (4) (ip_part_67)) in 
  let created_at_72 : int64 :=
    u64_from_le_bytes (array_from_seq (8) (created_at_part_68)) in 
  let valid_to_73 : int64 :=
    u64_from_le_bytes (array_from_seq (8) (valid_to_part_69)) in 
  let remaining_items_74 : int16 :=
    u16_from_le_bytes (array_from_seq (2) (len_part_70)) in 
  let attributes_start_75 : int32 :=
    (((((pos_63) .+ (@repr WORDSIZE32 2)) .+ (@repr WORDSIZE32 4)) .+ (
          @repr WORDSIZE32 8)) .+ (@repr WORDSIZE32 8)) .+ (
      @repr WORDSIZE32 2) in 
  let pos_63 :=
    ((pos_63) .+ (@cast _ uint32 _ (u16_from_le_bytes (array_from_seq (2) (
              skip_part_66))))) .+ (@repr WORDSIZE32 2) in 
  let remaining_items_74 :=
    (remaining_items_74) .- (@repr WORDSIZE16 1) in 
  @Some (policies_iterator_hacspec_t × policy_attributes_cursor_hacspec_t) ((
      (pos_63, remaining_items_74),
      (
        identity_provider_71,
        created_at_72,
        valid_to_73,
        (attributes_start_75, remaining_items_74)
      )
    ))).

Definition get_init_origin_hacspec
  (start_76 : public_byte_seq)
  : public_byte_seq :=
  start_76.

Definition get_receive_invoker_hacspec
  (start_77 : public_byte_seq)
  : public_byte_seq :=
  start_77.

Definition get_receive_self_address_hacspec
  (start_78 : public_byte_seq)
  : public_byte_seq :=
  start_78.

Definition get_receive_self_balance_hacspec  : int64 :=
  @repr WORDSIZE64 1.

Definition get_receive_sender_hacspec
  (start_79 : public_byte_seq)
  : public_byte_seq :=
  start_79.

Definition get_receive_owner_hacspec
  (start_80 : public_byte_seq)
  : public_byte_seq :=
  start_80.

Definition log_event_hacspec
  (start_81 : public_byte_seq)
  : (public_byte_seq × int32) :=
  (start_81, @repr WORDSIZE32 1).

Definition accept_hacspec  : int32 :=
  @repr WORDSIZE32 1.

Definition simple_transfer_hacspec
  (buf_82 : public_byte_seq)
  (amount_83 : int64)
  : int32 :=
  @repr WORDSIZE32 1.

Definition send_hacspec
  (addr_index_84 : int64)
  (addr_subindex_85 : int64)
  (receive_name_86 : public_byte_seq)
  (amount_87 : int64)
  (parameter_88 : public_byte_seq)
  : int32 :=
  @repr WORDSIZE32 1.

Definition combine_and_hacspec (l_89 : int32) (r_90 : int32) : int32 :=
  @repr WORDSIZE32 1.

Definition combine_or_hacspec (l_91 : int32) (r_92 : int32) : int32 :=
  @repr WORDSIZE32 1.

Definition user_address_t := nseq (int8) (usize 32).

Inductive auction_state_t :=
| NotSoldYet : auction_state_t
| Sold : user_address_t -> auction_state_t.

Definition eqb_auction_state_t (x y : auction_state_t) : bool :=
match x with
   | NotSoldYet => match y with | NotSoldYet=> true | _ => false end
   | Sold a => match y with | Sold b => a =.? b | _ => false end
   end.

Definition eqb_leibniz_auction_state_t (x y : auction_state_t) : eqb_auction_state_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_auction_state_t : EqDec (auction_state_t) :=
Build_EqDec (auction_state_t) (eqb_auction_state_t) (eqb_leibniz_auction_state_t).

Global Instance show_auction_state_t : Show (auction_state_t) :=
 @Build_Show (auction_state_t) (fun x =>
 match x with
 NotSoldYet => ("NotSoldYet")%string
 | Sold a => ("Sold" ++ show a)%string
 end).
Definition g_auction_state_t : G (auction_state_t) := oneOf_ (returnGen NotSoldYet) [returnGen NotSoldYet;bindGen arbitrary (fun a => returnGen (Sold a))].
Global Instance gen_auction_state_t : Gen (auction_state_t) := Build_Gen auction_state_t g_auction_state_t.


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


Notation "'amount_hacspec_t'" := (int64) : hacspec_scope.

Notation "'timestamp_hacspec_t'" := (int64) : hacspec_scope.

Notation "'itemtyp_t'" := (public_byte_seq) : hacspec_scope.

Inductive state_t :=
| State : (
  auction_state_t ×
  amount_hacspec_t ×
  itemtyp_t ×
  timestamp_hacspec_t ×
  seq_map_t
) -> state_t.

Definition eqb_state_t (x y : state_t) : bool :=
match x with
   | State a => match y with | State b => a =.? b end
   end.

Definition eqb_leibniz_state_t (x y : state_t) : eqb_state_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_state_t : EqDec (state_t) :=
Build_EqDec (state_t) (eqb_state_t) (eqb_leibniz_state_t).

Global Instance show_state_t : Show (state_t) :=
 @Build_Show (state_t) (fun x =>
 match x with
 State a => ("State" ++ show a)%string
 end).
Definition g_state_t : G (state_t) := oneOf_ (bindGen arbitrary (fun a => returnGen (State a))) [bindGen arbitrary (fun a => returnGen (State a))].
Global Instance gen_state_t : Gen (state_t) := Build_Gen state_t g_state_t.


Definition fresh_state (itm_93 : itemtyp_t) (exp_94 : int64) : state_t :=
  State ((
      NotSoldYet,
      @repr WORDSIZE64 0,
      itm_93,
      exp_94,
      SeqMap ((seq_new_ (default) (usize 0), seq_new_ (default) (usize 0)))
    )).

Theorem ensures_fresh_state : forall result_1 (itm_93 : itemtyp_t) (
  exp_94 : int64),
@fresh_state itm_93 exp_94 = result_1 ->
true.
Proof. Admitted.

Definition seq_map_entry
  (m_95 : seq_map_t)
  (sender_address_96 : user_address_t)
  : (int64 × seq_map_t) :=
  let 'SeqMap ((m0_97, m1_98)) :=
    m_95 in 
  let res_99 : (int64 × seq_map_t) :=
    (
      @repr WORDSIZE64 0,
      SeqMap ((
          seq_concat ((m0_97)) (sender_address_96),
          seq_concat ((m1_98)) (u64_to_be_bytes (@repr WORDSIZE64 0))
        ))
    ) in 
  let res_99 :=
    foldi (usize 0) ((seq_len ((m0_97))) / (usize 32)) (fun x_100 res_99 =>
      let '(res_99) :=
        if (array_from_seq (32) (seq_slice ((m0_97)) ((x_100) * (usize 32)) (
              usize 32))) array_eq (sender_address_96):bool then (let res_99 :=
            (
              u64_from_be_bytes (array_from_seq (8) (seq_slice ((m1_98)) ((
                      x_100) * (usize 8)) (usize 8))),
              SeqMap (((m0_97), (m1_98)))
            ) in 
          (res_99)) else ((res_99)) in 
      (res_99))
    res_99 in 
  res_99.

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
  (m_101 : seq_map_t)
  (sender_address_102 : user_address_t)
  (amount_103 : int64)
  : map_update_t :=
  let 'SeqMap ((m0_104, m1_105)) :=
    m_101 in 
  let res_106 : map_update_t :=
    Update ((
        amount_103,
        SeqMap ((
            seq_concat ((m0_104)) (sender_address_102),
            seq_concat ((m1_105)) (u64_to_be_bytes (amount_103))
          ))
      )) in 
  let res_106 :=
    foldi (usize 0) ((seq_len ((m0_104))) / (usize 32)) (fun x_107 res_106 =>
      let '(res_106) :=
        if (array_from_seq (32) (seq_slice ((m0_104)) ((x_107) * (usize 32)) (
              usize 32))) array_eq (sender_address_102):bool then (
          let res_106 :=
            Update ((
                amount_103,
                SeqMap ((
                    seq_update ((m0_104)) ((x_107) * (usize 32)) (
                      sender_address_102),
                    seq_update ((m1_105)) ((x_107) * (usize 8)) (
                      u64_to_be_bytes (amount_103))
                  ))
              )) in 
          (res_106)) else ((res_106)) in 
      (res_106))
    res_106 in 
  res_106.

Inductive bid_error_t :=
| ContractSender : bid_error_t
| BidTooLow : bid_error_t
| BidsOverWaitingForAuctionFinalization : bid_error_t
| AuctionIsFinalized : bid_error_t.

Definition eqb_bid_error_t (x y : bid_error_t) : bool :=
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

Definition eqb_leibniz_bid_error_t (x y : bid_error_t) : eqb_bid_error_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_bid_error_t : EqDec (bid_error_t) :=
Build_EqDec (bid_error_t) (eqb_bid_error_t) (eqb_leibniz_bid_error_t).

Global Instance show_bid_error_t : Show (bid_error_t) :=
 @Build_Show (bid_error_t) (fun x =>
 match x with
 ContractSender => ("ContractSender")%string
 | BidTooLow => ("BidTooLow")%string
 | BidsOverWaitingForAuctionFinalization => (
   "BidsOverWaitingForAuctionFinalization")%string
 | AuctionIsFinalized => ("AuctionIsFinalized")%string
 end).
Definition g_bid_error_t : G (bid_error_t) := oneOf_ (returnGen ContractSender) [returnGen ContractSender;returnGen BidTooLow;returnGen BidsOverWaitingForAuctionFinalization;returnGen AuctionIsFinalized].
Global Instance gen_bid_error_t : Gen (bid_error_t) := Build_Gen bid_error_t g_bid_error_t.


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
  result state_t bid_error_t)) : hacspec_scope.

Definition auction_bid
  (ctx_108 : context_t)
  (amount_109 : int64)
  (state_110 : state_t)
  : auction_bid_result_t :=
  let 'State ((auction_state_111, highest_bid_112, st2_113, expiry_114, st4_115
      )) :=
    (state_110) in 
  ifbnd negb ((auction_state_111) =.? (NotSoldYet)) : bool
  thenbnd (bind (@Err state_t bid_error_t (AuctionIsFinalized)) (fun _ => Ok (
        tt)))
  else (tt) >> (fun 'tt =>
  let '(slot_time_116, sender_117) :=
    ctx_108 in 
  ifbnd negb ((slot_time_116) <=.? (expiry_114)) : bool
  thenbnd (bind (@Err state_t bid_error_t (
        BidsOverWaitingForAuctionFinalization)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  ifbnd (sender_117) =.? (UserAddressNone) : bool
  thenbnd (bind (@Err state_t bid_error_t (ContractSender)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let sender_address_118 : user_address_t :=
    match sender_117 with
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
    | UserAddressSome account_address_119 => account_address_119
    end in 
  let '(bid_to_update_120, new_map_121) :=
    seq_map_entry ((st4_115)) (sender_address_118) in 
  let '(updated_bid_122, updated_map_123) :=
    match seq_map_update_entry ((st4_115)) (sender_address_118) ((
        bid_to_update_120) .+ (amount_109)) with
    | Update (updated_bid_124, updated_map_125) => (
      updated_bid_124,
      updated_map_125
    )
    end in 
  ifbnd negb ((updated_bid_122) >.? (highest_bid_112)) : bool
  thenbnd (bind (@Err state_t bid_error_t (BidTooLow)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  @Ok state_t bid_error_t (State ((
        auction_state_111,
        updated_bid_122,
        st2_113,
        expiry_114,
        updated_map_123
      ))))))).

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


Inductive finalize_error_t :=
| BidMapError : finalize_error_t
| AuctionStillActive : finalize_error_t
| AuctionFinalized : finalize_error_t.

Definition eqb_finalize_error_t (x y : finalize_error_t) : bool :=
match x with
   | BidMapError => match y with | BidMapError=> true | _ => false end
   | AuctionStillActive =>
       match y with
       | AuctionStillActive=> true
       | _ => false
       end
   | AuctionFinalized => match y with | AuctionFinalized=> true | _ => false end
   end.

Definition eqb_leibniz_finalize_error_t (x y : finalize_error_t) : eqb_finalize_error_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_finalize_error_t : EqDec (finalize_error_t) :=
Build_EqDec (finalize_error_t) (eqb_finalize_error_t) (eqb_leibniz_finalize_error_t).

Global Instance show_finalize_error_t : Show (finalize_error_t) :=
 @Build_Show (finalize_error_t) (fun x =>
 match x with
 BidMapError => ("BidMapError")%string
 | AuctionStillActive => ("AuctionStillActive")%string
 | AuctionFinalized => ("AuctionFinalized")%string
 end).
Definition g_finalize_error_t : G (finalize_error_t) := oneOf_ (returnGen BidMapError) [returnGen BidMapError;returnGen AuctionStillActive;returnGen AuctionFinalized].
Global Instance gen_finalize_error_t : Gen (finalize_error_t) := Build_Gen finalize_error_t g_finalize_error_t.


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


Notation "'auction_finalize_result_t'" := ((result (state_t × finalize_action_t
  ) finalize_error_t)) : hacspec_scope.

Definition auction_finalize
  (ctx_126 : finalize_context_t)
  (state_127 : state_t)
  : auction_finalize_result_t :=
  let 'State ((
        auction_state_128,
        highest_bid_129,
        st2_130,
        expiry_131,
        SeqMap ((m0_132, m1_133))
      )) :=
    (state_127) in 
  let result_134 : (result (state_t × finalize_action_t) finalize_error_t) :=
    @Ok (state_t × finalize_action_t) finalize_error_t (((state_127), Accept
      )) in 
  ifbnd negb ((auction_state_128) =.? (NotSoldYet)) : bool
  thenbnd (bind (@Err (state_t × finalize_action_t) finalize_error_t (
        AuctionFinalized)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let '(slot_time_135, owner_136, balance_137) :=
    ctx_126 in 
  ifbnd negb ((slot_time_135) >.? (expiry_131)) : bool
  thenbnd (bind (@Err (state_t × finalize_action_t) finalize_error_t (
        AuctionStillActive)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  ifbnd (balance_137) !=.? (@repr WORDSIZE64 0) : bool
  thenbnd (let return_action_138 : finalize_action_t :=
      SimpleTransfer (seq_concat (seq_concat (seq_new_ (default) (usize 0)) (
            owner_136)) (u64_to_be_bytes (highest_bid_129))) in 
    let remaining_bid_139 : bid_remain_t :=
      BidNone in 
    bind (foldibnd (usize 0) to ((seq_len ((m0_132))) / (usize 32)) for (
        auction_state_128,
        return_action_138,
        remaining_bid_139
      ) >> (fun x_140 '(auction_state_128, return_action_138, remaining_bid_139
      ) =>
      let addr_141 : user_address_t :=
        array_from_seq (32) (seq_slice ((m0_132)) ((x_140) * (usize 32)) (
            usize 32)) in 
      let amnt_142 : int64 :=
        u64_from_be_bytes (array_from_seq (8) (seq_slice ((m1_133)) ((x_140) * (
                usize 8)) (usize 8))) in 
      ifbnd (amnt_142) <.? (highest_bid_129) : bool
      then (let return_action_138 :=
          match return_action_138 with
          | Accept => Accept
          | SimpleTransfer m_143 => SimpleTransfer (seq_concat (seq_concat (
                m_143) (addr_141)) (u64_to_be_bytes (amnt_142)))
          end in 
        (auction_state_128, return_action_138, remaining_bid_139))
      elsebnd(ifbnd negb ((remaining_bid_139) =.? (BidNone)) : bool
        thenbnd (bind (@Err (state_t × finalize_action_t) finalize_error_t (
              BidMapError)) (fun _ => Ok (tt)))
        else (tt) >> (fun 'tt =>
        let auction_state_128 :=
          Sold (addr_141) in 
        let remaining_bid_139 :=
          BidSome (amnt_142) in 
        Ok ((auction_state_128, return_action_138, remaining_bid_139
          )))) >> (fun '(auction_state_128, return_action_138, remaining_bid_139
      ) =>
      Ok ((auction_state_128, return_action_138, remaining_bid_139))))) (fun '(
        auction_state_128,
        return_action_138,
        remaining_bid_139
      ) => let result_134 :=
        match remaining_bid_139 with
        | BidSome amount_144 => (if (negb ((amount_144) =.? (
                highest_bid_129))):bool then (@Err (state_t × finalize_action_t
            ) finalize_error_t (BidMapError)) else (@Ok (
              state_t ×
              finalize_action_t
            ) finalize_error_t ((
                State ((
                    auction_state_128,
                    highest_bid_129,
                    st2_130,
                    expiry_131,
                    SeqMap (((m0_132), (m1_133)))
                  )),
                return_action_138
              ))))
        | BidNone => @Err (state_t × finalize_action_t) finalize_error_t (
          BidMapError)
        end in 
      bind ((result_134)) (fun _ => Ok ((auction_state_128, result_134)))))
  else ((auction_state_128, result_134)) >> (fun '(auction_state_128, result_134
  ) =>
  result_134))).

Definition auction_test_init
  (item_145 : public_byte_seq)
  (time_146 : int64)
  : bool :=
  (fresh_state ((item_145)) (time_146)) =.? (State ((
        NotSoldYet,
        @repr WORDSIZE64 0,
        (item_145),
        time_146,
        SeqMap ((seq_new_ (default) (usize 0), seq_new_ (default) (usize 0)))
      ))).

Theorem ensures_auction_test_init : forall result_1 (
  item_145 : public_byte_seq) (time_146 : int64),
@auction_test_init item_145 time_146 = result_1 ->
result_1 = true.
Proof. Admitted.
QuickChick (
  forAll g_public_byte_seq (fun item_145 : public_byte_seq =>forAll g_int64 (fun time_146 : int64 =>auction_test_init item_145 time_146))).


Definition verify_bid
  (item_147 : public_byte_seq)
  (state_148 : state_t)
  (account_149 : user_address_t)
  (ctx_150 : context_t)
  (amount_151 : int64)
  (bid_map_152 : seq_map_t)
  (highest_bid_153 : int64)
  (time_154 : int64)
  : (state_t × seq_map_t × bool × bool) :=
  let t_155 : (result state_t bid_error_t) :=
    auction_bid (ctx_150) (amount_151) ((state_148)) in 
  let '(state_156, res_157) :=
    match t_155 with
    | Err e_158 => (state_148, false)
    | Ok s_159 => (s_159, true)
    end in 
  let bid_map_160 : seq_map_t :=
    match seq_map_update_entry ((bid_map_152)) (account_149) (
      highest_bid_153) with
    | Update (_, updated_map_161) => updated_map_161
    end in 
  (
    (state_156),
    (bid_map_160),
    res_157,
    ((state_156)) =.? (State ((
          NotSoldYet,
          highest_bid_153,
          (item_147),
          time_154,
          (bid_map_160)
        )))
  ).

Definition useraddress_from_u8 (i_162 : int8) : user_address_t :=
  array_from_list int8 (let l :=
      [
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162;
        i_162
      ] in  l).

Definition new_account
  (time_163 : int64)
  (i_164 : int8)
  : (user_address_t × context_t) :=
  let addr_165 : user_address_t :=
    useraddress_from_u8 (i_164) in 
  let ctx_166 : (int64 × user_address_set_t) :=
    (time_163, UserAddressSome (addr_165)) in 
  (addr_165, ctx_166).

Definition test_auction_bid_and_finalize
  (item_167 : public_byte_seq)
  (time_168 : int64)
  (input_amount_169 : int64)
  : bool :=
  let amount_170 : int64 :=
    (input_amount_169) .+ (@repr WORDSIZE64 1) in 
  let winning_amount_171 : int64 :=
    (amount_170) .* (@repr WORDSIZE64 3) in 
  let big_amount_172 : int64 :=
    (amount_170) .* (@repr WORDSIZE64 5) in 
  let bid_map_173 : seq_map_t :=
    SeqMap ((seq_new_ (default) (usize 0), seq_new_ (default) (usize 0))) in 
  let state_174 : state_t :=
    fresh_state ((item_167)) (time_168) in 
  let '(alice_175, alice_ctx_176) :=
    new_account (time_168) (@repr WORDSIZE8 0) in 
  let '(state_177, bid_map_178, res_0_179, result_0_180) :=
    verify_bid ((item_167)) (state_174) (alice_175) (alice_ctx_176) (
      amount_170) (bid_map_173) (amount_170) (time_168) in 
  let '(state_181, bid_map_182, res_1_183, result_1_184) :=
    verify_bid ((item_167)) (state_177) (alice_175) (alice_ctx_176) (
      amount_170) (bid_map_178) ((amount_170) .+ (amount_170)) (time_168) in 
  let '(bob_185, bob_ctx_186) :=
    new_account (time_168) (@repr WORDSIZE8 1) in 
  let '(state_187, bid_map_188, res_2_189, result_2_190) :=
    verify_bid ((item_167)) (state_181) (bob_185) (bob_ctx_186) (
      winning_amount_171) (bid_map_182) (winning_amount_171) (time_168) in 
  let owner_191 : user_address_t :=
    useraddress_from_u8 (@repr WORDSIZE8 0) in 
  let balance_192 : int64 :=
    @repr WORDSIZE64 100 in 
  let ctx4_193 : (int64 × user_address_t × int64) :=
    (time_168, owner_191, balance_192) in 
  let finres_194 : (result (state_t × finalize_action_t) finalize_error_t) :=
    auction_finalize (ctx4_193) ((state_187)) in 
  let '(state_195, result_3_196) :=
    match finres_194 with
    | Err err_197 => ((state_187), (err_197) =.? (AuctionStillActive))
    | Ok (state_198, _) => (state_198, false)
    end in 
  let '(carol_199, carol_ctx_200) :=
    new_account (time_168) (@repr WORDSIZE8 2) in 
  let ctx5_201 : (int64 × user_address_t × int64) :=
    ((time_168) .+ (@repr WORDSIZE64 1), carol_199, winning_amount_171) in 
  let finres2_202 : (result (state_t × finalize_action_t) finalize_error_t) :=
    auction_finalize (ctx5_201) ((state_195)) in 
  let '(state_203, result_4_204) :=
    match finres2_202 with
    | Err _ => ((state_195), false)
    | Ok (state_205, action_206) => (
      state_205,
      (action_206) =.? (SimpleTransfer (seq_concat (seq_concat (seq_concat (
                seq_concat (seq_new_ (default) (usize 0)) (carol_199)) (
                u64_to_be_bytes (winning_amount_171))) (alice_175)) (
            u64_to_be_bytes ((amount_170) .+ (amount_170)))))
    )
    end in 
  let result_5_207 : bool :=
    ((state_203)) =.? (State ((
          Sold (bob_185),
          winning_amount_171,
          (item_167),
          time_168,
          (bid_map_188)
        ))) in 
  let finres3_208 : (result (state_t × finalize_action_t) finalize_error_t) :=
    auction_finalize (ctx5_201) ((state_203)) in 
  let '(state_209, result_6_210) :=
    match finres3_208 with
    | Err err_211 => (state_203, (err_211) =.? (AuctionFinalized))
    | Ok (state_212, action_213) => (state_212, false)
    end in 
  let t_214 : (result state_t bid_error_t) :=
    auction_bid (bob_ctx_186) (big_amount_172) ((state_209)) in 
  let result_7_215 : bool :=
    match t_214 with
    | Err e_216 => (e_216) =.? (AuctionIsFinalized)
    | Ok _ => false
    end in 
  (((((((result_0_180) && (result_1_184)) && (result_2_190)) && (
            result_3_196)) && (result_4_204)) && (result_5_207)) && (
      result_6_210)) && (result_7_215).

Theorem ensures_test_auction_bid_and_finalize : forall result_1 (
  item_167 : public_byte_seq) (time_168 : int64) (input_amount_169 : int64),
@test_auction_bid_and_finalize item_167 time_168 input_amount_169 = result_1 ->
result_1 = true.
Proof. Admitted.
QuickChick (
  forAll g_public_byte_seq (fun item_167 : public_byte_seq =>forAll g_int64 (fun time_168 : int64 =>forAll g_int64 (fun input_amount_169 : int64 =>test_auction_bid_and_finalize item_167 time_168 input_amount_169)))).


