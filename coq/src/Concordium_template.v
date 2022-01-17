(* [[file:concordium.org::*Coq code][Coq code:1]] *)
(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
(* Coq code:1 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:2]] *)
Definition max_contract_state_size_v : int32 :=
  @repr WORDSIZE32 16384.
(* Coq code:2 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:3]] *)
Definition max_log_size_v : uint_size :=
  usize 512.
(* Coq code:3 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:4]] *)
Definition max_num_logs_v : uint_size :=
  usize 64.
(* Coq code:4 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:5]] *)
Inductive log_error_t :=
| Full : log_error_t
| Malformed : log_error_t.

Definition eqb_log_error_t (x y : log_error_t) : bool :=
match x with
   | Full => match y with | Full=> true | _ => false end
   | Malformed => match y with | Malformed=> true | _ => false end
   end.

Definition eqb_leibniz_log_error_t (x y : log_error_t) : eqb_log_error_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_log_error_t : EqDec (log_error_t) :=
Build_EqDec (log_error_t) (eqb_log_error_t) (eqb_leibniz_log_error_t).

(* Coq code:5 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:6]] *)
Require Import Hacspec.Lib.
(* Coq code:6 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:7]] *)
Definition load_state_hacspec
  (buf_0 : public_byte_seq)
  (offset_1 : int32)
  : (public_byte_seq × int32) :=
  (buf_0, @repr WORDSIZE32 1).
(* Coq code:7 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:8]] *)
Definition write_state_hacspec
  (buf_2 : public_byte_seq)
  (offset_3 : int32)
  : (public_byte_seq × int32) :=
  (buf_2, @repr WORDSIZE32 1).
(* Coq code:8 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:9]] *)
Definition state_size_hacspec  : int32 :=
  @repr WORDSIZE32 1.
(* Coq code:9 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:10]] *)
Definition resize_state_hacspec (new_size_4 : int32) : int32 :=
  @repr WORDSIZE32 1.
(* Coq code:10 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:11]] *)
Definition get_parameter_section_hacspec
  (buf_5 : public_byte_seq)
  (offset_6 : int32)
  : (public_byte_seq × int32) :=
  (buf_5, @repr WORDSIZE32 1).
(* Coq code:11 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:12]] *)
Definition get_parameter_size_hacspec  : int32 :=
  @repr WORDSIZE32 1.
(* Coq code:12 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:13]] *)
Definition get_slot_time_hacspec  : int64 :=
  @repr WORDSIZE64 1.
(* Coq code:13 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:14]] *)
Definition get_policy_section_hacspec
  (policy_bytes_7 : public_byte_seq)
  (offset_8 : int32)
  : (public_byte_seq × int32) :=
  (policy_bytes_7, @repr WORDSIZE32 1).
(* Coq code:14 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:15]] *)
Definition get_init_origin_hacspec
  (start_9 : public_byte_seq)
  : public_byte_seq :=
  start_9.
(* Coq code:15 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:16]] *)
Definition get_receive_invoker_hacspec
  (start_10 : public_byte_seq)
  : public_byte_seq :=
  start_10.
(* Coq code:16 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:17]] *)
Definition get_receive_self_address_hacspec
  (start_11 : public_byte_seq)
  : public_byte_seq :=
  start_11.
(* Coq code:17 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:18]] *)
Definition get_receive_self_balance_hacspec  : int64 :=
  @repr WORDSIZE64 1.
(* Coq code:18 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:19]] *)
Definition get_receive_sender_hacspec
  (start_12 : public_byte_seq)
  : public_byte_seq :=
  start_12.
(* Coq code:19 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:20]] *)
Definition get_receive_owner_hacspec
  (start_13 : public_byte_seq)
  : public_byte_seq :=
  start_13.
(* Coq code:20 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:21]] *)
Definition log_event_hacspec
  (start_14 : public_byte_seq)
  : (public_byte_seq × int32) :=
  (start_14, @repr WORDSIZE32 1).
(* Coq code:21 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:22]] *)
Definition accept_hacspec  : int32 :=
  @repr WORDSIZE32 1.
(* Coq code:22 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:23]] *)
Definition simple_transfer_hacspec
  (buf_15 : public_byte_seq)
  (amount_16 : int64)
  : int32 :=
  @repr WORDSIZE32 1.
(* Coq code:23 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:24]] *)
Definition send_hacspec
  (addr_index_17 : int64)
  (addr_subindex_18 : int64)
  (receive_name_19 : public_byte_seq)
  (amount_20 : int64)
  (parameter_21 : public_byte_seq)
  : int32 :=
  @repr WORDSIZE32 1.
(* Coq code:24 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:25]] *)
Definition combine_and_hacspec (l_22 : int32) (r_23 : int32) : int32 :=
  @repr WORDSIZE32 1.
(* Coq code:25 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:26]] *)
Definition combine_or_hacspec (l_24 : int32) (r_25 : int32) : int32 :=
  @repr WORDSIZE32 1.
(* Coq code:26 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:27]] *)
Require Import Hacspec.Lib.
(* Coq code:27 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:28]] *)
Notation "'reject_hacspec_t'" := (int32) : hacspec_scope.
(* Coq code:28 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:29]] *)
Definition reject_impl_deafult  : reject_hacspec_t :=
  min_v.
(* Coq code:29 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:30]] *)
Definition new_reject_impl (x_26 : int32) : (option int32) :=
  (if ((x_26) <.? (@repr WORDSIZE32 0)):bool then (@Some int32 (x_26)) else (
      @None int32)).
(* Coq code:30 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:31]] *)
Definition reject_impl_convert_from_unit  : reject_hacspec_t :=
  (min_v) .+ (@repr WORDSIZE32 1).

Theorem ensures_reject_impl_convert_from_unit : forall result_27 ,
@reject_impl_convert_from_unit  = result_27 ->
~ (result_27 = @repr WORDSIZE32 0).
Proof. Admitted.
(* Coq code:31 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:32]] *)
Definition reject_impl_convert_from_parse_error  : reject_hacspec_t :=
  (min_v) .+ (@repr WORDSIZE32 2).

Theorem ensures_reject_impl_convert_from_parse_error : forall result_27 ,
@reject_impl_convert_from_parse_error  = result_27 ->
~ (result_27 = @repr WORDSIZE32 0).
Proof. Admitted.
(* Coq code:32 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:33]] *)
Definition reject_impl_from_log_error
  (le_28 : log_error_t)
  : reject_hacspec_t :=
  match le_28 with
  | Full => (min_v) .+ (@repr WORDSIZE32 3)
  | Malformed => (min_v) .+ (@repr WORDSIZE32 4)
  end.

Theorem ensures_reject_impl_from_log_error : forall result_27 (
  le_28 : log_error_t),
@reject_impl_from_log_error le_28 = result_27 ->
~ (result_27 = @repr WORDSIZE32 0).
Proof. Admitted.
(* Coq code:33 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:34]] *)
Inductive new_contract_name_error_t :=
| NewContractNameErrorMissingInitPrefix : new_contract_name_error_t
| NewContractNameErrorTooLong : new_contract_name_error_t
| NewContractNameErrorContainsDot : new_contract_name_error_t
| NewContractNameErrorInvalidCharacters : new_contract_name_error_t.
(* Coq code:34 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:35]] *)
Definition reject_impl_from_new_contract_name_error
  (nre_29 : new_contract_name_error_t)
  : reject_hacspec_t :=
  match nre_29 with
  | NewContractNameErrorMissingInitPrefix => (min_v) .+ (@repr WORDSIZE32 5)
  | NewContractNameErrorTooLong => (min_v) .+ (@repr WORDSIZE32 6)
  | NewContractNameErrorContainsDot => (min_v) .+ (@repr WORDSIZE32 9)
  | NewContractNameErrorInvalidCharacters => (min_v) .+ (@repr WORDSIZE32 10)
  end.

Theorem ensures_reject_impl_from_new_contract_name_error : forall result_27 (
  nre_29 : new_contract_name_error_t),
@reject_impl_from_new_contract_name_error nre_29 = result_27 ->
~ (result_27 = @repr WORDSIZE32 0).
Proof. Admitted.
(* Coq code:35 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:36]] *)
Inductive new_receive_name_error_t :=
| NewReceiveNameErrorMissingDotSeparator : new_receive_name_error_t
| NewReceiveNameErrorTooLong : new_receive_name_error_t
| NewReceiveNameErrorInvalidCharacters : new_receive_name_error_t.
(* Coq code:36 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:37]] *)
Definition reject_impl_from_new_receive_name_error
  (nre_30 : new_receive_name_error_t)
  : reject_hacspec_t :=
  match nre_30 with
  | NewReceiveNameErrorMissingDotSeparator => (min_v) .+ (@repr WORDSIZE32 7)
  | NewReceiveNameErrorTooLong => (min_v) .+ (@repr WORDSIZE32 8)
  | NewReceiveNameErrorInvalidCharacters => (min_v) .+ (@repr WORDSIZE32 11)
  end.

Theorem ensures_reject_impl_from_new_receive_name_error : forall result_27 (
  nre_30 : new_receive_name_error_t),
@reject_impl_from_new_receive_name_error nre_30 = result_27 ->
~ (result_27 = @repr WORDSIZE32 0).
Proof. Admitted.
(* Coq code:37 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:38]] *)
Notation "'contract_state_hacspec_t'" := (int32) : hacspec_scope.
(* Coq code:38 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:39]] *)
Inductive seek_from_hacspec_t :=
| Start : int64 -> seek_from_hacspec_t
| End : int64 -> seek_from_hacspec_t
| Current : int64 -> seek_from_hacspec_t.
(* Coq code:39 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:40]] *)
Notation "'uint32_option_t'" := ((option int32)) : hacspec_scope.
(* Coq code:40 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:41]] *)
Notation "'iint64_option_t'" := ((option int64)) : hacspec_scope.
(* Coq code:41 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:42]] *)
Definition contract_state_impl_seek
  (current_position_31 : contract_state_hacspec_t)
  (pos_32 : seek_from_hacspec_t)
  : (result (contract_state_hacspec_t × int64) unit) :=
  match pos_32 with
  | Start offset_33 => @Ok (contract_state_hacspec_t × int64) unit ((
      @cast _ uint32 _ (offset_33),
      offset_33
    ))
  | End delta_34 => (if ((delta_34) >=.? (@repr WORDSIZE64 0)):bool then (
      match pub_uint32_checked_add (current_position_31) (@cast _ uint32 _ (
          delta_34)) with
      | Some b_35 => @Ok (contract_state_hacspec_t × int64) unit ((
          b_35,
          @cast _ uint64 _ (delta_34)
        ))
      | None => @Err (contract_state_hacspec_t × int64) unit (tt)
      end) else (match pub_int64_checked_abs (delta_34) with
      | Some b_36 => @Ok (contract_state_hacspec_t × int64) unit ((
          (@repr WORDSIZE32 4) .- (@cast _ uint32 _ (b_36)),
          @cast _ uint64 _ ((@repr WORDSIZE32 4) .- (@cast _ uint32 _ (b_36)))
        ))
      | None => @Err (contract_state_hacspec_t × int64) unit (tt)
      end))
  | Current delta_37 => (if ((delta_37) >=.? (@repr WORDSIZE64 0)):bool then (
      match pub_uint32_checked_add (current_position_31) (@cast _ uint32 _ (
          delta_37)) with
      | Some offset_38 => @Ok (contract_state_hacspec_t × int64) unit ((
          offset_38,
          @cast _ uint64 _ (offset_38)
        ))
      | None => @Err (contract_state_hacspec_t × int64) unit (tt)
      end) else (match pub_int64_checked_abs (delta_37) with
      | Some b_39 => match pub_uint32_checked_sub (current_position_31) (
        @cast _ uint32 _ (b_39)) with
      | Some offset_40 => @Ok (contract_state_hacspec_t × int64) unit ((
          offset_40,
          @cast _ uint64 _ (offset_40)
        ))
      | None => @Err (contract_state_hacspec_t × int64) unit (tt)
      end
      | None => @Err (contract_state_hacspec_t × int64) unit (tt)
      end))
  end.
(* Coq code:42 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:43]] *)
Definition contract_state_impl_read_read
  (current_position_41 : contract_state_hacspec_t)
  (buf_42 : public_byte_seq)
  : (contract_state_hacspec_t × uint_size) :=
  let '(buf_43, num_read_44) :=
    load_state_hacspec (buf_42) (current_position_41) in 
  ((current_position_41) .+ (num_read_44), @cast _ uint32 _ (num_read_44)).
(* Coq code:43 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:44]] *)
Definition contract_state_impl_read_read_u64
  (current_position_45 : contract_state_hacspec_t)
  : (contract_state_hacspec_t × int64) :=
  let buf_46 : seq int8 :=
    seq_new_ (default) (usize 8) in 
  let '(buf_47, num_read_48) :=
    load_state_hacspec (buf_46) (current_position_45) in 
  (
    (current_position_45) .+ (num_read_48),
    u64_from_le_bytes (array_from_seq (8) (buf_47))
  ).
(* Coq code:44 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:45]] *)
Definition contract_state_impl_read_read_u32
  (current_position_49 : contract_state_hacspec_t)
  : (contract_state_hacspec_t × int32) :=
  let buf_50 : seq int8 :=
    seq_new_ (default) (usize 4) in 
  let '(buf_51, num_read_52) :=
    load_state_hacspec (buf_50) (current_position_49) in 
  (
    (current_position_49) .+ (num_read_52),
    u32_from_le_bytes (array_from_seq (4) (buf_51))
  ).
(* Coq code:45 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:46]] *)
Definition contract_state_impl_read_read_u8
  (current_position_53 : contract_state_hacspec_t)
  : (contract_state_hacspec_t × int8) :=
  let buf_54 : seq int8 :=
    seq_new_ (default) (usize 1) in 
  let '(buf_55, num_read_56) :=
    load_state_hacspec (buf_54) (current_position_53) in 
  ((current_position_53) .+ (num_read_56), seq_index (buf_55) (usize 0)).
(* Coq code:46 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:47]] *)
Definition contract_state_impl_write
  (current_position_57 : contract_state_hacspec_t)
  (buf_58 : public_byte_seq)
  : (result (contract_state_hacspec_t × uint_size) unit) :=
  ifbnd option_is_none (pub_uint32_checked_add (current_position_57) (pub_u32 (
        seq_len (buf_58)))) : bool
  thenbnd (bind (@Err (contract_state_hacspec_t × uint_size) unit (tt)) (
      fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_59, num_bytes_60) :=
    write_state_hacspec (buf_58) (current_position_57) in 
  @Ok (contract_state_hacspec_t × uint_size) unit ((
      (current_position_57) .+ (num_bytes_60),
      @cast _ uint32 _ (num_bytes_60)
    ))).
(* Coq code:47 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:48]] *)
Definition has_contract_state_impl_for_contract_state_open
  
  : contract_state_hacspec_t :=
  @repr WORDSIZE32 0.
(* Coq code:48 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:49]] *)
Definition has_contract_state_impl_for_contract_state_reserve
  (contract_state_61 : contract_state_hacspec_t)
  (len_62 : int32)
  : bool :=
  let cur_size_63 : int32 :=
    state_size_hacspec  in 
  (if ((cur_size_63) <.? (len_62)):bool then ((resize_state_hacspec (
          len_62)) =.? (@repr WORDSIZE32 1)) else (true)).
(* Coq code:49 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:50]] *)
Definition has_contract_state_impl_for_contract_state_truncate
  (current_position_64 : contract_state_hacspec_t)
  (cur_size_65 : int32)
  (new_size_66 : int32)
  : contract_state_hacspec_t :=
  let 'tt :=
    if (cur_size_65) >.? (new_size_66):bool then (let _ : int32 :=
        resize_state_hacspec (new_size_66) in 
      tt) else (tt) in 
  (if ((new_size_66) <.? (current_position_64)):bool then (new_size_66) else (
      current_position_64)).
(* Coq code:50 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:51]] *)
Notation "'parameter_hacspec_t'" := (int32) : hacspec_scope.
(* Coq code:51 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:52]] *)
Definition read_impl_for_parameter_read
  (current_position_67 : parameter_hacspec_t)
  (buf_68 : public_byte_seq)
  : (parameter_hacspec_t × uint_size) :=
  let '(buf_69, num_read_70) :=
    get_parameter_section_hacspec (buf_68) (current_position_67) in 
  ((current_position_67) .+ (num_read_70), @cast _ uint32 _ (num_read_70)).
(* Coq code:52 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:53]] *)
Notation "'attributes_cursor_hacspec_t'" := ((int32 × int16)) : hacspec_scope.
(* Coq code:53 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:54]] *)
Definition has_policy_impl_for_policy_attributes_cursor_next_item
  (policy_attribute_items_71 : attributes_cursor_hacspec_t)
  (buf_72 : public_byte_seq)
  : (option (attributes_cursor_hacspec_t × (int8 × int8))) :=
  let '(current_position_73, remaining_items_74) :=
    policy_attribute_items_71 in 
  ifbnd (remaining_items_74) =.? (@repr WORDSIZE16 0) : bool
  thenbnd (bind (@None (attributes_cursor_hacspec_t × (int8 × int8))) (
      fun _ =>  Some (tt)))
  else (tt) >> (fun 'tt =>
  let '(tag_value_len_75, num_read_76) :=
    get_policy_section_hacspec (seq_new_ (default) (usize 2)) (
      current_position_73) in 
  let current_position_73 :=
    (current_position_73) .+ (num_read_76) in 
  ifbnd (seq_index (tag_value_len_75) (usize 1)) >.? (@repr WORDSIZE8 31) : bool
  thenbnd (bind (@None (attributes_cursor_hacspec_t × (int8 × int8))) (
      fun _ =>  Some (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_77, num_read_78) :=
    get_policy_section_hacspec (buf_72) (current_position_73) in 
  let current_position_73 :=
    (current_position_73) .+ (num_read_78) in 
  let remaining_items_74 :=
    (remaining_items_74) .- (@repr WORDSIZE16 1) in 
  @Some (attributes_cursor_hacspec_t × (int8 × int8)) ((
      (current_position_73, remaining_items_74),
      (
        seq_index (tag_value_len_75) (usize 0),
        seq_index (tag_value_len_75) (usize 1)
      )
    )))).
(* Coq code:54 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:55]] *)
Notation "'policies_iterator_hacspec_t'" := ((int32 × int16)) : hacspec_scope.
(* Coq code:55 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:56]] *)
Notation "'policy_attributes_cursor_hacspec_t'" := ((
  int32 ×
  int64 ×
  int64 ×
  attributes_cursor_hacspec_t
)) : hacspec_scope.
(* Coq code:56 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:57]] *)
Definition iterator_impl_for_policies_iterator_next
  (policies_iterator_79 : policies_iterator_hacspec_t)
  : (option (policies_iterator_hacspec_t × policy_attributes_cursor_hacspec_t
    )) :=
  let '(pos_80, remaining_items_81) :=
    policies_iterator_79 in 
  ifbnd (remaining_items_81) =.? (@repr WORDSIZE16 0) : bool
  thenbnd (bind (@None (
        policies_iterator_hacspec_t ×
        policy_attributes_cursor_hacspec_t
      )) (fun _ =>  Some (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_82, _) :=
    get_policy_section_hacspec (seq_new_ (default) (((((usize 2) + (
                usize 4)) + (usize 8)) + (usize 8)) + (usize 2))) (pos_80) in 
  let skip_part_83 : public_byte_seq :=
    seq_slice_range (buf_82) ((usize 0, usize 2)) in 
  let ip_part_84 : public_byte_seq :=
    seq_slice_range (buf_82) ((usize 2, (usize 2) + (usize 4))) in 
  let created_at_part_85 : public_byte_seq :=
    seq_slice_range (buf_82) ((
        (usize 2) + (usize 4),
        ((usize 2) + (usize 4)) + (usize 8)
      )) in 
  let valid_to_part_86 : public_byte_seq :=
    seq_slice_range (buf_82) ((
        ((usize 2) + (usize 4)) + (usize 8),
        (((usize 2) + (usize 4)) + (usize 8)) + (usize 8)
      )) in 
  let len_part_87 : public_byte_seq :=
    seq_slice_range (buf_82) ((
        (((usize 2) + (usize 4)) + (usize 8)) + (usize 8),
        ((((usize 2) + (usize 4)) + (usize 8)) + (usize 8)) + (usize 2)
      )) in 
  let identity_provider_88 : int32 :=
    u32_from_le_bytes (array_from_seq (4) (ip_part_84)) in 
  let created_at_89 : int64 :=
    u64_from_le_bytes (array_from_seq (8) (created_at_part_85)) in 
  let valid_to_90 : int64 :=
    u64_from_le_bytes (array_from_seq (8) (valid_to_part_86)) in 
  let remaining_items_91 : int16 :=
    u16_from_le_bytes (array_from_seq (2) (len_part_87)) in 
  let attributes_start_92 : int32 :=
    (((((pos_80) .+ (@repr WORDSIZE32 2)) .+ (@repr WORDSIZE32 4)) .+ (
          @repr WORDSIZE32 8)) .+ (@repr WORDSIZE32 8)) .+ (
      @repr WORDSIZE32 2) in 
  let pos_80 :=
    ((pos_80) .+ (@cast _ uint32 _ (u16_from_le_bytes (array_from_seq (2) (
              skip_part_83))))) .+ (@repr WORDSIZE32 2) in 
  let remaining_items_91 :=
    (remaining_items_91) .- (@repr WORDSIZE16 1) in 
  @Some (policies_iterator_hacspec_t × policy_attributes_cursor_hacspec_t) ((
      (pos_80, remaining_items_91),
      (
        identity_provider_88,
        created_at_89,
        valid_to_90,
        (attributes_start_92, remaining_items_91)
      )
    ))).
(* Coq code:57 ends here *)

