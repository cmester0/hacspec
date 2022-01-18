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
Require Import Hacspec.Lib.
(* Coq code:2 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:3]] *)
Definition max_contract_state_size_v : int32 :=
  @repr WORDSIZE32 16384.
(* Coq code:3 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:4]] *)
Definition max_log_size_v : uint_size :=
  usize 512.
(* Coq code:4 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:5]] *)
Definition max_num_logs_v : uint_size :=
  usize 64.
(* Coq code:5 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:6]] *)
Notation "'reject_hacspec_t'" := (int32) : hacspec_scope.
(* Coq code:6 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:7]] *)
Definition reject_impl_deafult  : reject_hacspec_t :=
  min_v.
(* Coq code:7 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:8]] *)
Definition new_reject_impl (x_0 : int32) : (option int32) :=
  (if ((x_0) <.? (@repr WORDSIZE32 0)):bool then (@Some int32 (x_0)) else (
      @None int32)).
(* Coq code:8 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:9]] *)
Definition reject_impl_convert_from_unit  : reject_hacspec_t :=
  (min_v) .+ (@repr WORDSIZE32 1).

Theorem ensures_reject_impl_convert_from_unit : forall result_1 ,
@reject_impl_convert_from_unit  = result_1 ->
~ (result_1 = @repr WORDSIZE32 0).
Proof. Admitted.
(* Coq code:9 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:10]] *)
Definition reject_impl_convert_from_parse_error  : reject_hacspec_t :=
  (min_v) .+ (@repr WORDSIZE32 2).

Theorem ensures_reject_impl_convert_from_parse_error : forall result_1 ,
@reject_impl_convert_from_parse_error  = result_1 ->
~ (result_1 = @repr WORDSIZE32 0).
Proof. Admitted.
(* Coq code:10 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:11]] *)
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
(* Coq code:11 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:12]] *)
Inductive new_contract_name_error_t :=
| NewContractNameErrorMissingInitPrefix : new_contract_name_error_t
| NewContractNameErrorTooLong : new_contract_name_error_t
| NewContractNameErrorContainsDot : new_contract_name_error_t
| NewContractNameErrorInvalidCharacters : new_contract_name_error_t.
(* Coq code:12 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:13]] *)
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
(* Coq code:13 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:14]] *)
Inductive new_receive_name_error_t :=
| NewReceiveNameErrorMissingDotSeparator : new_receive_name_error_t
| NewReceiveNameErrorTooLong : new_receive_name_error_t
| NewReceiveNameErrorInvalidCharacters : new_receive_name_error_t.
(* Coq code:14 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:15]] *)
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
(* Coq code:15 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:16]] *)
Notation "'contract_state_hacspec_t'" := (int32) : hacspec_scope.
(* Coq code:16 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:17]] *)
Inductive seek_from_hacspec_t :=
| Start : int64 -> seek_from_hacspec_t
| End : int64 -> seek_from_hacspec_t
| Current : int64 -> seek_from_hacspec_t.
(* Coq code:17 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:18]] *)
Notation "'uint32_option_t'" := ((option int32)) : hacspec_scope.
(* Coq code:18 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:19]] *)
Notation "'iint64_option_t'" := ((option int64)) : hacspec_scope.
(* Coq code:19 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:20]] *)
Definition contract_state_impl_seek
  (current_position_5 : contract_state_hacspec_t)
  (pos_6 : seek_from_hacspec_t)
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
(* Coq code:20 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:21]] *)
Definition contract_state_impl_read_read
  (current_position_15 : contract_state_hacspec_t)
  (buf_16 : public_byte_seq)
  : (contract_state_hacspec_t × uint_size) :=
  let '(buf_17, num_read_18) :=
    load_state_hacspec (buf_16) (current_position_15) in 
  ((current_position_15) .+ (num_read_18), @cast _ uint32 _ (num_read_18)).
(* Coq code:21 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:22]] *)
Definition contract_state_impl_read_read_u64
  (current_position_19 : contract_state_hacspec_t)
  : (contract_state_hacspec_t × int64) :=
  let buf_20 : seq int8 :=
    seq_new_ (default) (usize 8) in 
  let '(buf_21, num_read_22) :=
    load_state_hacspec (buf_20) (current_position_19) in 
  (
    (current_position_19) .+ (num_read_22),
    u64_from_le_bytes (array_from_seq (8) (buf_21))
  ).
(* Coq code:22 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:23]] *)
Definition contract_state_impl_read_read_u32
  (current_position_23 : contract_state_hacspec_t)
  : (contract_state_hacspec_t × int32) :=
  let buf_24 : seq int8 :=
    seq_new_ (default) (usize 4) in 
  let '(buf_25, num_read_26) :=
    load_state_hacspec (buf_24) (current_position_23) in 
  (
    (current_position_23) .+ (num_read_26),
    u32_from_le_bytes (array_from_seq (4) (buf_25))
  ).
(* Coq code:23 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:24]] *)
Definition contract_state_impl_read_read_u8
  (current_position_27 : contract_state_hacspec_t)
  : (contract_state_hacspec_t × int8) :=
  let buf_28 : seq int8 :=
    seq_new_ (default) (usize 1) in 
  let '(buf_29, num_read_30) :=
    load_state_hacspec (buf_28) (current_position_27) in 
  ((current_position_27) .+ (num_read_30), seq_index (buf_29) (usize 0)).
(* Coq code:24 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:25]] *)
Definition contract_state_impl_write
  (current_position_31 : contract_state_hacspec_t)
  (buf_32 : public_byte_seq)
  : (result (contract_state_hacspec_t × uint_size) unit) :=
  ifbnd option_is_none (pub_uint32_checked_add (current_position_31) (pub_u32 (
        seq_len (buf_32)))) : bool
  thenbnd (bind (@Err (contract_state_hacspec_t × uint_size) unit (tt)) (
      fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_33, num_bytes_34) :=
    write_state_hacspec (buf_32) (current_position_31) in 
  @Ok (contract_state_hacspec_t × uint_size) unit ((
      (current_position_31) .+ (num_bytes_34),
      @cast _ uint32 _ (num_bytes_34)
    ))).
(* Coq code:25 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:26]] *)
Definition has_contract_state_impl_for_contract_state_open
  
  : contract_state_hacspec_t :=
  @repr WORDSIZE32 0.
(* Coq code:26 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:27]] *)
Definition has_contract_state_impl_for_contract_state_reserve
  (len_35 : int32)
  : bool :=
  let cur_size_36 : int32 :=
    state_size_hacspec  in 
  (if ((cur_size_36) <.? (len_35)):bool then ((resize_state_hacspec (
          len_35)) =.? (@repr WORDSIZE32 1)) else (true)).
(* Coq code:27 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:28]] *)
Definition has_contract_state_impl_for_contract_state_truncate
  (current_position_37 : contract_state_hacspec_t)
  (cur_size_38 : int32)
  (new_size_39 : int32)
  : contract_state_hacspec_t :=
  let 'tt :=
    if (cur_size_38) >.? (new_size_39):bool then (let _ : int32 :=
        resize_state_hacspec (new_size_39) in 
      tt) else (tt) in 
  (if ((new_size_39) <.? (current_position_37)):bool then (new_size_39) else (
      current_position_37)).
(* Coq code:28 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:29]] *)
Notation "'parameter_hacspec_t'" := (int32) : hacspec_scope.
(* Coq code:29 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:30]] *)
Definition read_impl_for_parameter_read
  (current_position_40 : parameter_hacspec_t)
  (buf_41 : public_byte_seq)
  : (parameter_hacspec_t × uint_size) :=
  let '(buf_42, num_read_43) :=
    get_parameter_section_hacspec (buf_41) (current_position_40) in 
  ((current_position_40) .+ (num_read_43), @cast _ uint32 _ (num_read_43)).
(* Coq code:30 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:31]] *)
Notation "'attributes_cursor_hacspec_t'" := ((int32 × int16)) : hacspec_scope.
(* Coq code:31 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:32]] *)
Definition has_policy_impl_for_policy_attributes_cursor_next_item
  (policy_attribute_items_44 : attributes_cursor_hacspec_t)
  (buf_45 : public_byte_seq)
  : (option (attributes_cursor_hacspec_t × (int8 × int8))) :=
  let '(current_position_46, remaining_items_47) :=
    policy_attribute_items_44 in 
  ifbnd (remaining_items_47) =.? (@repr WORDSIZE16 0) : bool
  thenbnd (bind (@None (attributes_cursor_hacspec_t × (int8 × int8))) (
      fun _ =>  Some (tt)))
  else (tt) >> (fun 'tt =>
  let '(tag_value_len_48, num_read_49) :=
    get_policy_section_hacspec (seq_new_ (default) (usize 2)) (
      current_position_46) in 
  let current_position_46 :=
    (current_position_46) .+ (num_read_49) in 
  ifbnd (seq_index (tag_value_len_48) (usize 1)) >.? (@repr WORDSIZE8 31) : bool
  thenbnd (bind (@None (attributes_cursor_hacspec_t × (int8 × int8))) (
      fun _ =>  Some (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_50, num_read_51) :=
    get_policy_section_hacspec (buf_45) (current_position_46) in 
  let current_position_46 :=
    (current_position_46) .+ (num_read_51) in 
  let remaining_items_47 :=
    (remaining_items_47) .- (@repr WORDSIZE16 1) in 
  @Some (attributes_cursor_hacspec_t × (int8 × int8)) ((
      (current_position_46, remaining_items_47),
      (
        seq_index (tag_value_len_48) (usize 0),
        seq_index (tag_value_len_48) (usize 1)
      )
    )))).
(* Coq code:32 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:33]] *)
Notation "'policies_iterator_hacspec_t'" := ((int32 × int16)) : hacspec_scope.
(* Coq code:33 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:34]] *)
Notation "'policy_attributes_cursor_hacspec_t'" := ((
  int32 ×
  int64 ×
  int64 ×
  attributes_cursor_hacspec_t
)) : hacspec_scope.
(* Coq code:34 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:35]] *)
Definition iterator_impl_for_policies_iterator_next
  (policies_iterator_52 : policies_iterator_hacspec_t)
  : (option (policies_iterator_hacspec_t × policy_attributes_cursor_hacspec_t
    )) :=
  let '(pos_53, remaining_items_54) :=
    policies_iterator_52 in 
  ifbnd (remaining_items_54) =.? (@repr WORDSIZE16 0) : bool
  thenbnd (bind (@None (
        policies_iterator_hacspec_t ×
        policy_attributes_cursor_hacspec_t
      )) (fun _ =>  Some (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_55, _) :=
    get_policy_section_hacspec (seq_new_ (default) (((((usize 2) + (
                usize 4)) + (usize 8)) + (usize 8)) + (usize 2))) (pos_53) in 
  let skip_part_56 : public_byte_seq :=
    seq_slice_range (buf_55) ((usize 0, usize 2)) in 
  let ip_part_57 : public_byte_seq :=
    seq_slice_range (buf_55) ((usize 2, (usize 2) + (usize 4))) in 
  let created_at_part_58 : public_byte_seq :=
    seq_slice_range (buf_55) ((
        (usize 2) + (usize 4),
        ((usize 2) + (usize 4)) + (usize 8)
      )) in 
  let valid_to_part_59 : public_byte_seq :=
    seq_slice_range (buf_55) ((
        ((usize 2) + (usize 4)) + (usize 8),
        (((usize 2) + (usize 4)) + (usize 8)) + (usize 8)
      )) in 
  let len_part_60 : public_byte_seq :=
    seq_slice_range (buf_55) ((
        (((usize 2) + (usize 4)) + (usize 8)) + (usize 8),
        ((((usize 2) + (usize 4)) + (usize 8)) + (usize 8)) + (usize 2)
      )) in 
  let identity_provider_61 : int32 :=
    u32_from_le_bytes (array_from_seq (4) (ip_part_57)) in 
  let created_at_62 : int64 :=
    u64_from_le_bytes (array_from_seq (8) (created_at_part_58)) in 
  let valid_to_63 : int64 :=
    u64_from_le_bytes (array_from_seq (8) (valid_to_part_59)) in 
  let remaining_items_64 : int16 :=
    u16_from_le_bytes (array_from_seq (2) (len_part_60)) in 
  let attributes_start_65 : int32 :=
    (((((pos_53) .+ (@repr WORDSIZE32 2)) .+ (@repr WORDSIZE32 4)) .+ (
          @repr WORDSIZE32 8)) .+ (@repr WORDSIZE32 8)) .+ (
      @repr WORDSIZE32 2) in 
  let pos_53 :=
    ((pos_53) .+ (@cast _ uint32 _ (u16_from_le_bytes (array_from_seq (2) (
              skip_part_56))))) .+ (@repr WORDSIZE32 2) in 
  let remaining_items_64 :=
    (remaining_items_64) .- (@repr WORDSIZE16 1) in 
  @Some (policies_iterator_hacspec_t × policy_attributes_cursor_hacspec_t) ((
      (pos_53, remaining_items_64),
      (
        identity_provider_61,
        created_at_62,
        valid_to_63,
        (attributes_start_65, remaining_items_64)
      )
    ))).
(* Coq code:35 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:36]] *)
Definition load_state_hacspec
  (buf_66 : public_byte_seq)
  (offset_67 : int32)
  : (public_byte_seq × int32) :=
  (buf_66, @repr WORDSIZE32 1).
(* Coq code:36 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:37]] *)
Definition write_state_hacspec
  (buf_68 : public_byte_seq)
  (offset_69 : int32)
  : (public_byte_seq × int32) :=
  (buf_68, @repr WORDSIZE32 1).
(* Coq code:37 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:38]] *)
Definition state_size_hacspec  : int32 :=
  @repr WORDSIZE32 1.
(* Coq code:38 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:39]] *)
Definition resize_state_hacspec (new_size_70 : int32) : int32 :=
  @repr WORDSIZE32 1.
(* Coq code:39 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:40]] *)
Definition get_parameter_section_hacspec
  (buf_71 : public_byte_seq)
  (offset_72 : int32)
  : (public_byte_seq × int32) :=
  (buf_71, @repr WORDSIZE32 1).
(* Coq code:40 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:41]] *)
Definition get_parameter_size_hacspec  : int32 :=
  @repr WORDSIZE32 1.
(* Coq code:41 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:42]] *)
Definition get_slot_time_hacspec  : int64 :=
  @repr WORDSIZE64 1.
(* Coq code:42 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:43]] *)
Definition get_policy_section_hacspec
  (policy_bytes_73 : public_byte_seq)
  (offset_74 : int32)
  : (public_byte_seq × int32) :=
  (policy_bytes_73, @repr WORDSIZE32 1).
(* Coq code:43 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:44]] *)
Definition get_init_origin_hacspec
  (start_75 : public_byte_seq)
  : public_byte_seq :=
  start_75.
(* Coq code:44 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:45]] *)
Definition get_receive_invoker_hacspec
  (start_76 : public_byte_seq)
  : public_byte_seq :=
  start_76.
(* Coq code:45 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:46]] *)
Definition get_receive_self_address_hacspec
  (start_77 : public_byte_seq)
  : public_byte_seq :=
  start_77.
(* Coq code:46 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:47]] *)
Definition get_receive_self_balance_hacspec  : int64 :=
  @repr WORDSIZE64 1.
(* Coq code:47 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:48]] *)
Definition get_receive_sender_hacspec
  (start_78 : public_byte_seq)
  : public_byte_seq :=
  start_78.
(* Coq code:48 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:49]] *)
Definition log_event_hacspec
  (start_79 : public_byte_seq)
  : (public_byte_seq × int32) :=
  (start_79, @repr WORDSIZE32 1).
(* Coq code:49 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:50]] *)
Definition accept_hacspec  : int32 :=
  @repr WORDSIZE32 1.
(* Coq code:50 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:51]] *)
Definition simple_transfer_hacspec
  (buf_80 : public_byte_seq)
  (amount_81 : int64)
  : int32 :=
  @repr WORDSIZE32 1.
(* Coq code:51 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:52]] *)
Definition send_hacspec
  (addr_index_82 : int64)
  (addr_subindex_83 : int64)
  (receive_name_84 : public_byte_seq)
  (amount_85 : int64)
  (parameter_86 : public_byte_seq)
  : int32 :=
  @repr WORDSIZE32 1.
(* Coq code:52 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:53]] *)
Definition combine_and_hacspec (l_87 : int32) (r_88 : int32) : int32 :=
  @repr WORDSIZE32 1.
(* Coq code:53 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:54]] *)
Definition combine_or_hacspec (l_89 : int32) (r_90 : int32) : int32 :=
  @repr WORDSIZE32 1.
(* Coq code:54 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:55]] *)
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

(* Coq code:55 ends here *)

