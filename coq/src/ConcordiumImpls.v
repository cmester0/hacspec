(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Notation "'reject'" := (int32) : hacspec_scope.

Definition reject_impl_deafult  : reject :=
  min.

Notation "'option_reject'" := ((option reject)) : hacspec_scope.

Definition new_reject_impl (x_0 : int32) : option_reject :=
  (if ((x_0) <.? (@repr WORDSIZE32 0)):bool then (@Some reject (x_0)) else (
      @None int32)).

Definition reject_impl_convert_from_unit  : reject :=
  (min) .+ (@repr WORDSIZE32 1).

Theorem ensures_reject_impl_convert_from_unit : forall result_1 ,
@reject_impl_convert_from_unit  = result_1 ->
(result_1) !=.? (@repr WORDSIZE32 0).
Proof. Admitted.

Definition reject_impl_convert_from_parse_error  : reject :=
  (min) .+ (@repr WORDSIZE32 2).

Theorem ensures_reject_impl_convert_from_parse_error : forall result_1 ,
@reject_impl_convert_from_parse_error  = result_1 ->
(result_1) !=.? (@repr WORDSIZE32 0).
Proof. Admitted.

Inductive log_error :=
| Full : log_error
| Malformed : log_error.

Definition reject_impl_from_log_error (le_2 : log_error) : reject :=
  match le_2 with
  | Full => (min) .+ (@repr WORDSIZE32 3)
  | Malformed => (min) .+ (@repr WORDSIZE32 4)
  end.

Theorem ensures_reject_impl_from_log_error : forall result_1 (le_2 : log_error),
@reject_impl_from_log_error le_2 = result_1 ->
(result_1) !=.? (@repr WORDSIZE32 0).
Proof. Admitted.

Inductive new_contract_name_error :=
| NewContractNameErrorMissingInitPrefix : new_contract_name_error
| NewContractNameErrorTooLong : new_contract_name_error
| NewContractNameErrorContainsDot : new_contract_name_error
| NewContractNameErrorInvalidCharacters : new_contract_name_error.

Definition reject_impl_from_new_contract_name_error
  (nre_3 : new_contract_name_error)
  : reject :=
  match nre_3 with
  | NewContractNameErrorMissingInitPrefix => (min) .+ (@repr WORDSIZE32 5)
  | NewContractNameErrorTooLong => (min) .+ (@repr WORDSIZE32 6)
  | NewContractNameErrorContainsDot => (min) .+ (@repr WORDSIZE32 9)
  | NewContractNameErrorInvalidCharacters => (min) .+ (@repr WORDSIZE32 10)
  end.

Theorem ensures_reject_impl_from_new_contract_name_error : forall result_1 (
  nre_3 : new_contract_name_error),
@reject_impl_from_new_contract_name_error nre_3 = result_1 ->
(result_1) !=.? (@repr WORDSIZE32 0).
Proof. Admitted.

Inductive new_receive_name_error :=
| NewReceiveNameErrorMissingDotSeparator : new_receive_name_error
| NewReceiveNameErrorTooLong : new_receive_name_error
| NewReceiveNameErrorInvalidCharacters : new_receive_name_error.

Definition reject_impl_from_new_receive_name_error
  (nre_4 : new_receive_name_error)
  : reject :=
  match nre_4 with
  | NewReceiveNameErrorMissingDotSeparator => (min) .+ (@repr WORDSIZE32 7)
  | NewReceiveNameErrorTooLong => (min) .+ (@repr WORDSIZE32 8)
  | NewReceiveNameErrorInvalidCharacters => (min) .+ (@repr WORDSIZE32 11)
  end.

Theorem ensures_reject_impl_from_new_receive_name_error : forall result_1 (
  nre_4 : new_receive_name_error),
@reject_impl_from_new_receive_name_error nre_4 = result_1 ->
(result_1) !=.? (@repr WORDSIZE32 0).
Proof. Admitted.

Notation "'contract_state'" := (int32) : hacspec_scope.

Notation "'seek_result'" := ((result (contract_state × int64
  ) unit)) : hacspec_scope.

Inductive seek_from :=
| Start : int64 -> seek_from
| End : int64 -> seek_from
| Current : int64 -> seek_from.

Notation "'uint32_option'" := ((option int32)) : hacspec_scope.

Notation "'iint64_option'" := ((option int64)) : hacspec_scope.

Definition contract_state_impl_seek
  (current_position_5 : contract_state)
  (pos_6 : seek_from)
  `{forall delta_7 ,
  pos_6 = End (delta_7) ->
  exists b_8 true}
  : seek_result :=
  match pos_6 with
  | Start offset_9 => @Ok (contract_state × int64) unit ((
      @cast _ uint32 _ (offset_9),
      offset_9
    ))
  | End delta_10 => (if ((delta_10) >=.? (@repr WORDSIZE64 0)):bool then (
      match pub_uint32_checked_add (current_position_5) (@cast _ uint32 _ (
          delta_10)) with
      | Some b_11 => @Ok (contract_state × int64) unit ((
          b_11,
          @cast _ uint64 _ (delta_10)
        ))
      | None => @Err (contract_state × int64) unit (tt)
      end) else (match pub_int64_checked_abs (delta_10) with
      | Some b_12 => @Ok (contract_state × int64) unit ((
          (@repr WORDSIZE32 4) .- (@cast _ uint32 _ (b_12)),
          @cast _ uint64 _ ((@repr WORDSIZE32 4) .- (@cast _ uint32 _ (b_12)))
        ))
      | None => @Err (contract_state × int64) unit (tt)
      end))
  | Current delta_13 => (if ((delta_13) >=.? (@repr WORDSIZE64 0)):bool then (
      match pub_uint32_checked_add (current_position_5) (@cast _ uint32 _ (
          delta_13)) with
      | Some offset_14 => @Ok (contract_state × int64) unit ((
          offset_14,
          @cast _ uint64 _ (offset_14)
        ))
      | None => @Err (contract_state × int64) unit (tt)
      end) else (match pub_int64_checked_abs (delta_13) with
      | Some b_15 => match pub_uint32_checked_sub (current_position_5) (
        @cast _ uint32 _ (b_15)) with
      | Some offset_16 => @Ok (contract_state × int64) unit ((
          offset_16,
          @cast _ uint64 _ (offset_16)
        ))
      | None => @Err (contract_state × int64) unit (tt)
      end
      | None => @Err (contract_state × int64) unit (tt)
      end))
  end.

Definition load_state_hacspec
  (buf_17 : public_byte_seq)
  (offset_18 : int32)
  : (public_byte_seq × int32) :=
  (buf_17, @repr WORDSIZE32 1).

Theorem ensures_load_state_hacspec : forall result_1 (
  buf_17 : public_byte_seq) (offset_18 : int32),
@load_state_hacspec buf_17 offset_18 = result_1 ->
(result_1) !=.? ((buf_17, @repr WORDSIZE32 2)).
Proof. Admitted.

Definition contract_state_impl_read_read
  (current_position_19 : contract_state)
  (buf_20 : public_byte_seq)
  : (contract_state × uint_size) :=
  let '(buf_21, num_read_22) :=
    load_state_hacspec (buf_20) (current_position_19) in 
  ((current_position_19) .+ (num_read_22), @cast _ uint32 _ (num_read_22)).

Definition contract_state_impl_read_read_u64
  (current_position_23 : contract_state)
  (num_read_24 : int32)
  : (contract_state × bool) :=
  (
    (current_position_23) .+ (num_read_24),
    (num_read_24) =.? (@repr WORDSIZE32 8)
  ).

Definition contract_state_impl_read_read_u32
  (current_position_25 : contract_state)
  (num_read_26 : int32)
  : (contract_state × bool) :=
  (
    (current_position_25) .+ (num_read_26),
    (num_read_26) =.? (@repr WORDSIZE32 4)
  ).

Definition contract_state_impl_read_read_u8
  (current_position_27 : contract_state)
  (num_read_28 : int32)
  : (contract_state × bool) :=
  (
    (current_position_27) .+ (num_read_28),
    (num_read_28) =.? (@repr WORDSIZE32 1)
  ).

Definition write_impl_for_contract_state_test
  (current_position_29 : contract_state)
  (len_30 : int32)
  : bool :=
  option_is_none (pub_uint32_checked_add (current_position_29) (len_30)).

Definition write_impl_for_contract_state
  (current_position_31 : contract_state)
  (num_bytes_32 : int32)
  : (contract_state × uint_size) :=
  ((current_position_31) .+ (num_bytes_32), @cast _ uint32 _ (num_bytes_32)).

Definition has_contract_state_impl_for_contract_state_open  : contract_state :=
  @repr WORDSIZE32 0.

Definition has_contract_state_impl_for_contract_state_reserve_0
  (len_33 : int32)
  (cur_size_34 : int32)
  : bool :=
  (cur_size_34) <.? (len_33).

Definition has_contract_state_impl_for_contract_state_reserve_1
  (res_35 : int32)
  : bool :=
  (res_35) =.? (@repr WORDSIZE32 1).

Definition has_contract_state_impl_for_contract_state_truncate_0
  (cur_size_36 : int32)
  (new_size_37 : int32)
  : bool :=
  (cur_size_36) >.? (new_size_37).

Definition has_contract_state_impl_for_contract_state_truncate_1
  (current_position_38 : contract_state)
  (new_size_39 : int32)
  : contract_state :=
  (if ((new_size_39) <.? (current_position_38)):bool then (new_size_39) else (
      current_position_38)).

Notation "'parameter'" := (int32) : hacspec_scope.

Definition read_impl_for_parameter_read
  (current_position_40 : parameter)
  (num_read_41 : int32)
  : (parameter × uint_size) :=
  ((current_position_40) .+ (num_read_41), @cast _ uint32 _ (num_read_41)).

Notation "'attributes_cursor'" := ((int32 × int16)) : hacspec_scope.

Definition has_policy_impl_for_policy_attributes_cursor_next_test
  (policy_attribute_items_42 : attributes_cursor)
  : bool :=
  let '(_, remaining_items_43) :=
    policy_attribute_items_42 in 
  (remaining_items_43) =.? (@repr WORDSIZE16 0).

Definition has_policy_impl_for_policy_attributes_cursor_next_tag_invalid
  (policy_attribute_items_44 : attributes_cursor)
  (tag_value_len_1_45 : int8)
  (num_read_46 : int32)
  : (attributes_cursor × bool) :=
  let '(current_position_47, remaining_items_48) :=
    policy_attribute_items_44 in 
  let policy_attribute_items_49 : (int32 × int16) :=
    ((current_position_47) .+ (num_read_46), remaining_items_48) in 
  (policy_attribute_items_49, (tag_value_len_1_45) >.? (@repr WORDSIZE8 31)).

Definition has_policy_impl_for_policy_attributes_cursor_next
  (policy_attribute_items_50 : attributes_cursor)
  (num_read_51 : int32)
  : attributes_cursor :=
  let '(current_position_52, remaining_items_53) :=
    policy_attribute_items_50 in 
  (
    (current_position_52) .+ (num_read_51),
    (remaining_items_53) .- (@repr WORDSIZE16 1)
  ).
