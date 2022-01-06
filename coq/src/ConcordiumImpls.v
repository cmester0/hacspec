(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Notation "'reject_t'" := (int32) : hacspec_scope.

Definition reject_impl_deafult  : reject_t :=
  min_v.

Definition new_reject_impl (x_0 : int32) : (option reject_t) :=
  (if ((x_0) <.? (@repr WORDSIZE32 0)):bool then (@Some int32 (x_0)) else (
      @None int32)).

Definition reject_impl_convert_from_unit  : reject_t :=
  (min_v) .+ (@repr WORDSIZE32 1).

Theorem ensures_reject_impl_convert_from_unit : forall result_1 ,
@reject_impl_convert_from_unit  = result_1 ->
(result_1) !=.? (@repr WORDSIZE32 0).
Proof. Admitted.

Definition reject_impl_convert_from_parse_error  : reject_t :=
  (min_v) .+ (@repr WORDSIZE32 2).

Theorem ensures_reject_impl_convert_from_parse_error : forall result_1 ,
@reject_impl_convert_from_parse_error  = result_1 ->
(result_1) !=.? (@repr WORDSIZE32 0).
Proof. Admitted.

Inductive log_error_t :=
| Full : log_error_t
| Malformed : log_error_t.

Definition reject_impl_from_log_error (le_2 : log_error_t) : reject_t :=
  match le_2 with
  | Full => (min_v) .+ (@repr WORDSIZE32 3)
  | Malformed => (min_v) .+ (@repr WORDSIZE32 4)
  end.

Theorem ensures_reject_impl_from_log_error : forall result_1 (
  le_2 : log_error_t),
@reject_impl_from_log_error le_2 = result_1 ->
(result_1) !=.? (@repr WORDSIZE32 0).
Proof. Admitted.

Inductive new_contract_name_error_t :=
| NewContractNameErrorMissingInitPrefix : new_contract_name_error_t
| NewContractNameErrorTooLong : new_contract_name_error_t
| NewContractNameErrorContainsDot : new_contract_name_error_t
| NewContractNameErrorInvalidCharacters : new_contract_name_error_t.

Definition reject_impl_from_new_contract_name_error
  (nre_3 : new_contract_name_error_t)
  : reject_t :=
  match nre_3 with
  | NewContractNameErrorMissingInitPrefix => (min_v) .+ (@repr WORDSIZE32 5)
  | NewContractNameErrorTooLong => (min_v) .+ (@repr WORDSIZE32 6)
  | NewContractNameErrorContainsDot => (min_v) .+ (@repr WORDSIZE32 9)
  | NewContractNameErrorInvalidCharacters => (min_v) .+ (@repr WORDSIZE32 10)
  end.

Theorem ensures_reject_impl_from_new_contract_name_error : forall result_1 (
  nre_3 : new_contract_name_error_t),
@reject_impl_from_new_contract_name_error nre_3 = result_1 ->
(result_1) !=.? (@repr WORDSIZE32 0).
Proof. Admitted.

Inductive new_receive_name_error_t :=
| NewReceiveNameErrorMissingDotSeparator : new_receive_name_error_t
| NewReceiveNameErrorTooLong : new_receive_name_error_t
| NewReceiveNameErrorInvalidCharacters : new_receive_name_error_t.

Definition reject_impl_from_new_receive_name_error
  (nre_4 : new_receive_name_error_t)
  : reject_t :=
  match nre_4 with
  | NewReceiveNameErrorMissingDotSeparator => (min_v) .+ (@repr WORDSIZE32 7)
  | NewReceiveNameErrorTooLong => (min_v) .+ (@repr WORDSIZE32 8)
  | NewReceiveNameErrorInvalidCharacters => (min_v) .+ (@repr WORDSIZE32 11)
  end.

Theorem ensures_reject_impl_from_new_receive_name_error : forall result_1 (
  nre_4 : new_receive_name_error_t),
@reject_impl_from_new_receive_name_error nre_4 = result_1 ->
(result_1) !=.? (@repr WORDSIZE32 0).
Proof. Admitted.

Notation "'contract_state_t'" := (int32) : hacspec_scope.

Inductive seek_from_t :=
| Start : int64 -> seek_from_t
| End : int64 -> seek_from_t
| Current : int64 -> seek_from_t.

Notation "'uint32_option_t'" := ((option int32)) : hacspec_scope.

Notation "'iint64_option_t'" := ((option int64)) : hacspec_scope.

Definition contract_state_impl_seek
  (current_position_5 : contract_state_t)
  (pos_6 : seek_from_t)
  : (result (contract_state_t × int64) unit) :=
  match pos_6 with
  | Start offset_7 => @Ok (contract_state_t × int64) unit ((
      @cast _ uint32 _ (offset_7),
      offset_7
    ))
  | End delta_8 => (if ((delta_8) >=.? (@repr WORDSIZE64 0)):bool then (
      match pub_uint32_checked_add (current_position_5) (@cast _ uint32 _ (
          delta_8)) with
      | Some b_9 => @Ok (contract_state_t × int64) unit ((
          b_9,
          @cast _ uint64 _ (delta_8)
        ))
      | None => @Err (contract_state_t × int64) unit (tt)
      end) else (match pub_int64_checked_abs (delta_8) with
      | Some b_10 => @Ok (contract_state_t × int64) unit ((
          (@repr WORDSIZE32 4) .- (@cast _ uint32 _ (b_10)),
          @cast _ uint64 _ ((@repr WORDSIZE32 4) .- (@cast _ uint32 _ (b_10)))
        ))
      | None => @Err (contract_state_t × int64) unit (tt)
      end))
  | Current delta_11 => (if ((delta_11) >=.? (@repr WORDSIZE64 0)):bool then (
      match pub_uint32_checked_add (current_position_5) (@cast _ uint32 _ (
          delta_11)) with
      | Some offset_12 => @Ok (contract_state_t × int64) unit ((
          offset_12,
          @cast _ uint64 _ (offset_12)
        ))
      | None => @Err (contract_state_t × int64) unit (tt)
      end) else (match pub_int64_checked_abs (delta_11) with
      | Some b_13 => match pub_uint32_checked_sub (current_position_5) (
        @cast _ uint32 _ (b_13)) with
      | Some offset_14 => @Ok (contract_state_t × int64) unit ((
          offset_14,
          @cast _ uint64 _ (offset_14)
        ))
      | None => @Err (contract_state_t × int64) unit (tt)
      end
      | None => @Err (contract_state_t × int64) unit (tt)
      end))
  end.

Definition load_state_hacspec
  (buf_15 : public_byte_seq)
  (offset_16 : int32)
  : (public_byte_seq × int32) :=
  (buf_15, @repr WORDSIZE32 1).

Definition contract_state_impl_read_read
  (current_position_17 : contract_state_t)
  (buf_18 : public_byte_seq)
  : (contract_state_t × uint_size) :=
  let '(buf_19, num_read_20) :=
    load_state_hacspec (buf_18) (current_position_17) in 
  ((current_position_17) .+ (num_read_20), @cast _ uint32 _ (num_read_20)).

Definition contract_state_impl_read_read_u64
  (current_position_21 : contract_state_t)
  (num_read_22 : int32)
  : (contract_state_t × bool) :=
  (
    (current_position_21) .+ (num_read_22),
    (num_read_22) =.? (@repr WORDSIZE32 8)
  ).

Definition contract_state_impl_read_read_u32
  (current_position_23 : contract_state_t)
  (num_read_24 : int32)
  : (contract_state_t × bool) :=
  (
    (current_position_23) .+ (num_read_24),
    (num_read_24) =.? (@repr WORDSIZE32 4)
  ).

Definition contract_state_impl_read_read_u8
  (current_position_25 : contract_state_t)
  (num_read_26 : int32)
  : (contract_state_t × bool) :=
  (
    (current_position_25) .+ (num_read_26),
    (num_read_26) =.? (@repr WORDSIZE32 1)
  ).

Definition write_impl_for_contract_state_test
  (current_position_27 : contract_state_t)
  (len_28 : int32)
  : bool :=
  option_is_none (pub_uint32_checked_add (current_position_27) (len_28)).

Definition write_impl_for_contract_state
  (current_position_29 : contract_state_t)
  (num_bytes_30 : int32)
  : (contract_state_t × uint_size) :=
  ((current_position_29) .+ (num_bytes_30), @cast _ uint32 _ (num_bytes_30)).

Definition has_contract_state_impl_for_contract_state_open
  
  : contract_state_t :=
  @repr WORDSIZE32 0.

Definition has_contract_state_impl_for_contract_state_reserve_0
  (len_31 : int32)
  (cur_size_32 : int32)
  : bool :=
  (cur_size_32) <.? (len_31).

Definition has_contract_state_impl_for_contract_state_reserve_1
  (res_33 : int32)
  : bool :=
  (res_33) =.? (@repr WORDSIZE32 1).

Definition has_contract_state_impl_for_contract_state_truncate_0
  (cur_size_34 : int32)
  (new_size_35 : int32)
  : bool :=
  (cur_size_34) >.? (new_size_35).

Definition has_contract_state_impl_for_contract_state_truncate_1
  (current_position_36 : contract_state_t)
  (new_size_37 : int32)
  : contract_state_t :=
  (if ((new_size_37) <.? (current_position_36)):bool then (new_size_37) else (
      current_position_36)).

Notation "'parameter_t'" := (int32) : hacspec_scope.

Definition read_impl_for_parameter_read
  (current_position_38 : parameter_t)
  (num_read_39 : int32)
  : (parameter_t × uint_size) :=
  ((current_position_38) .+ (num_read_39), @cast _ uint32 _ (num_read_39)).

Notation "'attributes_cursor_t'" := ((int32 × int16)) : hacspec_scope.

Definition has_policy_impl_for_policy_attributes_cursor_next_test
  (policy_attribute_items_40 : attributes_cursor_t)
  : bool :=
  let '(_, remaining_items_41) :=
    policy_attribute_items_40 in 
  (remaining_items_41) =.? (@repr WORDSIZE16 0).

Definition has_policy_impl_for_policy_attributes_cursor_next_tag_invalid
  (policy_attribute_items_42 : attributes_cursor_t)
  (tag_value_len_1_43 : int8)
  (num_read_44 : int32)
  : (attributes_cursor_t × bool) :=
  let '(current_position_45, remaining_items_46) :=
    policy_attribute_items_42 in 
  let policy_attribute_items_47 : (int32 × int16) :=
    ((current_position_45) .+ (num_read_44), remaining_items_46) in 
  (policy_attribute_items_47, (tag_value_len_1_43) >.? (@repr WORDSIZE8 31)).

Definition has_policy_impl_for_policy_attributes_cursor_next
  (policy_attribute_items_48 : attributes_cursor_t)
  (num_read_49 : int32)
  : attributes_cursor_t :=
  let '(current_position_50, remaining_items_51) :=
    policy_attribute_items_48 in 
  (
    (current_position_50) .+ (num_read_49),
    (remaining_items_51) .- (@repr WORDSIZE16 1)
  ).

