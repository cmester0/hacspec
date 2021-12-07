(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Notation "'reject'" := (int32) : hacspec_scope.

Definition reject_impl_default  : reject :=
  min.

Inductive option_reject :=
| SomeReject : reject -> option_reject
| NoneReject : option_reject.

Definition new_reject_impl (x_0 : int32) : option_reject :=
  (if ((x_0) <.? (@repr WORDSIZE32 0)):bool then (SomeReject (x_0)) else (
      NoneReject)).

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

Inductive seek_result :=
| SeekResultOk : int64 -> seek_result
| SeekResultErr : unit -> seek_result.

Inductive seek_from :=
| Start : int64 -> seek_from
| End : int64 -> seek_from
| Current : int64 -> seek_from.

Notation "'uint32_option'" := ((option int32)) : hacspec_scope.

Notation "'iint64_option'" := ((option int64)) : hacspec_scope.

Definition contract_state_impl_seek
  (current_position_5 : contract_state)
  (pos_6 : seek_from)
  : (contract_state × seek_result) :=
  match pos_6 with
  | Start offset_7 => (@cast _ uint32 _ (offset_7), SeekResultOk (offset_7))
  | End delta_8 => (if ((delta_8) >=.? (@repr WORDSIZE64 0)):bool then (
      match pub_uint32_checked_add (current_position_5) (@cast _ uint32 _ (
          delta_8)) with
      | Some b_9 => (b_9, SeekResultOk (@cast _ uint64 _ (delta_8)))
      | None => (current_position_5, SeekResultErr (tt))
      end) else (match pub_int64_checked_abs (delta_8) with
      | Some b_10 => (
        (@repr WORDSIZE32 4) .- (@cast _ uint32 _ (b_10)),
        SeekResultOk (@cast _ uint64 _ ((@repr WORDSIZE32 4) .- (
              @cast _ uint32 _ (b_10))))
      )
      | None => (current_position_5, SeekResultErr (tt))
      end))
  | Current delta_11 => (if ((delta_11) >=.? (@repr WORDSIZE64 0)):bool then (
      match pub_uint32_checked_add (current_position_5) (@cast _ uint32 _ (
          delta_11)) with
      | Some offset_12 => (
        offset_12,
        SeekResultOk (@cast _ uint64 _ (offset_12))
      )
      | None => (current_position_5, SeekResultErr (tt))
      end) else (match pub_int64_checked_abs (delta_11) with
      | Some b_13 => match pub_uint32_checked_sub (current_position_5) (
        @cast _ uint32 _ (b_13)) with
      | Some offset_14 => (
        offset_14,
        SeekResultOk (@cast _ uint64 _ (offset_14))
      )
      | None => (current_position_5, SeekResultErr (tt))
      end
      | None => (current_position_5, SeekResultErr (tt))
      end))
  end.

Definition contract_state_impl_read_read
  (current_position_15 : contract_state)
  (num_read_16 : int32)
  : (contract_state × uint_size) :=
  ((current_position_15) .+ (num_read_16), @cast _ uint32 _ (num_read_16)).

Definition contract_state_impl_read_read_u64
  (current_position_17 : contract_state)
  (num_read_18 : int32)
  : (contract_state × bool) :=
  (
    (current_position_17) .+ (num_read_18),
    (num_read_18) =.? (@repr WORDSIZE32 8)
  ).

Definition contract_state_impl_read_read_u32
  (current_position_19 : contract_state)
  (num_read_20 : int32)
  : (contract_state × bool) :=
  (
    (current_position_19) .+ (num_read_20),
    (num_read_20) =.? (@repr WORDSIZE32 4)
  ).

Definition contract_state_impl_read_read_u8
  (current_position_21 : contract_state)
  (num_read_22 : int32)
  : (contract_state × bool) :=
  (
    (current_position_21) .+ (num_read_22),
    (num_read_22) =.? (@repr WORDSIZE32 1)
  ).

Definition write_impl_for_contract_state_test
  (current_position_23 : contract_state)
  (len_24 : int32)
  : bool :=
  option_is_none (pub_uint32_checked_add (current_position_23) (len_24)).

Definition write_impl_for_contract_state
  (current_position_25 : contract_state)
  (num_bytes_26 : int32)
  : (contract_state × uint_size) :=
  ((current_position_25) .+ (num_bytes_26), @cast _ uint32 _ (num_bytes_26)).

Definition has_contract_state_impl_for_contract_state_open  : contract_state :=
  @repr WORDSIZE32 0.

Definition has_contract_state_impl_for_contract_state_reserve_0
  (len_27 : int32)
  (cur_size_28 : int32)
  : bool :=
  (cur_size_28) <.? (len_27).

Definition has_contract_state_impl_for_contract_state_reserve_1
  (res_29 : int32)
  : bool :=
  (res_29) =.? (@repr WORDSIZE32 1).

Definition has_contract_state_impl_for_contract_state_truncate_0
  (cur_size_30 : int32)
  (new_size_31 : int32)
  : bool :=
  (cur_size_30) >.? (new_size_31).

Definition has_contract_state_impl_for_contract_state_truncate_1
  (current_position_32 : contract_state)
  (new_size_33 : int32)
  : contract_state :=
  (if ((new_size_33) <.? (current_position_32)):bool then (new_size_33) else (
      current_position_32)).

Notation "'parameter'" := (int32) : hacspec_scope.

Definition read_impl_for_parameter_read
  (current_position_34 : parameter)
  (num_read_35 : int32)
  : (parameter × uint_size) :=
  ((current_position_34) .+ (num_read_35), @cast _ uint32 _ (num_read_35)).

Notation "'attributes_cursor'" := ((int32 × int16)) : hacspec_scope.

Definition has_policy_impl_for_policy_attributes_cursor_next_test
  (policy_attribute_items_36 : attributes_cursor)
  : bool :=
  let '(_, remaining_items_37) :=
    policy_attribute_items_36 in 
  (remaining_items_37) =.? (@repr WORDSIZE16 0).

Definition has_policy_impl_for_policy_attributes_cursor_next_tag_invalid
  (policy_attribute_items_38 : attributes_cursor)
  (tag_value_len_1_39 : int8)
  (num_read_40 : int32)
  : (attributes_cursor × bool) :=
  let '(current_position_41, remaining_items_42) :=
    policy_attribute_items_38 in 
  let policy_attribute_items_43 : (int32 × int16) :=
    ((current_position_41) .+ (num_read_40), remaining_items_42) in 
  (policy_attribute_items_43, (tag_value_len_1_39) >.? (@repr WORDSIZE8 31)).

Definition has_policy_impl_for_policy_attributes_cursor_next
  (policy_attribute_items_44 : attributes_cursor)
  (num_read_45 : int32)
  : attributes_cursor :=
  let '(current_position_46, remaining_items_47) :=
    policy_attribute_items_44 in 
  (
    (current_position_46) .+ (num_read_45),
    (remaining_items_47) .- (@repr WORDSIZE16 1)
  ).

