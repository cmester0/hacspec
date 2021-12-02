(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Notation "'reject'" := (int32) : hacspec_scope.

Definition iint32_min  : int32 :=
  (not (@repr WORDSIZE32 0)) .^ (@cast _ int32 _ ((not (
          @repr WORDSIZE32 0)) shift_right (usize 1))).

Definition reject_impl_default  : reject :=
  iint32_min .

Inductive option_reject :=
| SomeReject : reject -> option_reject
| NoneReject : option_reject.

Definition new_reject_impl (x_0 : int32) : option_reject :=
  (if ((x_0) <.? (@repr WORDSIZE32 0)):bool then (SomeReject (x_0)) else (
      NoneReject)).

Definition reject_impl_convert_from_unit  : reject :=
  (iint32_min ) .+ (@repr WORDSIZE32 1).

Definition reject_impl_convert_from_parse_error  : reject :=
  (iint32_min ) .+ (@repr WORDSIZE32 2).

Inductive log_error :=
| Full : log_error
| Malformed : log_error.

Definition reject_impl_from_log_error (le_1 : log_error) : reject :=
  match le_1 with
  | Full => (iint32_min ) .+ (@repr WORDSIZE32 3)
  | Malformed => (iint32_min ) .+ (@repr WORDSIZE32 4)
  end.

Inductive new_contract_name_error :=
| NewContractNameErrorMissingInitPrefix : new_contract_name_error
| NewContractNameErrorTooLong : new_contract_name_error
| NewContractNameErrorContainsDot : new_contract_name_error
| NewContractNameErrorInvalidCharacters : new_contract_name_error.

Definition reject_impl_from_new_contract_name_error
  (nre_2 : new_contract_name_error)
  : reject :=
  match nre_2 with
  | NewContractNameErrorMissingInitPrefix => (iint32_min ) .+ (
    @repr WORDSIZE32 5)
  | NewContractNameErrorTooLong => (iint32_min ) .+ (@repr WORDSIZE32 6)
  | NewContractNameErrorContainsDot => (iint32_min ) .+ (@repr WORDSIZE32 9)
  | NewContractNameErrorInvalidCharacters => (iint32_min ) .+ (
    @repr WORDSIZE32 10)
  end.

Inductive new_receive_name_error :=
| NewReceiveNameErrorMissingDotSeparator : new_receive_name_error
| NewReceiveNameErrorTooLong : new_receive_name_error
| NewReceiveNameErrorInvalidCharacters : new_receive_name_error.

Definition reject_impl_from_new_receive_name_error
  (nre_3 : new_receive_name_error)
  : reject :=
  match nre_3 with
  | NewReceiveNameErrorMissingDotSeparator => (iint32_min ) .+ (
    @repr WORDSIZE32 7)
  | NewReceiveNameErrorTooLong => (iint32_min ) .+ (@repr WORDSIZE32 8)
  | NewReceiveNameErrorInvalidCharacters => (iint32_min ) .+ (
    @repr WORDSIZE32 11)
  end.

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
  (current_position_4 : contract_state)
  (pos_5 : seek_from)
  : (contract_state × seek_result) :=
  match pos_5 with
  | Start offset_6 => (@cast _ uint32 _ (offset_6), SeekResultOk (offset_6))
  | End delta_7 => (if ((delta_7) >=.? (@repr WORDSIZE64 0)):bool then (
      match pub_uint32_checked_add (current_position_4) (@cast _ uint32 _ (
          delta_7)) with
      | Some b_8 => (b_8, SeekResultOk (@cast _ uint64 _ (delta_7)))
      | None => (current_position_4, SeekResultErr (tt))
      end) else (match pub_int64_checked_abs (delta_7) with
      | Some b_9 => (
        (@repr WORDSIZE32 4) .- (@cast _ uint32 _ (b_9)),
        SeekResultOk (@cast _ uint64 _ ((@repr WORDSIZE32 4) .- (
              @cast _ uint32 _ (b_9))))
      )
      | None => (current_position_4, SeekResultErr (tt))
      end))
  | Current delta_10 => (if ((delta_10) >=.? (@repr WORDSIZE64 0)):bool then (
      match pub_uint32_checked_add (current_position_4) (@cast _ uint32 _ (
          delta_10)) with
      | Some offset_11 => (
        offset_11,
        SeekResultOk (@cast _ uint64 _ (offset_11))
      )
      | None => (current_position_4, SeekResultErr (tt))
      end) else (match pub_int64_checked_abs (delta_10) with
      | Some b_12 => match pub_uint32_checked_sub (current_position_4) (
        @cast _ uint32 _ (b_12)) with
      | Some offset_13 => (
        offset_13,
        SeekResultOk (@cast _ uint64 _ (offset_13))
      )
      | None => (current_position_4, SeekResultErr (tt))
      end
      | None => (current_position_4, SeekResultErr (tt))
      end))
  end.

Definition contract_state_impl_read_read
  (current_position_14 : contract_state)
  (num_read_15 : int32)
  : (contract_state × uint_size) :=
  ((current_position_14) .+ (num_read_15), @cast _ uint32 _ (num_read_15)).

Definition contract_state_impl_read_read_u64
  (current_position_16 : contract_state)
  (num_read_17 : int32)
  : (contract_state × bool) :=
  (
    (current_position_16) .+ (num_read_17),
    (num_read_17) =.? (@repr WORDSIZE32 8)
  ).

Definition contract_state_impl_read_read_u32
  (current_position_18 : contract_state)
  (num_read_19 : int32)
  : (contract_state × bool) :=
  (
    (current_position_18) .+ (num_read_19),
    (num_read_19) =.? (@repr WORDSIZE32 4)
  ).

Definition contract_state_impl_read_read_u8
  (current_position_20 : contract_state)
  (num_read_21 : int32)
  : (contract_state × bool) :=
  (
    (current_position_20) .+ (num_read_21),
    (num_read_21) =.? (@repr WORDSIZE32 1)
  ).

Definition write_impl_for_contract_state_test
  (current_position_22 : contract_state)
  (len_23 : int32)
  : bool :=
  option_is_none (pub_uint32_checked_add (current_position_22) (len_23)).

Definition write_impl_for_contract_state
  (current_position_24 : contract_state)
  (num_bytes_25 : int32)
  : (contract_state × uint_size) :=
  ((current_position_24) .+ (num_bytes_25), @cast _ uint32 _ (num_bytes_25)).

Definition has_contract_state_impl_for_contract_state_open  : contract_state :=
  @repr WORDSIZE32 0.

Definition has_contract_state_impl_for_contract_state_reserve_0
  (len_26 : int32)
  (cur_size_27 : int32)
  : bool :=
  (cur_size_27) <.? (len_26).

Definition has_contract_state_impl_for_contract_state_reserve_1
  (res_28 : int32)
  : bool :=
  (res_28) =.? (@repr WORDSIZE32 1).

Definition has_contract_state_impl_for_contract_state_truncate_0
  (cur_size_29 : int32)
  (new_size_30 : int32)
  : bool :=
  (cur_size_29) >.? (new_size_30).

Definition has_contract_state_impl_for_contract_state_truncate_1
  (current_position_31 : contract_state)
  (new_size_32 : int32)
  : contract_state :=
  (if ((new_size_32) <.? (current_position_31)):bool then (new_size_32) else (
      current_position_31)).

Notation "'parameter'" := (int32) : hacspec_scope.

Definition read_impl_for_parameter_read
  (current_position_33 : parameter)
  (num_read_34 : int32)
  : (parameter × uint_size) :=
  ((current_position_33) .+ (num_read_34), @cast _ uint32 _ (num_read_34)).

Notation "'attributes_cursor'" := ((int32 × int16)) : hacspec_scope.

Definition has_policy_impl_for_policy_attributes_cursor_next_test
  (policy_attribute_items_35 : attributes_cursor)
  : bool :=
  let '(_, remaining_items_36) :=
    policy_attribute_items_35 in 
  (remaining_items_36) =.? (@repr WORDSIZE16 0).

Definition has_policy_impl_for_policy_attributes_cursor_next_tag_invalid
  (policy_attribute_items_37 : attributes_cursor)
  (tag_value_len_1_38 : int8)
  (num_read_39 : int32)
  : (attributes_cursor × bool) :=
  let '(current_position_40, remaining_items_41) :=
    policy_attribute_items_37 in 
  let policy_attribute_items_42 : (int32 × int16) :=
    ((current_position_40) .+ (num_read_39), remaining_items_41) in 
  (policy_attribute_items_42, (tag_value_len_1_38) >.? (@repr WORDSIZE8 31)).

Definition has_policy_impl_for_policy_attributes_cursor_next
  (policy_attribute_items_43 : attributes_cursor)
  (num_read_44 : int32)
  : attributes_cursor :=
  let '(current_position_45, remaining_items_46) :=
    policy_attribute_items_43 in 
  (
    (current_position_45) .+ (num_read_44),
    (remaining_items_46) .- (@repr WORDSIZE16 1)
  ).

