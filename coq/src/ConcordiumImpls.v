(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
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
(result_1) !=.? (@repr WORDSIZE32 0).
Proof. Admitted.

Definition reject_impl_convert_from_parse_error  : reject_hacspec_t :=
  (min_v) .+ (@repr WORDSIZE32 2).

Theorem ensures_reject_impl_convert_from_parse_error : forall result_1 ,
@reject_impl_convert_from_parse_error  = result_1 ->
(result_1) !=.? (@repr WORDSIZE32 0).
Proof. Admitted.

Inductive log_error_t :=
| Full : log_error_t
| Malformed : log_error_t.

Definition reject_impl_from_log_error (le_2 : log_error_t) : reject_hacspec_t :=
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
(result_1) !=.? (@repr WORDSIZE32 0).
Proof. Admitted.

Inductive new_receive_name_error_t :=
| NewReceiveNameErrorMissingDotSeparator : new_receive_name_error_t
| NewReceiveNameErrorTooLong : new_receive_name_error_t
| NewReceiveNameErrorInvalidCharacters : new_receive_name_error_t.

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
(result_1) !=.? (@repr WORDSIZE32 0).
Proof. Admitted.

Notation "'contract_state_hacspec_t'" := (int32) : hacspec_scope.

Inductive seek_from_t :=
| Start : int64 -> seek_from_t
| End : int64 -> seek_from_t
| Current : int64 -> seek_from_t.

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

Definition has_policy_impl_for_policy_attributes_cursor_next_item
  (policy_attribute_items_54 : attributes_cursor_hacspec_t)
  (buf_55 : public_byte_seq)
  : (option (attributes_cursor_hacspec_t × (int8 × int8))) :=
  let '(current_position_56, remaining_items_57) :=
    policy_attribute_items_54 in 
  let tag_value_len_58 : seq int8 :=
    seq_new_ (default) (usize 2) in 
  let '(tag_value_len_59, num_read_60) :=
    get_policy_section_hacspec (tag_value_len_58) (current_position_56) in 
  let current_position_56 :=
    (current_position_56) .+ (num_read_60) in 
  let '(buf_61, num_read_62) :=
    get_policy_section_hacspec (buf_55) (current_position_56) in 
  let current_position_56 :=
    (current_position_56) .+ (num_read_62) in 
  let remaining_items_57 :=
    (remaining_items_57) .- (@repr WORDSIZE16 1) in 
  @Some (attributes_cursor_hacspec_t × (int8 × int8)) ((
      (current_position_56, remaining_items_57),
      (
        seq_index (tag_value_len_59) (usize 0),
        seq_index (tag_value_len_59) (usize 1)
      )
    )).

Notation "'policies_iterator_hacspec_t'" := ((int32 × int16)) : hacspec_scope.

Notation "'policy_attributes_cursor_hacspec_t'" := ((
  int32 ×
  int64 ×
  int64 ×
  attributes_cursor_hacspec_t
)) : hacspec_scope.

Definition iterator_impl_for_policies_iterator_next
  (policies_iterator_63 : policies_iterator_hacspec_t)
  : (option (policies_iterator_hacspec_t × policy_attributes_cursor_hacspec_t
    )) :=
  let '(pos_64, _) :=
    policies_iterator_63 in 
  let '(buf_65, _) :=
    get_policy_section_hacspec (seq_new_ (default) (((((usize 2) + (
                usize 4)) + (usize 8)) + (usize 8)) + (usize 2))) (pos_64) in 
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
    (((((pos_64) .+ (@repr WORDSIZE32 2)) .+ (@repr WORDSIZE32 4)) .+ (
          @repr WORDSIZE32 8)) .+ (@repr WORDSIZE32 8)) .+ (
      @repr WORDSIZE32 2) in 
  let pos_64 :=
    ((pos_64) .+ (@cast _ uint32 _ (u16_from_le_bytes (array_from_seq (2) (
              skip_part_66))))) .+ (@repr WORDSIZE32 2) in 
  let remaining_items_74 :=
    (remaining_items_74) .- (@repr WORDSIZE16 1) in 
  @Some (policies_iterator_hacspec_t × policy_attributes_cursor_hacspec_t) ((
      (pos_64, remaining_items_74),
      (
        identity_provider_71,
        created_at_72,
        valid_to_73,
        (attributes_start_75, remaining_items_74)
      )
    )).

