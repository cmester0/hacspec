(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.
Export Hacspec_Lib.

Require Import Concordium_Prims.
Export Concordium_Prims.

Require Import Concordium_Types.
Export Concordium_Types.

Require Import Concordium_Traits.
Export Concordium_Traits.

Notation "'reject_hacspec_t'" := (int32) : hacspec_scope.

Definition reject_impl_deafult   : reject_hacspec_t :=
  - (@repr WORDSIZE32 (Z.neg 2147483648)).


Definition new_reject_impl (x_26 : int32)  : (option int32) :=
  (if ((x_26) <.? (@repr WORDSIZE32 (0))):bool then (@Some int32 (x_26)) else (
      @None int32)).


Definition reject_impl_convert_from_unit   : reject_hacspec_t :=
  (- (@repr WORDSIZE32 (Z.neg 2147483648))) .+ (@repr WORDSIZE32 (1)).


Theorem ensures_reject_impl_convert_from_unit : forall result_27 ,
 @reject_impl_convert_from_unit  = result_27 ->
 ~ (result_27 = @repr WORDSIZE32 (0)).
 Proof. Admitted.

Definition reject_impl_convert_from_parse_error   : reject_hacspec_t :=
  (- (@repr WORDSIZE32 (Z.neg 2147483648))) .+ (@repr WORDSIZE32 (2)).


Theorem ensures_reject_impl_convert_from_parse_error : forall result_27 ,
 @reject_impl_convert_from_parse_error  = result_27 ->
 ~ (result_27 = @repr WORDSIZE32 (0)).
 Proof. Admitted.

Definition reject_impl_from_log_error
  (le_28 : log_error_t)
  
  : reject_hacspec_t :=
  match le_28 with
  | Full => (- (@repr WORDSIZE32 (Z.neg 2147483648))) .+ (@repr WORDSIZE32 (3))
  | Malformed => (- (@repr WORDSIZE32 (Z.neg 2147483648))) .+ (
    @repr WORDSIZE32 (4))
  end.


Theorem ensures_reject_impl_from_log_error : forall result_27 (
  le_28 : log_error_t),
 @reject_impl_from_log_error le_28 = result_27 ->
 ~ (result_27 = @repr WORDSIZE32 (0)).
 Proof. Admitted.

Inductive new_contract_name_error_t :=
| NewContractNameErrorMissingInitPrefix : new_contract_name_error_t
| NewContractNameErrorTooLong : new_contract_name_error_t
| NewContractNameErrorContainsDot : new_contract_name_error_t
| NewContractNameErrorInvalidCharacters : new_contract_name_error_t.

Definition reject_impl_from_new_contract_name_error
  (nre_29 : new_contract_name_error_t)
  
  : reject_hacspec_t :=
  match nre_29 with
  | NewContractNameErrorMissingInitPrefix => (- (
      @repr WORDSIZE32 (Z.neg 2147483648))) .+ (@repr WORDSIZE32 (5))
  | NewContractNameErrorTooLong => (- (
      @repr WORDSIZE32 (Z.neg 2147483648))) .+ (@repr WORDSIZE32 (6))
  | NewContractNameErrorContainsDot => (- (
      @repr WORDSIZE32 (Z.neg 2147483648))) .+ (@repr WORDSIZE32 (9))
  | NewContractNameErrorInvalidCharacters => (- (
      @repr WORDSIZE32 (Z.neg 2147483648))) .+ (@repr WORDSIZE32 (10))
  end.


Theorem ensures_reject_impl_from_new_contract_name_error : forall result_27 (
  nre_29 : new_contract_name_error_t),
 @reject_impl_from_new_contract_name_error nre_29 = result_27 ->
 ~ (result_27 = @repr WORDSIZE32 (0)).
 Proof. Admitted.

Inductive new_receive_name_error_t :=
| NewReceiveNameErrorMissingDotSeparator : new_receive_name_error_t
| NewReceiveNameErrorTooLong : new_receive_name_error_t
| NewReceiveNameErrorInvalidCharacters : new_receive_name_error_t.

Definition reject_impl_from_new_receive_name_error
  (nre_30 : new_receive_name_error_t)
  
  : reject_hacspec_t :=
  match nre_30 with
  | NewReceiveNameErrorMissingDotSeparator => (- (
      @repr WORDSIZE32 (Z.neg 2147483648))) .+ (@repr WORDSIZE32 (7))
  | NewReceiveNameErrorTooLong => (- (@repr WORDSIZE32 (Z.neg 2147483648))) .+ (
    @repr WORDSIZE32 (8))
  | NewReceiveNameErrorInvalidCharacters => (- (
      @repr WORDSIZE32 (Z.neg 2147483648))) .+ (@repr WORDSIZE32 (11))
  end.


Theorem ensures_reject_impl_from_new_receive_name_error : forall result_27 (
  nre_30 : new_receive_name_error_t),
 @reject_impl_from_new_receive_name_error nre_30 = result_27 ->
 ~ (result_27 = @repr WORDSIZE32 (0)).
 Proof. Admitted.

Definition reject_impl_from_not_payable_error   : reject_hacspec_t :=
  (- (@repr WORDSIZE32 (Z.neg 2147483648))) .+ (@repr WORDSIZE32 (12)).


Theorem ensures_reject_impl_from_not_payable_error : forall result_27 ,
 @reject_impl_from_not_payable_error  = result_27 ->
 ~ (result_27 = @repr WORDSIZE32 (0)).
 Proof. Admitted.

Notation "'contract_state_hacspec_t'" := (int32) : hacspec_scope.

Inductive seek_from_hacspec_t :=
| Start : int64 -> seek_from_hacspec_t
| End : int64 -> seek_from_hacspec_t
| Current : int64 -> seek_from_hacspec_t.

Notation "'uint32_option_t'" := ((option int32)) : hacspec_scope.

Notation "'iint64_option_t'" := ((option int64)) : hacspec_scope.

Definition contract_state_impl_seek
  (current_position_31 : contract_state_hacspec_t)
  (end_32 : int32)
  (pos_33 : seek_from_hacspec_t)
  
  : (result (contract_state_hacspec_t '× int64) unit) :=
  match pos_33 with
  | Start (offset_34) => @Ok (contract_state_hacspec_t '× int64) unit ((
      @cast _ uint32 _ (offset_34),
      offset_34
    ))
  | End (delta_35) => (if ((delta_35) >=.? (@repr WORDSIZE64 (0))):bool then (
      match pub_uint32_checked_add (current_position_31) (@cast _ uint32 _ (
          delta_35)) with
      | Some (b_36) => @Ok (contract_state_hacspec_t '× int64) unit ((
          b_36,
          @cast _ uint64 _ (b_36)
        ))
      | None => @Err (contract_state_hacspec_t '× int64) unit (tt)
      end) else (match pub_int64_checked_abs (delta_35) with
      | Some (before_37) => (if ((@cast _ uint32 _ (before_37)) <=.? (
            end_32)):bool then (@Ok (contract_state_hacspec_t '× int64) unit ((
              (end_32) .- (@cast _ uint32 _ (before_37)),
              @cast _ uint64 _ ((end_32) .- (@cast _ uint32 _ (before_37)))
            ))) else (@Err (contract_state_hacspec_t '× int64) unit (tt)))
      | None => @Err (contract_state_hacspec_t '× int64) unit (tt)
      end))
  | Current (delta_38) => (if ((delta_38) >=.? (
        @repr WORDSIZE64 (0))):bool then (match pub_uint32_checked_add (
        current_position_31) (@cast _ uint32 _ (delta_38)) with
      | Some (offset_39) => @Ok (contract_state_hacspec_t '× int64) unit ((
          offset_39,
          @cast _ uint64 _ (offset_39)
        ))
      | None => @Err (contract_state_hacspec_t '× int64) unit (tt)
      end) else (match pub_int64_checked_abs (delta_38) with
      | Some (b_40) => match pub_uint32_checked_sub (current_position_31) (
        @cast _ uint32 _ (b_40)) with
      | Some (offset_41) => @Ok (contract_state_hacspec_t '× int64) unit ((
          offset_41,
          @cast _ uint64 _ (offset_41)
        ))
      | None => @Err (contract_state_hacspec_t '× int64) unit (tt)
      end
      | None => @Err (contract_state_hacspec_t '× int64) unit (tt)
      end))
  end.


Definition contract_state_impl_read_read
  (current_position_42 : contract_state_hacspec_t)
  (buf_43 : public_byte_seq)
  
  : (contract_state_hacspec_t '× uint_size) :=
  let '(buf_44, num_read_45) :=
    load_state_hacspec (buf_43) (current_position_42) in 
  ((current_position_42) .+ (num_read_45), @cast _ uint32 _ (num_read_45)).


Definition contract_state_impl_read_read_u64
  (current_position_46 : contract_state_hacspec_t)
  
  : (contract_state_hacspec_t '× (result int64 unit)) :=
  let buf_47 : seq int8 :=
    seq_new_ (default : int8) (usize 8) in 
  let '(buf_48, num_read_49) :=
    load_state_hacspec (buf_47) (current_position_46) in 
  (
    (current_position_46) .+ (num_read_49),
    (if ((num_read_49) =.? (@repr WORDSIZE32 (8))):bool then (@Ok int64 unit (
          u64_from_le_bytes (array_from_seq (8) (buf_48)))) else (
        @Err int64 unit (tt)))
  ).


Definition contract_state_impl_read_read_u32
  (current_position_50 : contract_state_hacspec_t)
  
  : (contract_state_hacspec_t '× (result int32 unit)) :=
  let buf_51 : seq int8 :=
    seq_new_ (default : int8) (usize 4) in 
  let '(buf_52, num_read_53) :=
    load_state_hacspec (buf_51) (current_position_50) in 
  (
    (current_position_50) .+ (num_read_53),
    (if ((num_read_53) =.? (@repr WORDSIZE32 (4))):bool then (@Ok int32 unit (
          u32_from_le_bytes (array_from_seq (4) (buf_52)))) else (
        @Err int32 unit (tt)))
  ).


Definition contract_state_impl_read_read_u8
  (current_position_54 : contract_state_hacspec_t)
  
  : (contract_state_hacspec_t '× (result int8 unit)) :=
  let buf_55 : seq int8 :=
    seq_new_ (default : int8) (usize 1) in 
  let '(buf_56, num_read_57) :=
    load_state_hacspec (buf_55) (current_position_54) in 
  (
    (current_position_54) .+ (num_read_57),
    (if ((num_read_57) =.? (@repr WORDSIZE32 (1))):bool then (@Ok int8 unit (
          seq_index (buf_56) (usize 0))) else (@Err int8 unit (tt)))
  ).


Definition contract_state_impl_write
  (current_position_58 : contract_state_hacspec_t)
  (buf_59 : public_byte_seq)
  
  : (result (contract_state_hacspec_t '× uint_size) unit) :=
  ifbnd option_is_none (pub_uint32_checked_add (current_position_58) (pub_u32 (
        seq_len (buf_59)))) : bool
  thenbnd (bind (@Err (contract_state_hacspec_t '× uint_size) unit (tt)) (
      fun _ => @Ok unit unit (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_60, num_bytes_61) :=
    write_state_hacspec (buf_59) (current_position_58) in 
  @Ok (contract_state_hacspec_t '× uint_size) unit ((
      (current_position_58) .+ (num_bytes_61),
      @cast _ uint32 _ (num_bytes_61)
    ))).


Definition has_contract_state_impl_for_contract_state_open
  
  
  : contract_state_hacspec_t :=
  @repr WORDSIZE32 (0).


Definition has_contract_state_impl_for_contract_state_reserve
  (len_62 : int32)
  
  : bool :=
  let cur_size_63 : int32 :=
    state_size_hacspec  in 
  (if ((cur_size_63) <.? (len_62)):bool then ((resize_state_hacspec (
          len_62)) =.? (@repr WORDSIZE32 (1))) else (true)).


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


Notation "'parameter_hacspec_t'" := (int32) : hacspec_scope.

Definition read_impl_for_parameter_read
  (current_position_67 : parameter_hacspec_t)
  (buf_68 : public_byte_seq)
  
  : (parameter_hacspec_t '× uint_size) :=
  let '(buf_69, num_read_70) :=
    get_parameter_section_hacspec (buf_68) (current_position_67) in 
  ((current_position_67) .+ (num_read_70), @cast _ uint32 _ (num_read_70)).


Notation "'attributes_cursor_hacspec_t'" := ((int32 '× int16)) : hacspec_scope.

Definition has_policy_impl_for_policy_attributes_cursor_next_item
  (policy_attribute_items_71 : attributes_cursor_hacspec_t)
  (buf_72 : public_byte_seq)
  
  : (option (attributes_cursor_hacspec_t '× (int8 '× int8))) :=
  let '(current_position_73, remaining_items_74) :=
    policy_attribute_items_71 in 
  ifbnd (remaining_items_74) =.? (@repr WORDSIZE16 0) : bool
  thenbnd (bind (@None (attributes_cursor_hacspec_t '× (int8 '× int8))) (
      fun _ => @Some unit (tt)))
  else (tt) >> (fun 'tt =>
  let '(tag_value_len_75, num_read_76) :=
    get_policy_section_hacspec (seq_new_ (default : int8) (usize 2)) (
      current_position_73) in 
  let current_position_73 :=
    (current_position_73) .+ (num_read_76) in 
  ifbnd (seq_index (tag_value_len_75) (usize 1)) >.? (@repr WORDSIZE8 31) : bool
  thenbnd (bind (@None (attributes_cursor_hacspec_t '× (int8 '× int8))) (
      fun _ => @Some unit (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_77, num_read_78) :=
    get_policy_section_hacspec (buf_72) (current_position_73) in 
  let current_position_73 :=
    (current_position_73) .+ (num_read_78) in 
  let remaining_items_74 :=
    (remaining_items_74) .- (@repr WORDSIZE16 1) in 
  @Some (attributes_cursor_hacspec_t '× (int8 '× int8)) ((
      (current_position_73, remaining_items_74),
      (
        seq_index (tag_value_len_75) (usize 0),
        seq_index (tag_value_len_75) (usize 1)
      )
    )))).


Notation "'policies_iterator_hacspec_t'" := ((int32 '× int16)) : hacspec_scope.

Notation "'policy_attributes_cursor_hacspec_t'" := ((
  int32 '×
  int64 '×
  int64 '×
  attributes_cursor_hacspec_t
)) : hacspec_scope.

Definition iterator_impl_for_policies_iterator_next
  (policies_iterator_79 : policies_iterator_hacspec_t)
  
  : (option (policies_iterator_hacspec_t '× policy_attributes_cursor_hacspec_t
    )) :=
  let '(pos_80, remaining_items_81) :=
    policies_iterator_79 in 
  ifbnd (remaining_items_81) =.? (@repr WORDSIZE16 0) : bool
  thenbnd (bind (@None (
        policies_iterator_hacspec_t '×
        policy_attributes_cursor_hacspec_t
      )) (fun _ => @Some unit (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_82, _) :=
    get_policy_section_hacspec (seq_new_ (default : int8) (((((usize 2) + (
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
    (((((pos_80) .+ (@repr WORDSIZE32 (2))) .+ (@repr WORDSIZE32 (4))) .+ (
          @repr WORDSIZE32 (8))) .+ (@repr WORDSIZE32 (8))) .+ (
      @repr WORDSIZE32 (2)) in 
  let pos_80 :=
    ((pos_80) .+ (@cast _ uint32 _ (u16_from_le_bytes (array_from_seq (2) (
              skip_part_83))))) .+ (@repr WORDSIZE32 (2)) in 
  let remaining_items_91 :=
    (remaining_items_91) .- (@repr WORDSIZE16 1) in 
  @Some (policies_iterator_hacspec_t '× policy_attributes_cursor_hacspec_t) ((
      (pos_80, remaining_items_91),
      (
        identity_provider_88,
        created_at_89,
        valid_to_90,
        (attributes_start_92, remaining_items_91)
      )
    ))).


Definition user_address_t := nseq (int8) (usize 32).

Inductive has_action_t :=
| Accept : unit -> has_action_t
| SimpleTransfer : (user_address_t '× int64) -> has_action_t
| SendRaw : (user_address_t '× string_t '× int64 '× public_byte_seq
) -> has_action_t.

Notation "'list_action_t'" := (seq has_action_t) : hacspec_scope.

Definition accept_action   : has_action_t :=
  Accept (tt).


Inductive context_t :=
| Context : (user_address_t '× user_address_t '× int64 '× int64
) -> context_t.

Definition send_wrap_hacspec
  (ca_index_93 : int64)
  (ca_subindex_94 : int64)
  (receive_name_bytes_95 : public_byte_seq)
  (amount_96 : int64)
  (param_bytes_97 : public_byte_seq)
  
  : int32 :=
  send_hacspec (ca_index_93) (ca_subindex_94) (receive_name_bytes_95) (
    amount_96) (param_bytes_97).


