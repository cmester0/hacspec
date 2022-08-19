(** This file was automatically generated using Hacspec **)

Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.

(* Require Import ConCertLib. *)
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import Automation.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ContractCommon.
From Coq Require Import Morphisms ZArith Basics.
Open Scope Z.
Set Nonrecursive Elimination Schemes.
Require Import Hacspec_Lib.
Export Hacspec_Lib.

Require Import Concordium_Prims.
Export Concordium_Prims.

Require Import Concordium_Types.
Export Concordium_Types.

Require Import Concordium_Traits.
Export Concordium_Traits.

Notation "'reject_hacspec_t'" := (int32) : hacspec_scope.

Definition reject_impl_deafult : reject_hacspec_t :=
  min_v.


Definition new_reject_impl (x_25 : int32): (option int32) :=
  (if ((x_25) <.? (@repr WORDSIZE32 0)):bool then (@Some int32 (x_25)) else (
      @None int32)).


Definition reject_impl_convert_from_unit : reject_hacspec_t :=
  (min_v) .+ (@repr WORDSIZE32 1).


Theorem ensures_reject_impl_convert_from_unit : forall result_26 ,
 @reject_impl_convert_from_unit  = result_26 ->
 ~ ((result_26) =.? (@repr WORDSIZE32 0)).
 Proof. Admitted.

Definition reject_impl_convert_from_parse_error : reject_hacspec_t :=
  (min_v) .+ (@repr WORDSIZE32 2).


Theorem ensures_reject_impl_convert_from_parse_error : forall result_26 ,
 @reject_impl_convert_from_parse_error  = result_26 ->
 ~ ((result_26) =.? (@repr WORDSIZE32 0)).
 Proof. Admitted.

Definition reject_impl_from_log_error (le_27 : log_error_t): reject_hacspec_t :=
  match le_27 with
  | Full => (min_v) .+ (@repr WORDSIZE32 3)
  | Malformed => (min_v) .+ (@repr WORDSIZE32 4)
  end.


Theorem ensures_reject_impl_from_log_error : forall result_26 (
  le_27 : log_error_t),
 @reject_impl_from_log_error le_27 = result_26 ->
 ~ ((result_26) =.? (@repr WORDSIZE32 0)).
 Proof. Admitted.

Inductive new_contract_name_error_t :=
| NewContractNameErrorMissingInitPrefix : new_contract_name_error_t
| NewContractNameErrorTooLong : new_contract_name_error_t
| NewContractNameErrorContainsDot : new_contract_name_error_t
| NewContractNameErrorInvalidCharacters : new_contract_name_error_t.
(* Global Instance serializable_new_contract_name_error_t : Serializable new_contract_name_error_t := *)
(*   Derive Serializable new_contract_name_error_t_rect<NewContractNameErrorMissingInitPrefix,NewContractNameErrorTooLong,NewContractNameErrorContainsDot,NewContractNameErrorInvalidCharacters>. *)

Definition reject_impl_from_new_contract_name_error
  (nre_28 : new_contract_name_error_t): reject_hacspec_t :=
  match nre_28 with
  | NewContractNameErrorMissingInitPrefix => (min_v) .+ (@repr WORDSIZE32 5)
  | NewContractNameErrorTooLong => (min_v) .+ (@repr WORDSIZE32 6)
  | NewContractNameErrorContainsDot => (min_v) .+ (@repr WORDSIZE32 9)
  | NewContractNameErrorInvalidCharacters => (min_v) .+ (@repr WORDSIZE32 10)
  end.


Theorem ensures_reject_impl_from_new_contract_name_error : forall result_26 (
  nre_28 : new_contract_name_error_t),
 @reject_impl_from_new_contract_name_error nre_28 = result_26 ->
 ~ ((result_26) =.? (@repr WORDSIZE32 0)).
 Proof. Admitted.

Inductive new_receive_name_error_t :=
| NewReceiveNameErrorMissingDotSeparator : new_receive_name_error_t
| NewReceiveNameErrorTooLong : new_receive_name_error_t
| NewReceiveNameErrorInvalidCharacters : new_receive_name_error_t.
(* Global Instance serializable_new_receive_name_error_t : Serializable new_receive_name_error_t := *)
(*   Derive Serializable new_receive_name_error_t_rect<NewReceiveNameErrorMissingDotSeparator,NewReceiveNameErrorTooLong,NewReceiveNameErrorInvalidCharacters>. *)

Definition reject_impl_from_new_receive_name_error
  (nre_29 : new_receive_name_error_t): reject_hacspec_t :=
  match nre_29 with
  | NewReceiveNameErrorMissingDotSeparator => (min_v) .+ (@repr WORDSIZE32 7)
  | NewReceiveNameErrorTooLong => (min_v) .+ (@repr WORDSIZE32 8)
  | NewReceiveNameErrorInvalidCharacters => (min_v) .+ (@repr WORDSIZE32 11)
  end.


Theorem ensures_reject_impl_from_new_receive_name_error : forall result_26 (
  nre_29 : new_receive_name_error_t),
 @reject_impl_from_new_receive_name_error nre_29 = result_26 ->
 ~ ((result_26) =.? (@repr WORDSIZE32 0)).
 Proof. Admitted.

Definition reject_impl_from_not_payable_error : reject_hacspec_t :=
  (min_v) .+ (@repr WORDSIZE32 12).


Theorem ensures_reject_impl_from_not_payable_error : forall result_26 ,
 @reject_impl_from_not_payable_error  = result_26 ->
 ~ ((result_26) =.? (@repr WORDSIZE32 0)).
 Proof. Admitted.

Notation "'contract_state_hacspec_t'" := (int32) : hacspec_scope.

Inductive seek_from_hacspec_t :=
| Start : int64 -> seek_from_hacspec_t
| End : int64 -> seek_from_hacspec_t
| Current : int64 -> seek_from_hacspec_t.
(* Global Instance serializable_seek_from_hacspec_t : Serializable seek_from_hacspec_t := *)
(*   Derive Serializable seek_from_hacspec_t_rect<Start,End,Current>. *)

Notation "'uint32_option_t'" := ((option int32)) : hacspec_scope.

Notation "'iint64_option_t'" := ((option int64)) : hacspec_scope.

Definition contract_state_impl_seek
  (current_position_30 : contract_state_hacspec_t)
  (end_31 : int32)
  (pos_32 : seek_from_hacspec_t): (result (contract_state_hacspec_t ∏ int64
    ) unit) :=
  match pos_32 with
  | Start offset_33 => @Ok (contract_state_hacspec_t ∏ int64) unit ((
      @cast _ uint32 _ (offset_33),
      offset_33
    ))
  | End delta_34 => (if ((delta_34) >=.? (@repr WORDSIZE64 0)):bool then (
      match pub_uint32_checked_add (current_position_30) (@cast _ uint32 _ (
          delta_34)) with
      | Some b_35 => @Ok (contract_state_hacspec_t ∏ int64) unit ((
          b_35,
          @cast _ uint64 _ (b_35)
        ))
      | None => @Err (contract_state_hacspec_t ∏ int64) unit (tt)
      end) else (match pub_int64_checked_abs (delta_34) with
      | Some before_36 => (if ((@cast _ uint32 _ (before_36)) <=.? (
            end_31)):bool then (@Ok (contract_state_hacspec_t ∏ int64) unit ((
              (end_31) .- (@cast _ uint32 _ (before_36)),
              @cast _ uint64 _ ((end_31) .- (@cast _ uint32 _ (before_36)))
            ))) else (@Err (contract_state_hacspec_t ∏ int64) unit (tt)))
      | None => @Err (contract_state_hacspec_t ∏ int64) unit (tt)
      end))
  | Current delta_37 => (if ((delta_37) >=.? (@repr WORDSIZE64 0)):bool then (
      match pub_uint32_checked_add (current_position_30) (@cast _ uint32 _ (
          delta_37)) with
      | Some offset_38 => @Ok (contract_state_hacspec_t ∏ int64) unit ((
          offset_38,
          @cast _ uint64 _ (offset_38)
        ))
      | None => @Err (contract_state_hacspec_t ∏ int64) unit (tt)
      end) else (match pub_int64_checked_abs (delta_37) with
      | Some b_39 => match pub_uint32_checked_sub (current_position_30) (
        @cast _ uint32 _ (b_39)) with
      | Some offset_40 => @Ok (contract_state_hacspec_t ∏ int64) unit ((
          offset_40,
          @cast _ uint64 _ (offset_40)
        ))
      | None => @Err (contract_state_hacspec_t ∏ int64) unit (tt)
      end
      | None => @Err (contract_state_hacspec_t ∏ int64) unit (tt)
      end))
  end.


Definition contract_state_impl_read_read
  (current_position_41 : contract_state_hacspec_t)
  (buf_42 : public_byte_seq): (contract_state_hacspec_t ∏ uint_size) :=
  let '(buf_43, num_read_44) :=
    load_state_hacspec (buf_42) (current_position_41) in 
  ((current_position_41) .+ (num_read_44), @cast _ uint32 _ (num_read_44)).


Definition contract_state_impl_read_read_u64
  (current_position_45 : contract_state_hacspec_t): (
    contract_state_hacspec_t ∏
    (result int64 unit)
  ) :=
  let buf_46 : seq int8 :=
    seq_new_ (default) (usize 8) in 
  let '(buf_47, num_read_48) :=
    load_state_hacspec (buf_46) (current_position_45) in 
  (
    (current_position_45) .+ (num_read_48),
    (if ((num_read_48) =.? (@repr WORDSIZE32 8)):bool then (@Ok int64 unit (
          u64_from_le_bytes (array_from_seq (8) (buf_47)))) else (
        @Err int64 unit (tt)))
  ).


Definition contract_state_impl_read_read_u32
  (current_position_49 : contract_state_hacspec_t): (
    contract_state_hacspec_t ∏
    (result int32 unit)
  ) :=
  let buf_50 : seq int8 :=
    seq_new_ (default) (usize 4) in 
  let '(buf_51, num_read_52) :=
    load_state_hacspec (buf_50) (current_position_49) in 
  (
    (current_position_49) .+ (num_read_52),
    (if ((num_read_52) =.? (@repr WORDSIZE32 4)):bool then (@Ok int32 unit (
          u32_from_le_bytes (array_from_seq (4) (buf_51)))) else (
        @Err int32 unit (tt)))
  ).


Definition contract_state_impl_read_read_u8
  (current_position_53 : contract_state_hacspec_t): (
    contract_state_hacspec_t ∏
    (result int8 unit)
  ) :=
  let buf_54 : seq int8 :=
    seq_new_ (default) (usize 1) in 
  let '(buf_55, num_read_56) :=
    load_state_hacspec (buf_54) (current_position_53) in 
  (
    (current_position_53) .+ (num_read_56),
    (if ((num_read_56) =.? (@repr WORDSIZE32 1)):bool then (@Ok int8 unit (
          seq_index (buf_55) (usize 0))) else (@Err int8 unit (tt)))
  ).


Definition contract_state_impl_write
  (current_position_57 : contract_state_hacspec_t)
  (buf_58 : public_byte_seq): (result (contract_state_hacspec_t ∏ uint_size
    ) unit) :=
  ifbnd option_is_none (pub_uint32_checked_add (current_position_57) (pub_u32 (
        seq_len (buf_58)))) : bool
  thenbnd (bind (@Err (contract_state_hacspec_t ∏ uint_size) unit (tt)) (
      fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_59, num_bytes_60) :=
    write_state_hacspec (buf_58) (current_position_57) in 
  @Ok (contract_state_hacspec_t ∏ uint_size) unit ((
      (current_position_57) .+ (num_bytes_60),
      @cast _ uint32 _ (num_bytes_60)
    ))).


Definition has_contract_state_impl_for_contract_state_open
  : contract_state_hacspec_t :=
  @repr WORDSIZE32 0.


Definition has_contract_state_impl_for_contract_state_reserve
  (len_61 : int32): bool :=
  let cur_size_62 : int32 :=
    state_size_hacspec  in 
  (if ((cur_size_62) <.? (len_61)):bool then ((resize_state_hacspec (
          len_61)) =.? (@repr WORDSIZE32 1)) else (true)).


Definition has_contract_state_impl_for_contract_state_truncate
  (current_position_63 : contract_state_hacspec_t)
  (cur_size_64 : int32)
  (new_size_65 : int32): contract_state_hacspec_t :=
  let 'tt :=
    if (cur_size_64) >.? (new_size_65):bool then (let _ : int32 :=
        resize_state_hacspec (new_size_65) in 
      tt) else (tt) in 
  (if ((new_size_65) <.? (current_position_63)):bool then (new_size_65) else (
      current_position_63)).


Notation "'parameter_hacspec_t'" := (int32) : hacspec_scope.

Definition read_impl_for_parameter_read
  (current_position_66 : parameter_hacspec_t)
  (buf_67 : public_byte_seq): (parameter_hacspec_t ∏ uint_size) :=
  let '(buf_68, num_read_69) :=
    get_parameter_section_hacspec (buf_67) (current_position_66) in 
  ((current_position_66) .+ (num_read_69), @cast _ uint32 _ (num_read_69)).


Notation "'attributes_cursor_hacspec_t'" := ((int32 ∏ int16)) : hacspec_scope.

Definition has_policy_impl_for_policy_attributes_cursor_next_item
  (policy_attribute_items_70 : attributes_cursor_hacspec_t)
  (buf_71 : public_byte_seq): (option (
      attributes_cursor_hacspec_t ∏
      (int8 ∏ int8)
    )) :=
  let '(current_position_72, remaining_items_73) :=
    policy_attribute_items_70 in 
  ifbnd (remaining_items_73) =.? (@repr WORDSIZE16 0) : bool
  thenbnd (bind (@None (attributes_cursor_hacspec_t ∏ (int8 ∏ int8))) (
      fun _ =>  Some (tt)))
  else (tt) >> (fun 'tt =>
  let '(tag_value_len_74, num_read_75) :=
    get_policy_section_hacspec (seq_new_ (default) (usize 2)) (
      current_position_72) in 
  let current_position_72 :=
    (current_position_72) .+ (num_read_75) in 
  ifbnd (seq_index (tag_value_len_74) (usize 1)) >.? (@repr WORDSIZE8 31) : bool
  thenbnd (bind (@None (attributes_cursor_hacspec_t ∏ (int8 ∏ int8))) (
      fun _ =>  Some (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_76, num_read_77) :=
    get_policy_section_hacspec (buf_71) (current_position_72) in 
  let current_position_72 :=
    (current_position_72) .+ (num_read_77) in 
  let remaining_items_73 :=
    (remaining_items_73) .- (@repr WORDSIZE16 1) in 
  @Some (attributes_cursor_hacspec_t ∏ (int8 ∏ int8)) ((
      (current_position_72, remaining_items_73),
      (
        seq_index (tag_value_len_74) (usize 0),
        seq_index (tag_value_len_74) (usize 1)
      )
    )))).


Notation "'policies_iterator_hacspec_t'" := ((int32 ∏ int16)) : hacspec_scope.

Notation "'policy_attributes_cursor_hacspec_t'" := ((
  int32 ∏
  int64 ∏
  int64 ∏
  attributes_cursor_hacspec_t
)) : hacspec_scope.

Definition iterator_impl_for_policies_iterator_next
  (policies_iterator_78 : policies_iterator_hacspec_t): (option (
      policies_iterator_hacspec_t ∏
      policy_attributes_cursor_hacspec_t
    )) :=
  let '(pos_79, remaining_items_80) :=
    policies_iterator_78 in 
  ifbnd (remaining_items_80) =.? (@repr WORDSIZE16 0) : bool
  thenbnd (bind (@None (
        policies_iterator_hacspec_t ∏
        policy_attributes_cursor_hacspec_t
      )) (fun _ =>  Some (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_81, _) :=
    get_policy_section_hacspec (seq_new_ (default) (((((usize 2) + (
                usize 4)) + (usize 8)) + (usize 8)) + (usize 2))) (pos_79) in 
  let skip_part_82 : public_byte_seq :=
    seq_slice_range (buf_81) ((usize 0, usize 2)) in 
  let ip_part_83 : public_byte_seq :=
    seq_slice_range (buf_81) ((usize 2, (usize 2) + (usize 4))) in 
  let created_at_part_84 : public_byte_seq :=
    seq_slice_range (buf_81) ((
        (usize 2) + (usize 4),
        ((usize 2) + (usize 4)) + (usize 8)
      )) in 
  let valid_to_part_85 : public_byte_seq :=
    seq_slice_range (buf_81) ((
        ((usize 2) + (usize 4)) + (usize 8),
        (((usize 2) + (usize 4)) + (usize 8)) + (usize 8)
      )) in 
  let len_part_86 : public_byte_seq :=
    seq_slice_range (buf_81) ((
        (((usize 2) + (usize 4)) + (usize 8)) + (usize 8),
        ((((usize 2) + (usize 4)) + (usize 8)) + (usize 8)) + (usize 2)
      )) in 
  let identity_provider_87 : int32 :=
    u32_from_le_bytes (array_from_seq (4) (ip_part_83)) in 
  let created_at_88 : int64 :=
    u64_from_le_bytes (array_from_seq (8) (created_at_part_84)) in 
  let valid_to_89 : int64 :=
    u64_from_le_bytes (array_from_seq (8) (valid_to_part_85)) in 
  let remaining_items_90 : int16 :=
    u16_from_le_bytes (array_from_seq (2) (len_part_86)) in 
  let attributes_start_91 : int32 :=
    (((((pos_79) .+ (@repr WORDSIZE32 2)) .+ (@repr WORDSIZE32 4)) .+ (
          @repr WORDSIZE32 8)) .+ (@repr WORDSIZE32 8)) .+ (
      @repr WORDSIZE32 2) in 
  let pos_79 :=
    ((pos_79) .+ (@cast _ uint32 _ (u16_from_le_bytes (array_from_seq (2) (
              skip_part_82))))) .+ (@repr WORDSIZE32 2) in 
  let remaining_items_90 :=
    (remaining_items_90) .- (@repr WORDSIZE16 1) in 
  @Some (policies_iterator_hacspec_t ∏ policy_attributes_cursor_hacspec_t) ((
      (pos_79, remaining_items_90),
      (
        identity_provider_87,
        created_at_88,
        valid_to_89,
        (attributes_start_91, remaining_items_90)
      )
    ))).


Definition user_address_t := nseq (int8) (usize 32).

Inductive has_action_t :=
| Accept : unit -> has_action_t
| SimpleTransfer : (user_address_t ∏ int64) -> has_action_t.
(* Global Instance serializable_has_action_t : Serializable has_action_t := *)
(*   Derive Serializable has_action_t_rect<Accept,SimpleTransfer>. *)
Instance default_has_action_t : Default has_action_t := {| default := Accept tt |}.

Notation "'list_action_t'" := (seq has_action_t) : hacspec_scope.

Definition accept_action : has_action_t :=
  Accept (tt).


