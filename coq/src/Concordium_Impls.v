(* [[file:concordium.org::*Coq code][Coq code:1]] *)
(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
(* Coq code:1 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:25]] *)
Require Import Hacspec.Lib.
(* Coq code:25 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:26]] *)
Require Import Hacspec.Concordium_Prims.
(* Coq code:26 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:27]] *)
Require Import Hacspec.Concordium_Types.
(* Coq code:27 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:28]] *)
Notation "'reject_hacspec_t'" := (int32) : hacspec_scope.
(* Coq code:28 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:29]] *)
Definition reject_impl_deafult  : reject_hacspec_t :=
  min_v.
(* Coq code:29 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:30]] *)
Definition new_reject_impl (x_25 : int32) : (option int32) :=
  (if ((x_25) <.? (@repr WORDSIZE32 0)):bool then (@Some int32 (x_25)) else (
      @None int32)).
(* Coq code:30 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:31]] *)
Definition reject_impl_convert_from_unit  : reject_hacspec_t :=
  (min_v) .+ (@repr WORDSIZE32 1).

Theorem ensures_reject_impl_convert_from_unit : forall result_26 ,
 @reject_impl_convert_from_unit  = result_26 ->
 ~ (result_26 = @repr WORDSIZE32 0).
 Proof. Admitted.
(* Coq code:31 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:32]] *)
Definition reject_impl_convert_from_parse_error  : reject_hacspec_t :=
  (min_v) .+ (@repr WORDSIZE32 2).

Theorem ensures_reject_impl_convert_from_parse_error : forall result_26 ,
 @reject_impl_convert_from_parse_error  = result_26 ->
 ~ (result_26 = @repr WORDSIZE32 0).
 Proof. Admitted.
(* Coq code:32 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:33]] *)
Definition reject_impl_from_log_error
  (le_27 : log_error_t)
  : reject_hacspec_t :=
  match le_27 with
  | Full => (min_v) .+ (@repr WORDSIZE32 3)
  | Malformed => (min_v) .+ (@repr WORDSIZE32 4)
  end.

Theorem ensures_reject_impl_from_log_error : forall result_26 (
  le_27 : log_error_t),
 @reject_impl_from_log_error le_27 = result_26 ->
 ~ (result_26 = @repr WORDSIZE32 0).
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
  (nre_28 : new_contract_name_error_t)
  : reject_hacspec_t :=
  match nre_28 with
  | NewContractNameErrorMissingInitPrefix => (min_v) .+ (@repr WORDSIZE32 5)
  | NewContractNameErrorTooLong => (min_v) .+ (@repr WORDSIZE32 6)
  | NewContractNameErrorContainsDot => (min_v) .+ (@repr WORDSIZE32 9)
  | NewContractNameErrorInvalidCharacters => (min_v) .+ (@repr WORDSIZE32 10)
  end.

Theorem ensures_reject_impl_from_new_contract_name_error : forall result_26 (
  nre_28 : new_contract_name_error_t),
 @reject_impl_from_new_contract_name_error nre_28 = result_26 ->
 ~ (result_26 = @repr WORDSIZE32 0).
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
  (nre_29 : new_receive_name_error_t)
  : reject_hacspec_t :=
  match nre_29 with
  | NewReceiveNameErrorMissingDotSeparator => (min_v) .+ (@repr WORDSIZE32 7)
  | NewReceiveNameErrorTooLong => (min_v) .+ (@repr WORDSIZE32 8)
  | NewReceiveNameErrorInvalidCharacters => (min_v) .+ (@repr WORDSIZE32 11)
  end.

Theorem ensures_reject_impl_from_new_receive_name_error : forall result_26 (
  nre_29 : new_receive_name_error_t),
 @reject_impl_from_new_receive_name_error nre_29 = result_26 ->
 ~ (result_26 = @repr WORDSIZE32 0).
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
  (current_position_30 : contract_state_hacspec_t)
  (pos_31 : seek_from_hacspec_t)
  : (result (contract_state_hacspec_t × int64) unit) :=
  match pos_31 with
  | Start offset_32 => @Ok (contract_state_hacspec_t × int64) unit ((
      @cast _ uint32 _ (offset_32),
      offset_32
    ))
  | End delta_33 => (if ((delta_33) >=.? (@repr WORDSIZE64 0)):bool then (
      match pub_uint32_checked_add (current_position_30) (@cast _ uint32 _ (
          delta_33)) with
      | Some b_34 => @Ok (contract_state_hacspec_t × int64) unit ((
          b_34,
          @cast _ uint64 _ (delta_33)
        ))
      | None => @Err (contract_state_hacspec_t × int64) unit (tt)
      end) else (match pub_int64_checked_abs (delta_33) with
      | Some b_35 => @Ok (contract_state_hacspec_t × int64) unit ((
          (@repr WORDSIZE32 4) .- (@cast _ uint32 _ (b_35)),
          @cast _ uint64 _ ((@repr WORDSIZE32 4) .- (@cast _ uint32 _ (b_35)))
        ))
      | None => @Err (contract_state_hacspec_t × int64) unit (tt)
      end))
  | Current delta_36 => (if ((delta_36) >=.? (@repr WORDSIZE64 0)):bool then (
      match pub_uint32_checked_add (current_position_30) (@cast _ uint32 _ (
          delta_36)) with
      | Some offset_37 => @Ok (contract_state_hacspec_t × int64) unit ((
          offset_37,
          @cast _ uint64 _ (offset_37)
        ))
      | None => @Err (contract_state_hacspec_t × int64) unit (tt)
      end) else (match pub_int64_checked_abs (delta_36) with
      | Some b_38 => match pub_uint32_checked_sub (current_position_30) (
        @cast _ uint32 _ (b_38)) with
      | Some offset_39 => @Ok (contract_state_hacspec_t × int64) unit ((
          offset_39,
          @cast _ uint64 _ (offset_39)
        ))
      | None => @Err (contract_state_hacspec_t × int64) unit (tt)
      end
      | None => @Err (contract_state_hacspec_t × int64) unit (tt)
      end))
  end.
(* Coq code:42 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:43]] *)
Definition contract_state_impl_read_read
  (current_position_40 : contract_state_hacspec_t)
  (buf_41 : public_byte_seq)
  : (contract_state_hacspec_t × uint_size) :=
  let '(buf_42, num_read_43) :=
    load_state_hacspec (buf_41) (current_position_40) in 
  ((current_position_40) .+ (num_read_43), @cast _ uint32 _ (num_read_43)).
(* Coq code:43 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:44]] *)
Definition contract_state_impl_read_read_u64
  (current_position_44 : contract_state_hacspec_t)
  : (contract_state_hacspec_t × int64) :=
  let buf_45 : seq int8 :=
    seq_new_ (default) (usize 8) in 
  let '(buf_46, num_read_47) :=
    load_state_hacspec (buf_45) (current_position_44) in 
  (
    (current_position_44) .+ (num_read_47),
    u64_from_le_bytes (array_from_seq (8) (buf_46))
  ).
(* Coq code:44 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:45]] *)
Definition contract_state_impl_read_read_u32
  (current_position_48 : contract_state_hacspec_t)
  : (contract_state_hacspec_t × int32) :=
  let buf_49 : seq int8 :=
    seq_new_ (default) (usize 4) in 
  let '(buf_50, num_read_51) :=
    load_state_hacspec (buf_49) (current_position_48) in 
  (
    (current_position_48) .+ (num_read_51),
    u32_from_le_bytes (array_from_seq (4) (buf_50))
  ).
(* Coq code:45 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:46]] *)
Definition contract_state_impl_read_read_u8
  (current_position_52 : contract_state_hacspec_t)
  : (contract_state_hacspec_t × int8) :=
  let buf_53 : seq int8 :=
    seq_new_ (default) (usize 1) in 
  let '(buf_54, num_read_55) :=
    load_state_hacspec (buf_53) (current_position_52) in 
  ((current_position_52) .+ (num_read_55), seq_index (buf_54) (usize 0)).
(* Coq code:46 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:47]] *)
Definition contract_state_impl_write
  (current_position_56 : contract_state_hacspec_t)
  (buf_57 : public_byte_seq)
  : (result (contract_state_hacspec_t × uint_size) unit) :=
  ifbnd option_is_none (pub_uint32_checked_add (current_position_56) (pub_u32 (
        seq_len (buf_57)))) : bool
  thenbnd (bind (@Err (contract_state_hacspec_t × uint_size) unit (tt)) (
      fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_58, num_bytes_59) :=
    write_state_hacspec (buf_57) (current_position_56) in 
  @Ok (contract_state_hacspec_t × uint_size) unit ((
      (current_position_56) .+ (num_bytes_59),
      @cast _ uint32 _ (num_bytes_59)
    ))).
(* Coq code:47 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:48]] *)
Definition has_contract_state_impl_for_contract_state_open
  
  : contract_state_hacspec_t :=
  @repr WORDSIZE32 0.
(* Coq code:48 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:49]] *)
Definition has_contract_state_impl_for_contract_state_reserve
  (len_60 : int32)
  : bool :=
  let cur_size_61 : int32 :=
    state_size_hacspec  in 
  (if ((cur_size_61) <.? (len_60)):bool then ((resize_state_hacspec (
          len_60)) =.? (@repr WORDSIZE32 1)) else (true)).
(* Coq code:49 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:50]] *)
Definition has_contract_state_impl_for_contract_state_truncate
  (current_position_62 : contract_state_hacspec_t)
  (cur_size_63 : int32)
  (new_size_64 : int32)
  : contract_state_hacspec_t :=
  let 'tt :=
    if (cur_size_63) >.? (new_size_64):bool then (let _ : int32 :=
        resize_state_hacspec (new_size_64) in 
      tt) else (tt) in 
  (if ((new_size_64) <.? (current_position_62)):bool then (new_size_64) else (
      current_position_62)).
(* Coq code:50 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:51]] *)
Notation "'parameter_hacspec_t'" := (int32) : hacspec_scope.
(* Coq code:51 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:52]] *)
Definition read_impl_for_parameter_read
  (current_position_65 : parameter_hacspec_t)
  (buf_66 : public_byte_seq)
  : (parameter_hacspec_t × uint_size) :=
  let '(buf_67, num_read_68) :=
    get_parameter_section_hacspec (buf_66) (current_position_65) in 
  ((current_position_65) .+ (num_read_68), @cast _ uint32 _ (num_read_68)).
(* Coq code:52 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:53]] *)
Notation "'attributes_cursor_hacspec_t'" := ((int32 × int16)) : hacspec_scope.
(* Coq code:53 ends here *)

(* [[file:concordium.org::*Coq code][Coq code:54]] *)
Definition has_policy_impl_for_policy_attributes_cursor_next_item
  (policy_attribute_items_69 : attributes_cursor_hacspec_t)
  (buf_70 : public_byte_seq)
  : (option (attributes_cursor_hacspec_t × (int8 × int8))) :=
  let '(current_position_71, remaining_items_72) :=
    policy_attribute_items_69 in 
  ifbnd (remaining_items_72) =.? (@repr WORDSIZE16 0) : bool
  thenbnd (bind (@None (attributes_cursor_hacspec_t × (int8 × int8))) (
      fun _ =>  Some (tt)))
  else (tt) >> (fun 'tt =>
  let '(tag_value_len_73, num_read_74) :=
    get_policy_section_hacspec (seq_new_ (default) (usize 2)) (
      current_position_71) in 
  let current_position_71 :=
    (current_position_71) .+ (num_read_74) in 
  ifbnd (seq_index (tag_value_len_73) (usize 1)) >.? (@repr WORDSIZE8 31) : bool
  thenbnd (bind (@None (attributes_cursor_hacspec_t × (int8 × int8))) (
      fun _ =>  Some (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_75, num_read_76) :=
    get_policy_section_hacspec (buf_70) (current_position_71) in 
  let current_position_71 :=
    (current_position_71) .+ (num_read_76) in 
  let remaining_items_72 :=
    (remaining_items_72) .- (@repr WORDSIZE16 1) in 
  @Some (attributes_cursor_hacspec_t × (int8 × int8)) ((
      (current_position_71, remaining_items_72),
      (
        seq_index (tag_value_len_73) (usize 0),
        seq_index (tag_value_len_73) (usize 1)
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
  (policies_iterator_77 : policies_iterator_hacspec_t)
  : (option (policies_iterator_hacspec_t × policy_attributes_cursor_hacspec_t
    )) :=
  let '(pos_78, remaining_items_79) :=
    policies_iterator_77 in 
  ifbnd (remaining_items_79) =.? (@repr WORDSIZE16 0) : bool
  thenbnd (bind (@None (
        policies_iterator_hacspec_t ×
        policy_attributes_cursor_hacspec_t
      )) (fun _ =>  Some (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_80, _) :=
    get_policy_section_hacspec (seq_new_ (default) (((((usize 2) + (
                usize 4)) + (usize 8)) + (usize 8)) + (usize 2))) (pos_78) in 
  let skip_part_81 : public_byte_seq :=
    seq_slice_range (buf_80) ((usize 0, usize 2)) in 
  let ip_part_82 : public_byte_seq :=
    seq_slice_range (buf_80) ((usize 2, (usize 2) + (usize 4))) in 
  let created_at_part_83 : public_byte_seq :=
    seq_slice_range (buf_80) ((
        (usize 2) + (usize 4),
        ((usize 2) + (usize 4)) + (usize 8)
      )) in 
  let valid_to_part_84 : public_byte_seq :=
    seq_slice_range (buf_80) ((
        ((usize 2) + (usize 4)) + (usize 8),
        (((usize 2) + (usize 4)) + (usize 8)) + (usize 8)
      )) in 
  let len_part_85 : public_byte_seq :=
    seq_slice_range (buf_80) ((
        (((usize 2) + (usize 4)) + (usize 8)) + (usize 8),
        ((((usize 2) + (usize 4)) + (usize 8)) + (usize 8)) + (usize 2)
      )) in 
  let identity_provider_86 : int32 :=
    u32_from_le_bytes (array_from_seq (4) (ip_part_82)) in 
  let created_at_87 : int64 :=
    u64_from_le_bytes (array_from_seq (8) (created_at_part_83)) in 
  let valid_to_88 : int64 :=
    u64_from_le_bytes (array_from_seq (8) (valid_to_part_84)) in 
  let remaining_items_89 : int16 :=
    u16_from_le_bytes (array_from_seq (2) (len_part_85)) in 
  let attributes_start_90 : int32 :=
    (((((pos_78) .+ (@repr WORDSIZE32 2)) .+ (@repr WORDSIZE32 4)) .+ (
          @repr WORDSIZE32 8)) .+ (@repr WORDSIZE32 8)) .+ (
      @repr WORDSIZE32 2) in 
  let pos_78 :=
    ((pos_78) .+ (@cast _ uint32 _ (u16_from_le_bytes (array_from_seq (2) (
              skip_part_81))))) .+ (@repr WORDSIZE32 2) in 
  let remaining_items_89 :=
    (remaining_items_89) .- (@repr WORDSIZE16 1) in 
  @Some (policies_iterator_hacspec_t × policy_attributes_cursor_hacspec_t) ((
      (pos_78, remaining_items_89),
      (
        identity_provider_86,
        created_at_87,
        valid_to_88,
        (attributes_start_90, remaining_items_89)
      )
    ))).
(* Coq code:57 ends here *)

