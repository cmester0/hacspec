(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Notation "'reject'" := (int32) : hacspec_scope.

Definition iint32_min  : int32 :=
  (not (repr 0)) .^ (@cast _ int32 _ ((not (repr 0)) shift_right (usize 1))).

Definition reject_impl_default  : reject :=
  iint32_min .

Inductive option_reject :=
| SomeReject : reject -> option_reject
| NoneReject : option_reject.

Definition eqb_option_reject (x y : option_reject) : bool := match x with
   | SomeReject a => match y with | SomeReject b => a =.? b | _ => false end
   | NoneReject => match y with | NoneReject=> true | _ => false end
   end.

Definition eqb_leibniz_option_reject (x y : option_reject) : eqb_option_reject x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Instance eq_dec_option_reject : EqDec (option_reject) :=
Build_EqDec (option_reject) (eqb_option_reject) (eqb_leibniz_option_reject).


Definition new_reject_impl (x_0 : int32) : option_reject :=
  (if ((x_0) <.? (repr 0)):bool then (SomeReject (x_0)) else (NoneReject)).

Definition reject_impl_convert_from_unit  : reject :=
  (iint32_min ) .+ (repr 1).

Definition reject_impl_convert_from_parse_error  : reject :=
  (iint32_min ) .+ (repr 2).

Inductive log_error :=
| Full : log_error
| Malformed : log_error.

Definition eqb_log_error (x y : log_error) : bool := match x with
   | Full => match y with | Full=> true | _ => false end
   | Malformed => match y with | Malformed=> true | _ => false end
   end.

Definition eqb_leibniz_log_error (x y : log_error) : eqb_log_error x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Instance eq_dec_log_error : EqDec (log_error) :=
Build_EqDec (log_error) (eqb_log_error) (eqb_leibniz_log_error).


Definition reject_impl_from_log_error (le_1 : log_error) : reject :=
  match le_1 with
  | Full => (iint32_min ) .+ (repr 3)
  | Malformed => (iint32_min ) .+ (repr 4) end.

Inductive new_contract_name_error :=
| NewContractNameErrorMissingInitPrefix : new_contract_name_error
| NewContractNameErrorTooLong : new_contract_name_error
| NewContractNameErrorContainsDot : new_contract_name_error
| NewContractNameErrorInvalidCharacters : new_contract_name_error.

Definition eqb_new_contract_name_error (x y : new_contract_name_error) : bool := match x with
   | NewContractNameErrorMissingInitPrefix =>
       match y with
       | NewContractNameErrorMissingInitPrefix=> true
       | _ => false
       end
   | NewContractNameErrorTooLong =>
       match y with
       | NewContractNameErrorTooLong=> true
       | _ => false
       end
   | NewContractNameErrorContainsDot =>
       match y with
       | NewContractNameErrorContainsDot=> true
       | _ => false
       end
   | NewContractNameErrorInvalidCharacters =>
       match y with
       | NewContractNameErrorInvalidCharacters=> true
       | _ => false
       end
   end.

Definition eqb_leibniz_new_contract_name_error (x y : new_contract_name_error) : eqb_new_contract_name_error x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Instance eq_dec_new_contract_name_error : EqDec (new_contract_name_error) :=
Build_EqDec (new_contract_name_error) (eqb_new_contract_name_error) (eqb_leibniz_new_contract_name_error).


Definition reject_impl_from_new_contract_name_error
  (nre_2 : new_contract_name_error)
  : reject :=
  match nre_2 with
  | NewContractNameErrorMissingInitPrefix => (iint32_min ) .+ (repr 5)
  | NewContractNameErrorTooLong => (iint32_min ) .+ (repr 6)
  | NewContractNameErrorContainsDot => (iint32_min ) .+ (repr 9)
  | NewContractNameErrorInvalidCharacters => (iint32_min ) .+ (repr 10) end.

Inductive new_receive_name_error :=
| NewReceiveNameErrorMissingDotSeparator : new_receive_name_error
| NewReceiveNameErrorTooLong : new_receive_name_error
| NewReceiveNameErrorInvalidCharacters : new_receive_name_error.

Definition eqb_new_receive_name_error (x y : new_receive_name_error) : bool := match x with
   | NewReceiveNameErrorMissingDotSeparator =>
       match y with
       | NewReceiveNameErrorMissingDotSeparator=> true
       | _ => false
       end
   | NewReceiveNameErrorTooLong =>
       match y with
       | NewReceiveNameErrorTooLong=> true
       | _ => false
       end
   | NewReceiveNameErrorInvalidCharacters =>
       match y with
       | NewReceiveNameErrorInvalidCharacters=> true
       | _ => false
       end
   end.

Definition eqb_leibniz_new_receive_name_error (x y : new_receive_name_error) : eqb_new_receive_name_error x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Instance eq_dec_new_receive_name_error : EqDec (new_receive_name_error) :=
Build_EqDec (new_receive_name_error) (eqb_new_receive_name_error) (eqb_leibniz_new_receive_name_error).


Definition reject_impl_from_new_receive_name_error
  (nre_3 : new_receive_name_error)
  : reject :=
  match nre_3 with
  | NewReceiveNameErrorMissingDotSeparator => (iint32_min ) .+ (repr 7)
  | NewReceiveNameErrorTooLong => (iint32_min ) .+ (repr 8)
  | NewReceiveNameErrorInvalidCharacters => (iint32_min ) .+ (repr 11) end.

Notation "'contract_state'" := (int32) : hacspec_scope.

Inductive seek_result :=
| SeekResultOk : int64 -> seek_result
| SeekResultErr : unit -> seek_result.

Definition eqb_seek_result (x y : seek_result) : bool := match x with
   | SeekResultOk a => match y with | SeekResultOk b => a =.? b | _ => false end
   | SeekResultErr a =>
       match y with
       | SeekResultErr b => a =.? b
       | _ => false
       end
   end.

Definition eqb_leibniz_seek_result (x y : seek_result) : eqb_seek_result x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Instance eq_dec_seek_result : EqDec (seek_result) :=
Build_EqDec (seek_result) (eqb_seek_result) (eqb_leibniz_seek_result).


Inductive seek_from :=
| Start : int64 -> seek_from
| End : int64 -> seek_from
| Current : int64 -> seek_from.

Definition eqb_seek_from (x y : seek_from) : bool := match x with
   | Start a => match y with | Start b => a =.? b | _ => false end
   | End a => match y with | End b => a =.? b | _ => false end
   | Current a => match y with | Current b => a =.? b | _ => false end
   end.

Definition eqb_leibniz_seek_from (x y : seek_from) : eqb_seek_from x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Instance eq_dec_seek_from : EqDec (seek_from) :=
Build_EqDec (seek_from) (eqb_seek_from) (eqb_leibniz_seek_from).


Notation "'uint32_option'" := ((option int32)) : hacspec_scope.

Notation "'iint64_option'" := ((option int64)) : hacspec_scope.

Definition contract_state_impl_seek
  (current_position_4 : contract_state)
  (pos_5 : seek_from)
  : (contract_state × seek_result) :=
  match pos_5 with
  | Start offset_6 => (@cast _ uint32 _ (offset_6), SeekResultOk (offset_6))
  | End delta_7 => (if ((delta_7) >=.? (repr 0)):bool then (
    match pub_uint32_checked_add (current_position_4) (
      @cast _ uint32 _ (delta_7)) with
    | Some b_8 => (b_8, SeekResultOk (@cast _ uint64 _ (delta_7)))
    | None => (current_position_4, SeekResultErr (tt)) end) else (
    match pub_int64_checked_abs (delta_7) with
    | Some b_9 => (
      (repr 4) .- (@cast _ uint32 _ (b_9)),
      SeekResultOk (@cast _ uint64 _ ((repr 4) .- (@cast _ uint32 _ (b_9))))
    )
    | None => (current_position_4, SeekResultErr (tt)) end))
  | Current delta_10 => (if ((delta_10) >=.? (repr 0)):bool then (
    match pub_uint32_checked_add (current_position_4) (
      @cast _ uint32 _ (delta_10)) with
    | Some offset_11 => (offset_11, SeekResultOk (@cast _ uint64 _ (offset_11)))
    | None => (current_position_4, SeekResultErr (tt)) end) else (
    match pub_int64_checked_abs (delta_10) with
    | Some b_12 => match pub_uint32_checked_sub (current_position_4) (
      @cast _ uint32 _ (b_12)) with
    | Some offset_13 => (offset_13, SeekResultOk (@cast _ uint64 _ (offset_13)))
    | None => (current_position_4, SeekResultErr (tt)) end
    | None => (current_position_4, SeekResultErr (tt)) end)) end.

Definition contract_state_impl_read_read
  (current_position_14 : contract_state)
  (num_read_15 : int32)
  : (contract_state × uint_size) :=
  ((current_position_14) .+ (num_read_15), @cast _ uint32 _ (num_read_15)).

Definition contract_state_impl_read_read_u64
  (current_position_16 : contract_state)
  (num_read_17 : int32)
  : (contract_state × bool) :=
  ((current_position_16) .+ (num_read_17), (num_read_17) =.? (repr 8)).

Definition contract_state_impl_read_read_u32
  (current_position_18 : contract_state)
  (num_read_19 : int32)
  : (contract_state × bool) :=
  ((current_position_18) .+ (num_read_19), (num_read_19) =.? (repr 4)).

Definition contract_state_impl_read_read_u8
  (current_position_20 : contract_state)
  (num_read_21 : int32)
  : (contract_state × bool) :=
  ((current_position_20) .+ (num_read_21), (num_read_21) =.? (repr 1)).

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
  repr 0.

Definition has_contract_state_impl_for_contract_state_reserve_0
  (len_26 : int32)
  (cur_size_27 : int32)
  : bool :=
  (cur_size_27) <.? (len_26).

Definition has_contract_state_impl_for_contract_state_reserve_1
  (res_28 : int32)
  : bool :=
  (res_28) =.? (repr 1).

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
  (remaining_items_36) =.? (repr 0).

Definition has_policy_impl_for_policy_attributes_cursor_next_tag_invalid
  (policy_attribute_items_37 : attributes_cursor)
  (tag_value_len_1_38 : int8)
  (num_read_39 : int32)
  : (attributes_cursor × bool) :=
  let '(current_position_40, remaining_items_41) :=
    policy_attribute_items_37 in 
  let policy_attribute_items_42 :=
    ((current_position_40) .+ (num_read_39), remaining_items_41) in 
  (policy_attribute_items_42, (tag_value_len_1_38) >.? (repr 31)).

Definition has_policy_impl_for_policy_attributes_cursor_next
  (policy_attribute_items_43 : attributes_cursor)
  (num_read_44 : int32)
  : attributes_cursor :=
  let '(current_position_45, remaining_items_46) :=
    policy_attribute_items_43 in 
  ((current_position_45) .+ (num_read_44), (remaining_items_46) .- (repr 1)).

