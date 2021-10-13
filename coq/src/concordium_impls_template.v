(** This file was automatically generated using Hacspec **)
Require Import Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Lib.

Notation "'reject'" := (int32) : hacspec_scope.

Definition iint32_min : int32 :=
  (not (repr 0)) .^ (@cast _ int32 _ ((not (repr 0)) shift_right (usize 1))).

Definition reject_impl_default  : reject :=
  iint32_min.

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


Inductive bool_emum :=
| is_true : bool_emum
| is_false : bool_emum.

Definition eqb_bool_emum (x y : bool_emum) : bool := match x with
   | is_true => match y with | is_true=> true | _ => false end
   | is_false => match y with | is_false=> true | _ => false end
   end.

Definition eqb_leibniz_bool_emum (x y : bool_emum) : eqb_bool_emum x y = true -> x = y.
Proof. intros. destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. Qed.

Instance eq_dec_bool_emum : EqDec (bool_emum) :=
Build_EqDec (bool_emum) (eqb_bool_emum) (eqb_leibniz_bool_emum).


Definition is_lt (x_0 : int32) : bool_emum :=
  (if ((x_0) <.? (repr 0)):bool then (is_true) else (is_false)).

Definition new_reject_impl (x_1 : int32) : option_reject :=
  (if ((x_1) <.? (repr 0)):bool then (SomeReject (x_1)) else (NoneReject)).

Definition reject_impl_convert_from_unit  : reject :=
  (iint32_min) .+ (repr 1).

Definition reject_impl_convert_from_parse_error  : reject :=
  (iint32_min) .+ (repr 2).

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


Definition reject_impl_from_log_error (le_2 : log_error) : reject :=
  match le_2 with
  | Full => (iint32_min) .+ (repr 3)
  | Malformed => (iint32_min) .+ (repr 4) end.

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
  (nre_3 : new_contract_name_error)
  : reject :=
  match nre_3 with
  | NewContractNameErrorMissingInitPrefix => (iint32_min) .+ (repr 5)
  | NewContractNameErrorTooLong => (iint32_min) .+ (repr 6)
  | NewContractNameErrorContainsDot => (iint32_min) .+ (repr 9)
  | NewContractNameErrorInvalidCharacters => (iint32_min) .+ (repr 10) end.

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
  (nre_4 : new_receive_name_error)
  : reject :=
  match nre_4 with
  | NewReceiveNameErrorMissingDotSeparator => (iint32_min) .+ (repr 7)
  | NewReceiveNameErrorTooLong => (iint32_min) .+ (repr 8)
  | NewReceiveNameErrorInvalidCharacters => (iint32_min) .+ (repr 11) end.

Notation "'contract_state'" := (int32) : hacspec_scope.

Notation "'seek_result'" := ((result int64 unit)) : hacspec_scope.

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


Notation "'u32_option'" := ((option int32)) : hacspec_scope.

Notation "'i64_option'" := ((option int64)) : hacspec_scope.

Definition contract_state_impl_seek
  (current_position_5 : contract_state)
  (pos_6 : seek_from)
  : (contract_state × seek_result) :=
  match pos_6 with
  | Start offset_7 => (@cast _ uint32 _ (offset_7), Ok (offset_7))
  | End delta_8 => (if ((delta_8) >=.? (repr 0)):bool then (
    match pub_uint32_checked_add (current_position_5) (
      @cast _ uint32 _ (delta_8)) with
    | Some b_9 => (b_9, Ok (@cast _ uint64 _ (delta_8)))
    | None => (current_position_5, Err (tt)) end) else (
    match pub_int64_checked_abs (delta_8) with
    | Some b_10 => (
      (repr 4) .- (@cast _ uint32 _ (b_10)),
      Ok (@cast _ uint64 _ ((repr 4) .- (@cast _ uint32 _ (b_10))))
    )
    | None => (current_position_5, Err (tt)) end))
  | Current delta_11 => (if ((delta_11) >=.? (repr 0)):bool then (
    match pub_uint32_checked_add (current_position_5) (
      @cast _ uint32 _ (delta_11)) with
    | Some offset_12 => (offset_12, Ok (@cast _ uint64 _ (offset_12)))
    | None => (current_position_5, Err (tt)) end) else (
    match pub_int64_checked_abs (delta_11) with
    | Some b_13 => match pub_uint32_checked_sub (current_position_5) (
      @cast _ uint32 _ (b_13)) with
    | Some offset_14 => (offset_14, Ok (@cast _ uint64 _ (offset_14)))
    | None => (current_position_5, Err (tt)) end
    | None => (current_position_5, Err (tt)) end)) end.

Definition contract_state_impl_read_read
  (current_position_15 : contract_state)
  (num_read_16 : int32)
  : (contract_state × uint_size) :=
  ((current_position_15) .+ (num_read_16), @cast _ uint32 _ (num_read_16)).

Definition contract_state_impl_read_read_u64
  (current_position_17 : contract_state)
  (num_read_18 : int32)
  : (contract_state × bool) :=
  ((current_position_17) .+ (num_read_18), (num_read_18) =.? (repr 8)).

Definition contract_state_impl_read_read_u32
  (current_position_19 : contract_state)
  (num_read_20 : int32)
  : (contract_state × bool) :=
  ((current_position_19) .+ (num_read_20), (num_read_20) =.? (repr 4)).

Definition contract_state_impl_read_read_u8
  (current_position_21 : contract_state)
  (num_read_22 : int32)
  : (contract_state × bool) :=
  ((current_position_21) .+ (num_read_22), (num_read_22) =.? (repr 1)).

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
  repr 0.

Definition has_contract_state_impl_for_contract_state_reserve_0
  (len_27 : int32)
  (cur_size_28 : int32)
  : bool :=
  (cur_size_28) <.? (len_27).

Definition has_contract_state_impl_for_contract_state_reserve_1
  (res_29 : int32)
  : bool :=
  (res_29) =.? (repr 1).

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
  (remaining_items_37) =.? (repr 0).

Definition has_policy_impl_for_policy_attributes_cursor_next_tag_invalid
  (policy_attribute_items_38 : attributes_cursor)
  (tag_value_len_1_39 : int8)
  (num_read_40 : int32)
  : (attributes_cursor × bool) :=
  let '(current_position_41, remaining_items_42) :=
    policy_attribute_items_38 in 
  let policy_attribute_items_43 :=
    ((current_position_41) .+ (num_read_40), remaining_items_42) in 
  (policy_attribute_items_43, (tag_value_len_1_39) >.? (repr 31)).

Definition has_policy_impl_for_policy_attributes_cursor_next
  (policy_attribute_items_44 : attributes_cursor)
  (num_read_45 : int32)
  : attributes_cursor :=
  let '(current_position_46, remaining_items_47) :=
    policy_attribute_items_44 in 
  ((current_position_46) .+ (num_read_45), (remaining_items_47) .- (repr 1)).

