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


Definition new_reject_impl (x_2551 : int32)  : (option int32) :=
  (if ((x_2551) <.? (@repr WORDSIZE32 (0))):bool then (@Some int32 (
        x_2551)) else (@None int32)).


Definition reject_impl_convert_from_unit   : reject_hacspec_t :=
  (- (@repr WORDSIZE32 (Z.neg 2147483648))) .+ (@repr WORDSIZE32 (1)).


Theorem ensures_reject_impl_convert_from_unit : forall result_2552 ,
 @reject_impl_convert_from_unit  = result_2552 ->
 (~ (result_2552 = @repr WORDSIZE32 (0))).
 Proof. Admitted.

Definition reject_impl_convert_from_parse_error   : reject_hacspec_t :=
  (- (@repr WORDSIZE32 (Z.neg 2147483648))) .+ (@repr WORDSIZE32 (2)).


Theorem ensures_reject_impl_convert_from_parse_error : forall result_2552 ,
 @reject_impl_convert_from_parse_error  = result_2552 ->
 (~ (result_2552 = @repr WORDSIZE32 (0))).
 Proof. Admitted.

Definition reject_impl_from_log_error
  (le_2553 : log_error_t)
  
  : reject_hacspec_t :=
  match le_2553 with
  | Full => (- (@repr WORDSIZE32 (Z.neg 2147483648))) .+ (@repr WORDSIZE32 (3))
  | Malformed => (- (@repr WORDSIZE32 (Z.neg 2147483648))) .+ (
    @repr WORDSIZE32 (4))
  end.


Theorem ensures_reject_impl_from_log_error : forall result_2552 (
  le_2553 : log_error_t),
 @reject_impl_from_log_error le_2553 = result_2552 ->
 (~ (result_2552 = @repr WORDSIZE32 (0))).
 Proof. Admitted.

Inductive new_contract_name_error_t :=
| NewContractNameErrorMissingInitPrefix : new_contract_name_error_t
| NewContractNameErrorTooLong : new_contract_name_error_t
| NewContractNameErrorContainsDot : new_contract_name_error_t
| NewContractNameErrorInvalidCharacters : new_contract_name_error_t.

Definition reject_impl_from_new_contract_name_error
  (nre_2554 : new_contract_name_error_t)
  
  : reject_hacspec_t :=
  match nre_2554 with
  | NewContractNameErrorMissingInitPrefix => (- (
      @repr WORDSIZE32 (Z.neg 2147483648))) .+ (@repr WORDSIZE32 (5))
  | NewContractNameErrorTooLong => (- (
      @repr WORDSIZE32 (Z.neg 2147483648))) .+ (@repr WORDSIZE32 (6))
  | NewContractNameErrorContainsDot => (- (
      @repr WORDSIZE32 (Z.neg 2147483648))) .+ (@repr WORDSIZE32 (9))
  | NewContractNameErrorInvalidCharacters => (- (
      @repr WORDSIZE32 (Z.neg 2147483648))) .+ (@repr WORDSIZE32 (10))
  end.


Theorem ensures_reject_impl_from_new_contract_name_error : forall result_2552 (
  nre_2554 : new_contract_name_error_t),
 @reject_impl_from_new_contract_name_error nre_2554 = result_2552 ->
 (~ (result_2552 = @repr WORDSIZE32 (0))).
 Proof. Admitted.

Inductive new_receive_name_error_t :=
| NewReceiveNameErrorMissingDotSeparator : new_receive_name_error_t
| NewReceiveNameErrorTooLong : new_receive_name_error_t
| NewReceiveNameErrorInvalidCharacters : new_receive_name_error_t.

Definition reject_impl_from_new_receive_name_error
  (nre_2555 : new_receive_name_error_t)
  
  : reject_hacspec_t :=
  match nre_2555 with
  | NewReceiveNameErrorMissingDotSeparator => (- (
      @repr WORDSIZE32 (Z.neg 2147483648))) .+ (@repr WORDSIZE32 (7))
  | NewReceiveNameErrorTooLong => (- (@repr WORDSIZE32 (Z.neg 2147483648))) .+ (
    @repr WORDSIZE32 (8))
  | NewReceiveNameErrorInvalidCharacters => (- (
      @repr WORDSIZE32 (Z.neg 2147483648))) .+ (@repr WORDSIZE32 (11))
  end.


Theorem ensures_reject_impl_from_new_receive_name_error : forall result_2552 (
  nre_2555 : new_receive_name_error_t),
 @reject_impl_from_new_receive_name_error nre_2555 = result_2552 ->
 (~ (result_2552 = @repr WORDSIZE32 (0))).
 Proof. Admitted.

Definition reject_impl_from_not_payable_error   : reject_hacspec_t :=
  (- (@repr WORDSIZE32 (Z.neg 2147483648))) .+ (@repr WORDSIZE32 (12)).


Theorem ensures_reject_impl_from_not_payable_error : forall result_2552 ,
 @reject_impl_from_not_payable_error  = result_2552 ->
 (~ (result_2552 = @repr WORDSIZE32 (0))).
 Proof. Admitted.

Notation "'contract_state_hacspec_t'" := (int32) : hacspec_scope.

Inductive seek_from_hacspec_t :=
| Start : int64 -> seek_from_hacspec_t
| End : int64 -> seek_from_hacspec_t
| Current : int64 -> seek_from_hacspec_t.

Notation "'uint32_option_t'" := ((option int32)) : hacspec_scope.

Notation "'iint64_option_t'" := ((option int64)) : hacspec_scope.

Definition contract_state_impl_seek
  (current_position_2556 : contract_state_hacspec_t)
  (end_2557 : int32)
  (pos_2558 : seek_from_hacspec_t)
  
  : (result (contract_state_hacspec_t '× int64) unit) :=
  match pos_2558 with
  | Start (offset_2559) => @Ok (contract_state_hacspec_t '× int64) unit ((
      @cast _ uint32 _ (offset_2559),
      offset_2559
    ))
  | End (delta_2560) => (if ((delta_2560) >=.? (
        @repr WORDSIZE64 (0))):bool then (match pub_uint32_checked_add (
        current_position_2556) (@cast _ uint32 _ (delta_2560)) with
      | Some (b_2561) => @Ok (contract_state_hacspec_t '× int64) unit ((
          b_2561,
          @cast _ uint64 _ (b_2561)
        ))
      | None => @Err (contract_state_hacspec_t '× int64) unit (tt)
      end) else (match pub_int64_checked_abs (delta_2560) with
      | Some (before_2562) => (if ((@cast _ uint32 _ (before_2562)) <=.? (
            end_2557)):bool then (@Ok (contract_state_hacspec_t '× int64
          ) unit ((
              (end_2557) .- (@cast _ uint32 _ (before_2562)),
              @cast _ uint64 _ ((end_2557) .- (@cast _ uint32 _ (before_2562)))
            ))) else (@Err (contract_state_hacspec_t '× int64) unit (tt)))
      | None => @Err (contract_state_hacspec_t '× int64) unit (tt)
      end))
  | Current (delta_2563) => (if ((delta_2563) >=.? (
        @repr WORDSIZE64 (0))):bool then (match pub_uint32_checked_add (
        current_position_2556) (@cast _ uint32 _ (delta_2563)) with
      | Some (offset_2564) => @Ok (contract_state_hacspec_t '× int64) unit ((
          offset_2564,
          @cast _ uint64 _ (offset_2564)
        ))
      | None => @Err (contract_state_hacspec_t '× int64) unit (tt)
      end) else (match pub_int64_checked_abs (delta_2563) with
      | Some (b_2565) => match pub_uint32_checked_sub (current_position_2556) (
        @cast _ uint32 _ (b_2565)) with
      | Some (offset_2566) => @Ok (contract_state_hacspec_t '× int64) unit ((
          offset_2566,
          @cast _ uint64 _ (offset_2566)
        ))
      | None => @Err (contract_state_hacspec_t '× int64) unit (tt)
      end
      | None => @Err (contract_state_hacspec_t '× int64) unit (tt)
      end))
  end.


Definition contract_state_impl_read_read
  (current_position_2567 : contract_state_hacspec_t)
  (buf_2568 : public_byte_seq)
  
  : (contract_state_hacspec_t '× uint_size) :=
  let '(buf_2569, num_read_2570) :=
    load_state_hacspec (buf_2568) (current_position_2567) in 
  ((current_position_2567) .+ (num_read_2570), @cast _ uint32 _ (num_read_2570)
  ).


Definition contract_state_impl_read_read_u64
  (current_position_2571 : contract_state_hacspec_t)
  
  : (contract_state_hacspec_t '× (result int64 unit)) :=
  let buf_2572 : seq int8 :=
    seq_new_ (default : int8) (usize 8) in 
  let '(buf_2573, num_read_2574) :=
    load_state_hacspec (buf_2572) (current_position_2571) in 
  (
    (current_position_2571) .+ (num_read_2574),
    (if ((num_read_2574) =.? (@repr WORDSIZE32 (8))):bool then (@Ok int64 unit (
          u64_from_le_bytes (array_from_seq (8) (buf_2573)))) else (
        @Err int64 unit (tt)))
  ).


Definition contract_state_impl_read_read_u32
  (current_position_2575 : contract_state_hacspec_t)
  
  : (contract_state_hacspec_t '× (result int32 unit)) :=
  let buf_2576 : seq int8 :=
    seq_new_ (default : int8) (usize 4) in 
  let '(buf_2577, num_read_2578) :=
    load_state_hacspec (buf_2576) (current_position_2575) in 
  (
    (current_position_2575) .+ (num_read_2578),
    (if ((num_read_2578) =.? (@repr WORDSIZE32 (4))):bool then (@Ok int32 unit (
          u32_from_le_bytes (array_from_seq (4) (buf_2577)))) else (
        @Err int32 unit (tt)))
  ).


Definition contract_state_impl_read_read_u8
  (current_position_2579 : contract_state_hacspec_t)
  
  : (contract_state_hacspec_t '× (result int8 unit)) :=
  let buf_2580 : seq int8 :=
    seq_new_ (default : int8) (usize 1) in 
  let '(buf_2581, num_read_2582) :=
    load_state_hacspec (buf_2580) (current_position_2579) in 
  (
    (current_position_2579) .+ (num_read_2582),
    (if ((num_read_2582) =.? (@repr WORDSIZE32 (1))):bool then (@Ok int8 unit (
          seq_index (buf_2581) (usize 0))) else (@Err int8 unit (tt)))
  ).


Definition contract_state_impl_write
  (current_position_2583 : contract_state_hacspec_t)
  (buf_2584 : public_byte_seq)
  
  : (result (contract_state_hacspec_t '× uint_size) unit) :=
  ifbnd option_is_none (pub_uint32_checked_add (current_position_2583) (
      pub_u32 (seq_len (buf_2584)))) : bool
  thenbnd (bind (@Err (contract_state_hacspec_t '× uint_size) unit (tt)) (
      fun _ => @Ok unit unit (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_2585, num_bytes_2586) :=
    write_state_hacspec (buf_2584) (current_position_2583) in 
  @Ok (contract_state_hacspec_t '× uint_size) unit ((
      (current_position_2583) .+ (num_bytes_2586),
      @cast _ uint32 _ (num_bytes_2586)
    ))).


Definition has_contract_state_impl_for_contract_state_open
  
  
  : contract_state_hacspec_t :=
  @repr WORDSIZE32 (0).


Definition has_contract_state_impl_for_contract_state_reserve
  (len_2587 : int32)
  
  : bool :=
  let cur_size_2588 : int32 :=
    state_size_hacspec  in 
  (if ((cur_size_2588) <.? (len_2587)):bool then ((resize_state_hacspec (
          len_2587)) =.? (@repr WORDSIZE32 (1))) else (true)).


Definition has_contract_state_impl_for_contract_state_truncate
  (current_position_2589 : contract_state_hacspec_t)
  (cur_size_2590 : int32)
  (new_size_2591 : int32)
  
  : contract_state_hacspec_t :=
  let 'tt :=
    if (cur_size_2590) >.? (new_size_2591):bool then (let _ : int32 :=
        resize_state_hacspec (new_size_2591) in 
      tt) else (tt) in 
  (if ((new_size_2591) <.? (current_position_2589)):bool then (
      new_size_2591) else (current_position_2589)).


Notation "'parameter_hacspec_t'" := (int32) : hacspec_scope.

Definition read_impl_for_parameter_read
  (current_position_2592 : parameter_hacspec_t)
  (buf_2593 : public_byte_seq)
  
  : (parameter_hacspec_t '× uint_size) :=
  let '(buf_2594, num_read_2595) :=
    get_parameter_section_hacspec (buf_2593) (current_position_2592) in 
  ((current_position_2592) .+ (num_read_2595), @cast _ uint32 _ (num_read_2595)
  ).


Notation "'attributes_cursor_hacspec_t'" := ((int32 '× int16)) : hacspec_scope.

Definition has_policy_impl_for_policy_attributes_cursor_next_item
  (policy_attribute_items_2596 : attributes_cursor_hacspec_t)
  (buf_2597 : public_byte_seq)
  
  : (option (attributes_cursor_hacspec_t '× (int8 '× int8))) :=
  let '(current_position_2598, remaining_items_2599) :=
    policy_attribute_items_2596 in 
  ifbnd (remaining_items_2599) =.? (@repr WORDSIZE16 0) : bool
  thenbnd (bind (@None (attributes_cursor_hacspec_t '× (int8 '× int8))) (
      fun _ => @Some unit (tt)))
  else (tt) >> (fun 'tt =>
  let '(tag_value_len_2600, num_read_2601) :=
    get_policy_section_hacspec (seq_new_ (default : int8) (usize 2)) (
      current_position_2598) in 
  let current_position_2598 :=
    (current_position_2598) .+ (num_read_2601) in 
  ifbnd (seq_index (tag_value_len_2600) (usize 1)) >.? (
    @repr WORDSIZE8 31) : bool
  thenbnd (bind (@None (attributes_cursor_hacspec_t '× (int8 '× int8))) (
      fun _ => @Some unit (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_2602, num_read_2603) :=
    get_policy_section_hacspec (buf_2597) (current_position_2598) in 
  let current_position_2598 :=
    (current_position_2598) .+ (num_read_2603) in 
  let remaining_items_2599 :=
    (remaining_items_2599) .- (@repr WORDSIZE16 1) in 
  @Some (attributes_cursor_hacspec_t '× (int8 '× int8)) ((
      (current_position_2598, remaining_items_2599),
      (
        seq_index (tag_value_len_2600) (usize 0),
        seq_index (tag_value_len_2600) (usize 1)
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
  (policies_iterator_2604 : policies_iterator_hacspec_t)
  
  : (option (policies_iterator_hacspec_t '× policy_attributes_cursor_hacspec_t
    )) :=
  let '(pos_2605, remaining_items_2606) :=
    policies_iterator_2604 in 
  ifbnd (remaining_items_2606) =.? (@repr WORDSIZE16 0) : bool
  thenbnd (bind (@None (
        policies_iterator_hacspec_t '×
        policy_attributes_cursor_hacspec_t
      )) (fun _ => @Some unit (tt)))
  else (tt) >> (fun 'tt =>
  let '(buf_2607, _) :=
    get_policy_section_hacspec (seq_new_ (default : int8) (((((usize 2) + (
                usize 4)) + (usize 8)) + (usize 8)) + (usize 2))) (pos_2605) in 
  let skip_part_2608 : public_byte_seq :=
    seq_slice_range (buf_2607) ((usize 0, usize 2)) in 
  let ip_part_2609 : public_byte_seq :=
    seq_slice_range (buf_2607) ((usize 2, (usize 2) + (usize 4))) in 
  let created_at_part_2610 : public_byte_seq :=
    seq_slice_range (buf_2607) ((
        (usize 2) + (usize 4),
        ((usize 2) + (usize 4)) + (usize 8)
      )) in 
  let valid_to_part_2611 : public_byte_seq :=
    seq_slice_range (buf_2607) ((
        ((usize 2) + (usize 4)) + (usize 8),
        (((usize 2) + (usize 4)) + (usize 8)) + (usize 8)
      )) in 
  let len_part_2612 : public_byte_seq :=
    seq_slice_range (buf_2607) ((
        (((usize 2) + (usize 4)) + (usize 8)) + (usize 8),
        ((((usize 2) + (usize 4)) + (usize 8)) + (usize 8)) + (usize 2)
      )) in 
  let identity_provider_2613 : int32 :=
    u32_from_le_bytes (array_from_seq (4) (ip_part_2609)) in 
  let created_at_2614 : int64 :=
    u64_from_le_bytes (array_from_seq (8) (created_at_part_2610)) in 
  let valid_to_2615 : int64 :=
    u64_from_le_bytes (array_from_seq (8) (valid_to_part_2611)) in 
  let remaining_items_2616 : int16 :=
    u16_from_le_bytes (array_from_seq (2) (len_part_2612)) in 
  let attributes_start_2617 : int32 :=
    (((((pos_2605) .+ (@repr WORDSIZE32 (2))) .+ (@repr WORDSIZE32 (4))) .+ (
          @repr WORDSIZE32 (8))) .+ (@repr WORDSIZE32 (8))) .+ (
      @repr WORDSIZE32 (2)) in 
  let pos_2605 :=
    ((pos_2605) .+ (@cast _ uint32 _ (u16_from_le_bytes (array_from_seq (2) (
              skip_part_2608))))) .+ (@repr WORDSIZE32 (2)) in 
  let remaining_items_2616 :=
    (remaining_items_2616) .- (@repr WORDSIZE16 1) in 
  @Some (policies_iterator_hacspec_t '× policy_attributes_cursor_hacspec_t) ((
      (pos_2605, remaining_items_2616),
      (
        identity_provider_2613,
        created_at_2614,
        valid_to_2615,
        (attributes_start_2617, remaining_items_2616)
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
  (ca_index_2618 : int64)
  (ca_subindex_2619 : int64)
  (receive_name_bytes_2620 : public_byte_seq)
  (amount_2621 : int64)
  (param_bytes_2622 : public_byte_seq)
  
  : int32 :=
  send_hacspec (ca_index_2618) (ca_subindex_2619) (receive_name_bytes_2620) (
    amount_2621) (param_bytes_2622).


