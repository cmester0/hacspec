(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp.word Require Import ssrZ word.
From Jasmin Require Import word.

From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.

Require Import ChoiceEquality.
Require Import LocationUtility.
Require Import Hacspec_Lib_Comparable.
Require Import Hacspec_Lib_Pre.
Require Import Hacspec_Lib.

Open Scope hacspec_scope.
Import choice.Choice.Exports.

Obligation Tactic := try timeout 8 solve_ssprove_obligations.


Definition block_size_v : uint_size :=
  usize 64.

Definition len_size_v : uint_size :=
  usize 8.

Definition k_size_v : uint_size :=
  usize 64.

Definition hash_size_v : uint_size :=
  ((usize 256) ./ (usize 8)).

Definition block_t := nseq (uint8) (block_size_v).

Definition op_table_type_t := nseq (uint_size) (usize 12).

Definition sha256_digest_t := nseq (uint8) (hash_size_v).

Definition round_constants_table_t := nseq (uint32) (k_size_v).

Definition hash_t := nseq (uint32) (usize 8).


Notation "'ch_inp'" :=(
  uint32 × uint32 × uint32 : choice_type) (in custom pack_type at level 2).
Notation "'ch_out'" :=(uint32 : choice_type) (in custom pack_type at level 2).
Definition CH : nat :=
  648.
Program Definition ch (x_645 : uint32) (y_646 : uint32) (z_647 : uint32)
  : both (fset.fset0) [interface] (uint32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 x_645) .& (lift_to_both0 y_646)) .^ ((not (
              lift_to_both0 x_645)) .& (lift_to_both0 z_647)))
      ) : both (fset.fset0) [interface] (uint32)).
Fail Next Obligation.


Notation "'maj_inp'" :=(
  uint32 × uint32 × uint32 : choice_type) (in custom pack_type at level 2).
Notation "'maj_out'" :=(uint32 : choice_type) (in custom pack_type at level 2).
Definition MAJ : nat :=
  652.
Program Definition maj (x_649 : uint32) (y_650 : uint32) (z_651 : uint32)
  : both (fset.fset0) [interface] (uint32) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((
            lift_to_both0 x_649) .& (lift_to_both0 y_650)) .^ (((
              lift_to_both0 x_649) .& (lift_to_both0 z_651)) .^ ((
              lift_to_both0 y_650) .& (lift_to_both0 z_651))))
      ) : both (fset.fset0) [interface] (uint32)).
Fail Next Obligation.

Definition op_table_v : op_table_type_t :=
  @array_from_list uint_size [
    (usize 2) : uint_size;
    (usize 13) : uint_size;
    (usize 22) : uint_size;
    (usize 6) : uint_size;
    (usize 11) : uint_size;
    (usize 25) : uint_size;
    (usize 7) : uint_size;
    (usize 18) : uint_size;
    (usize 3) : uint_size;
    (usize 17) : uint_size;
    (usize 19) : uint_size;
    (usize 10) : uint_size
  ].

Definition k_table_v : round_constants_table_t :=
  @array_from_list uint32 [
    (secret (@repr U32 1116352408)) : uint32;
    (secret (@repr U32 1899447441)) : uint32;
    (secret (@repr U32 3049323471)) : uint32;
    (secret (@repr U32 3921009573)) : uint32;
    (secret (@repr U32 961987163)) : uint32;
    (secret (@repr U32 1508970993)) : uint32;
    (secret (@repr U32 2453635748)) : uint32;
    (secret (@repr U32 2870763221)) : uint32;
    (secret (@repr U32 3624381080)) : uint32;
    (secret (@repr U32 310598401)) : uint32;
    (secret (@repr U32 607225278)) : uint32;
    (secret (@repr U32 1426881987)) : uint32;
    (secret (@repr U32 1925078388)) : uint32;
    (secret (@repr U32 2162078206)) : uint32;
    (secret (@repr U32 2614888103)) : uint32;
    (secret (@repr U32 3248222580)) : uint32;
    (secret (@repr U32 3835390401)) : uint32;
    (secret (@repr U32 4022224774)) : uint32;
    (secret (@repr U32 264347078)) : uint32;
    (secret (@repr U32 604807628)) : uint32;
    (secret (@repr U32 770255983)) : uint32;
    (secret (@repr U32 1249150122)) : uint32;
    (secret (@repr U32 1555081692)) : uint32;
    (secret (@repr U32 1996064986)) : uint32;
    (secret (@repr U32 2554220882)) : uint32;
    (secret (@repr U32 2821834349)) : uint32;
    (secret (@repr U32 2952996808)) : uint32;
    (secret (@repr U32 3210313671)) : uint32;
    (secret (@repr U32 3336571891)) : uint32;
    (secret (@repr U32 3584528711)) : uint32;
    (secret (@repr U32 113926993)) : uint32;
    (secret (@repr U32 338241895)) : uint32;
    (secret (@repr U32 666307205)) : uint32;
    (secret (@repr U32 773529912)) : uint32;
    (secret (@repr U32 1294757372)) : uint32;
    (secret (@repr U32 1396182291)) : uint32;
    (secret (@repr U32 1695183700)) : uint32;
    (secret (@repr U32 1986661051)) : uint32;
    (secret (@repr U32 2177026350)) : uint32;
    (secret (@repr U32 2456956037)) : uint32;
    (secret (@repr U32 2730485921)) : uint32;
    (secret (@repr U32 2820302411)) : uint32;
    (secret (@repr U32 3259730800)) : uint32;
    (secret (@repr U32 3345764771)) : uint32;
    (secret (@repr U32 3516065817)) : uint32;
    (secret (@repr U32 3600352804)) : uint32;
    (secret (@repr U32 4094571909)) : uint32;
    (secret (@repr U32 275423344)) : uint32;
    (secret (@repr U32 430227734)) : uint32;
    (secret (@repr U32 506948616)) : uint32;
    (secret (@repr U32 659060556)) : uint32;
    (secret (@repr U32 883997877)) : uint32;
    (secret (@repr U32 958139571)) : uint32;
    (secret (@repr U32 1322822218)) : uint32;
    (secret (@repr U32 1537002063)) : uint32;
    (secret (@repr U32 1747873779)) : uint32;
    (secret (@repr U32 1955562222)) : uint32;
    (secret (@repr U32 2024104815)) : uint32;
    (secret (@repr U32 2227730452)) : uint32;
    (secret (@repr U32 2361852424)) : uint32;
    (secret (@repr U32 2428436474)) : uint32;
    (secret (@repr U32 2756734187)) : uint32;
    (secret (@repr U32 3204031479)) : uint32;
    (secret (@repr U32 3329325298)) : uint32
  ].

Definition hash_init_v : hash_t :=
  @array_from_list uint32 [
    (secret (@repr U32 1779033703)) : uint32;
    (secret (@repr U32 3144134277)) : uint32;
    (secret (@repr U32 1013904242)) : uint32;
    (secret (@repr U32 2773480762)) : uint32;
    (secret (@repr U32 1359893119)) : uint32;
    (secret (@repr U32 2600822924)) : uint32;
    (secret (@repr U32 528734635)) : uint32;
    (secret (@repr U32 1541459225)) : uint32
  ].

Definition tmp_653_loc : ChoiceEqualityLocation :=
  (uint32 ; 654%nat).
Notation "'sigma_inp'" :=(
  uint32 × uint_size × uint_size : choice_type) (in custom pack_type at level 2).
Notation "'sigma_out'" :=(
  uint32 : choice_type) (in custom pack_type at level 2).
Definition SIGMA : nat :=
  658.
Program Definition sigma (x_655 : uint32) (i_656 : uint_size) (
    op_657 : uint_size)
  : both (CEfset ([tmp_653_loc])) [interface] (uint32) :=
  ((letbm tmp_653 : uint32 loc( tmp_653_loc ) :=
        uint32_rotate_right (lift_to_both0 x_655) (array_index (op_table_v) (((
                lift_to_both0 (usize 3)) .* (lift_to_both0 i_656)) .+ (
              lift_to_both0 (usize 2)))) in
      letb '(tmp_653) :=
        if (lift_to_both0 op_657) =.? (lift_to_both0 (
            usize 0)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset ([tmp_653_loc])) (L2 := CEfset (
            [tmp_653_loc])) (I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm tmp_653 loc( tmp_653_loc ) :=
            (lift_to_both0 x_655) shift_right (array_index (op_table_v) (((
                    lift_to_both0 (usize 3)) .* (lift_to_both0 i_656)) .+ (
                  lift_to_both0 (usize 2)))) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
            lift_to_both0 tmp_653)
          )
        else lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
          lift_to_both0 tmp_653)
         in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (((uint32_rotate_right (
              lift_to_both0 x_655) (array_index (op_table_v) ((lift_to_both0 (
                    usize 3)) .* (lift_to_both0 i_656)))) .^ (
            uint32_rotate_right (lift_to_both0 x_655) (array_index (
                op_table_v) (((lift_to_both0 (usize 3)) .* (
                    lift_to_both0 i_656)) .+ (lift_to_both0 (usize 1)))))) .^ (
          lift_to_both0 tmp_653))
      ) : both (CEfset ([tmp_653_loc])) [interface] (uint32)).
Fail Next Obligation.

Definition s_659_loc : ChoiceEqualityLocation :=
  (round_constants_table_t ; 660%nat).
Notation "'schedule_inp'" :=(
  block_t : choice_type) (in custom pack_type at level 2).
Notation "'schedule_out'" :=(
  round_constants_table_t : choice_type) (in custom pack_type at level 2).
Definition SCHEDULE : nat :=
  670.
Program Definition schedule (block_661 : block_t)
  : both (CEfset ([tmp_653_loc ; s_659_loc])) [interface] (
    round_constants_table_t) :=
  ((letb b_662 : seq uint32 := array_to_be_uint32s (lift_to_both0 block_661) in
      letbm s_659 : round_constants_table_t loc( s_659_loc ) :=
        array_new_ (default : uint32) (k_size_v) in
      letb s_659 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 k_size_v) s_659 (
            L := (CEfset ([tmp_653_loc ; s_659_loc]))) (I := [interface]) (
            fun i_663 s_659 =>
            letb '(s_659) :=
              if (lift_to_both0 i_663) <.? (lift_to_both0 (
                  usize 16)) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset ([s_659_loc])) (L2 := CEfset (
                  [tmp_653_loc ; s_659_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb s_659 : round_constants_table_t :=
                  array_upd s_659 (lift_to_both0 i_663) (is_pure (seq_index (
                        b_662) (lift_to_both0 i_663))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 s_659)
                )
              else  lift_scope (L1 := CEfset ([tmp_653_loc ; s_659_loc])) (
                L2 := CEfset ([tmp_653_loc ; s_659_loc])) (I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb t16_664 : uint32 :=
                  array_index (s_659) ((lift_to_both0 i_663) .- (lift_to_both0 (
                        usize 16))) in
                letb t15_665 : uint32 :=
                  array_index (s_659) ((lift_to_both0 i_663) .- (lift_to_both0 (
                        usize 15))) in
                letb t7_666 : uint32 :=
                  array_index (s_659) ((lift_to_both0 i_663) .- (lift_to_both0 (
                        usize 7))) in
                letb t2_667 : uint32 :=
                  array_index (s_659) ((lift_to_both0 i_663) .- (lift_to_both0 (
                        usize 2))) in
                letb s1_668 : uint32 :=
                  sigma (lift_to_both0 t2_667) (lift_to_both0 (usize 3)) (
                    lift_to_both0 (usize 0)) in
                letb s0_669 : uint32 :=
                  sigma (lift_to_both0 t15_665) (lift_to_both0 (usize 2)) (
                    lift_to_both0 (usize 0)) in
                letb s_659 : round_constants_table_t :=
                  array_upd s_659 (lift_to_both0 i_663) (is_pure ((((
                            lift_to_both0 s1_668) .+ (
                            lift_to_both0 t7_666)) .+ (
                          lift_to_both0 s0_669)) .+ (lift_to_both0 t16_664))) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
                  lift_to_both0 s_659)
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 s_659)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 s_659)
      ) : both (CEfset ([tmp_653_loc ; s_659_loc])) [interface] (
      round_constants_table_t)).
Fail Next Obligation.

Definition h_671_loc : ChoiceEqualityLocation :=
  (hash_t ; 672%nat).
Notation "'shuffle_inp'" :=(
  round_constants_table_t × hash_t : choice_type) (in custom pack_type at level 2).
Notation "'shuffle_out'" :=(
  hash_t : choice_type) (in custom pack_type at level 2).
Definition SHUFFLE : nat :=
  686.
Program Definition shuffle (ws_683 : round_constants_table_t) (
    hashi_673 : hash_t)
  : both (CEfset ([tmp_653_loc ; h_671_loc])) [interface] (hash_t) :=
  ((letbm h_671 : hash_t loc( h_671_loc ) := lift_to_both0 hashi_673 in
      letb h_671 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 k_size_v) h_671 (
            L := (CEfset ([tmp_653_loc ; h_671_loc]))) (I := [interface]) (
            fun i_674 h_671 =>
            letb a0_675 : uint32 :=
              array_index (h_671) (lift_to_both0 (usize 0)) in
            letb b0_676 : uint32 :=
              array_index (h_671) (lift_to_both0 (usize 1)) in
            letb c0_677 : uint32 :=
              array_index (h_671) (lift_to_both0 (usize 2)) in
            letb d0_678 : uint32 :=
              array_index (h_671) (lift_to_both0 (usize 3)) in
            letb e0_679 : uint32 :=
              array_index (h_671) (lift_to_both0 (usize 4)) in
            letb f0_680 : uint32 :=
              array_index (h_671) (lift_to_both0 (usize 5)) in
            letb g0_681 : uint32 :=
              array_index (h_671) (lift_to_both0 (usize 6)) in
            letb h0_682 : uint32 :=
              array_index (h_671) (lift_to_both0 (usize 7)) in
            letb t1_684 : uint32 :=
              ((((lift_to_both0 h0_682) .+ (sigma (lift_to_both0 e0_679) (
                        lift_to_both0 (usize 1)) (lift_to_both0 (
                          usize 1)))) .+ (ch (lift_to_both0 e0_679) (
                      lift_to_both0 f0_680) (lift_to_both0 g0_681))) .+ (
                  array_index (k_table_v) (lift_to_both0 i_674))) .+ (
                array_index (ws_683) (lift_to_both0 i_674)) in
            letb t2_685 : uint32 :=
              (sigma (lift_to_both0 a0_675) (lift_to_both0 (usize 0)) (
                  lift_to_both0 (usize 1))) .+ (maj (lift_to_both0 a0_675) (
                  lift_to_both0 b0_676) (lift_to_both0 c0_677)) in
            letb h_671 : hash_t :=
              array_upd h_671 (lift_to_both0 (usize 0)) (is_pure ((
                    lift_to_both0 t1_684) .+ (lift_to_both0 t2_685))) in
            letb h_671 : hash_t :=
              array_upd h_671 (lift_to_both0 (usize 1)) (is_pure (
                  lift_to_both0 a0_675)) in
            letb h_671 : hash_t :=
              array_upd h_671 (lift_to_both0 (usize 2)) (is_pure (
                  lift_to_both0 b0_676)) in
            letb h_671 : hash_t :=
              array_upd h_671 (lift_to_both0 (usize 3)) (is_pure (
                  lift_to_both0 c0_677)) in
            letb h_671 : hash_t :=
              array_upd h_671 (lift_to_both0 (usize 4)) (is_pure ((
                    lift_to_both0 d0_678) .+ (lift_to_both0 t1_684))) in
            letb h_671 : hash_t :=
              array_upd h_671 (lift_to_both0 (usize 5)) (is_pure (
                  lift_to_both0 e0_679)) in
            letb h_671 : hash_t :=
              array_upd h_671 (lift_to_both0 (usize 6)) (is_pure (
                  lift_to_both0 f0_680)) in
            letb h_671 : hash_t :=
              array_upd h_671 (lift_to_both0 (usize 7)) (is_pure (
                  lift_to_both0 g0_681)) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 h_671)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 h_671)
      ) : both (CEfset ([tmp_653_loc ; h_671_loc])) [interface] (hash_t)).
Fail Next Obligation.

Definition h_687_loc : ChoiceEqualityLocation :=
  (hash_t ; 688%nat).
Notation "'compress_inp'" :=(
  block_t × hash_t : choice_type) (in custom pack_type at level 2).
Notation "'compress_out'" :=(
  hash_t : choice_type) (in custom pack_type at level 2).
Definition COMPRESS : nat :=
  693.
Program Definition compress (block_689 : block_t) (h_in_691 : hash_t)
  : both (CEfset (
      [tmp_653_loc ; s_659_loc ; h_671_loc ; h_687_loc])) [interface] (
    hash_t) :=
  ((letb s_690 : round_constants_table_t :=
        schedule (lift_to_both0 block_689) in
      letbm h_687 : hash_t loc( h_687_loc ) :=
        shuffle (lift_to_both0 s_690) (lift_to_both0 h_in_691) in
      letb h_687 :=
        foldi_both' (lift_to_both0 (usize 0)) (lift_to_both0 (usize 8)) h_687 (
            L := (CEfset ([tmp_653_loc ; s_659_loc ; h_671_loc ; h_687_loc]))) (
            I := [interface]) (fun i_692 h_687 =>
            letb h_687 : hash_t :=
              array_upd h_687 (lift_to_both0 i_692) (is_pure ((array_index (
                      h_687) (lift_to_both0 i_692)) .+ (array_index (h_in_691) (
                      lift_to_both0 i_692)))) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (
              lift_to_both0 h_687)
            ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (lift_to_both0 h_687)
      ) : both (CEfset (
        [tmp_653_loc ; s_659_loc ; h_671_loc ; h_687_loc])) [interface] (
      hash_t)).
Fail Next Obligation.

Definition last_block_len_696_loc : ChoiceEqualityLocation :=
  (uint_size ; 698%nat).
Definition pad_block_697_loc : ChoiceEqualityLocation :=
  (block_t ; 699%nat).
Definition last_block_695_loc : ChoiceEqualityLocation :=
  (block_t ; 700%nat).
Definition h_694_loc : ChoiceEqualityLocation :=
  (hash_t ; 701%nat).
Notation "'hash_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'hash_out'" :=(
  sha256_digest_t : choice_type) (in custom pack_type at level 2).
Definition HASH : nat :=
  708.
Program Definition hash (msg_702 : byte_seq)
  : both (CEfset (
      [tmp_653_loc ; s_659_loc ; h_671_loc ; h_687_loc ; h_694_loc ; last_block_695_loc ; last_block_len_696_loc ; pad_block_697_loc])) [interface] (
    sha256_digest_t) :=
  ((letbm h_694 : hash_t loc( h_694_loc ) := lift_to_both0 hash_init_v in
      letbm last_block_695 : block_t loc( last_block_695_loc ) :=
        array_new_ (default : uint8) (block_size_v) in
      letbm last_block_len_696 : uint_size loc( last_block_len_696_loc ) :=
        lift_to_both0 (usize 0) in
      letb '(h_694, last_block_695, last_block_len_696) :=
        foldi_both' (lift_to_both0 (usize 0)) (seq_num_chunks (
              lift_to_both0 msg_702) (lift_to_both0 block_size_v)) prod_ce(
            h_694,
            last_block_695,
            last_block_len_696
          ) (L := (CEfset (
                [tmp_653_loc ; s_659_loc ; h_671_loc ; h_687_loc ; h_694_loc ; last_block_695_loc ; last_block_len_696_loc ; pad_block_697_loc]))) (
            I := [interface]) (fun i_703 '(
              h_694,
              last_block_695,
              last_block_len_696
            ) =>
            letb '(block_len_704, block_705) : (uint_size '× seq uint8) :=
              seq_get_chunk (lift_to_both0 msg_702) (
                lift_to_both0 block_size_v) (lift_to_both0 i_703) in
            letb '(h_694, last_block_695, last_block_len_696) :=
              if (lift_to_both0 block_len_704) <.? (
                lift_to_both0 block_size_v) :bool_ChoiceEquality
              then lift_scope (L1 := CEfset (
                  [h_694_loc ; last_block_695_loc ; last_block_len_696_loc])) (
                L2 := CEfset (
                  [tmp_653_loc ; s_659_loc ; h_671_loc ; h_687_loc ; h_694_loc ; last_block_695_loc ; last_block_len_696_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letbm last_block_695 loc( last_block_695_loc ) :=
                  array_update_start (array_new_ (default : uint8) (
                      block_size_v)) (lift_to_both0 block_705) in
                letbm last_block_len_696 loc( last_block_len_696_loc ) :=
                  lift_to_both0 block_len_704 in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 h_694,
                    lift_to_both0 last_block_695,
                    lift_to_both0 last_block_len_696
                  ))
                )
              else  lift_scope (L1 := CEfset (
                  [tmp_653_loc ; s_659_loc ; h_671_loc ; h_687_loc ; h_694_loc ; last_block_695_loc ; last_block_len_696_loc])) (
                L2 := CEfset (
                  [tmp_653_loc ; s_659_loc ; h_671_loc ; h_687_loc ; h_694_loc ; last_block_695_loc ; last_block_len_696_loc])) (
                I1 := [interface]) (
                I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
                letb compress_input_706 : block_t :=
                  array_from_seq (block_size_v) (lift_to_both0 block_705) in
                letbm h_694 loc( h_694_loc ) :=
                  compress (lift_to_both0 compress_input_706) (
                    lift_to_both0 h_694) in
                lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                    lift_to_both0 h_694,
                    lift_to_both0 last_block_695,
                    lift_to_both0 last_block_len_696
                  ))
                ) in
            lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
                lift_to_both0 h_694,
                lift_to_both0 last_block_695,
                lift_to_both0 last_block_len_696
              ))
            ) in
      letb last_block_695 : block_t :=
        array_upd last_block_695 (lift_to_both0 last_block_len_696) (is_pure (
            secret (lift_to_both0 (@repr U8 128)))) in
      letb len_bist_707 : uint64 :=
        secret (pub_u64 (is_pure ((seq_len (lift_to_both0 msg_702)) .* (
                lift_to_both0 (usize 8))))) in
      letb '(h_694, last_block_695) :=
        if (lift_to_both0 last_block_len_696) <.? ((
            lift_to_both0 block_size_v) .- (
            lift_to_both0 len_size_v)) :bool_ChoiceEquality
        then lift_scope (L1 := CEfset (
            [tmp_653_loc ; s_659_loc ; h_671_loc ; h_687_loc ; h_694_loc ; last_block_695_loc ; last_block_len_696_loc])) (
          L2 := CEfset (
            [tmp_653_loc ; s_659_loc ; h_671_loc ; h_687_loc ; h_694_loc ; last_block_695_loc ; last_block_len_696_loc ; pad_block_697_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm last_block_695 loc( last_block_695_loc ) :=
            array_update (lift_to_both0 last_block_695) ((
                lift_to_both0 block_size_v) .- (lift_to_both0 len_size_v)) (
              array_to_seq (uint64_to_be_bytes (lift_to_both0 len_bist_707))) in
          letbm h_694 loc( h_694_loc ) :=
            compress (lift_to_both0 last_block_695) (lift_to_both0 h_694) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 h_694,
              lift_to_both0 last_block_695
            ))
          )
        else  lift_scope (L1 := CEfset (
            [tmp_653_loc ; s_659_loc ; h_671_loc ; h_687_loc ; h_694_loc ; last_block_695_loc ; last_block_len_696_loc ; pad_block_697_loc])) (
          L2 := CEfset (
            [tmp_653_loc ; s_659_loc ; h_671_loc ; h_687_loc ; h_694_loc ; last_block_695_loc ; last_block_len_696_loc ; pad_block_697_loc])) (
          I1 := [interface]) (
          I2 := [interface]) (H_loc_incl := _) (H_opsig_incl := _) (
          letbm pad_block_697 : block_t loc( pad_block_697_loc ) :=
            array_new_ (default : uint8) (block_size_v) in
          letbm pad_block_697 loc( pad_block_697_loc ) :=
            array_update (lift_to_both0 pad_block_697) ((
                lift_to_both0 block_size_v) .- (lift_to_both0 len_size_v)) (
              array_to_seq (uint64_to_be_bytes (lift_to_both0 len_bist_707))) in
          letbm h_694 loc( h_694_loc ) :=
            compress (lift_to_both0 last_block_695) (lift_to_both0 h_694) in
          letbm h_694 loc( h_694_loc ) :=
            compress (lift_to_both0 pad_block_697) (lift_to_both0 h_694) in
          lift_scope (H_loc_incl := _) (H_opsig_incl := _) (prod_b(
              lift_to_both0 h_694,
              lift_to_both0 last_block_695
            ))
          ) in
      lift_scope (H_loc_incl := _) (H_opsig_incl := _) (array_from_seq (
          hash_size_v) (array_to_be_bytes (lift_to_both0 h_694)))
      ) : both (CEfset (
        [tmp_653_loc ; s_659_loc ; h_671_loc ; h_687_loc ; h_694_loc ; last_block_695_loc ; last_block_len_696_loc ; pad_block_697_loc])) [interface] (
      sha256_digest_t)).
Fail Next Obligation.


Notation "'sha256_inp'" :=(
  byte_seq : choice_type) (in custom pack_type at level 2).
Notation "'sha256_out'" :=(
  sha256_digest_t : choice_type) (in custom pack_type at level 2).
Definition SHA256 : nat :=
  710.
Program Definition sha256 (msg_709 : byte_seq)
  : both (CEfset (
      [tmp_653_loc ; s_659_loc ; h_671_loc ; h_687_loc ; h_694_loc ; last_block_695_loc ; last_block_len_696_loc ; pad_block_697_loc])) [interface] (
    sha256_digest_t) :=
  ((lift_scope (H_loc_incl := _) (H_opsig_incl := _) (hash (
          lift_to_both0 msg_709))
      ) : both (CEfset (
        [tmp_653_loc ; s_659_loc ; h_671_loc ; h_687_loc ; h_694_loc ; last_block_695_loc ; last_block_len_696_loc ; pad_block_697_loc])) [interface] (
      sha256_digest_t)).
Fail Next Obligation.

