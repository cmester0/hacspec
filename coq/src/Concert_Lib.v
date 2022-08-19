Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import Morphisms ZArith.
From Coq Require Import List.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.

From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.

Require Import Hacspec_Concordium.
Export Hacspec_Concordium.

Global Program Instance int_serializable {ws : WORDSIZE} : Serializable int :=
  {| serialize m := (serialize (unsigned m)) ;
    deserialize l := option_map (fun (x : Z) => @repr ws x) (deserialize l) |}.
Next Obligation.
  intros. cbn. rewrite deserialize_serialize. cbn. rewrite repr_unsigned. reflexivity.
Defined.

Global Program Instance nseq_serializable len : Serializable (nseq int8 len) :=
  {| serialize m := (serialize (nat_from_be_bytes m)) ;
    deserialize l := option_map (fun (x : nat) => nat_to_be_bytes x) (deserialize l) |}.
Next Obligation.
  intros. cbn. rewrite deserialize_serialize. cbn. rewrite nat_to_from_be_bytes. reflexivity.
Defined.

Global Program Instance nseq_countable len : countable.Countable (nseq int8 len) :=
{|
    countable.encode := fun X : nseq int8 _ => countable.encode (nat_from_be_bytes X);
    countable.decode := fun H : positive => option_map (@nat_to_be_bytes _) (countable.decode H : option nat);
|}.
Next Obligation.
  intros.
  rewrite countable.decode_encode.
  cbn.
  now rewrite nat_to_from_be_bytes.
Qed.

Instance BaseTypes : ChainBase := {|
    Address := nseq int8 (usize 32);
    address_eqb a b := a =.? b ;
    address_eqb_spec a b := Bool.iff_reflect (a = b) (a array_eq b) (symmetry (eqb_leibniz a b));
    (* address_eqdec x y := (EqDecIsDecidable x y); *)
    address_countable := nseq_countable _;
    address_serializable := nseq_serializable _;
    address_is_contract := (fun x => Nat.even (nat_from_be_bytes x)); |}.

(* Definition context_t_from_context (ctx : ContractCallContext) : context_t := *)
(*   (ctx.(ctx_from), ctx.(ctx_origin), repr (ctx.(ctx_amount))). *)

(* Definition accept (ctx : ContractCallContext) := act_transfer ctx.(ctx_origin) ctx.(ctx_amount). *)

(* Definition has_action_t := ActionBody. *)

(* Definition action_body_t := ActionBody. *)
(* Definition list_action_t := list ActionBody. *)
(* Definition ACT_TRANSFER (p : Address ∏ int64) := act_transfer (fst p) (unsigned (snd p)).   *)
(* Instance d_ab : Default ActionBody := {| default := act_transfer (array_new_ (default : int8) 32) 0 |}. *)

Definition to_action_body (ctx : ContractCallContext) (y : has_action_t) : ActionBody :=
  match y with
  | (Accept _) => act_transfer (ctx.(ctx_from)) (ctx.(ctx_amount))
  | (SimpleTransfer (ua, i)) => act_transfer (ua) (i)
  end.
Instance default_has_action : Default has_action_t := {| default := Accept tt |}.

Definition to_action_body_list (ctx : ContractCallContext) {X} : option (X ∏ list has_action_t) -> option (X ∏ list ActionBody)  :=
  option_map (fun '(x, y) => (x, List.map (to_action_body ctx) y)).
