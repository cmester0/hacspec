(** This file was automatically generated using Hacspec **)

Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.

Require Import ConCertLib.
From ConCert.Utils Require Import Extras.
From ConCert.Utils Require Import Automation.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ContractCommon.
From Coq Require Import Morphisms ZArith Basics.
Open Scope Z.
Set Nonrecursive Elimination Schemes.
Definition Setup := unit.
Require Import Hacspec_Lib.
Export Hacspec_Lib.

Require Import Hacspec_Concordium.
Export Hacspec_Concordium.

Inductive piggy_bank_state_hacspec_t :=
| Intact : piggy_bank_state_hacspec_t
| Smashed : piggy_bank_state_hacspec_t.
Global Instance serializable_piggy_bank_state_hacspec_t : Serializable piggy_bank_state_hacspec_t :=
  Derive Serializable piggy_bank_state_hacspec_t_rect<Intact,Smashed>.

Definition eqb_piggy_bank_state_hacspec_t (x y : piggy_bank_state_hacspec_t) : bool :=
match x with
   | Intact => match y with | Intact=> true | _ => false end
   | Smashed => match y with | Smashed=> true | _ => false end
   end.

Definition eqb_leibniz_piggy_bank_state_hacspec_t (x y : piggy_bank_state_hacspec_t) : eqb_piggy_bank_state_hacspec_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_piggy_bank_state_hacspec_t : EqDec (piggy_bank_state_hacspec_t) :=
  Build_EqDec (piggy_bank_state_hacspec_t) (eqb_piggy_bank_state_hacspec_t) (eqb_leibniz_piggy_bank_state_hacspec_t).


Definition user_address_t := nseq (int8) (usize 32).

Notation "'context_t'" := ((user_address_t ∏ user_address_t ∏ int64
)) : hacspec_scope.

Notation "'context_state_hacspec_t'" := ((
  context_t ∏
  piggy_bank_state_hacspec_t
)) : hacspec_scope.

Definition piggy_init_hacspec : piggy_bank_state_hacspec_t :=
  Intact.


Definition piggy_init (ctx_0 : context_t): context_state_hacspec_t :=
  (ctx_0, piggy_init_hacspec ).
Definition State := 
    context_state_hacspec_t.
  Definition PiggyBank_State (chain : Chain) (ctx : ContractCallContext) (_ : Setup) : option State :=
  Some (piggy_init (ctx.(ctx_from), ctx.(ctx_origin), repr (ctx.(ctx_amount)))).


Notation "'piggy_insert_result_t'" := ((result unit unit)) : hacspec_scope.

Definition piggy_insert_hacspec
  (ctx_1 : context_t)
  (amount_2 : int64)
  (state_3 : piggy_bank_state_hacspec_t): piggy_insert_result_t :=
  match state_3 with
  | Intact => @Ok unit unit (tt)
  | Smashed => @Err unit unit (tt)
  end.


Definition piggy_insert
  (ctx_state_4 : context_state_hacspec_t)
  (amount_5 : int64): (option context_state_hacspec_t) :=
  let '(ctx_6, state_7) :=
    ctx_state_4 in 
  let '(a_8, c_9, balance_10) :=
    ctx_6 in 
  let _ : int32 :=
    accept_hacspec  in 
  let temp_11 : (result unit unit) :=
    piggy_insert_hacspec (ctx_6) (amount_5) (state_7) in 
  bind (match temp_11 with
    | Ok _ => @Some unit (tt)
    | Err _ => @None unit
    end) (fun _ =>  @Some context_state_hacspec_t ((
        (a_8, c_9, (balance_10) .+ (amount_5)),
        state_7
      ))).

Definition insert (amount : int64)(st : State) :=
  piggy_insert st amount.


Inductive smash_error_t :=
| NotOwner : smash_error_t
| AlreadySmashed : smash_error_t.
Global Instance serializable_smash_error_t : Serializable smash_error_t :=
  Derive Serializable smash_error_t_rect<NotOwner,AlreadySmashed>.

Definition eqb_smash_error_t (x y : smash_error_t) : bool :=
match x with
   | NotOwner => match y with | NotOwner=> true | _ => false end
   | AlreadySmashed => match y with | AlreadySmashed=> true | _ => false end
   end.

Definition eqb_leibniz_smash_error_t (x y : smash_error_t) : eqb_smash_error_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_smash_error_t : EqDec (smash_error_t) :=
  Build_EqDec (smash_error_t) (eqb_smash_error_t) (eqb_leibniz_smash_error_t).


Notation "'piggy_smash_result_t'" := ((
  result piggy_bank_state_hacspec_t smash_error_t)) : hacspec_scope.

Definition piggy_smash_hacspec
  (ctx_12 : context_t)
  (state_13 : piggy_bank_state_hacspec_t): piggy_smash_result_t :=
  let '(owner_14, sender_15, balance_16) :=
    ctx_12 in 
  ifbnd negb ((owner_14) array_eq (sender_15)) : bool
  thenbnd (bind (@Err piggy_bank_state_hacspec_t smash_error_t (NotOwner)) (
      fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  ifbnd negb ((state_13) =.? (Intact)) : bool
  thenbnd (bind (@Err piggy_bank_state_hacspec_t smash_error_t (
        AlreadySmashed)) (fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  @Ok piggy_bank_state_hacspec_t smash_error_t (Smashed))).


Definition piggy_smash
  (ctx_state_17 : context_state_hacspec_t): (option context_state_hacspec_t) :=
  let '(ctx_18, state_19) :=
    ctx_state_17 in 
  let '(a_20, c_21, _) :=
    ctx_18 in 
  let _ : int32 :=
    accept_hacspec  in 
  let smash_22 : (result piggy_bank_state_hacspec_t smash_error_t) :=
    piggy_smash_hacspec (ctx_18) (state_19) in 
  bind (match smash_22 with
    | Ok a_23 => @Some piggy_bank_state_hacspec_t (a_23)
    | Err b_24 => @None piggy_bank_state_hacspec_t
    end) (fun new_state_25 =>  @Some context_state_hacspec_t ((
        (a_20, c_21, @repr WORDSIZE64 0),
        new_state_25
      ))).

Definition smash (st : State) :=
  piggy_smash st.


Inductive Msg :=
| INSERT
| SMASH.
Global Instance Msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect<INSERT,SMASH>.
Definition PiggyBank_receive (chain : Chain) (ctx : ContractCallContext) (state : State) (msg : option Msg) : option (State * list ActionBody) :=
  match msg with
  | Some INSERT => option_map (fun x => (x , [])) (insert (repr (ctx.(ctx_amount))) state)
  | Some SMASH => option_map (fun x => (x , [act_transfer (fst (fst (fst state))) (snd (fst state))])) (smash state)
  | None => None
  end.

Definition piggyBank_contract : Contract Setup Msg State :=
  build_contract PiggyBank_State PiggyBank_receive.

  
(** * Functional correctness *)
Lemma piggybank_correct {prev_state next_state acts msg chain ctx} :
  snd prev_state = Intact -> PiggyBank_receive chain ctx prev_state msg = Some (next_state, acts) ->
  match msg with
    | Some m => 
      match m with
      | INSERT => ( (snd (fst prev_state)) .+ repr ctx.(ctx_amount)) = (snd (fst next_state))
      | SMASH =>
          fst (fst (fst prev_state)) = ctx.(ctx_from)
          -> snd next_state = Smashed
            /\ snd (fst next_state) = 0
            /\ acts = [act_transfer (fst (fst (fst prev_state))) (snd (fst prev_state))]
      end
    | None => False
  end.
Proof.
  intros H1 H2. 
  unfold PiggyBank_receive in H2. 
  destruct msg(* ;  *)
  (* unfold piggyBank in H2 *).
  destruct m.
  - destruct prev_state. cbn in *. rewrite H1 in H2. unfold insert in *.
    cbn in H2. destruct p as [[]]. cbn in *. destruct next_state as [[]].
    cbn in *.
    inversion H2. subst.
    Set Printing Coercions.
    reflexivity.    
  - intros H3. destruct prev_state as [[[]]]. cbn in *. rewrite H1 in H2. destruct next_state as [[[]]]. cbn in H2. subst. cbn in *.
    destruct negb in H2.
    + cbn in *.
      discriminate.
    + cbn in *.
      inversion H2. subst.
      repeat split.
  - discriminate.
Qed.
