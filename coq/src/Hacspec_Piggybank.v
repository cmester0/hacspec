(** This file was automatically generated using Hacspec **)

Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
(* From QuickChick Require Import QuickChick. *)
(* Require Import QuickChickLib. *)

Require Import Hacspec_Lib.

Require Import Hacspec_Concordium.

Inductive piggy_bank_state_hacspec_t :=
| Intact : piggy_bank_state_hacspec_t
| Smashed : piggy_bank_state_hacspec_t.

Definition eqb_piggy_bank_state_hacspec_t (x y : piggy_bank_state_hacspec_t) : bool :=
match x with
   | Intact => match y with | Intact=> true | _ => false end
   | Smashed => match y with | Smashed=> true | _ => false end
   end.

Definition eqb_leibniz_piggy_bank_state_hacspec_t (x y : piggy_bank_state_hacspec_t) : eqb_piggy_bank_state_hacspec_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_piggy_bank_state_hacspec_t : EqDec (piggy_bank_state_hacspec_t) :=
Build_EqDec (piggy_bank_state_hacspec_t) (eqb_piggy_bank_state_hacspec_t) (eqb_leibniz_piggy_bank_state_hacspec_t).

(* Global Instance show_piggy_bank_state_hacspec_t : Show (piggy_bank_state_hacspec_t) := *)
(*  @Build_Show (piggy_bank_state_hacspec_t) (fun x => *)
(*  match x with *)
(*  Intact => ("Intact")%string *)
(*  | Smashed => ("Smashed")%string *)
(*  end). *)
(* Definition g_piggy_bank_state_hacspec_t : G (piggy_bank_state_hacspec_t) := oneOf_ (returnGen Intact) [returnGen Intact;returnGen Smashed]. *)
(* Global Instance gen_piggy_bank_state_hacspec_t : Gen (piggy_bank_state_hacspec_t) := Build_Gen piggy_bank_state_hacspec_t g_piggy_bank_state_hacspec_t. *)


Definition piggy_init_hacspec  : piggy_bank_state_hacspec_t :=
  Intact.

Definition user_address_t := nseq (int8) (usize 32).
(* Instance show_user_address_t : Show (user_address_t) := Build_Show (user_address_t) show. *)
(* Definition g_user_address_t : G (user_address_t) := arbitrary. *)
(* Instance gen_user_address_t : Gen (user_address_t) := Build_Gen user_address_t g_user_address_t. *)

Notation "'piggy_insert_result_t'" := ((result unit unit)) : hacspec_scope.

Definition piggy_insert_hacspec
  (state_0 : piggy_bank_state_hacspec_t)
  : piggy_insert_result_t :=
  match state_0 with
  | Intact => @Ok unit unit (tt)
  | Smashed => @Err unit unit (tt)
  end.

Notation "'context_t'" := ((user_address_t ∏ user_address_t ∏ int64
)) : hacspec_scope.
(* Instance show_context_t : Show (context_t) := *)
(* Build_Show context_t (fun x => *)
(*   let (x, x0) := x in *)
(*   let (x, x1) := x in *)
(*   ( *)
(*     ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string. *)
(* Definition g_context_t : G (context_t) := *)
(* bindGen arbitrary (fun x0 : user_address_t => *)
(*   bindGen arbitrary (fun x1 : user_address_t => *)
(*   bindGen arbitrary (fun x2 : int64 => *)
(*   returnGen (x0,x1,x2)))). *)
(* Instance gen_context_t : Gen (context_t) := Build_Gen context_t g_context_t. *)

Inductive smash_error_t :=
| NotOwner : smash_error_t
| AlreadySmashed : smash_error_t.

Definition eqb_smash_error_t (x y : smash_error_t) : bool :=
match x with
   | NotOwner => match y with | NotOwner=> true | _ => false end
   | AlreadySmashed => match y with | AlreadySmashed=> true | _ => false end
   end.

Definition eqb_leibniz_smash_error_t (x y : smash_error_t) : eqb_smash_error_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_smash_error_t : EqDec (smash_error_t) :=
Build_EqDec (smash_error_t) (eqb_smash_error_t) (eqb_leibniz_smash_error_t).

(* Global Instance show_smash_error_t : Show (smash_error_t) := *)
(*  @Build_Show (smash_error_t) (fun x => *)
(*  match x with *)
(*  NotOwner => ("NotOwner")%string *)
(*  | AlreadySmashed => ("AlreadySmashed")%string *)
(*  end). *)
(* Definition g_smash_error_t : G (smash_error_t) := oneOf_ (returnGen NotOwner) [returnGen NotOwner;returnGen AlreadySmashed]. *)
(* Global Instance gen_smash_error_t : Gen (smash_error_t) := Build_Gen smash_error_t g_smash_error_t. *)


Notation "'piggy_smash_result_t'" := ((
  result piggy_bank_state_hacspec_t smash_error_t)) : hacspec_scope.

Definition piggy_smash_hacspec
  (ctx_1 : context_t)
  (state_2 : piggy_bank_state_hacspec_t)
  : piggy_smash_result_t :=
  let '(owner_3, sender_4, balance_5) :=
    ctx_1 in 
  ifbnd negb ((owner_3) array_eq (sender_4)) : bool
  thenbnd (bind (@Err piggy_bank_state_hacspec_t smash_error_t (NotOwner)) (
      fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  ifbnd negb ((state_2) =.? (Intact)) : bool
  thenbnd (bind (@Err piggy_bank_state_hacspec_t smash_error_t (
        AlreadySmashed)) (fun _ =>  Ok (tt)))
  else (tt) >> (fun 'tt =>
  @Ok piggy_bank_state_hacspec_t smash_error_t (Smashed))).

Definition test_init_hacspec  : bool :=
  (piggy_init_hacspec ) =.? (Intact).

Definition test_insert_intact  : bool :=
  (piggy_insert_hacspec (Intact)) =.? (@Ok unit unit (tt)).

Definition test_insert_smashed  : bool :=
  (piggy_insert_hacspec (Smashed)) =.? (@Err unit unit (tt)).

Definition test_smash_intact
  (owner_6 : user_address_t)
  (balance_7 : int64)
  : bool :=
  let sender_8 : user_address_t :=
    owner_6 in 
  let ctx_9 : (user_address_t ∏ user_address_t ∏ int64) :=
    (owner_6, sender_8, balance_7) in 
  (piggy_smash_hacspec (ctx_9) (Intact)) =.? (
    @Ok piggy_bank_state_hacspec_t smash_error_t (Smashed)).
(* QuickChick ( *)
(*   forAll g_user_address_t (fun owner_6 : user_address_t => forAll g_int64 (fun balance_7 : int64 => test_smash_intact owner_6 balance_7))). *)

Definition test_smash_intact_not_owner
  (owner_10 : user_address_t)
  (sender_11 : user_address_t)
  (balance_12 : int64)
  : bool :=
  let ctx_13 : (user_address_t ∏ user_address_t ∏ int64) :=
    (owner_10, sender_11, balance_12) in 
  ((owner_10) array_eq (sender_11)) || ((piggy_smash_hacspec (ctx_13) (
        Intact)) =.? (@Err piggy_bank_state_hacspec_t smash_error_t (
        NotOwner))).
(* QuickChick ( *)
(*   forAll g_user_address_t (fun owner_10 : user_address_t => forAll g_user_address_t (fun sender_11 : user_address_t => forAll g_int64 (fun balance_12 : int64 => test_smash_intact_not_owner owner_10 sender_11 balance_12)))). *)

Definition test_smash_smashed
  (owner_14 : user_address_t)
  (balance_15 : int64)
  : bool :=
  let sender_16 : user_address_t :=
    owner_14 in 
  let ctx_17 : (user_address_t ∏ user_address_t ∏ int64) :=
    (owner_14, sender_16, balance_15) in 
  (piggy_smash_hacspec (ctx_17) (Smashed)) =.? (
    @Err piggy_bank_state_hacspec_t smash_error_t (AlreadySmashed)).
(* QuickChick ( *)
(*   forAll g_user_address_t (fun owner_14 : user_address_t => forAll g_int64 (fun balance_15 : int64 => test_smash_smashed owner_14 balance_15))). *)




(** * Data types for the crowdfunding contract *)

From Coq Require Import String.
From Coq Require Import List.
From ConCert.Embedding Require Import Ast.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import PCUICTranslate.
From ConCert.Embedding Require Import Prelude.
From ConCert.Embedding Require Import SimpleBlockchain.
From ConCert.Embedding Require Import Utils.
From ConCert.Embedding Require Import TranslationUtils.

Import ListNotations.
From MetaCoq.Template Require Import All.

Import MonadNotation.
Import BaseTypes.
Open Scope list.

Import AcornBlockchain Prelude.Maps.

(** Note that we define the deep embedding (abstract syntax trees) of the data structures and programs using notations. These notations are defined in  [Ast.v] and make use of the "custom entries" feature. *)

(** Brackets like [[\ \]] delimit the scope of data type definitions and like [[| |]] the scope of programs *)

(** Generating names for the data structures. We also add a prefix, corresponsing ti the current module path.  *)
MetaCoq Run
        ( mp_ <- tmCurrentModPath tt ;;
          let mp := (PCUICTranslate.string_of_modpath mp_ ++ "@")%string in
          mkNames mp
             ["ctx" ; "state" ;
              "State" ; "mkState"; "balance" ; "donations" ; "owner";
              "deadline"; "goal"; "done";
              "Res" ; "Error";
              "Msg"; "Donate"; "GetFunds"; "Claim";
              "Action"; "Transfer"; "Empty" ] "_coq").

Import ListNotations.

(** ** Definitions of data structures for the contract *)

Check Ast.inductive.
Definition piggy_bank_state := to_string_name <% piggy_bank_state_hacspec_t %>.
Definition piggy_bank_ctx_owner := Address.
(* Definition piggy_bank_ctx_sender := Address. *)
Definition piggy_bank_ctx_balance := Nat.
(* (user_address_t ∏ user_address_t ∏ int64) *)

Check Ctx_contract_address.

(** The internal state of the contract *)
Definition state_syn : global_dec :=
  [\ record State := 
     mkState {
         state : Bool ; (* PiggyBankState *)
         owner : piggy_bank_ctx_owner ;
         balance : Money } \].

(** Unquoting the definition of a record *)
Set Nonrecursive Elimination Schemes.

MetaCoq Unquote Inductive (global_to_tc state_syn).

(* Definition context_to_coq_state : piggy_bank_state_hacspec_t ∏ context_t -> State_coq. *)
(* Proof. *)
(*   intros [? [[]]]. *)
(*   apply mkState_coq. *)
(*   - apply p. *)
(*   - apply (nat_from_be_bytes u). *)
(*   - apply (nat_from_be_bytes u0). *)
(*   - apply (int64_to_nat i). *)
(* Defined. *)

(** As a result, we get a new Coq record [State_coq] *)

Definition msg_syn :=
  [\ data Msg =
       Donate [_]
     | GetFunds [_]
     | Claim [_] \].

MetaCoq Unquote Inductive (global_to_tc msg_syn).

(** Custom notations for patterns, projections and constructors *)
Module Notations.

  Notation "'ctx_from' a" := [| {eConst (to_string_name <% Ctx_from %>)} {a} |]
                               (in custom expr at level 0).
  Notation "'ctx_contract_address' a" :=
    [| {eConst (to_string_name <% Ctx_contract_address %>)} {a} |]
      (in custom expr at level 0).
  Notation "'amount' a" := [| {eConst (to_string_name <% Ctx_amount %>)} {a} |]
                             (in custom expr at level 0).


  (** Projections *)
  Notation "'balance' a" :=
    [| {eConst balance} {a} |]
      (in custom expr at level 0).
  Notation "'donations' a" :=
    [| {eConst donations} {a} |]
      (in custom expr at level 0).
  Notation "'owner' a" :=
    [| {eConst owner} {a} |]
      (in custom expr at level 0).
  Notation "'deadline' a" :=
    [| {eConst deadline} {a} |]
      (in custom expr at level 0).
  Notation "'goal' a" :=
    [| {eConst goal} {a} |]
      (in custom expr at level 0).
  Notation "'done' a" :=
    [| {eConst done} {a} |]
      (in custom expr at level 0).


  Notation "'Nil'" := [| {eConstr List "nil"} {eTy (tyInd SActionBody)} |]
                        (in custom expr at level 0).

  Notation " x ::: xs" := [| {eConstr List "cons"} {eTy (tyInd SActionBody)} {x} {xs} |]
                            ( in custom expr at level 0).

  Notation "[ x ]" := [| {eConstr List "cons"} {eTy (tyInd SActionBody)} {x} Nil |]
                        ( in custom expr at level 0,
                            x custom expr at level 1).
  (** Constructors. [Res] is an abbreviation for [Some (st, [action]) : option (State * list ActionBody)] *)

  Definition actions_ty := [! List SActionBody !].

  Notation "'Result'" := [! Prod State (List SActionBody) !]
                           (in custom type at level 2).


  Definition mk_res a b := [| {eConstr "option" "Some"}
                                {eTy [! Result !]}
                                ({eConstr Prod "pair"} {eTy (tyInd State)}
                                                       {eTy actions_ty} {a} {b}) |].
  Notation "'Res' a b" := (mk_res a b)
                            (in custom expr at level 2,
                                a custom expr at level 4,
                                b custom expr at level 4).

  Notation "'mkState' a" :=
    [| {eConstr State mkState} {a} |]
      (in custom expr at level 0,
          a custom expr at level 1).

  Notation "'Transfer' a b" :=
    [| {eConstr SActionBody "Act_transfer"} {b} {a} |]
      (in custom expr at level 0,
          a custom expr at level 1,
          b custom expr at level 1).

  Notation "'Empty'" := (eConstr Action Empty)
                          (in custom expr at level 0).

  (** New global context with the constants defined above (in addition to the ones defined in the Oak's "StdLib") *)

  Import Maps.

  Definition Σ' :=
    StdLib.Σ ++ [ Prelude.AcornMaybe;
                  state_syn;
                  msg_syn;
                  addr_map_acorn;
                  AcornBlockchain.SimpleChainAcorn;
                  AcornBlockchain.SimpleContractCallContextAcorn;
                  AcornBlockchain.SimpleActionBodyAcorn;
                  gdInd "Z" 0 [("Z0", []); ("Zpos", [(None,tyInd "positive")]);
                               ("Zneg", [(None,tyInd "positive")])] false].

End Notations.


Import Prelude.

(** Generating string constants for variable names *)

MetaCoq Run (mkNames "" ["c";"s";"e";"m";"v";"dl"; "g"; "chain";
                     "tx_amount"; "bal"; "own"; "isdone" ; "sender" ; "st" ;
                     "accs"; "now";
                     "newstate"; "newmap"; "cond"] "").

Definition SCtx := to_string_name <% SimpleContractCallContext_coq %>.

(**  We develop a deep embedding of a crowdfunding contract and prove some of its functional correctness properties using the corresponding shallow embedding *)

From ConCert.Embedding Require Import Ast.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import PCUICTranslate.
From ConCert.Embedding Require Import Prelude.
From ConCert.Embedding Require Import SimpleBlockchain.
From ConCert.Embedding Require Import TranslationUtils.
(* From ConCert.Examples.Crowdfunding Require Import CrowdfundingData. *)
From ConCert.Utils Require Import Automation.

From Coq Require Import String.
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import ssrbool.
From Coq Require Import Lia.

Import ListNotations.
From MetaCoq.Template Require Import All.

Import MonadNotation.
Import BaseTypes StdLib.
Open Scope list.

Import Prelude.Maps.

(** Note that we define the deep embedding (abstract syntax trees) of the data structures and programs using notations. These notations are defined in  [Ast.v] and make use of the "custom entries" feature. *)

(** Brackets like [[\ \]] delimit the scope of data type definitions and like [[| |]] the scope of programs *)


(** * The crowdfunding contract *)

Module CrowdfundingContract.

  Import AcornBlockchain.

  (** ** AST of the [init] function *)
  Module Init.
    Import Notations.

    Import Notations.
    Definition crowdfunding_init : expr :=
      [| mkState False 0 0z |].
    
    MetaCoq Unquote Definition init :=
      (expr_to_tc Σ' (indexify nil crowdfunding_init)).

    Check init.
 End Init.

(** ** AST of the [receive] function *)
(* Receive becomes Insert *)
Module Receive.
  Import Notations.

   (** We specialise some polymorphic constructors to avoid writing types all the time *)
   Notation "'#Just' a" :=
     [| {eConstr (to_string_name <% option %>) "Some"}  {eTy [! Result!]} {a}|]
       (in custom expr at level 0, a custom expr at level 1).

   Notation "'#Pair' a b" := [| {eConstr Prod "pair"}
                               {eTy (tyInd State)}
                               {eTy actions_ty} {a} {b} |]
                           (in custom expr at level 0,
                               a custom expr at level 1,
                               b custom expr at level 1).

   Notation "'#Nothing'" := (eApp (eConstr (to_string_name <% option %>) "None") (eTy [!Result!]))
                             (in custom expr at level 0).

   Definition SCtx := to_string_name <% SimpleContractCallContext_coq %>.
   Definition SChain := to_string_name <% SimpleChain_coq %>.

   Check piggy_insert_hacspec.
   
   Definition crowdfunding : expr :=
     [| \chain : SChain =>  \c : SCtx => \m : Msg => \s : State =>
          let bal : Money := balance s in
          let tx_amount : Money := amount c in
          let sender : Address := ctx_from c in
          let own : Address := owner s in
          (* let st : Bool := state s in *)
          (* #Just (#Pair (mkState False own (tx_amount + bal)) Nil) *)
          (case False : Bool return Maybe Result of
          | False (* Intact *) -> #Just (#Pair (mkState False own (tx_amount + bal)) Nil)
                              
          (* (* (* (Ok unit unit (tt)) *) *) *)
          | True (* Smashed *) -> #Nothing
          (* (* (* (Err unit unit (tt)) *) *) *)
          )               
     |].

   MetaCoq Unquote Definition receive :=
    (expr_to_tc Σ' (indexify nil crowdfunding)).

  

  End Receive.
End CrowdfundingContract.



(** * Integration with the execution framework, properties of [crowdfunding] *)
From ConCert.Embedding Require Import Misc.
From ConCert.Embedding Require Import Notations.
From ConCert.Embedding Require Import PCUICtoTemplate.
From ConCert.Embedding Require Import PCUICTranslate.
From ConCert.Embedding Require Import SimpleBlockchain.

From Coq Require Import String.
From Coq Require Import Basics.
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import ssrbool.
From Coq Require Import Program.Tactics.

From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import ResultMonad.

Import ListNotations.

Open Scope list.
(* Import AcornBlockchain CrowdfundingContract CrowdfundingProperties. *)

(* Definition expr_to_tc Σ := compose trans (expr_to_term Σ). *)
(* Definition type_to_tc := compose trans type_to_term. *)
(* Definition global_to_tc := compose trans_minductive_entry trans_global_dec. *)

Global Program Instance CB : ChainBase :=
  build_chain_base nat Nat.eqb _ _ _ _ Nat.odd. (* Odd addresses are addresses of contracts :) *)
Next Obligation.
  eapply NPeano.Nat.eqb_spec.
Defined.

Definition to_chain (sc : SimpleChain_coq) : Chain :=
  let '(Build_chain_coq h s fh) := sc in build_chain h s fh.

Definition of_chain (c : Chain) : SimpleChain_coq :=
  let '(build_chain h s fh) := c in Build_chain_coq h s fh.

Definition to_action_body (sab : SimpleActionBody_coq) : ActionBody :=
  match sab with
  | Act_transfer addr x => act_transfer addr x
  end.

Definition to_contract_call_context (scc : SimpleContractCallContext_coq) : ContractCallContext :=
  let '(Build_ctx_coq origin from contr_addr contr_bal am) := scc in
  build_ctx origin from contr_addr contr_bal am.

Definition of_contract_call_context (cc : ContractCallContext) : SimpleContractCallContext_coq :=
  let '(build_ctx origin from contr_addr contr_bal am) := cc in
  Build_ctx_coq origin from contr_addr contr_bal am.

Import Serializable Prelude.Maps.

Section Serialize.
  Hint Rewrite to_list_of_list of_list_to_list : hints.
  Global Program Instance addr_map_serialize : Serializable addr_map_coq :=
    {| serialize m := serialize (to_list m);
       deserialize l := option_map of_list (deserialize l); |}.
  Next Obligation.
    intros. cbn. rewrite deserialize_serialize. cbn.
    now autorewrite with hints.
  Defined.

  Global Instance State_serializable : Serializable State_coq :=
    Derive Serializable State_coq_rect<mkState_coq>.

  Global Instance Msg_serializable : Serializable Msg_coq :=
    Derive Serializable Msg_coq_rect<Donate_coq, GetFunds_coq, Claim_coq>.

End Serialize.

(** ** Wrappers *)
Section Wrappers.
  Definition Setup := (nat * Z)%type.    
    
  Definition init_wrapper (f : State_coq):
    Chain -> ContractCallContext -> Setup -> option State_coq
    := fun c cc setup => Some (f).

  Definition wrapped_init
    : Chain -> ContractCallContext -> Setup -> option State_coq
    := init_wrapper CrowdfundingContract.Init.init.

    Definition receive_wrapper
             (f : SimpleChain_coq ->
                  SimpleContractCallContext_coq ->
                   Msg_coq -> State_coq -> option (State_coq * list SimpleActionBody_coq)) :
    Chain -> ContractCallContext ->
    State_coq -> option Msg_coq -> option (State_coq * list ActionBody) :=
    fun ch cc st msg => match msg with
                       Some msg' => option_map (fun '(st0,acts) => (st0, map to_action_body acts)) (f (of_chain ch) (of_contract_call_context cc) msg' st)
                     | None => None
                     end.

  Definition wrapped_receive
    : Chain -> ContractCallContext -> State_coq -> option Msg_coq -> option (State_coq * list ActionBody)
    := receive_wrapper CrowdfundingContract.Receive.receive.

End Wrappers.
  
Definition cf_contract : Contract Setup Msg_coq State_coq :=
  build_contract wrapped_init wrapped_receive.
