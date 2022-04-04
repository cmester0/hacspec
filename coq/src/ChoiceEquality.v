From mathcomp Require Import choice.

From Crypt Require Import choice_type.

Class ChoiceEquality := {
    T : Type ;
    ct : choice_type ;
    ChoiceEq : Choice.sort (chElement ct) = T ;
  }.

Definition ct_T {ce : ChoiceEquality} (x : @ct ce) : @T ce :=
  eq_rect (Choice.sort (chElement (@ct ce))) id x (@T ce) ChoiceEq.

Definition T_ct {ce : ChoiceEquality} (x : @T ce) : @ct ce :=
  eq_rect_r id x ChoiceEq.

Theorem ct_T_id : forall {ce : ChoiceEquality} t, ct_T (T_ct t) = t.
Proof (fun ce => rew_opp_r id (@ChoiceEq ce)). 

Theorem T_ct_id : forall {ce : ChoiceEquality} t, T_ct (ct_T t) = t.
Proof (fun ce => rew_opp_l id (@ChoiceEq ce)).

(* Local Coercion T : ChoiceEquality >-> Sortclass. *)
(* Local Coercion ct : ChoiceEquality >-> choice_type. *)
