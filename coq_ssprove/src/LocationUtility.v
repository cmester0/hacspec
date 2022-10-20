From Coq Require Import ZArith List.
From Crypt Require Import choice_type Package.
Import PackageNotation.
From Crypt Require Import pkg_interpreter.
From extructures Require Import ord fset fmap.
Require Import Hacspec_Lib_Comparable.

Require Import Coq.Logic.FunctionalExtensionality.

(*** Location *)

(* Fixpoint Inb {A : Type} `{EqDec A} (a:A) (l:list A) : bool := *)
(*   match l with *)
(*   | nil => false *)
(*   | cons b m => (eqb b a) || Inb a m *)
(*   end. *)

Definition loc_eqType :=
  (@eqtype.tag_eqType choice_type_eqType (fun _ : choice_type => ssrnat.nat_eqType)).

Definition location_eqb (ℓ ℓ' : Location) :=
  andb (@eqtype.eq_op ssrnat.nat_eqType (projT2 ℓ) (projT2 ℓ'))
       (@eqtype.eq_op _ (projT1 ℓ) (projT1 ℓ')).
       (* (@eqtype.eq_op loc_eqType ℓ ℓ'). *)

(* Axiom location_is_types : (forall l1 l2 : Location , *)
(*                               is_true (eqb (ssrfun.tagged l1) (ssrfun.tagged l2)) -> *)
(*                               is_true (eqtype.eq_op (ssrfun.tag l1) (ssrfun.tag l2))). *)


Definition location_eqbP : forall (l1 l2 : Location),
    @location_eqb (l1) (l2)
    = (@eqtype.eq_op
         (@eqtype.tag_eqType choice_type_eqType
                             (fun _ : choice_type => ssrnat.nat_eqType)) l1 l2).
Proof.
  intros.

  unfold location_eqb.
  unfold eqtype.eq_op.

  cbn.
  rewrite ssrnat.eqnE.
  unfold eqtype.tag_eq.
  unfold eqtype.tagged_as.
  unfold ssrfun.tag.
  unfold ssrfun.tagged.

  rewrite Bool.andb_comm.
  
  unfold eq_rect_r, eq_rect.

  set (eqtype.eq_op _ _) at 2.
  replace (choice_type_eq _ _) with b by reflexivity.
  
  destruct b eqn:b_eq ; subst b.
  - f_equal.
    case eqtype.eqP ; intros.
    + rewrite e in *.
      unfold eq_sym.
      reflexivity.
    + exfalso.
      apply (ssrbool.elimT eqtype.eqP) in b_eq.
      apply n.
      eapply b_eq.
  - reflexivity.
Qed.

Theorem is_true_split_or : forall a b, is_true (a || b) = (is_true a \/ is_true b).
Proof.
  intros.
  rewrite boolp.propeqE.
  symmetry.
  apply (ssrbool.rwP ssrbool.orP).
Qed.  
Theorem is_true_split_and : forall a b, is_true (a && b) = (is_true a /\ is_true b).
Proof.
  intros.
  rewrite boolp.propeqE.
  symmetry.
  apply (ssrbool.rwP ssrbool.andP).
Qed.  




Theorem LocsSubset : (forall {A} (L1 L2 : list A) (a : A),
                         List.incl L1 L2 ->
                         List.In a L1 ->
                         List.In a L2).
  intros.
  induction L1 as [ | a0 L ] ; cbn in *.
  - contradiction.
  - destruct (List.incl_cons_inv H).
    destruct H0.
    + subst.
      assumption.
    + apply IHL ; assumption.
Qed.

(* Theorem in_bool_iff : forall {A : Type} `{EqDec A} (a:A) (l:list A), is_true (Inb a l) <-> List.In a l. *)
(*   induction l ; cbn. *)
(*   - rewrite boolp.falseE. *)
(*     reflexivity. *)
(*   - cbn. *)
(*     rewrite is_true_split_or.     *)
(*     apply ZifyClasses.or_morph. *)
(*     apply eqb_leibniz. *)
(*     apply IHl. *)
(* Qed. *)


Lemma location_eqb_sound : forall ℓ ℓ' : Location, is_true (location_eqb ℓ ℓ') <-> ℓ = ℓ'.
Proof.
  intros.
  rewrite location_eqbP.
  (* unfold location_eqb. *)
  pose (@eqtype.eqP loc_eqType).
  unfold eqtype.Equality.axiom in a.
  pose (ssrbool.elimT).
  pose (@eqtype.tag_eqP ).

  split.
  
  pose (Couplings.reflection_nonsense (@eqtype.tag_eqType choice_type_eqType (fun _ : choice_type => ssrnat.nat_eqType)) ℓ ℓ').

  
  (* rewrite is_true_split_and. *)
  (* intros [_].   *)
  apply e.  
  (* apply H. *)
  intros. subst.
  (* rewrite eqb_refl. *)
  apply eqtype.eq_refl.
Qed.

Global Program Instance location_eqdec: EqDec (Location) := {
    eqb := location_eqb;
    eqb_leibniz := location_eqb_sound;
  }.

Definition location_ltb : Location -> Location -> bool :=
  (tag_leq (I:=choice_type_ordType) (T_:=fun _ : choice_type => nat_ordType)).

Definition location_ltb_simple : Location -> Location -> bool :=
  fun x y => ltb (projT2 x) (projT2 y).

Global Instance location_comparable : Comparable (Location) :=
  eq_dec_lt_Comparable location_ltb.

Definition le_is_ord_leq : forall s s0 : nat_ordType,
    eqtype.eq_op s s0 = false -> ltb s s0 = (s <= s0)%ord.
Proof.
  intros s s0.
  unfold ltb , nat_comparable , Nat.ltb.
  intros e.
  
  generalize dependent s.
  induction s0 ; intros.
  * destruct s ; easy.
  * destruct s. reflexivity.
    (* unfold Nat.leb ; fold Nat.leb. *)
    cbn.
    cbn in IHs0.
    rewrite IHs0.
    reflexivity.
    assumption.
Qed.

Definition opsig_eqb (ℓ ℓ' : opsig) : bool :=
  andb (@eqtype.eq_op ssrnat.nat_eqType (fst ℓ) (fst ℓ'))
       (andb (@eqtype.eq_op _ (fst (snd ℓ)) (fst (snd ℓ')))
             (@eqtype.eq_op _ (snd (snd ℓ)) (snd (snd ℓ')))).

Lemma opsig_eqb_sound : forall ℓ ℓ' : opsig, is_true (opsig_eqb ℓ ℓ') <-> ℓ = ℓ'.
Proof.
  intros.
  
  destruct ℓ as [? []] , ℓ' as [? []]. 
  setoid_rewrite is_true_split_and.
  rewrite is_true_split_and.
  unfold fst, snd in *.

  transitivity (i = i0 /\ c = c1 /\ c0 = c2).
  {
    apply ZifyClasses.and_morph.
    symmetry.
    apply (ssrbool.rwP (@eqtype.eqP ssrnat.nat_eqType i i0)).
    apply ZifyClasses.and_morph.
    symmetry.
    apply (ssrbool.rwP (@eqtype.eqP _ c c1)).
    symmetry.
    apply (ssrbool.rwP (@eqtype.eqP _ c0 c2)).
  }
  
  split ; [ intros [? []] | intros H ; inversion H ] ; subst ; easy.
Qed.

Global Program Instance opsig_eqdec: EqDec (opsig) := {
    eqb := opsig_eqb;
    eqb_leibniz := opsig_eqb_sound;
  }.

Theorem loc_compute : forall l : (@sigT choice_type (fun _ : choice_type => nat)), forall n : list (@sigT choice_type (fun _ : choice_type => nat)), List.In l n <-> is_true (ssrbool.in_mem l (@ssrbool.mem _ (seq.seq_predType (Ord.eqType (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType)))) n)).
Proof.
  intros.
  apply (ssrbool.rwP (@xseq.InP (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType)) _ _)).
    
  (* induction n. *)
  (* - cbn. split ; easy. *)
  (* - cbn. *)

  (*   setoid_rewrite seq.in_cons.     *)
  (*   rewrite is_true_split_or. *)
  (*   rewrite IHn. *)

  (*   apply or_iff_compat_r. *)
  (*   rewrite eqtype.eq_sym. *)
  (*   apply (ssrbool.rwP (@eqtype.eqP loc_eqType a l)). *)
Qed.

Theorem opsig_compute :
  forall l : opsig,
  forall n : Interface,
        List.In l n <-> is_true (ssrbool.in_mem l (@ssrbool.mem _ (fset_predType
             (prod_ordType nat_ordType
                           (prod_ordType choice_type_ordType choice_type_ordType))) n)).
Proof.
  intros.
  cbn.
  apply (ssrbool.rwP (@xseq.InP (
             (prod_ordType nat_ordType
                           (prod_ordType choice_type_ordType choice_type_ordType))) _ _)).
    
  (* unfold ssrbool.in_mem. *)
  (* unfold ssrbool.pred_of_mem. *)
  (* unfold ssrbool.mem ; cbn. *)
  
  (* set (k := FSet.fsval n). *)
  (* induction k. *)
  (* - cbn. split ; easy. *)
  (* - cbn. *)

  (*   setoid_rewrite seq.in_cons.     *)
  (*   rewrite is_true_split_or. *)

  (*   rewrite IHk. *)
    
  (*   apply or_iff_compat_r. *)

  (*   rewrite eqtype.eq_sym. *)
  (*   apply (ssrbool.rwP (@eqtype.eqP _ a l)). *)
Qed.
  
(* Theorem in_bool_eq : forall {A : Type} `{EqDec A} (a:A) (l:list A), is_true (Inb a l) = List.In a l. *)
(*   intros. *)
(*   rewrite boolp.propeqE. apply in_bool_iff. *)
(* Qed. *)

(* Fixpoint incl_sort_compute A `{EqDec A} (l1 l2 : list A) : bool := *)
(*   match l1 with *)
(*   | nil => true *)
(*   | (x :: xs) => (andb (Inb x l2) (incl_sort_compute A xs l2)) *)
(*   end. *)

Fixpoint incl_expand A `{EqDec A} (l1 l2 : list A) : Prop :=
  match l1 with
  | nil => True
  | (x :: xs) => In x l2 /\ incl_expand A xs l2
  end.

(* Proof. *)
(*   induction l1. *)
(*   - exact true. *)
(*   - exact (andb (Inb a l2) (IHl1)).       *)
(* Defined. *)
 
(* Definition incl_fset_sort_compute (l1 l2 : {fset Location}) : bool. *)
(* Proof. *)
(*   destruct l1 as [l1]. *)
(*   induction l1. *)
(*   - exact true. *)
(*   - assert (is_true (path.sorted Ord.lt l1)). *)
(*     { *)
(*       pose (path.drop_sorted). *)
(*       specialize i0 with (n := 1) (s := a :: l1). *)
(*       rewrite seq.drop1 in i0. *)
(*       unfold seq.behead in i0. *)
(*       apply i0. *)
(*       apply i. *)
(*     } *)
(*     exact (andb (Inb a l2) (IHl1 H)).       *)
(* Defined. *)

Theorem loc_in_remove_fset : forall a (l : list Location), List.In a l <-> List.In a (fset l).
Proof.
  intros.
  do 2 rewrite loc_compute.
  unfold fset ; rewrite ssreflect.locked_withE.
  cbn.
  rewrite (@path.mem_sort (Ord.eqType
                             (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType))) (tag_leq (I:=choice_type_ordType) (T_:=fun _ : choice_type => nat_ordType)) (@seq.undup
                                                                                                                                                                                     (Ord.eqType
                                                                                                                                                                                        (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType)))
                                                                                                                                                                                     l)).
  
  generalize dependent a.
  induction l ; intros.
  + easy.
  + cbn.

    rewrite (@seq.in_cons (Ord.eqType
                             (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType))) a l).
    rewrite is_true_split_or.

    match goal with
    | [ |- context[match ?x with | true => _ | false => _ end] ] =>
        destruct x eqn:so
    end.
    * rewrite <- IHl.
      split.
      -- intros [].
         ++ apply Couplings.reflection_nonsense in H.
            subst.
            apply so.
         ++ apply H.
      -- intros.
         right.
         apply H.
    * split.
      -- intros [].
         ++ apply Couplings.reflection_nonsense in H.
            subst.
            apply seq.mem_head.
         ++ apply seq.mem_drop with (n0 := 1%nat).
            cbn.
            rewrite seq.drop0.
            apply IHl.
            apply H.
      -- intros.
         destruct (eqtype.eq_op) eqn:so2.
         ++ left.
            reflexivity.
         ++ right.
            unfold ssrbool.in_mem in H.
            unfold ssrbool.pred_of_mem in H.
            unfold ssrbool.mem in H.
            cbn in H.
            cbn in so2.
            rewrite so2 in H.
            cbn in H.

            apply IHl.
            apply H.
Qed.

(* Theorem has_is_in : forall A (a : A) (l : list A), List.In a l = is_true (seq.has (fun x => a = x) l). *)

Theorem opsig_in_remove_fset : forall a (l : list opsig), List.In a l <-> List.In a (fset l).
Proof.
  intros.
  rewrite opsig_compute.

  transitivity (is_true (ssrbool.in_mem a (@ssrbool.mem _ (seq.seq_predType (prod_ordType _ _)) l))).
  2:{
    setoid_rewrite <- seq.has_pred1.
    now setoid_rewrite has_fset.
  }

  Set Printing Implicit.
  
  induction l.
  - cbn. split ; easy.
  - cbn.

    setoid_rewrite seq.in_cons.    
    rewrite is_true_split_or.

    rewrite IHl.
    
    apply or_iff_compat_r.

    rewrite eqtype.eq_sym.
    now rewrite (ssrbool.rwP (@eqtype.eqP (Ord.eqType
                   (prod_ordType nat_ordType
                      (prod_ordType choice_type_ordType choice_type_ordType))) _ _)).
Qed.


Theorem in_split_cat : forall a (l0 l1 : list Location), List.In a (seq.cat l0 l1) <-> List.In a l0 \/ List.In a l1.
Proof.
  split ; intros.
  - induction l0.
    + right. apply H.
    + destruct H.
      * left. left. assumption.
      * destruct (IHl0 H).
        -- left. right. assumption.
        -- right. assumption.
  - destruct H.
    + induction l0.
      * contradiction.
      * destruct H.
        -- left. assumption.
        -- right.
           apply IHl0.
           assumption.
    + induction l0.
      * assumption.
      * right.
        assumption.
Qed.

Theorem in_split_fset_cat : forall a (l0 l1 : {fset tag_ordType (I:=choice_type_ordType) (fun _ : choice_type => nat_ordType)}), List.In a (l0 :|: l1) <-> List.In a l0 \/ List.In a l1.
Proof.
  intros.
  transitivity (In a (seq.cat (eqtype.val l0) (eqtype.val l1))).
  symmetry.
  apply loc_in_remove_fset.
  apply in_split_cat.
Qed.

Theorem loc_list_incl_fsubset : forall (l0 l1 : {fset tag_ordType (I:=choice_type_ordType) (fun _ : choice_type => nat_ordType)}), is_true (fsubset l0 l1) <-> List.incl l0 l1.
Proof.
  intros.
  rewrite <- (ssrbool.rwP (@fsubsetP _ l0 l1)).
  
  unfold ssrbool.sub_mem.
  unfold incl.

  assert (forall {A} (P Q : A -> Prop), (forall x, P x <-> Q x) -> (forall x, P x) <-> (forall x, Q x)).
  { split ; intros ; apply H ; apply H0. }
  apply H. clear H.
  intros x. cbn in *.

  rewrite loc_compute.
  rewrite loc_compute.

  reflexivity.
Qed.

Theorem opsig_list_incl_fsubset : forall (l0 l1 : _), is_true (fsubset (T := (prod_ordType nat_ordType
                           (prod_ordType choice_type_ordType choice_type_ordType))) l0 l1) <-> List.incl l0 l1.
Proof.
  intros.
  rewrite <- (ssrbool.rwP (@fsubsetP _ l0 l1)).
  
  unfold ssrbool.sub_mem.
  unfold incl.

  assert (forall {A} (P Q : A -> Prop), (forall x, P x <-> Q x) -> (forall x, P x) <-> (forall x, Q x)).
  { split ; intros ; apply H ; apply H0. }
  apply H. clear H.
  intros x. cbn in *.

  rewrite opsig_compute.
  rewrite opsig_compute.

  reflexivity.
Qed.


Lemma valid_injectLocations_b :
  forall (import : Interface) (A : choice.Choice.type)
         (L1 L2 : {fset tag_ordType (I:=choice_type_ordType) (fun _ : choice_type => nat_ordType)})
         (v : raw_code A),
    List.incl L1 L2 -> ValidCode L1 import v -> ValidCode L2 import v.
Proof.  
  intros I A L1 L2 v incl.
  apply valid_injectLocations.
  apply loc_list_incl_fsubset.
  apply incl.
Qed.

Lemma valid_injectOpsig_b :
  forall (I1 I2 : Interface) (A : choice.Choice.type)
         (L : {fset tag_ordType (I:=choice_type_ordType) (fun _ : choice_type => nat_ordType)})
         (v : raw_code A),
    List.incl I1 I2 -> ValidCode L I1 v -> ValidCode L I2 v.
Proof.  
  intros I1 I2 A L v incl.
  apply valid_injectMap.
  apply opsig_list_incl_fsubset.
  apply incl.
Qed.

Theorem loc_list_incl_remove_fset {A} `{EqDec A} : forall (l1 l2 : list Location), List.incl l1 l2 <-> List.incl (fset l1) (fset l2).
Proof.
  intros.

  cbn in *.
  
  induction l1.
  - rewrite <- fset0E. easy.
  - cbn.
    unfold incl.
    cbn.
    split.
    + intros.
      rewrite <- loc_in_remove_fset.
      rewrite <- loc_in_remove_fset in H1.
      apply H0.
      apply H1.
    + intros.        
      rewrite -> loc_in_remove_fset.
      apply H0.
      rewrite <- loc_in_remove_fset.
      apply H1.
Qed.        


Theorem opsig_list_incl_remove_fset {A} `{EqDec A} : forall (l1 l2 : list opsig), List.incl l1 l2 <-> List.incl (fset l1) (fset l2).
Proof.
  intros.

  cbn in *.
  
  induction l1.
  - rewrite <- fset0E. easy.
  - cbn.
    unfold incl.
    cbn.
    split.
    + intros.
      rewrite <- opsig_in_remove_fset in H1 |- *.
      apply H0.
      apply H1.
    + intros.        
      rewrite -> opsig_in_remove_fset.
      apply H0.
      rewrite <- opsig_in_remove_fset.
      apply H1.
Qed.        

Theorem list_incl_cons_iff : (forall A (a : A) l1 l2, List.incl (a :: l1) l2 <-> (List.In a l2 /\ List.incl l1 l2)).
Proof.
  split.
  - pose List.incl_cons_inv.
    apply List.incl_cons_inv.
  - intros [].
    apply List.incl_cons ; assumption.          
Qed.

(* Theorem list_incl_compute {A} `{EqDec A} : forall (l1 l2 : list Location), *)
(*     List.incl l1 l2 <-> is_true (incl_sort_compute _ l1 l2). *)
(* Proof. *)
(*   induction l1. *)
(*   - split ; intros. *)
(*     reflexivity. *)
(*     apply incl_nil_l. *)
(*   - intros. *)
    
(*     rewrite list_incl_cons_iff. *)

(*     cbn. *)
(*     rewrite is_true_split_and. *)
(*     rewrite in_bool_eq. *)

(*     apply and_iff_compat_l. *)
(*     apply IHl1. *)
(* Qed.         *)

Theorem loc_list_incl_expand {A} `{EqDec A} : forall (l1 l2 : list Location),
    List.incl l1 l2 <-> incl_expand _ l1 l2.
Proof.
  induction l1.
  - split ; intros.
    reflexivity.
    apply incl_nil_l.
  - intros.
    rewrite list_incl_cons_iff.
    cbn.
    apply and_iff_compat_l.
    apply IHl1.
Qed.

Theorem opsig_list_incl_expand {A} `{EqDec A} : forall (l1 l2 : list opsig),
    List.incl l1 l2 <-> incl_expand _ l1 l2.
Proof.
  induction l1.
  - split ; intros.
    reflexivity.
    apply incl_nil_l.
  - intros.
    rewrite list_incl_cons_iff.
    cbn.
    apply and_iff_compat_l.
    apply IHl1.
Qed.

(* Theorem forall l1 l2, incl_sort_compute <-> list_incl_compute  *)

Definition location_lebP : (tag_leq (I:=choice_type_ordType) (T_:=fun _ : choice_type => nat_ordType)) = leb.
Proof.
  intros.
  do 2 (apply (@functional_extensionality Location) ; intros []).
  cbn.
  
  unfold tag_leq.
  unfold eqtype.tag_eq.

  unfold location_ltb.
  unfold tag_leq.
  
  (* set (_ && _)%bool. *)
  (* set (_ && _)%bool. *)

  unfold location_eqb.
  
  unfold ssrfun.tag , ssrfun.tagged , projT1 , projT2 in *.

  rewrite (Bool.andb_comm _ (eqtype.eq_op _ _)).
  
  destruct (eqtype.eq_op x _) eqn:x_eq_x0.
  2: reflexivity.
  apply Couplings.reflection_nonsense in x_eq_x0.
  subst.
  rewrite eqtype.eq_refl.
  rewrite Bool.andb_true_l.
  rewrite Bool.andb_true_l.
  rewrite Ord.ltxx.
  rewrite Bool.orb_false_l.

  destruct (eqtype.eq_op _ _) eqn:n_eq_n0.
  2: reflexivity.

  unfold eqtype.tagged_as in *.
  unfold ssrfun.tagged ,  projT2 in *.
  unfold eq_rect_r , eq_rect in *.
  
  destruct eqtype.eqP in *.
  2: contradiction.
  cbn in n_eq_n0.
  destruct eq_sym in *.
  rewrite ssrnat.eqnE in n_eq_n0.
  apply Couplings.reflection_nonsense in n_eq_n0.
  apply Ord.eq_leq. assumption.
Qed.

Lemma iff_extensionality : forall {A} (P Q : A -> Prop), (forall a, P a <-> Q a) -> ((forall a, P a) <-> (forall a, Q a)).
Proof.
  intros. split ; intuition.
Qed.

Lemma iff_eq_sym : forall {A} (x y : A), (x = y) <-> (y = x).
Proof.
  intros. split ; intuition.
Qed.

Definition loc_seq_has (a : Location) := seq.has (ssrbool.fun_of_rel (@eqtype.eq_op loc_eqType) a).

Theorem loc_seq_has_remove_sort {A} `{EqDec A} : forall (l : list Location) (a : Location) leb,
    is_true (loc_seq_has a l) <->
    is_true (loc_seq_has a (path.sort leb l)).
Proof.
  intros.
  rewrite <- (Bool.negb_involutive (loc_seq_has a (path.sort leb l))).

  unfold loc_seq_has.
  
  rewrite <- seq.all_predC.
  rewrite path.all_sort.
  rewrite seq.all_predC.

  rewrite Bool.negb_involutive.

  reflexivity.
Qed.  

Theorem list_in_iff_seq_has {A} `{EqDec A} : forall (l : list Location) (a : Location),
    is_true (loc_seq_has a l) <-> List.In a l.
Proof.
  induction l ; intros.
  - split ; intros ; easy. 
  - cbn.
    rewrite is_true_split_or.
    apply ZifyClasses.or_morph.
    + rewrite <- (ssrbool.rwP (@eqtype.eqP loc_eqType a0 a)).      
      apply iff_eq_sym.
    + apply IHl.
Qed.    

Theorem list_in_iff_list_in_sort {A} `{EqDec A} : forall (l : list Location) (a : Location) leb,
    List.In a l <-> List.In a (path.sort leb l).
Proof.
  intros.
  rewrite <- (list_in_iff_seq_has (path.sort leb l)).
  rewrite <- loc_seq_has_remove_sort.
  rewrite list_in_iff_seq_has.
  reflexivity.
Qed.    

Theorem list_in_sort_order_ignorant_compute {A} `{EqDec A} : forall (l : list Location) leb1 leb2 a,
    (List.In a (path.sort leb1 l)) <-> List.In a (path.sort leb2 l).
Proof.
  intros.
  rewrite <- list_in_iff_list_in_sort.
  rewrite <- list_in_iff_list_in_sort.
  reflexivity.
Qed.
  
Theorem list_incl_sort_order_ignorant_compute {A} `{EqDec A} : forall (l1 l2 : list Location) leb1 leb2,
    List.incl (path.sort leb1 l1) (path.sort leb1 l2) <-> List.incl (path.sort leb2 l1) (path.sort leb2 l2).
Proof.
  intros.
  apply iff_extensionality.
  intros a.

  rewrite list_in_sort_order_ignorant_compute with (leb1 := leb1) (leb2 := leb2).
  rewrite list_in_sort_order_ignorant_compute with (leb1 := leb1) (leb2 := leb2).
  reflexivity.
Qed.    

Theorem list_incl_sort {A} `{EqDec A} : forall (l1 l2 : list Location) leb,
    List.incl l1 l2 <-> List.incl (path.sort leb l1) (path.sort leb l2).
Proof.
  intros.
  apply iff_extensionality.
  intros a.
  rewrite <- list_in_iff_list_in_sort.
  rewrite <- list_in_iff_list_in_sort.
  reflexivity.
Qed.  

Theorem choice_type_test_refl : forall x , is_true (choice_type_test x x).
Proof.
  intros.
  replace (choice_type_test _ _) with (eqtype.eq_op x x) by reflexivity.
  apply eqtype.eq_refl.
Qed.

Theorem fset_eqEincl: forall a b : list Location, fset a = fset b <-> List.incl a b /\ List.incl b a.
Proof.
  intros.
  rewrite (ssrbool.rwP (@eqtype.eqP _ (fset a) (fset b))).
  rewrite (@eqEfsubset _ (fset a) (fset b)).
  rewrite is_true_split_and.

  apply ZifyClasses.and_morph ; rewrite loc_list_incl_fsubset ; rewrite <- loc_list_incl_remove_fset ; reflexivity.
Qed.
