From Coq Require Import Classical_Prop Bool.Bool Lia Relations.Relation_Definitions
                        Classes.RelationClasses Program.
Require Import Typ Term Var Substitution Typing Context.

(** * Transition - Evaluation

arrow's semantics are divided in three sub semantics:
- evaluation transition <--
- functional transition
- temporal transition

This file focuses on the evaluation transition which is a small step semantics with a call by value evaluation strategy.
*)


(** *** Definition *)

Reserved Notation "'⊨' t '⟼' t1" (at level 57, t custom arrow, 
                                                   t1 custom arrow, no associativity).
Reserved Notation "'⊨' t '⟼⋆' t1" (at level 57, t custom arrow, 
                                                    t1 custom arrow, no associativity).
Reserved Notation "'⊨' t '⊢' st '⟶' t1" (at level 57, t custom arrow, 
                                                         t1 custom arrow, no associativity).


Inductive evaluate : Λ -> Λ -> Prop :=
  | eT_appv   : forall x τ t v,
                              value(v) ->
                (*----------------------------------- ET-Appv *)
                    ⊨ ((\x:τ,t) v) ⟼ ([x:= v] t)


  | eT_fix   : forall f τ t,
                (*-------------------------------------------------- ET-Fix *)
                    ⊨ (Fix (\f:τ,t)) ⟼ ([f := (Fix (\f:τ,t))] t)

  | eT_app1   : forall t1 t1' t2,
                       ⊨ t1 ⟼ t1' -> 
                (*-------------------------- ET-App1 *)
                    ⊨ (t1 t2) ⟼ (t1' t2)

  | eT_app2   : forall v t t',
                    value(v) -> ⊨ t ⟼ t' -> 
                (*----------------------------- ET-App2 *)
                       ⊨ (v t) ⟼ (v t') 

  | eT_pair1  : forall t1 t1' t2,
                        ⊨ t1 ⟼ t1' -> 
                (*-------------------------- ET-Pair1 *)
                    ⊨ ⟨t1,t2⟩ ⟼ ⟨t1',t2⟩

  | eT_pair2  : forall v t t',
                    value(v) -> ⊨ t ⟼ t' -> 
                (*----------------------------- ET-Pair2 *)
                      ⊨ ⟨v,t⟩ ⟼ ⟨v,t'⟩ 

  | eT_fst1   : forall t t',
                      ⊨ t ⟼ t' -> 
                (*---------------------- ET-Fst1 *)
                    ⊨ t.fst ⟼ t'.fst

  | eT_fstv   : forall v1 v2,
                    value(v1) -> value(v2) -> 
                (*----------------------------- ET-Fstv *)
                    ⊨ ⟨v1,v2⟩.fst ⟼ v1

  | eT_snd1   : forall t t',
                        ⊨ t ⟼ t' -> 
                (*------------------------ ET-Snd1 *)
                    ⊨ t.snd ⟼ t'.snd

  | eT_sndv   : forall v1 v2,
                    value(v1) -> value(v2) -> 
                (*---------------------------- ET-Sndv *)
                    ⊨ ⟨v1,v2⟩.snd ⟼ v2
                            
  | eT_comp1  : forall t1 t1' t2,
                            ⊨ t1 ⟼ t1' -> 
                (*------------------------------- ET-Comp1 *)
                    ⊨ t1 >>> t2 ⟼ t1' >>> t2

  | eT_comp2  : forall v t t',
                      value(v) -> ⊨ t ⟼ t' -> 
                (*------------------------------- ET-Comp2 *)
                      ⊨ v >>> t ⟼ v >>> t'

  | eT_arr  : forall t t',
                      ⊨ t ⟼ t' -> 
              (*------------------------ ET-Arr *)
                  ⊨ arr(t) ⟼ arr(t')

  | eT_first  : forall τ t t',
                            ⊨ t ⟼ t' -> 
                (*------------------------------- ET-First *)
                    ⊨ first(τ:t) ⟼ first(τ:t')

where "'⊨' t '⟼' t1" := (evaluate t t1)
.

(** **** Multi transition step with fuel *)
Inductive indexed : nat -> Λ -> Λ -> Prop :=
  | index_refl : forall x, ⊨ x ⊢ 0 ⟶ x
  | index_step : forall k x y z, ⊨ x ⟼ y -> ⊨ y ⊢ k ⟶ z -> ⊨ x ⊢(S k)⟶ z
where "'⊨' t '⊢' st '⟶' t1" := (indexed st t t1)
.

(** **** Multi transition step *)
Inductive multi : Λ -> Λ -> Prop :=
  | multi_refl : forall x, ⊨ x ⟼⋆ x
  | multi_step : forall x y z, ⊨ x ⟼ y -> ⊨ y ⟼⋆ z -> ⊨ x ⟼⋆ z
where "'⊨' t '⟼⋆' t1" := (multi t t1).

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop := not (exists t', R t t').
Definition halts (t : Λ) : Prop :=  exists t', ⊨ t ⟼⋆ t' /\  value(t').

#[export] Hint Constructors evaluate multi indexed : core.

(** *** Lift semantics rules from evaluation to multi evaluation *)

Lemma multi_var : forall (x : variable), ⊨ x ⟼⋆ x.
Proof. intros x; apply multi_refl. Qed.

Lemma multi_appv : forall x t τ v, 
  value(v) -> ⊨ ((\x:τ, t) v) ⟼⋆ ([x := v] t).
Proof. 
  intros x t τ v Hv. apply multi_step with (y := <[[x := v] t]>); auto.
Qed.

Lemma multi_fix : forall x t τ, 
  ⊨ (Fix (\x:τ, t)) ⟼⋆ ([x := (Fix (\x:τ, t))] t).
Proof. 
  intros x t τ. apply multi_step with (y := <[[x := (Fix (\x:τ, t))] t]>); auto.
Qed.

Lemma multi_app1 : forall t t' t2, ⊨ t ⟼⋆ t' -> ⊨ (t t2) ⟼⋆ (t' t2).
Proof. 
  intros t t' t2 HeT; induction HeT; subst; auto.
  apply multi_step with <[y t2]>; auto.
Qed.

Lemma multi_app2 : forall t t' t1, value(t1) -> ⊨ t ⟼⋆ t' -> ⊨ (t1 t) ⟼⋆ (t1 t').
Proof. 
  intros t t' t1 Hvt HeT; induction HeT; subst; auto.
  apply multi_step with <[t1 y]>; auto.
Qed.

Lemma multi_pair1 : forall t t' t2, ⊨ t ⟼⋆ t' -> ⊨ ⟨t,t2⟩ ⟼⋆ ⟨t',t2⟩.
Proof.
  intros t t' t2 HeT; induction HeT; subst; auto.
  apply multi_step with <[⟨y,t2⟩]>; auto. 
Qed.

Lemma multi_pair2 : forall t t' t1, value(t1) -> ⊨ t ⟼⋆ t' -> ⊨ ⟨t1,t⟩ ⟼⋆ ⟨t1,t'⟩.
Proof.
  intros t t' t1 Hvt HeT; induction HeT; subst; auto.
  apply multi_step with <[⟨t1,y⟩]>; auto. 
Qed.

Lemma multi_fstv : forall t1 t2, value(t1) -> value(t2) -> ⊨ ⟨t1,t2⟩.fst ⟼⋆ t1.
Proof.
  intros t1 t2 Hvt1 Hvt2; apply multi_step with t1; auto.
Qed.

Lemma multi_fst1 : forall t t', ⊨ t ⟼⋆ t' -> ⊨ t.fst ⟼⋆ t'.fst.
Proof.
  intros t t' HeT; induction HeT; subst; auto.
  apply multi_step with <[y.fst]>; auto. 
Qed.

Lemma multi_sndv : forall t1 t2, value(t1) -> value(t2) -> ⊨ ⟨t1,t2⟩.snd ⟼⋆ t2.
Proof.
  intros t1 t2 Hvt1 Hvt2; apply multi_step with t2; auto.
Qed.

Lemma multi_snd1 : forall t t', ⊨ t ⟼⋆ t' -> ⊨ t.snd ⟼⋆ t'.snd.
Proof.
  intros t t' HeT; induction HeT; subst; auto.
  apply multi_step with <[y.snd]>; auto. 
Qed.

Lemma multi_arr : forall t t', ⊨ t ⟼⋆ t' -> ⊨ arr(t) ⟼⋆ arr(t').
Proof.
  intros t t' HeT; induction HeT; subst; auto.
  apply multi_step with <[arr(y)]>; auto. 
Qed.

Lemma multi_first : forall τ t t', ⊨ t ⟼⋆ t' -> ⊨ first(τ:t) ⟼⋆ first(τ:t').
Proof.
  intros τ t t' HeT; induction HeT; subst; auto.
  apply multi_step with <[first(τ:y)]>; auto. 
Qed.

Lemma multi_comp1 : forall t t' t2, ⊨ t ⟼⋆ t' -> ⊨ t >>> t2 ⟼⋆ t' >>> t2.
Proof. 
  intros t t' t2 HeT; induction HeT; subst; auto.
  apply multi_step with <[y >>> t2]>; auto.
Qed.

Lemma multi_comp2 : forall t t' t1, value(t1) -> ⊨ t ⟼⋆ t' -> ⊨ t1 >>> t ⟼⋆ t1 >>> t'.
Proof. 
  intros t t' t1 Hvt HeT; induction HeT; subst; auto.
  apply multi_step with <[t1 >>> y]>; auto.
Qed.



(** *** Value regards of evaluation transition *)

Lemma value_normal : forall t, value(t) -> normal_form evaluate t.
Proof.
  intros t H; induction H; intros [t' ST]; 
  try (inversion ST; subst; try destruct IHvalue; now eauto);
  try (inversion ST; subst; try destruct IHvalue1; now eauto).
Qed.

Lemma evaluate_not_value : forall t t', ⊨ t ⟼ t' -> ~ (value(t)).
Proof.
  intros; induction H; unfold not; intro c; inversion c; subst; eauto.
Qed.

(** *** Transitivity of multiple evaluation steps *)

Lemma multi_trans : Transitive multi.
Proof.
  red; intros x y z HmeT HmeT'; induction HmeT; try assumption.
  eapply multi_step; eauto.
Qed.

Lemma indexed_trans : forall k k' t t' t'',
  ⊨ t ⊢ k ⟶ t' -> ⊨ t' ⊢ k' ⟶ t'' -> ⊨ t ⊢ (k+k') ⟶ t''.
Proof.
  induction k; intros.
  - simpl; inversion H; subst; auto.
  - inversion H; subst. simpl. apply index_step with (y := y); auto.
    eapply IHk; eauto.
Qed.

(** *** Determinism *)

Theorem evaluate_deterministic : forall t t1 t2,
  ⊨ t ⟼ t1 -> ⊨ t ⟼ t2 -> t1 = t2.
Proof with eauto.
  intros t t' t'' E1 E2; generalize dependent t''.
  induction E1; intros t'' E2; inversion E2; subst; try (f_equal; now auto); 
  exfalso; try (eapply value_normal; now eauto); clear E2...
  - eapply value_normal in H...
  - inversion E1; subst.
    -- eapply value_normal in H0...
    -- eapply value_normal in H1...
  - inversion H2; subst.
    -- eapply value_normal in H...
    -- eapply value_normal in H0...
  - inversion E1; subst.
    -- eapply value_normal in H0...
    -- eapply value_normal in H1...
  - inversion H2; subst.
    -- eapply value_normal in H...
    -- eapply value_normal in H0...
Qed.

Theorem indexed_deterministic : forall n t t1 t2,
  ⊨ t ⊢ n ⟶ t1 -> ⊨ t ⊢ n ⟶ t2 -> t1 = t2.
Proof.
intros n; induction n; intros t t1 t2 Hev1 Hev2.
- inversion Hev1; inversion Hev2; subst; reflexivity.
- inversion Hev1; inversion Hev2; subst.
  apply evaluate_deterministic with (t1 := y) in H5; auto; subst. 
  now apply IHn with (t := y0).
Qed.


(** *** Halts *)

Lemma value_halts : forall t, value(t) -> halts t.
Proof. 
  intros t Hv; unfold halts; exists t; split; try assumption.
  apply multi_refl.
Qed.

Lemma evaluate_preserves_halting : forall t t',
  ⊨ t ⟼ t' -> (halts t <-> halts t').
Proof.
  intros t t' HeT; unfold halts; split; intros [t'' [HmeT Hv]].
  - destruct HmeT.
    -- exfalso; apply value_normal in Hv; unfold normal_form,not in Hv; apply Hv.
       now exists t'.
    -- apply (evaluate_deterministic x t' y HeT) in H as Heq; subst.
      exists z; split; assumption.
  - exists t''; split; try assumption; now apply multi_step with (y := t').     
Qed.

Lemma multi_preserves_halting : forall t t',
  ⊨ t ⟼⋆ t' -> (halts t <-> halts t').
Proof.
  intros t t' HmeT; induction HmeT; unfold halts; split; intros [t'' [HmeT' Hv]];
  try (exists t''; now split).
  - apply evaluate_preserves_halting in H as H'.
    assert (halts x). { exists t''; now split. }
    rewrite H' in H0; now rewrite IHHmeT in H0.
  - apply evaluate_preserves_halting in H as H'.
    assert (halts z). { exists t''; now split. }
    rewrite <- IHHmeT in H0. now rewrite <- H' in H0.
Qed.

Lemma halts_pair : forall t1 t2,
  halts <[⟨t1,t2⟩]> <-> halts t1 /\ halts t2.
Proof.
  assert (Hpair : forall t1 t2 t, ⊨ ⟨t1,t2⟩ ⟼⋆ t -> exists t1' t2', t = <[⟨t1',t2'⟩]>).
  {
    intros t1 t2 t HeT; dependent induction HeT; subst.
    - exists t1; now exists t2.
    - inversion H; subst; eauto. 
  }
  intros t1 t2; split; intros HA.
  - destruct HA as [t [HmeT Hvt]]. apply Hpair in HmeT as Heq.
    destruct Heq as [t1' [t2' Heq]]; subst. dependent induction HmeT.
    -- inversion Hvt; subst; split.
       + exists t1'; split; auto.
       + exists t2'; split; auto.
    -- inversion H; subst.
       + apply IHHmeT with (t1 := t1'0) (t2 := t2) in Hvt; auto.
         destruct Hvt; split; auto; clear H1.
         rewrite evaluate_preserves_halting; eauto.
       + apply IHHmeT with (t1 := t1) (t2 := t') in Hvt; auto.
         destruct Hvt; split; auto; clear H0.
         rewrite evaluate_preserves_halting; eauto.
  - destruct HA. destruct H as [t1' [HmeT1 Hvt1']];
    destruct H0 as [t2' [HmeT2 Hvt2']].
    exists <[⟨t1',t2'⟩]>; split.
    -- apply multi_trans with <[⟨t1',t2⟩]>.
       + now apply multi_pair1.
       + now apply multi_pair2.
    -- now constructor.
Qed.


(** *** Relation between eval,multi and indexed transition *)

Lemma evaluate_indexed_1_iff : forall t t',
  ⊨ t ⟼ t' <-> ⊨ t ⊢ 1 ⟶ t'.
Proof.
  split; intros.
  - replace 1 with (0 + 1); eauto; 
    eapply index_step; eauto; apply index_refl; auto.
  - inversion H; subst. inversion H2; subst; auto.
Qed.

Lemma multi_indexed : forall t t',
  ⊨ t ⟼⋆ t' -> exists k, ⊨ t ⊢ k ⟶ t'.
Proof.
  intros. induction H.
  - exists 0. apply index_refl; auto.
  - destruct IHmulti. exists (S x0). eapply index_step; eauto.
Qed.

(** ** Preservation *)

(** *** Proof of preservation of typing through the evaluation transition

  **** Hypothesis

  Knowing that the term t is well typed according to a certain context Γ (1), 
  there is a certain t' that is the result of t after one step of transition (2);

  **** Result

  We can state that the term t' is well typed. 
*)
Theorem evaluate_preserves_typing : forall t t' τ,
  (* (1) *) ∅ᵧ ⊫ t ∈ τ ->  (* (2) *) ⊨ t ⟼ t' -> 

  ∅ᵧ ⊫ t' ∈ τ.
Proof. 
  intros t t' τ Hwt; generalize dependent t'; dependent induction Hwt; intros t' HeTt;
  inversion HeTt; subst; try (econstructor; now eauto); eauto.
  - inversion Hwt1; subst. eapply subst_preserves_typing; eauto.
  - inversion Hwt2; subst; inversion Hwt1.
  - inversion Hwt; subst; auto.
  - inversion Hwt; subst; auto.
  - inversion Hwt; subst. eapply subst_preserves_typing; eauto.
    now constructor.
Qed.

(** *** Proof of preservation of typing through multiple evaluation transitions

  **** Hypothesis

  Knowing that the term t is well typed (1), 
  there is a certain t' that is the result of t after zero or k steps of transition (2);

  **** Result

  We can state that the term t' is well typed. 
*)
Theorem multi_preserves_typing : forall t t' τ,
  (* (1) *) ∅ᵧ ⊫ t ∈ τ -> (* (2) *) ⊨ t ⟼⋆ t' -> 
  
  ∅ᵧ ⊫ t' ∈ τ.
Proof.
  intros t t' τ Hwt HmeT; dependent induction HmeT; subst; try assumption.
  apply IHHmeT; auto. eapply (evaluate_preserves_typing x y τ Hwt H).
Qed.

(** ** Progress *)

(** *** Proof of progress of the evaluation transtion

  If the term is well typed then 
  - either we have a value (1) or 
  - we can evaluate at least one time the term (2).

*)
Theorem progress_of_evaluate : forall t τ,
  ∅ᵧ ⊫ t ∈ τ -> 
  
  (* (1) *) value(t) \/ (* (2) *) exists t', ⊨ t ⟼ t'.
Proof.
  intro t; induction t; intros τ' Hwt; inversion Hwt; subst;
  try (now left); try (apply IHt1 in H2 as H2'; apply IHt2 in H4 as H4').
  - destruct H2',H4'; right.
    -- inversion H;subst; inversion H2; subst. exists <[[x:= t2] t]>.
      now constructor.
    -- destruct H0; exists <[t1 x]>; now constructor.
    -- destruct H; exists <[x t2]>; now constructor.
    -- destruct H; exists <[x t2]>; now constructor.
  - right; apply IHt2 in H3 as H3'; destruct H3'.
    -- destruct t2; inversion H3; subst; inversion H; subst.
        exists <[[v := Fix (\ v : τ', t2)] t2]>; constructor.
    -- destruct H; exists <[Fix x]>; constructor; auto.
  - destruct H2',H4'; auto.
    -- right; destruct H0; exists <[⟨t1,x⟩]>; now constructor.
    -- right; destruct H; exists <[⟨x,t2⟩]>; now constructor.
    -- right; destruct H; exists <[⟨x,t2⟩]>; now constructor.
  - apply IHt in H1 as H1'; destruct H1'; right.
    -- inversion H; subst; inversion H1; subst; exists v1; now constructor. 
    -- destruct H; exists (Term.tm_fst x); now constructor.
  - apply IHt in H1 as H1'; destruct H1'; right.
    -- inversion H; subst; inversion H1; subst; exists v2; now constructor. 
    -- destruct H; exists (Term.tm_snd x); now constructor.
  - apply IHt in H1 as H1'; destruct H1' as [Hvt | [t' HeT']]; 
    try (left; now constructor); right; exists <[arr(t')]>; now constructor.
  - apply IHt in H3 as H3'; destruct H3' as [Hvt | [t' HeT']]; 
    try (left; now constructor); right; exists <[first(τ:t')]>; now constructor.
  - destruct H2' as [Hvt1 | [t1' HeT1']]; destruct H4' as [Hvt2 | [t2' HeT2']];
    try (left; now constructor); right.
    -- exists <[t1 >>> t2']>; now constructor.
    -- exists <[t1' >>> t2]>; now constructor.
    -- exists <[t1' >>> t2]>; now constructor.
Qed.