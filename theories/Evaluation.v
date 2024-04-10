From Coq Require Import Classical_Prop Bool.Bool Lia Relations.Relation_Definitions
                        Classes.RelationClasses Program.
Require Import Typ Resource Resources Term Var VContext RContext Substitution Typing.

(** * Transition - Evaluation

Wormholes's semantics are divided in three sub semantics:
- evaluation transition <--
- functional transition
- temporal transition

This file focuses on the evaluation transition which is a small step semantics with a call by value evaluation strategy.
*)


(** *** Definition *)

Reserved Notation "k '⊨' t '⟼' t1" (at level 57, t custom wormholes, 
                                                   t1 custom wormholes, no associativity).
Reserved Notation "k '⊨' t '⟼⋆' t1" (at level 57, t custom wormholes, 
                                                    t1 custom wormholes, no associativity).
Reserved Notation "k '⊨' t '⊢' st '⟶' t1" (at level 57, t custom wormholes, 
                                                         t1 custom wormholes, no associativity).

(** **** Small-step semantics

  Evaluation transition is defined as we found in an stlc formalization with a slight difference. Indeed, we have an additional element
  [lb]. This is the current level that are valid. It is required because of the definition of validity of terms and for a well use of the 
  substitution in the [eT_appv] rule. 
*)
Inductive evaluate : nat -> Λ -> Λ -> Prop :=
  | eT_appv   : forall lb x τ t v,
                                  value(v) ->
                (*-------------------------------------------- ET-Appv *)
                    lb ⊨ ((\x:τ,t) v) ⟼ ([x:= v ~ lb ≤ 0] t)


  | eT_fix   : forall lb f τ t,
                (*------------------------------------------------------------ ET-Fix *)
                    lb ⊨ (Fix (\f:τ,t)) ⟼ ([f := (Fix (\f:τ,t)) ~ lb ≤ 0] t)

  | eT_app1   : forall lb t1 t1' t2,
                        lb ⊨ t1 ⟼ t1' -> 
                (*---------------------------- ET-App1 *)
                    lb ⊨ (t1 t2) ⟼ (t1' t2)

  | eT_app2   : forall lb v t t',
                    value(v) -> lb ⊨ t ⟼ t' -> 
                (*------------------------------- ET-App2 *)
                      lb ⊨ (v t) ⟼ (v t') 

  | eT_pair1  : forall lb t1 t1' t2,
                        lb ⊨ t1 ⟼ t1' -> 
                (*----------------------------- ET-Pair1 *)
                    lb ⊨ ⟨t1,t2⟩ ⟼ ⟨t1',t2⟩

  | eT_pair2  : forall lb v t t',
                    value(v) -> lb ⊨ t ⟼ t' -> 
                (*------------------------------- ET-Pair2 *)
                      lb ⊨ ⟨v,t⟩ ⟼ ⟨v,t'⟩ 

  | eT_fst1   : forall lb t t',
                      lb ⊨ t ⟼ t' -> 
                (*------------------------- ET-Fst1 *)
                    lb ⊨ t.fst ⟼ t'.fst

  | eT_fstv   : forall lb v1 v2,
                    value(v1) -> value(v2) -> 
                (*----------------------------- ET-Fstv *)
                    lb ⊨ ⟨v1,v2⟩.fst ⟼ v1

  | eT_snd1   : forall lb t t',
                        lb ⊨ t ⟼ t' -> 
                (*-------------------------- ET-Snd1 *)
                    lb ⊨ t.snd ⟼ t'.snd

  | eT_sndv   : forall lb v1 v2,
                    value(v1) -> value(v2) -> 
                (*----------------------------- ET-Sndv *)
                    lb ⊨ ⟨v1,v2⟩.snd ⟼ v2
                            
  | eT_comp1  : forall lb t1 t1' t2,
                            lb ⊨ t1 ⟼ t1' -> 
                (*--------------------------------- ET-Comp1 *)
                    lb ⊨ t1 >>> t2 ⟼ t1' >>> t2

  | eT_comp2  : forall lb v t t',
                      value(v) -> lb ⊨ t ⟼ t' -> 
                (*--------------------------------- ET-Comp2 *)
                      lb ⊨ v >>> t ⟼ v >>> t'

  | eT_arr  : forall lb t t',
                      lb ⊨ t ⟼ t' -> 
              (*------------------------- ET-Arr *)
                  lb ⊨ arr(t) ⟼ arr(t')

  | eT_first  : forall lb τ t t',
                            lb ⊨ t ⟼ t' -> 
                (*--------------------------------- ET-First *)
                    lb ⊨ first(τ:t) ⟼ first(τ:t')

  | eT_wh1   :  forall lb i i' t,
                                lb ⊨ i ⟼ i' -> 
                (*----------------------------------------- ET-Wh1 *)
                    lb ⊨ wormhole(i;t) ⟼ wormhole(i';t)

  | eT_wh2   :  forall lb i t t',
                    value(i) -> (S (S lb)) ⊨ t ⟼ t' -> 
                (*----------------------------------------- ET-Wh2 *)
                    lb ⊨ wormhole(i;t) ⟼ wormhole(i;t')

where "k '⊨' t '⟼' t1" := (evaluate k t t1)
.

(** **** Multi transition step with fuel *)
Inductive indexed : nat -> nat -> Λ -> Λ -> Prop :=
  | index_refl : forall lb x, lb ⊨ x ⊢ 0 ⟶ x
  | index_step : forall lb k x y z, lb ⊨ x ⟼ y -> lb ⊨ y ⊢ k ⟶ z -> lb ⊨ x ⊢(S k)⟶ z
where "k '⊨' t '⊢' st '⟶' t1" := (indexed k st t t1)
.

(** **** Multi transition step *)
Inductive multi : nat -> Λ -> Λ -> Prop :=
  | multi_refl : forall k x, k ⊨ x ⟼⋆ x
  | multi_step : forall k x y z, k ⊨ x ⟼ y -> k ⊨ y ⟼⋆ z -> k ⊨ x ⟼⋆ z
where "k '⊨' t '⟼⋆' t1" := (multi k t t1).

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop := not (exists t', R t t').
Definition halts (k : nat)  (t : Λ) : Prop :=  exists t', k ⊨ t ⟼⋆ t' /\  value(t').

#[export] Hint Constructors evaluate multi indexed : core.

(** *** Lift semantics rules from evaluation to multi evaluation *)

Lemma multi_var : forall k (x : variable), k ⊨ x ⟼⋆ x.
Proof. intros k x; apply multi_refl. Qed.

Lemma multi_appv : forall k x t τ v, 
  value(v) -> k ⊨ ((\x:τ, t) v) ⟼⋆ ([x := v ~ k ≤ 0] t).
Proof. 
  intros k x t τ v Hv. apply multi_step with (y := <[[x := v ~ k ≤ 0] t]>); auto.
Qed.

Lemma multi_fix : forall k x t τ, 
  k ⊨ (Fix (\x:τ, t)) ⟼⋆ ([x := (Fix (\x:τ, t)) ~ k ≤ 0] t).
Proof. 
  intros k x t τ. apply multi_step with (y := <[[x := (Fix (\x:τ, t)) ~ k ≤ 0] t]>); auto.
Qed.

Lemma multi_app1 : forall k t t' t2, k ⊨ t ⟼⋆ t' -> k ⊨ (t t2) ⟼⋆ (t' t2).
Proof. 
  intros k t t' t2 HeT; induction HeT; subst; auto.
  apply multi_step with <[y t2]>; auto.
Qed.

Lemma multi_app2 : forall k t t' t1, value(t1) -> k ⊨ t ⟼⋆ t' -> k ⊨ (t1 t) ⟼⋆ (t1 t').
Proof. 
  intros k t t' t1 Hvt HeT; induction HeT; subst; auto.
  apply multi_step with <[t1 y]>; auto.
Qed.

Lemma multi_pair1 : forall k t t' t2, k ⊨ t ⟼⋆ t' -> k ⊨ ⟨t,t2⟩ ⟼⋆ ⟨t',t2⟩.
Proof.
  intros k t t' t2 HeT; induction HeT; subst; auto.
  apply multi_step with <[⟨y,t2⟩]>; auto. 
Qed.

Lemma multi_pair2 : forall k t t' t1, value(t1) -> k ⊨ t ⟼⋆ t' -> k ⊨ ⟨t1,t⟩ ⟼⋆ ⟨t1,t'⟩.
Proof.
  intros k t t' t1 Hvt HeT; induction HeT; subst; auto.
  apply multi_step with <[⟨t1,y⟩]>; auto. 
Qed.

Lemma multi_fstv : forall k t1 t2, value(t1) -> value(t2) -> k ⊨ ⟨t1,t2⟩.fst ⟼⋆ t1.
Proof.
  intros k t1 t2 Hvt1 Hvt2; apply multi_step with t1; auto.
Qed.

Lemma multi_fst1 : forall k t t', k ⊨ t ⟼⋆ t' -> k ⊨ t.fst ⟼⋆ t'.fst.
Proof.
  intros k t t' HeT; induction HeT; subst; auto.
  apply multi_step with <[y.fst]>; auto. 
Qed.

Lemma multi_sndv : forall k t1 t2, value(t1) -> value(t2) -> k ⊨ ⟨t1,t2⟩.snd ⟼⋆ t2.
Proof.
  intros k t1 t2 Hvt1 Hvt2; apply multi_step with t2; auto.
Qed.

Lemma multi_snd1 : forall k t t', k ⊨ t ⟼⋆ t' -> k ⊨ t.snd ⟼⋆ t'.snd.
Proof.
  intros k t t' HeT; induction HeT; subst; auto.
  apply multi_step with <[y.snd]>; auto. 
Qed.

Lemma multi_arr : forall k t t', k ⊨ t ⟼⋆ t' -> k ⊨ arr(t) ⟼⋆ arr(t').
Proof.
  intros k t t' HeT; induction HeT; subst; auto.
  apply multi_step with <[arr(y)]>; auto. 
Qed.

Lemma multi_first : forall k τ t t', k ⊨ t ⟼⋆ t' -> k ⊨ first(τ:t) ⟼⋆ first(τ:t').
Proof.
  intros k τ t t' HeT; induction HeT; subst; auto.
  apply multi_step with <[first(τ:y)]>; auto. 
Qed.

Lemma multi_comp1 : forall k t t' t2, k ⊨ t ⟼⋆ t' -> k ⊨ t >>> t2 ⟼⋆ t' >>> t2.
Proof. 
  intros k t t' t2 HeT; induction HeT; subst; auto.
  apply multi_step with <[y >>> t2]>; auto.
Qed.

Lemma multi_comp2 : forall k t t' t1, value(t1) -> k ⊨ t ⟼⋆ t' -> k ⊨ t1 >>> t ⟼⋆ t1 >>> t'.
Proof. 
  intros k t t' t1 Hvt HeT; induction HeT; subst; auto.
  apply multi_step with <[t1 >>> y]>; auto.
Qed.

Lemma multi_wh1 : forall k t t' t2, k ⊨ t ⟼⋆ t' -> k ⊨ wormhole(t;t2) ⟼⋆ wormhole(t';t2).
Proof. 
  intros k t t' t2 HeT; induction HeT; subst; auto.
  apply multi_step with <[wormhole(y;t2)]>; auto.
Qed.

Lemma multi_wh2 : forall k t t' t1, 
  value(t1) -> (S (S k)) ⊨ t ⟼⋆ t' -> k ⊨ wormhole(t1;t) ⟼⋆ wormhole(t1;t').
Proof. 
  intros k t t' t1 Hvt HeT; dependent induction HeT; subst; auto.
  apply multi_step with <[wormhole(t1;y)]>; auto.
Qed.




(** *** Value regards of evaluation transition *)

Lemma value_normal : forall k t, value(t) -> normal_form (evaluate k) t.
Proof.
  intros k t H; generalize k; clear k; induction H; intros k [t' ST]; 
  try (inversion ST; subst; try destruct (IHvalue k); now eauto);
  try (inversion ST; subst; try destruct (IHvalue1 k); now eauto).
  - destruct (IHvalue2 k). inversion ST; subst.
    -- exfalso; apply (IHvalue1 k); now exists t1'.
    -- now exists t'0.
  - destruct (IHvalue2 k). inversion ST; subst.
    -- exfalso; apply (IHvalue1 k); now exists t1'.
    -- now exists t'0.
  - destruct (IHvalue2 (S (S k))). inversion ST; subst.
    -- exfalso; apply (IHvalue1 k); now exists i'.
    -- now exists t'0.
Qed.

Lemma evaluate_not_value : forall t t' k, k ⊨ t ⟼ t' -> ~ (value(t)).
Proof.
  intros; induction H; unfold not; intro c; inversion c; subst; eauto.
Qed.

(** *** Transitivity of multiple evaluation steps *)

Lemma multi_trans : forall k, Transitive (multi k).
Proof.
  red; intros k x y z HmeT HmeT'; induction HmeT; try assumption.
  eapply multi_step; eauto.
Qed.

Lemma indexed_trans : forall lb k k' t t' t'',
lb ⊨ t ⊢ k ⟶ t' -> lb ⊨ t' ⊢ k' ⟶ t'' -> lb ⊨ t ⊢ (k+k') ⟶ t''.
Proof.
  induction k; intros.
  - simpl; inversion H; subst; auto.
  - inversion H; subst. simpl. apply index_step with (y := y); auto.
    eapply IHk; eauto.
Qed.

(** *** Valid *)

Lemma evaluate_preserves_valid_term : forall t t' k,
  k ⊩ₜₘ t -> k ⊨ t ⟼ t' -> k ⊩ₜₘ t'.
Proof.
  intros t; induction t; intros t' k Hvt HeTt; inversion Hvt; inversion HeTt; 
  subst; auto; try (constructor; fold Term.valid in *; auto).
  - inversion Hvt; subst; inversion H4; subst. now apply subst_preserves_valid_4.
  - inversion Hvt; subst. inversion H5; subst; apply subst_preserves_valid_4; auto.
  - inversion H1; subst; auto.
  - inversion H1; subst; auto.
Qed.

Lemma multi_preserves_valid_term : forall k t t',
  k ⊩ₜₘ t -> k ⊨ t ⟼⋆ t' -> k ⊩ₜₘ t'.
Proof.
  intros; induction H0; auto; apply IHmulti.
  now apply evaluate_preserves_valid_term with (t := x).
Qed.

Lemma indexed_preserves_valid_term : forall n t t' k,
  k ⊩ₜₘ t -> k ⊨ t ⊢ n ⟶ t' -> k ⊩ₜₘ t'.
Proof.
  intro n; induction n; intros t t' k Hvt Hi.
  - inversion Hi; subst; assumption.
  - inversion Hi; subst; apply IHn with (t := y); try assumption.
    now apply evaluate_preserves_valid_term with (t := t).
Qed. 

Theorem evaluate_valid_weakening_gen : forall t t' lb lb' k k',
  lb <= lb' -> k <= lb -> k' <= lb' -> k <= k' -> lb' - lb = k' - k ->
  lb ⊨ t ⟼ t' -> lb' ⊨ ([⧐ₜₘ k ≤ {k' - k}] t) ⟼ ([⧐ₜₘ k ≤ {k' - k}] t').
Proof.
  intros t t' lb lb' k k' Hle1 Hle Hle' Hle2 Heq eT;
  revert lb' k k' Hle Hle1 Hle2 Hle' Heq; induction eT; 
  intros lb' k k' Hle Hle1 Hle2 Hle' Heq; simpl; eauto;
  try (constructor; eauto; now apply Term.shift_value_iff).
  - rewrite subst_shift_spec_2; auto. rewrite <- Heq. replace (lb + (lb' - lb)) with lb' by lia.
    constructor; now apply Term.shift_value_iff.
  - rewrite subst_shift_spec_2; auto. rewrite <- Heq. replace (lb + (lb' - lb)) with lb' by lia.
    constructor.
  - constructor; try (now rewrite <- Term.shift_value_iff); apply IHeT; lia.
Qed.

Theorem multi_evaluate_valid_weakening_gen : forall t t' lb lb' k k',
  lb <= lb' -> k <= lb -> k' <= lb' -> k <= k' -> lb' - lb = k' - k ->
  lb ⊨ t ⟼⋆ t' -> lb' ⊨ ([⧐ₜₘ k ≤ {k' - k}] t) ⟼⋆ ([⧐ₜₘ k ≤ {k' - k}] t').
Proof.
  intros; induction H4; try now constructor.
  eapply multi_step with (y := <[[⧐ₜₘ k ≤ {k' - k}] y ]>); auto.
  eapply evaluate_valid_weakening_gen with (lb := k0); auto.
Qed.

Theorem indexed_evaluate_valid_weakening_gen : forall t t' lb lb' k k' n,
  lb <= lb' -> k <= lb -> k' <= lb' -> k <= k' -> lb' - lb = k' - k ->
  lb ⊨ t ⊢ n ⟶ t' -> lb' ⊨ ([⧐ₜₘ k ≤ {k' - k}] t) ⊢ n ⟶ ([⧐ₜₘ k ≤ {k' - k}] t').
Proof.
  intros; induction H4; try now constructor.
  eapply index_step with (y := <[[⧐ₜₘ k ≤ {k' - k}] y ]>); auto.
  eapply evaluate_valid_weakening_gen with (lb := lb); auto.
Qed.

(** *** Determinism *)

Theorem evaluate_deterministic : forall k t t1 t2,
  k ⊨ t ⟼ t1 -> k ⊨ t ⟼ t2 -> t1 = t2.
Proof with eauto.
  intros k t t' t'' E1 E2; generalize dependent t''.
  induction E1; intros t'' E2; inversion E2; subst; try (f_equal; now auto); 
  exfalso; try (eapply value_normal; now eauto); clear E2...
  - eapply value_normal in H...
  - inversion E1; subst.
    -- eapply value_normal in H0...
    -- eapply value_normal in H2...
  - inversion H3; subst.
    -- eapply value_normal in H...
    -- eapply value_normal in H0...
  - inversion E1; subst.
    -- eapply value_normal in H0...
    -- eapply value_normal in H2...
  - inversion H3; subst.
    -- eapply value_normal in H...
    -- eapply value_normal in H0...
Qed.

Theorem indexed_deterministic : forall n k t t1 t2,
  k ⊨ t ⊢ n ⟶ t1 -> k ⊨ t ⊢ n ⟶ t2 -> t1 = t2.
Proof.
intros n; induction n; intros k t t1 t2 Hev1 Hev2.
- inversion Hev1; inversion Hev2; subst; reflexivity.
- inversion Hev1; inversion Hev2; subst.
  apply evaluate_deterministic with (t1 := y) in H6; auto; subst. 
  now apply IHn with (k := k) (t := y0).
Qed.


(** *** Halts *)

Lemma value_halts : forall k t, value(t) -> halts k t.
Proof. 
  intros k t Hv; unfold halts; exists t; split; try assumption.
  apply multi_refl.
Qed.

Lemma evaluate_preserves_halting : forall k t t',
  k ⊨ t ⟼ t' -> (halts k t <-> halts k t').
Proof.
  intros k t t' HeT; unfold halts; split; intros [t'' [HmeT Hv]].
  - destruct HmeT.
    -- exfalso; apply (value_normal k) in Hv; unfold normal_form,not in Hv; apply Hv.
      now exists t'.
    -- apply (evaluate_deterministic k x t' y HeT) in H as Heq; subst.
      exists z; split; assumption.
  - exists t''; split; try assumption; now apply multi_step with (y := t').     
Qed.

Lemma multi_preserves_halting : forall k t t',
  k ⊨ t ⟼⋆ t' -> (halts k t <-> halts k t').
Proof.
  intros k t t' HmeT; induction HmeT; unfold halts; split; intros [t'' [HmeT' Hv]];
  try (exists t''; now split).
  - apply evaluate_preserves_halting in H as H'.
    assert (halts k x). { exists t''; now split. }
    rewrite H' in H0; now rewrite IHHmeT in H0.
  - apply evaluate_preserves_halting in H as H'.
    assert (halts k z). { exists t''; now split. }
    rewrite <- IHHmeT in H0. now rewrite <- H' in H0.
Qed.

Lemma halts_weakening : forall k k' t, k <= k' -> halts k t -> halts k' <[[⧐ₜₘ k ≤ {k' - k}] t]>.
Proof.
  unfold halts; intros. destruct H0 as [t' [HeT Hvt']].
  exists <[[⧐ₜₘ k ≤ {k' - k}] t']>; split.
  - eapply multi_evaluate_valid_weakening_gen; eauto.
  - now apply Term.shift_value_iff.
Qed.

Lemma halts_pair : forall k t1 t2,
  halts k <[⟨t1,t2⟩]> <-> halts k t1 /\ halts k t2.
Proof.
  assert (Hpair : forall k t1 t2 t, k ⊨ ⟨t1,t2⟩ ⟼⋆ t -> exists t1' t2', t = <[⟨t1',t2'⟩]>).
  {
    intros k t1 t2 t HeT; dependent induction HeT; subst.
    - exists t1; now exists t2.
    - inversion H; subst; eauto. 
  }
  intros k t1 t2; split; intros HA.
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

Lemma evaluate_indexed_1_iff : forall k t t',
  k ⊨ t ⟼ t' <-> k ⊨ t ⊢ 1 ⟶ t'.
Proof.
  split; intros.
  - replace 1 with (0 + 1); eauto; 
    eapply index_step; eauto; apply index_refl; auto.
  - inversion H; subst. inversion H3; subst; auto.
Qed.

Lemma multi_indexed : forall lb t t',
  lb ⊨ t ⟼⋆ t' -> exists k, lb ⊨ t ⊢ k ⟶ t'.
Proof.
  intros. induction H.
  - exists 0. apply index_refl; auto.
  - destruct IHmulti. exists (S x0). eapply index_step; eauto.
Qed.

(** ** Preservation *)

(** *** Proof of preservation of typing through the evaluation transition

  **** Hypothesis

  Knowing the context is valid regards of its own new key (1),
  the term t is well typed according to a certain context Re (2), 
  there is a certain t' that is the result of t after one step of transition (3);

  **** Result

  We can state that the term t' is well typed. 
*)
Theorem evaluate_preserves_typing : forall Re t t' τ,
  (* (1) *) newᵣᵪ(Re) ⊩ᵣᵪ Re ->
  (* (2) *) ∅ᵥᵪ ⋅ Re ⊫ t ∈ τ -> 
  (* (3) *) (newᵣᵪ(Re)) ⊨ t ⟼ t' -> 

  ∅ᵥᵪ ⋅ Re ⊫ t' ∈ τ.
Proof. 
  intros Re t t' τ HvRe Hwt; generalize dependent t'; dependent induction Hwt; intros t' HeTt;
  inversion HeTt; subst; try (econstructor; now eauto); eauto.
  - inversion Hwt1; subst. eapply subst_preserves_typing; eauto.
  - inversion Hwt2; subst; inversion Hwt1.
  - inversion Hwt; subst; auto.
  - inversion Hwt; subst; auto.
  - inversion Hwt; subst. eapply subst_preserves_typing; eauto. constructor; eauto.
  - econstructor; eauto. apply IHHwt2; auto.
    -- rewrite RContext.new_key_wh_spec; apply RContext.valid_wh_spec; auto;
        unfold Typ.PairTyp.valid; simpl; split; try (constructor);
        apply well_typed_implies_valid in Hwt1 as [_ Hvτ]; auto; apply VContext.valid_empty_spec.
    -- now rewrite RContext.new_key_wh_spec.
Qed.

(** *** Proof of preservation of typing through multiple evaluation transitions

  **** Hypothesis

  Knowing the context is valid regards of its own new key (1),
  the term t is well typed according to a certain context Re (2), 
  there is a certain t' that is the result of t after zero or k steps of transition (3);

  **** Result

  We can state that the term t' is well typed. 
*)
Theorem multi_preserves_typing : forall Re t t' τ,
  (* (1) *) newᵣᵪ(Re) ⊩ᵣᵪ Re ->
  (* (2) *) ∅ᵥᵪ ⋅ Re ⊫ t ∈ τ -> 
  (* (3) *) (newᵣᵪ(Re)) ⊨ t ⟼⋆ t' -> 
  
  ∅ᵥᵪ ⋅ Re ⊫ t' ∈ τ.
Proof.
  intros Re t t' τ HvRe Hwt HmeT; dependent induction HmeT; subst; try assumption.
  apply IHHmeT; auto. eapply (evaluate_preserves_typing Re x y τ HvRe Hwt H).
Qed.

(** ** Progress *)

(** *** Proof of progress of the evaluation transtion

  If the term is well typed then 
  - either we have a value (1) or 
  - we can evaluate at least one time the term (2).

*)
Theorem progress_of_evaluate : forall t Re τ,
  ∅ᵥᵪ ⋅ Re ⊫ t ∈ τ -> 
  
  (* (1) *) value(t) \/ 
  (* (2) *) exists t', (newᵣᵪ(Re)) ⊨ t ⟼ t'.
Proof.
  intro t; induction t; intros Re τ' Hwt; inversion Hwt; subst; 
  try (now left); try (apply IHt1 in H3 as H3'; apply IHt2 in H5 as H5').
  - destruct H3',H5'; right. 
    -- inversion H; subst; inversion H3; subst. exists <[[x:= t2 ~ {newᵣᵪ(Re)} ≤ 0] t]>.
      now constructor.
    -- destruct H0; exists <[t1 x]>; now constructor.
    -- destruct H; exists <[x t2]>; now constructor.
    -- destruct H; exists <[x t2]>; now constructor.
  - right; apply IHt2 in H4 as H4'; destruct H4'.
    -- destruct t2; inversion H4; subst; inversion H; subst.
        exists <[[v := Fix (\ v : τ', t2) ~ {newᵣᵪ(Re)} ≤ 0] t2]>; constructor.
    -- destruct H; exists <[Fix x]>; constructor; auto.
  - destruct H3',H5'; auto.
    -- right; destruct H0; exists <[⟨t1,x⟩]>; now constructor.
    -- right; destruct H; exists <[⟨x,t2⟩]>; now constructor.
    -- right; destruct H; exists <[⟨x,t2⟩]>; now constructor.
  - apply IHt in H2 as H2'; destruct H2'; right.
    -- inversion H; subst; inversion H2; subst; exists v1; now constructor. 
    -- destruct H; exists (Term.tm_fst x); now constructor.
  - apply IHt in H2 as H2'; destruct H2'; right.
    -- inversion H; subst; inversion H2; subst; exists v2; now constructor. 
    -- destruct H; exists (Term.tm_snd x); now constructor.
  - apply IHt in H2 as H2'; destruct H2' as [Hvt | [t' HeT']]; 
    try (left; now constructor); right; exists <[arr(t')]>; now constructor.
  - apply IHt in H3 as H3'; destruct H3' as [Hvt | [t' HeT']]; 
    try (left; now constructor); right; exists <[first(τ:t')]>; now constructor.
  - apply IHt1 in H1 as H1'; apply IHt2 in H5 as H5';
    destruct H1' as [Hvt1 | [t1' HeT1']]; destruct H5' as [Hvt2 | [t2' HeT2']];
    try (left; now constructor); right.
    -- exists <[t1 >>> t2']>; now constructor.
    -- exists <[t1' >>> t2]>; now constructor.
    -- exists <[t1' >>> t2]>; now constructor.
  - apply IHt1 in H1 as H1'; apply IHt2 in H8 as H8';
    destruct H1' as [Hvt1 | [t1' HeT1']]; destruct H8' as [Hvt2 | [t2' HeT2']];
    try (left; now constructor); right.
    -- exists <[wormhole(t1;t2')]>; constructor; auto.
        unfold k in HeT2'; rewrite RContext.new_key_wh_spec in HeT2'; auto.
    -- exists <[wormhole(t1';t2)]>; now constructor.
    -- exists <[wormhole(t1';t2)]>; now constructor.
Qed.

(** *** Some corollaries *)  

Corollary evaluate_valid_weakening : forall t t' k k',
  k <= k' ->
  k ⊨ t ⟼ t' -> k' ⊨ ([⧐ₜₘ k ≤ {k' - k}] t) ⟼ ([⧐ₜₘ k ≤ {k' - k}] t').
Proof. intros. apply evaluate_valid_weakening_gen with (lb := k); eauto. Qed.

Corollary multi_evaluate_valid_weakening : forall t t' k k',
  k <= k' ->
  k ⊨ t ⟼⋆ t' -> k' ⊨ ([⧐ₜₘ k ≤ {k' - k}] t) ⟼⋆ ([⧐ₜₘ k ≤ {k' - k}] t').
Proof. intros; apply multi_evaluate_valid_weakening_gen with (lb := k); auto. Qed.

Corollary indexed_evaluate_valid_weakening : forall t t' k k' n,
  k <= k' ->
  k ⊨ t ⊢ n ⟶ t' -> k' ⊨ ([⧐ₜₘ k ≤ {k' - k}] t) ⊢ n ⟶ ([⧐ₜₘ k ≤ {k' - k}] t').
Proof. intros; apply indexed_evaluate_valid_weakening_gen with (lb := k); auto. Qed.