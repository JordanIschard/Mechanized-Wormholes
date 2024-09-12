From Coq Require Import Classical_Prop Bool.Bool Relations.Relation_Operators Lia Classes.RelationClasses Program.
From Mecha Require Import Typ Resource Term Var VContext RContext Typing ET_Definition.
Import VarNotations ResourceNotations TermNotations TypNotations RContextNotations.

Open Scope term_scope.

(** * Transition - Evaluation - Properties *)

(** ** Substitution function *)

(** *** Substitution regards of variables *)

Lemma subst_afi_refl : forall t x lb k,
  ~ isFV(x,t) -> forall v, <[ [x:= v ~ lb – k] t ]> = t.
Proof with eauto.
  intros t; induction t; unfold not; intros x lb k afi v1; try (now simpl);
  try (simpl; f_equal; now eauto).
  - simpl. destruct (Var.eqb_spec x v); subst; auto; exfalso; apply afi; constructor.
  - simpl; destruct (Var.eqb_spec x v); subst; auto.
    f_equal; apply IHt; unfold not; intros; apply afi; now constructor.
Qed.

Lemma subst_closed_refl : forall t lb k,
  cl(t) -> forall x t', <[ [x := t' ~ lb – k] t ]> = t.
Proof. intros. apply subst_afi_refl. apply H. Qed.

Lemma subst_refl : forall v (x : variable) lb, <[[x := v ~ lb – 0] x]> = v.
Proof. intros v x lb; simpl; rewrite Var.eqb_refl; now apply Term.shift_zero_refl. Qed.

Lemma closed_subst_not_afi : forall t x v lb k,
  cl(v) ->  ~ isFV(x,<[ [x := v ~ lb – k] t ]>).
Proof.
  unfold Term.closed, not; intro t; induction t; intros x v1 lb k Hcl HFV; simpl;
  try (inversion HFV; subst; now eauto); simpl in *;
  try (destruct (Var.eqb_spec x v); subst; eauto).
  - apply (Hcl v). rewrite Term.shift_afi_iff; eauto.
  - inversion HFV; auto.
  - inversion HFV; subst; eauto.
  - inversion HFV; subst; eauto.
Qed.

Lemma subst_shadow : forall t' x t v lb k,
  cl(v) -> <[[x := t ~ lb – k] ([ x := v ~ lb – k] t')]> = <[ [x := v ~ lb – k] t' ]>.
Proof. intros; eapply subst_afi_refl; apply closed_subst_not_afi; assumption. Qed.

Lemma subst_permute : forall t x x1 v v1 lb k,
  x <> x1 -> cl(v) -> cl(v1) ->
  <[[x1 := v1 ~ lb – k] ([ x := v ~ lb – k] t)]> = <[[x := v ~ lb – k] ([ x1 := v1 ~ lb – k] t)]>.
Proof.
  intro t; induction t; intros; simpl; try (now reflexivity); try (f_equal; now auto).
  - (* var *)
    destruct (Var.eqb_spec x v); destruct (Var.eqb_spec x1 v); subst; simpl.
    -- now contradiction H.
    -- rewrite Var.eqb_refl; rewrite subst_closed_refl; auto; now rewrite <- Term.shift_closed_iff.
    -- rewrite Var.eqb_refl; rewrite subst_closed_refl; auto; now rewrite <- Term.shift_closed_iff.
    -- rewrite <- Var.eqb_neq in *; rewrite n; now rewrite n0.
  - destruct (Var.eqb_spec x v); destruct (Var.eqb_spec x1 v); subst; simpl.
    -- now contradiction H.
    -- rewrite Var.eqb_refl; rewrite <- Var.eqb_neq in n; now rewrite n.
    -- rewrite Var.eqb_refl; rewrite <- Var.eqb_neq in n; now rewrite n.
    -- rewrite <- Var.eqb_neq in n,n0; rewrite n,n0; f_equal; now apply IHt.
Qed.

(** *** Substitution modulo shift function *)

Lemma subst_shift_spec : forall lb k k' t x v,
  <[[⧐ lb – k] ([x := v ~ lb – k'] t)]> = 
  <[[x := ([⧐ lb – k] v) ~ lb – k'] ([⧐ lb – k] t)]>.
Proof.
  intros lb k k' t; revert lb k k'; induction t; intros lb k k' x v1; simpl;
  f_equal; eauto.
  - destruct (Var.eqb_spec x v); subst.
    -- apply Term.shift_permute.
    -- now simpl.
  - destruct (Var.eqb x v); simpl; try reflexivity; f_equal; auto.
Qed.

Lemma subst_shift_spec_1 : forall lb k k' t x v,
  <[[⧐ lb – k] ([x := v ~ lb – k'] t)]> = 
  <[[x := ([⧐ lb – k] v) ~ {lb + k} – k'] ([⧐ lb – k] t)]>.
Proof.
  intros lb k k' t; revert lb k k'; induction t; intros lb k k' x v1; simpl;
  f_equal; eauto.
  - destruct (Var.eqb_spec x v); subst.
    -- apply Term.shift_permute_1.
    -- now simpl.
  - destruct (Var.eqb x v); simpl; try reflexivity; f_equal; auto.
Qed.

Lemma subst_shift_spec_2 : forall lb lb' k k' t x v,
  lb <= lb' ->
  <[[⧐ lb – k] ([x := v ~ lb' – k'] t)]> = 
  <[[x := ([⧐ lb – k] v) ~ {lb' + k} – k'] ([⧐ lb – k] t)]>.
Proof.
  intros lb lb' k k' t; revert lb lb' k k'; induction t; intros lb lb' k k' x v1 Hle; simpl;
  f_equal; eauto.
  - destruct (Var.eqb_spec x v); simpl; try reflexivity.
    now apply Term.shift_permute_2.
  - destruct (Var.eqb_spec x v); simpl; f_equal; auto.
Qed.

(** *** Valid through substitution *)

Lemma subst_preserves_valid : forall k k' v x t,
  k >= k' -> k ⊩ t -> k' ⊩ v -> k ⊩ <[[x := v ~ k' – {k - k'}] t]>.
Proof.
  intros k k' v x t; revert k k'; induction t; intros k k' Hle Hvt Hvv; auto;
  try (unfold Term.valid in *; inversion Hvt; subst; constructor; now eauto).
  - simpl; destruct (Var.eqb_spec x v0); subst; auto.
    replace k with (k' + (k - k')) at 1 by lia.
    now apply Term.shift_preserves_valid.
  - unfold Term.valid in *; inversion Hvt; subst; simpl. 
    destruct (Var.eqb_spec x v0); subst; auto; constructor; auto.
  - unfold Term.valid in *; inversion Hvt; subst; simpl; constructor; auto. 
    replace (S (S (k - k'))) with ((S (S k)) - k'); try lia. 
    apply IHt2; auto.
Qed.

Lemma subst_preserves_valid_4 : forall k x v t,
  k ⊩ t ->  k ⊩ v -> k ⊩ <[[x := v ~ k] t]>.
Proof.
  intros k x v t Hvt; replace 0 with (k - k) by lia. 
  apply subst_preserves_valid; auto.
Qed.

(** ** Evaluation Transition *)


(** *** Transitivity of multiple evaluation steps *)

#[export] Instance multi_trans : forall k, Transitive (multi k).
Proof.
  red; intros k x y z HmeT HmeT'; induction HmeT; try assumption.
  eapply rt1n_trans; eauto. now apply IHHmeT.
Qed.

Lemma indexed_trans : forall lb k k' t t' t'',
lb ⊨ t ⊢ k ⟶ t' -> lb ⊨ t' ⊢ k' ⟶ t'' -> lb ⊨ t ⊢ (k+k') ⟶ t''.
Proof.
  induction k; intros.
  - simpl; inversion H; subst; auto.
  - inversion H; subst. simpl. apply index_step with (y := y); auto.
    eapply IHk; eauto.
Qed.

(** *** Reflexivity of multiple evaluation steps *)

#[export] Instance multi_refl k : Reflexive (multi k).
Proof. repeat red; intros; apply rt1n_refl. Qed. 

Hint Constructors clos_refl_trans_1n : core.
Hint Resolve multi_refl multi_trans : core.

(** *** Lift semantics rules from evaluation to multi evaluation *)

Lemma multi_var : forall k (x : variable), k ⊨ x ⟼⋆ x.
Proof. now intros k x. Qed.

Lemma multi_appv : forall k x t τ v, 
  value(v) -> k ⊨ ((\x:τ, t) v) ⟼⋆ ([x := v ~ k – 0] t).
Proof. 
  intros k x t τ v Hv.
   apply rt1n_trans with (y := <[[x := v ~ k – 0] t]>); auto.
Qed.

Lemma multi_fix : forall k x t τ, 
  k ⊨ (Fix (\x:τ, t)) ⟼⋆ ([x := (Fix (\x:τ, t)) ~ k – 0] t).
Proof. 
  intros k x t τ. 
  apply rt1n_trans with (y := <[[x := (Fix (\x:τ, t)) ~ k – 0] t]>); auto.
Qed.

Lemma multi_app1 : forall k t t' t2, k ⊨ t ⟼⋆ t' -> k ⊨ (t t2) ⟼⋆ (t' t2).
Proof. 
  intros k t t' t2 HeT; induction HeT; subst; auto; try reflexivity.
  apply rt1n_trans with <[y t2]>; auto.
Qed.

Lemma multi_app2 : forall k t t' t1, value(t1) -> k ⊨ t ⟼⋆ t' -> k ⊨ (t1 t) ⟼⋆ (t1 t').
Proof. 
  intros k t t' t1 Hvt HeT; induction HeT; subst; auto; try reflexivity.
  apply rt1n_trans with <[t1 y]>; auto.
Qed.

Lemma multi_pair1 : forall k t t' t2, k ⊨ t ⟼⋆ t' -> k ⊨ ⟨t,t2⟩ ⟼⋆ ⟨t',t2⟩.
Proof.
  intros k t t' t2 HeT; induction HeT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[⟨y,t2⟩]>; auto. 
Qed.

Lemma multi_pair2 : forall k t t' t1, value(t1) -> k ⊨ t ⟼⋆ t' -> k ⊨ ⟨t1,t⟩ ⟼⋆ ⟨t1,t'⟩.
Proof.
  intros k t t' t1 Hvt HeT; induction HeT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[⟨t1,y⟩]>; auto. 
Qed.

Lemma multi_fstv : forall k t1 t2, value(t1) -> value(t2) -> k ⊨ ⟨t1,t2⟩.fst ⟼⋆ t1.
Proof.
  intros k t1 t2 Hvt1 Hvt2; apply rt1n_trans with t1; auto.
Qed.

Lemma multi_fst1 : forall k t t', k ⊨ t ⟼⋆ t' -> k ⊨ t.fst ⟼⋆ t'.fst.
Proof.
  intros k t t' HeT; induction HeT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[y.fst]>; auto. 
Qed.

Lemma multi_sndv : forall k t1 t2, value(t1) -> value(t2) -> k ⊨ ⟨t1,t2⟩.snd ⟼⋆ t2.
Proof.
  intros k t1 t2 Hvt1 Hvt2; apply rt1n_trans with t2; auto.
Qed.

Lemma multi_snd1 : forall k t t', k ⊨ t ⟼⋆ t' -> k ⊨ t.snd ⟼⋆ t'.snd.
Proof.
  intros k t t' HeT; induction HeT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[y.snd]>; auto. 
Qed.

Lemma multi_arr : forall k t t', k ⊨ t ⟼⋆ t' -> k ⊨ arr(t) ⟼⋆ arr(t').
Proof.
  intros k t t' HeT; induction HeT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[arr(y)]>; auto. 
Qed.

Lemma multi_first : forall k τ t t', k ⊨ t ⟼⋆ t' -> k ⊨ first(τ:t) ⟼⋆ first(τ:t').
Proof.
  intros k τ t t' HeT; induction HeT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[first(τ:y)]>; auto. 
Qed.

Lemma multi_comp1 : forall k t t' t2, k ⊨ t ⟼⋆ t' -> k ⊨ t >>> t2 ⟼⋆ t' >>> t2.
Proof. 
  intros k t t' t2 HeT; induction HeT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[y >>> t2]>; auto.
Qed.

Lemma multi_comp2 : forall k t t' t1, value(t1) -> k ⊨ t ⟼⋆ t' -> k ⊨ t1 >>> t ⟼⋆ t1 >>> t'.
Proof. 
  intros k t t' t1 Hvt HeT; induction HeT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[t1 >>> y]>; auto.
Qed.

Lemma multi_wh1 : forall k t t' t2, k ⊨ t ⟼⋆ t' -> k ⊨ wormhole(t;t2) ⟼⋆ wormhole(t';t2).
Proof. 
  intros k t t' t2 HeT; induction HeT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[wormhole(y;t2)]>; auto.
Qed.

Lemma multi_wh2 : forall k t t' t1, 
  value(t1) -> (S (S k)) ⊨ t ⟼⋆ t' -> k ⊨ wormhole(t1;t) ⟼⋆ wormhole(t1;t').
Proof. 
  intros k t t' t1 Hvt HeT; dependent induction HeT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[wormhole(t1;y)]>; auto.
    apply (IHHeT k); auto.
Qed.

(** *** Value regards of evaluation transition *)

Lemma value_normal : forall k t, value(t) -> normal_form k t.
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

(** *** Valid *)

Lemma evaluate_preserves_valid_term : forall t t' k,
  k ⊩ t -> k ⊨ t ⟼ t' -> k ⊩ t'.
Proof.
  intros t; induction t; intros t' k Hvt HeTt; inversion Hvt; inversion HeTt; 
  subst; auto; try (constructor; fold Term.valid in *; auto).
  - inversion Hvt; subst; inversion H4; subst. now apply subst_preserves_valid_4.
  - inversion Hvt; subst. inversion H5; subst; apply subst_preserves_valid_4; auto.
  - inversion H1; subst; auto.
  - inversion H1; subst; auto.
Qed.

Lemma multi_preserves_valid_term : forall k t t',
  k ⊩ t -> k ⊨ t ⟼⋆ t' -> k ⊩ t'.
Proof.
  intros; induction H0; auto. apply IHclos_refl_trans_1n.
  now apply evaluate_preserves_valid_term with (t := x).
Qed.

Lemma indexed_preserves_valid_term : forall n t t' k,
  k ⊩ t -> k ⊨ t ⊢ n ⟶ t' -> k ⊩ t'.
Proof.
  intro n; induction n; intros t t' k Hvt Hi.
  - inversion Hi; subst; assumption.
  - inversion Hi; subst; apply IHn with (t := y); try assumption.
    now apply evaluate_preserves_valid_term with (t := t).
Qed. 

Theorem evaluate_valid_weakening_gen : forall t t' lb lb' k k',
  lb <= lb' -> k <= lb -> k' <= lb' -> k <= k' -> lb' - lb = k' - k ->
  lb ⊨ t ⟼ t' -> lb' ⊨ ([⧐ k – {k' - k}] t) ⟼ ([⧐ k – {k' - k}] t').
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
  lb ⊨ t ⟼⋆ t' -> lb' ⊨ ([⧐ k – {k' - k}] t) ⟼⋆ ([⧐ k – {k' - k}] t').
Proof.
  intros; induction H4; try now constructor.
  eapply rt1n_trans with (y := <[[⧐ k – {k' - k}] y ]>); auto.
  eapply evaluate_valid_weakening_gen with (lb := lb); auto.
Qed.

Theorem indexed_evaluate_valid_weakening_gen : forall t t' lb lb' k k' n,
  lb <= lb' -> k <= lb -> k' <= lb' -> k <= k' -> lb' - lb = k' - k ->
  lb ⊨ t ⊢ n ⟶ t' -> lb' ⊨ ([⧐ k – {k' - k}] t) ⊢ n ⟶ ([⧐ k – {k' - k}] t').
Proof.
  intros; induction H4; try now constructor.
  eapply index_step with (y := <[[⧐ k – {k' - k}] y ]>); auto.
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
  apply rt1n_refl.
Qed.

Lemma evaluate_preserves_halting : forall k t t',
  k ⊨ t ⟼ t' -> (halts k t <-> halts k t').
Proof.
  intros k t t' HeT; unfold halts; split; intros [t'' [HmeT Hv]].
  - destruct HmeT.
    -- exfalso; apply (value_normal k) in Hv; unfold normal_form,not in Hv; apply Hv.
      now exists t'.
    -- apply (evaluate_deterministic k t t' y HeT) in H as Heq; subst.
      exists z; split; assumption.
  - exists t''; split; try assumption; now apply rt1n_trans with (y := t').     
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

Lemma halts_weakening : forall k k' t, k <= k' -> halts k t -> halts k' <[[⧐ k – {k' - k}] t]>.
Proof.
  unfold halts; intros. destruct H0 as [t' [HeT Hvt']].
  exists <[[⧐ k – {k' - k}] t']>; split.
  - eapply multi_evaluate_valid_weakening_gen; eauto.
  - now apply Term.shift_value_iff.
Qed.

Lemma halts_weakening_1 : 
  forall k k' t, halts k t -> halts (k + k') <[[⧐ k – k'] t]>.
Proof.
  intros. 
  replace <[[⧐ k – k'] t]> with <[[⧐ k – {(k + k') - k}] t ]> by (f_equal; lia).
  apply halts_weakening; auto; lia.
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
       + exists t1; split; now auto.
       + exists t2; split; now auto.
    -- inversion H; subst.
       + eapply IHHmeT with (t1' := t1') (t2' := t2') in Hvt; auto.
         destruct Hvt; split; auto; clear H1.
         rewrite evaluate_preserves_halting; eauto.
       + eapply IHHmeT with (t1 := t1) (t2 := t') in Hvt; eauto.
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

Lemma halts_first : forall k τ t,
  halts k <[first(τ:t)]> <-> halts k t.
Proof.
  intros k τ t; split; intros HA.
  - destruct HA as [t' [HmeT Hvt]]; dependent induction HmeT.
    -- inversion Hvt; subst; exists t; split; auto.  apply rt1n_refl.
    -- inversion H; subst. apply (IHHmeT τ t') in Hvt; eauto.
       rewrite evaluate_preserves_halting; eauto.
  - destruct HA as [t' [HmeT Hvt']]; exists <[first(τ:t')]>; split; auto.
    now apply multi_first.
Qed.

Lemma halts_comp : forall k t1 t2,
  halts k <[t1 >>> t2]> <-> halts k t1 /\ halts k t2.
Proof.
  assert (Hcomp : forall k t1 t2 t, k ⊨ t1 >>> t2 ⟼⋆ t ->
                             exists t1' t2', t = <[t1' >>> t2']>).
  {
    intros k t1 t2 t HeT; dependent induction HeT; subst.
    - exists t1; now exists t2.
    - inversion H; subst; eauto. 
  }
  intros k t1 t2; split; intros HA.
  - destruct HA as [t [HmeT Hvt]]. apply Hcomp in HmeT as Heq.
    destruct Heq as [t1' [t2' Heq]]; subst. dependent induction HmeT.
    -- inversion Hvt; subst; split.
       + exists t1; split; now auto.
       + exists t2; split; now auto.
    -- inversion H; subst.
       + eapply IHHmeT with (t1 := t1'0) (t2 := t2) in Hvt; eauto.
         destruct Hvt; split; auto; clear H1.
         rewrite evaluate_preserves_halting; eauto.
       + eapply IHHmeT with (t1 := t1) (t2 := t') in Hvt; eauto.
         destruct Hvt; split; auto; clear H0.
         rewrite evaluate_preserves_halting; eauto.
  - destruct HA. destruct H as [t1' [HmeT1 Hvt1']];
    destruct H0 as [t2' [HmeT2 Hvt2']].
    exists <[t1' >>> t2']>; split.
    -- apply multi_trans with <[t1' >>> t2]>.
       + now apply multi_comp1.
       + now apply multi_comp2.
    -- now constructor.
Qed.

Lemma halts_wh : forall k t1 t2,
  halts k <[wormhole(t1;t2)]> <-> halts k t1 /\ halts (S (S k)) t2.
Proof.
  assert (Hwh : forall k t1 t2 t, k ⊨ wormhole(t1;t2) ⟼⋆ t ->
                             exists t1' t2', t = <[wormhole(t1';t2')]>).
  {
    intros k t1 t2 t HeT; dependent induction HeT; subst.
    - exists t1; now exists t2.
    - inversion H; subst; eauto. 
  }
  intros k t1 t2; split; intros HA.
  - destruct HA as [t [HmeT Hvt]]. apply Hwh in HmeT as Heq.
    destruct Heq as [t1' [t2' Heq]]; subst. dependent induction HmeT.
    -- inversion Hvt; subst; split.
       + exists t1; split; now auto.
       + exists t2; split; now auto.
    -- inversion H; subst.
       + eapply IHHmeT with (t1 := i') (t2 := t2) in Hvt; eauto.
         destruct Hvt; split; auto; clear H1.
         rewrite evaluate_preserves_halting; eauto.
       + eapply IHHmeT with (t1 := t1) (t2 := t') in Hvt; eauto.
         destruct Hvt; split; auto; clear H0.
         rewrite evaluate_preserves_halting; eauto.
  - destruct HA. destruct H as [t1' [HmeT1 Hvt1']];
    destruct H0 as [t2' [HmeT2 Hvt2']].
    exists <[wormhole(t1';t2')]>; split.
    -- apply multi_trans with <[wormhole(t1';t2)]>.
       + now apply multi_wh1.
       + now apply multi_wh2.
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
  - destruct IHclos_refl_trans_1n. exists (S x0). eapply index_step; eauto.
Qed.


(** *** Some corollaries *)  

Corollary evaluate_valid_weakening : forall t t' k k',
  k <= k' ->
  k ⊨ t ⟼ t' -> k' ⊨ ([⧐ k – {k' - k}] t) ⟼ ([⧐ k – {k' - k}] t').
Proof. intros. apply evaluate_valid_weakening_gen with (lb := k); eauto. Qed.

Corollary multi_evaluate_valid_weakening : forall t t' k k',
  k <= k' ->
  k ⊨ t ⟼⋆ t' -> k' ⊨ ([⧐ k – {k' - k}] t) ⟼⋆ ([⧐ k – {k' - k}] t').
Proof. intros; apply multi_evaluate_valid_weakening_gen with (lb := k); auto. Qed.

Corollary indexed_evaluate_valid_weakening : forall t t' k k' n,
  k <= k' ->
  k ⊨ t ⊢ n ⟶ t' -> k' ⊨ ([⧐ k – {k' - k}] t) ⊢ n ⟶ ([⧐ k – {k' - k}] t').
Proof. intros; apply indexed_evaluate_valid_weakening_gen with (lb := k); auto. Qed.