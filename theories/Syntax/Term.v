From Coq Require Import Classes.Morphisms Lia.
From DeBrLevel Require Import LevelInterface Level OptionLevel.
From Mecha Require Import Var Resource Typ.


(** * Syntax - Term

  The Wormholes set of terms is an extended lambda calculus with classical arrows and two additional primitives named [rsf] and [wormhole].
*)

Module Term <: IsLvlDTWL.

(** ** Definitions *)


(** *** Inductive defintion of terms 

  The set of terms consists of an extended lambda calculus with pairs, projections, fixpoint, ground value (denoted [()]), as well as arrow primitives, i.e. [arr], [first] and [comp] (denoted [>>>]). Moreover, there are [rsf] and [wormhole], two additional arrow primitives. The former access to the environment through resources (see [Resource]). The latter creates local scope for two resources which will be used as local reference.
*)
Inductive raw : Type :=
  | tm_unit : raw
  | tm_var (x: Var.t) : raw
  | tm_abs (x: Var.t) (A: Typ.t) (t: raw) : raw
  | tm_app (t1 t2: raw) : raw
  | tm_pair (t1 t2: raw) : raw
  | tm_fix (t: raw) : raw
  | tm_fst (t: raw) : raw
  | tm_snd (t: raw) : raw
  | tm_arr (t: raw) : raw
  | tm_first (A: Typ.t) (t: raw) : raw
  | tm_rsf (r: Resource.t) : raw
  | tm_comp (t1 t2: raw) : raw
  | tm_wh   (t1 t2: raw) : raw
.

Definition t := raw.
Definition eq := @eq t.

(** *** Shift function 

  The [shift] function takes a lower bound [lb] a level [k] and a term [t], and produces a term [t'] where all resources [r] greater or equal to [lb] in [t] are incremented by [k]. The others are left unchanged. It is denoted [[⧐ lb – k] t].
*)
Fixpoint shift (lb k: Lvl.t) (e: t) : t := 
  match e with
  | tm_rsf r => tm_rsf (Resource.shift lb k r)

  | tm_abs x A e' => tm_abs x (Typ.shift lb k A) (shift lb k e')
  | tm_fix e'   => tm_fix   (shift lb k e')
  | tm_fst e'   => tm_fst   (shift lb k e')
  | tm_snd e'   => tm_snd   (shift lb k e')
  | tm_arr e'   => tm_arr   (shift lb k e')
  | tm_first A e' => tm_first (Typ.shift lb k A) (shift lb k e')

  | tm_app  t1 t2 => tm_app  (shift lb k t1) (shift lb k t2)
  | tm_pair t1 t2 => tm_pair (shift lb k t1) (shift lb k t2)
  | tm_comp t1 t2 => tm_comp (shift lb k t1) (shift lb k t2)
  | tm_wh   t1 t2 => tm_wh   (shift lb k t1) (shift lb k t2)

  | _ => e
  end
.

(** *** Multi shift function 

  As done in [Resource.v], [Resources.v] and [Typ.v], we define a [multi_shift] function that applies [n] shifts for two lists [lbs] and [ks] of length [n].
*)
Definition multi_shift (lbs: list Lvl.t) (ks: list Lvl.t) (t: t) :=
  List.fold_right (fun lbk acc => shift (fst lbk) (snd lbk) acc) t (List.combine lbs ks).


(** *** Well-formedness 

  A term [t] is well-formed under the level [k] if there are at most [k] free resources and that the inductive property below is satisfied. It is denoted as the infix operator ([⊩]). 
  
  
  In the case of [wormhole(t1;t2)], the level [k] increases by two for the [t2] because of the local scope that binds two resources. Consequently, [k] and [k+1] are the level for the local resources which are free in [t2].
*)
Inductive Wf': Lvl.t -> t -> Prop :=
  | wfΛ_unit (k: Lvl.t): Wf' k tm_unit
  | wfΛ_var  (k: Lvl.t) (x: Var.t): Wf' k (tm_var x)
  | wfΛ_abs  (k: Lvl.t) (A: Typ.t) (x: Var.t) (t: t): 
             Typ.Wf k A -> Wf' k t -> Wf' k (tm_abs x A t)

  | wfΛ_app  (k: Lvl.t) (t1 t2: t): Wf' k t1 -> Wf' k t2 -> Wf' k (tm_app t1 t2)
  | wfΛ_pair (k: Lvl.t) (t1 t2: t): Wf' k t1 -> Wf' k t2 -> Wf' k (tm_pair t1 t2)

  | wfΛ_fix   (k: Lvl.t) (t: t): Wf' k t -> Wf' k (tm_fix t) 
  | wfΛ_fst   (k: Lvl.t) (t: t): Wf' k t -> Wf' k (tm_fst t) 
  | wfΛ_snd   (k: Lvl.t) (t: t): Wf' k t -> Wf' k (tm_snd t)
  | wfΛ_arr   (k: Lvl.t) (t: t): Wf' k t -> Wf' k (tm_arr t)
  | wfΛ_first (k: Lvl.t) (A: Typ.t) (t: t): 
              Typ.Wf k A -> Wf' k t -> Wf' k (tm_first A t)

  | wfΛ_rsf (k: Lvl.t) (r: Resource.t): 
            Resource.Wf k r ->  Wf' k (tm_rsf r)

  | wfΛ_comp (k: Lvl.t) (t1 t2: t): Wf' k t1 -> Wf' k t2 -> Wf' k (tm_comp t1 t2)
  | wfΛ_wh   (k: Lvl.t) (t1 t2: t): Wf' k t1 -> Wf' (S (S k)) t2 -> Wf' k (tm_wh t1 t2)
.

Definition Wf := Wf'.

#[export] Hint Constructors Wf': core.

(** *** Value 

  The set of value is a subset of the set of term [t]. In our mechanization, we define it as an inductive property. Ground values are [()], abstractions and [rsf]. We also consider as value
  pairs, and reactive terms only if all of their sub-terms are also values.
*)
Inductive value: t -> Prop :=
  | v_unit: value tm_unit
  | v_rsf (r: Resource.t): value (tm_rsf r)
  | v_abs (x: Var.t) (A: Typ.t) (t: t): value (tm_abs x A t)

  | v_arr   (v: t): value (tm_arr v)
  | v_first (A: Typ.t) (v: t): value v -> value (tm_first A v)

  | v_pair (v1 v2: t): value v1 -> value v2 -> value (tm_pair v1 v2)
  | v_comp (v1 v2: t): value v1 -> value v2 -> value (tm_comp v1 v2)
  | v_wh   (v1 v2: t): value v1 -> value v2 -> value (tm_wh v1 v2)
.

#[export] Hint Constructors value Wf': core.

(** ** Properties *)

(** *** [eq] properties *)

#[export] Instance eq_refl: Reflexive eq := _.

#[export] Instance eq_sym: Symmetric eq := _.

#[export] Instance eq_trans: Transitive eq := _.

#[export] Instance eq_rr: RewriteRelation eq := {}.

#[export] Instance eq_equiv: Equivalence eq := _.

#[export] Hint Resolve eq_refl eq_sym eq_trans: core.

Lemma eq_dec (t1 t2: t): {eq t1 t2} + {~ eq t1 t2}.
Proof.
  unfold eq; revert t2; induction t1; intro; destruct t2; simpl; auto; 
  try (right; unfold not; intros contra; now inversion contra);
  try (destruct (IHt1_1 t2_1); destruct (IHt1_2 t2_2);
  try (right; unfold not; intros; inversion H; subst; contradiction); subst; f_equal; auto);
  try (destruct (IHt1 t2); subst; try (now left); right; intro c; 
        inversion c; subst; now contradiction).
  - destruct (Var.eqb_spec x x0); subst.
    -- now left.
    -- right; intro c; inversion c; subst; clear c; now contradiction n.
  - destruct (Var.eqb_spec x x0); subst;
    destruct (IHt1 t2); subst; 
    try (right; intro c; inversion c; subst; now contradiction).
    destruct (Typ.eq_dec A A0); try unfold Typ.eq in *; subst; auto.
    right; intro c; inversion c; contradiction.
  - destruct (IHt1 t2); destruct (Typ.eq_dec A A0); 
    try unfold Typ.eq in *; subst; auto;
    right; intro c; inversion c; contradiction.
  - destruct (Resource.eq_dec r r0); subst; try now left. right; intro c; inversion c; subst;
    contradiction.
Qed.

Lemma eq_leibniz (t1 t2: t): eq t1 t2 -> t1 = t2. 
Proof. auto. Qed.

(** *** [shift] properties *)

Lemma shift_zero_refl (lb: Lvl.t) (t: t): shift lb 0 t = t.
Proof.
  induction t; simpl; f_equal; auto;
  try (apply Typ.shift_zero_refl).
  apply Resource.shift_zero_refl.
Qed.

#[export] Instance shift_eq: 
  Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.

Lemma shift_eq_iff (lb k: Lvl.t) (t t1: t) :
  t = t1 <-> (shift lb k t) = (shift lb k t1).
Proof.
  split; intro Heq.
  - now subst.
  - revert t1 Heq; induction t; intros t' Heq; destruct t'; 
    simpl in *; try (now inversion Heq); try (inversion Heq;f_equal; eauto).
    -- eapply Typ.shift_eq_iff; eauto.
    -- eapply Typ.shift_eq_iff; eauto.
    -- eapply Resource.shift_eq_iff; eauto.
Qed.

Lemma shift_trans (lb k m: Lvl.t) (t: t) :
  shift lb k (shift lb m t) = shift lb (k + m) t.
Proof.
  induction t; simpl; f_equal; auto;
  try (apply Typ.shift_trans).
  apply Resource.shift_trans.
Qed.

Lemma shift_permute (lb k m: Lvl.t) (t: t) :
  shift lb k (shift lb m t) = shift lb m (shift lb k t).
Proof.
  induction t; simpl; f_equal; auto;
  try (apply Typ.shift_permute).
  apply Resource.shift_permute.
Qed.

Lemma shift_value_iff (lb k: Lvl.t) (t: t): value t <-> value (shift lb k t).
Proof.
  induction t; split; intros; auto; simpl;
  try (now inversion H); try (inversion H; subst; constructor);
  try (erewrite IHt1; now eauto); try (erewrite <- IHt1; now eauto);
  try (erewrite IHt2; now eauto); try (erewrite <- IHt2; now eauto);
  try (now apply IHt); try (erewrite IHt; eauto).
Qed.

Lemma shift_permute_1 (lb k m: Lvl.t) (t: t) :
  eq (shift lb k (shift lb m t)) (shift (lb + k) m (shift lb k t)).
Proof.
  unfold eq; induction t; simpl; f_equal; auto;
  try (apply Typ.shift_permute_1).
  apply Resource.shift_permute_1.
Qed.

Lemma shift_permute_2 (lb k m n: Lvl.t) (t: t) :
  lb <= k -> eq (shift lb m (shift k n t)) (shift (k + m) n (shift lb m t)).
Proof.
  unfold eq; induction t; simpl; intros; f_equal; auto;
  try (apply Typ.shift_permute_2; auto).
  now apply Resource.shift_permute_2.
Qed.

Lemma shift_unfold (lb k m: Lvl.t) (t: t) :
  eq (shift lb (k + m) t) (shift (lb + k) m (shift lb k t)). 
Proof.
  induction t; simpl; auto;
  try (rewrite IHt1; rewrite IHt2; now reflexivity);
  try (rewrite IHt; now reflexivity).
  - unfold eq; f_equal; auto. 
    now rewrite Typ.shift_unfold.
  - unfold eq; f_equal; auto.
    now rewrite Typ.shift_unfold.
  - now rewrite Resource.shift_unfold.
Qed.

Lemma shift_unfold_1 (k m n: Lvl.t) (t: t) :
  k <= m -> m <= n -> 
  eq (shift m (n - m) (shift k  (m - k) t)) (shift k (n - k) t).
Proof.
  intros Hlekm Hlemn; induction t; simpl; auto;
  try (rewrite IHt1; rewrite IHt2; now reflexivity);
  try (rewrite IHt; now reflexivity).
  - unfold eq; f_equal; auto. 
    now rewrite Typ.shift_unfold_1.
  - unfold eq; f_equal; auto.
    now rewrite Typ.shift_unfold_1.
  - now rewrite Resource.shift_unfold_1.
Qed.

(** *** [Wf] properties *)

#[export] Instance Wf_iff: Proper (Logic.eq ==> eq ==> iff) Wf := _.

Lemma Wf_weakening (k m: Lvl.t) (t: t): (k <= m) -> Wf k t -> Wf m t.
Proof.
  unfold Wf; revert k m; induction t; simpl; intros k m Hle Hvt; 
  auto; try (inversion Hvt; subst; now eauto).
  - inversion Hvt; subst; constructor.
    -- eapply Typ.Wf_weakening; eauto.
    -- eapply IHt; eauto.
  - inversion Hvt; subst; constructor.
    -- eapply Typ.Wf_weakening; eauto.
    -- eapply IHt; eauto.
  - inversion Hvt; subst; constructor; eapply Resource.Wf_weakening; eauto.
  - inversion Hvt; subst; apply wfΛ_wh.
    -- eapply IHt1; eauto.
    -- apply IHt2 with (k := S (S k)); eauto; lia.
Qed.

Theorem shift_preserves_wf_1 (lb k m: Lvl.t) (t: t) :
  Wf k t -> Wf (k + m) (shift lb m t).
Proof.
  unfold Wf; revert lb k m; induction t; intros lb k m Hvt; 
  inversion Hvt; subst; simpl; auto.
  - constructor; eauto.
    now apply Typ.shift_preserves_wf_1.
  - constructor; eauto.
    now apply Typ.shift_preserves_wf_1.
  - constructor; now apply Resource.shift_preserves_wf_1.
  - apply wfΛ_wh; auto. 
    replace (S (S (k + m))) with ((S (S k)) + m); auto; lia.
Qed.

Theorem shift_preserves_wf (k m: Lvl.t) (t: t) :
  Wf k t -> Wf (k + m) (shift k m t).
Proof. intros; now apply shift_preserves_wf_1. Qed. 

Theorem shift_preserves_wf_zero (k: Lvl.t) (t: t) :
  Wf k t -> Wf k (shift k 0 t).
Proof. 
  intro Hvt. 
  apply shift_preserves_wf with (m := 0) in Hvt. 
  replace (k + 0) with k in Hvt; auto.
Qed. 

Lemma shift_preserves_wf_gen (lb k m n: Lvl.t) (t: t) :
    m <= n -> lb <= k -> m <= lb -> n <= k -> n - m = k - lb -> 
    Wf lb t -> Wf k (shift m (n - m) t).
Proof.
  revert lb k m n; induction t; 
  intros lb k m n Hlemn Hlelbk Hlemlb Hlenk Heq Hvt; simpl; 
  inversion Hvt; subst; constructor;
  try (apply IHt1 with lb; now auto);
  try (apply IHt2 with lb; now auto); try (apply IHt with lb; now auto).
  - apply Typ.shift_preserves_wf_gen with lb; auto.
  - apply Typ.shift_preserves_wf_gen with lb; auto.
  - apply Resource.shift_preserves_wf_gen with lb; auto.
  - apply IHt2 with (lb := S (S lb)); auto; lia.
Qed.

Lemma shift_preserves_wf_2 (m n: Lvl.t) (t: t) :
  m <= n -> Wf m t -> Wf n (shift m (n - m) t).
Proof. 
  intros Hle Hvt. 
  eapply shift_preserves_wf_gen; eauto. 
Qed.

(** *** [multi_shift] properties *)

Lemma multi_shift_unit (lbs ks: list Lvl.t) :
  multi_shift lbs ks tm_unit = tm_unit.
Proof. 
  unfold multi_shift; revert ks.
  induction lbs; simpl; intros; auto.
  destruct ks; simpl; auto.
  now rewrite IHlbs.
Qed.

Lemma multi_shift_var (lbs ks: list Lvl.t) (x: Var.t) :
  multi_shift lbs ks (tm_var x) = tm_var x.
Proof. 
  unfold multi_shift; revert ks.
  induction lbs; simpl; intro ks; auto.
  destruct ks; simpl; auto.
  now rewrite IHlbs. 
Qed.

Lemma multi_shift_rsf (lbs ks: list Lvl.t) (r: Resource.t) :
  multi_shift lbs ks (tm_rsf r) = tm_rsf (Resource.multi_shift lbs ks r).
Proof. 
  unfold multi_shift; revert ks.
  induction lbs; simpl; intro ks; auto.
  destruct ks; simpl; auto.
  now rewrite IHlbs.
Qed.

Lemma multi_shift_app (lbs ks: list Lvl.t) (t1 t2: t) :
  multi_shift lbs ks (tm_app t1 t2) = tm_app (multi_shift lbs ks t1) (multi_shift lbs ks t2).
Proof. 
  unfold multi_shift; revert ks; induction lbs; intro ks; simpl; auto.
  destruct ks; simpl; auto; now rewrite IHlbs.
Qed.

Lemma multi_shift_pair (lbs ks: list Lvl.t) (t1 t2: t) :
  multi_shift lbs ks (tm_pair t1 t2) = tm_pair (multi_shift lbs ks t1) (multi_shift lbs ks t2).
Proof. 
  unfold multi_shift; revert ks; induction lbs; intro ks; simpl; auto.
  destruct ks; simpl; auto; now rewrite IHlbs.
Qed.

Lemma multi_shift_comp (lbs ks: list Lvl.t) (t1 t2: t) :
  multi_shift lbs ks (tm_comp t1 t2) = tm_comp (multi_shift lbs ks t1) (multi_shift lbs ks t2).
Proof. 
  unfold multi_shift; revert ks; induction lbs; intro ks; simpl; auto.
  destruct ks; simpl; auto; now rewrite IHlbs.
Qed.

Lemma multi_shift_wh (lbs ks: list Lvl.t) (t1 t2: t) :
  multi_shift lbs ks (tm_wh t1 t2) = tm_wh (multi_shift lbs ks t1) (multi_shift lbs ks t2).
Proof. 
  unfold multi_shift; revert ks; induction lbs; intro ks; simpl; auto.
  destruct ks; simpl; auto; now rewrite IHlbs.
Qed.

Lemma multi_shift_fix (lbs ks: list Lvl.t) (t: t) :
  multi_shift lbs ks (tm_fix t) = tm_fix (multi_shift lbs ks t).
Proof. 
  unfold multi_shift; revert ks; induction lbs; intro ks; simpl; auto.
  destruct ks; simpl; auto; now rewrite IHlbs.
Qed.

Lemma multi_shift_fst (lbs ks: list Lvl.t) (t: t) :
  multi_shift lbs ks (tm_fst t) = tm_fst (multi_shift lbs ks t).
Proof. 
  unfold multi_shift; revert ks; induction lbs; intro ks; simpl; auto.
  destruct ks; simpl; auto; now rewrite IHlbs.
Qed.

Lemma multi_shift_snd (lbs ks: list Lvl.t) (t: t) :
  multi_shift lbs ks (tm_snd t) = tm_snd (multi_shift lbs ks t).
Proof. 
  unfold multi_shift; revert ks; induction lbs; intro ks; simpl; auto.
  destruct ks; simpl; auto; now rewrite IHlbs.
Qed.

Lemma multi_shift_arr (lbs ks: list Lvl.t) (t: t) :
  multi_shift lbs ks (tm_arr t) = tm_arr (multi_shift lbs ks t).
Proof. 
  unfold multi_shift; revert ks; induction lbs; intro ks; simpl; auto.
  destruct ks; simpl; auto; now rewrite IHlbs.
Qed.

Lemma multi_shift_abs (lbs ks: list Lvl.t) (x: Var.t) (A: Typ.t) (t: t) :
  multi_shift lbs ks (tm_abs x A t) = tm_abs x (Typ.multi_shift lbs ks A) (multi_shift lbs ks t).
Proof. 
  unfold multi_shift; revert ks; induction lbs; intro ks; simpl; auto.
  destruct ks; simpl; auto; now rewrite IHlbs.
Qed.

Lemma multi_shift_first (lbs ks: list Lvl.t) (A: Typ.t) (t: t) :
  multi_shift lbs ks (tm_first A t) = tm_first (Typ.multi_shift lbs ks A) (multi_shift lbs ks t).
Proof. 
  unfold multi_shift; revert ks; induction lbs; intro ks; simpl; auto.
  destruct ks; simpl; auto; now rewrite IHlbs.
Qed.

Lemma multi_shift_nil_l (ks: list Lvl.t) (t: t): multi_shift nil ks t = t.
Proof. now unfold multi_shift; simpl. Qed.

Lemma multi_shift_nil_r (lbs: list Lvl.t) (t: t): multi_shift lbs nil t = t.
Proof. now unfold multi_shift; destruct lbs. Qed.

Lemma multi_shift_nil (t: t): multi_shift nil nil t = t.
Proof. now unfold multi_shift. Qed.

Lemma multi_shift_cons (lb k: Lvl.t) (lbs ks: list Lvl.t) (t: t) :
  multi_shift (lb :: lbs) (k :: ks) t = shift lb k (multi_shift lbs ks t).
Proof. now unfold multi_shift. Qed.

Lemma multi_shift_value_iff (lbs ks: list Lvl.t) (t: t): 
  value t <-> value (multi_shift lbs ks t).
Proof.
  split; revert ks t; induction lbs; simpl; intros ks t Hvt; auto.
  - destruct ks; simpl in *; auto.
    rewrite multi_shift_cons.
    apply shift_value_iff. 
    now apply IHlbs.
  - destruct ks; simpl in *; auto.
    rewrite multi_shift_cons in Hvt.
    apply shift_value_iff in Hvt. 
    now apply IHlbs in Hvt.
Qed.

End Term.