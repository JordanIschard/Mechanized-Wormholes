From Coq Require Import Classes.Morphisms.
From DeBrLevel Require Import LevelInterface Level PairLevel.
From Mecha Require Import Resource.

(** * Syntax - Type

  Based on the arrow-calculus, the set of types is endowed with a new kind of arrow that represent signal functions. This new arrow carries a set of RS.t used by this signal function. Consequently, the definition of types relies on the module [Resources.v].
*)

Module Typ <: IsBdlLvlDTWL.

(** ** Definitions *)


Module RS := Resources.

(** *** The set of types

  A type is either a ground type, named [unit], a function type, a product type or a reactive type, also named signal function type. The first three types are usual in the extended lambda-calculus. The last one is a type taken from the arrow-calculus and represent reactive expressions. In addition, it carries a set of resource names representing interaction with the environment done by the expression.
*)
Inductive raw: Type :=
  | ty_unit: raw
  | ty_arrow (A B: raw): raw
  | ty_prod  (A B: raw): raw
  | ty_reactive (A B: raw) (R: RS.t): raw
.

Definition t := raw.
Definition eq := @Logic.eq t.

(** *** Shift function 

  The shift function impacts only resource sets carried by signal function types. It takes a type goes through all sub-terms and applies the shift function defined for sets, in [Levels], on all resource sets encountered. It is denoted [[⧐ _ – _] _].
*)
Fixpoint shift (lb: Lvl.t) (k: Lvl.t) (A: t): t := 
  match A with
    | ty_arrow t1 t2 => ty_arrow (shift lb k t1) (shift lb k t2)    
    | ty_prod  t1 t2 => ty_prod  (shift lb k t1) (shift lb k t2)    
    | ty_reactive t1 t2 R => ty_reactive (shift lb k t1) 
                                         (shift lb k t2) 
                                         (RS.shift lb k R)
    | _ => A
  end
.

(** *** Multi shift function 

  As done in [Resource.v] and [Resources.v], we define a [multi_shift] function that applies [n] shifts for two lists [lbs] and [ks] of length [n].
*)
Definition multi_shift (lbs: list Lvl.t) (ks: list Lvl.t) (A: t) :=
  List.fold_right (fun lbk acc => shift (fst lbk) (snd lbk) acc) 
                  A 
                  (List.combine lbs ks).


(** *** Well-formedness

  The well-formed property, named [Wf] and denoted [(⊩)], takes a level [k] called the well-formedness level and states that all resource names in the type are well-formed under [k]. Recall that a resource name [r] is well-formed under [k] if [r < k] and a resource set [s] is well-formed under [k] if all [r] in [s] are well-formed under [k].
*)
Inductive Wf': Lvl.t -> t -> Prop :=
  | vΤ_unit (k: Lvl.t): Wf' k ty_unit
  | vΤ_prod (k: Lvl.t) (A B: t): Wf' k A -> Wf' k B -> Wf' k (ty_prod A B)
  | vΤ_func (k: Lvl.t) (A B: t): Wf' k A -> Wf' k B -> Wf' k (ty_arrow A B)
  | vΤ_reac (k: Lvl.t) (A B: t) (R: RS.t): 
                   Wf' k A -> Wf' k B -> RS.Wf k R -> Wf' k (ty_reactive A B R)
.

Definition Wf := Wf'.

#[export] Hint Constructors Wf': core.

(** ** Properties *)

(** *** [eq] properties *)

#[export] Instance eq_refl: Reflexive eq := _.

#[export] Instance eq_sym: Symmetric eq := _.

#[export] Instance eq_trans: Transitive eq := _.

#[export] Instance eq_equiv: Equivalence eq := _.

#[export] Instance eq_rr: RewriteRelation eq := {}.

#[export] Hint Resolve eq_refl eq_sym eq_trans: core.

Lemma eq_dec (A B: t): {eq A B} + {~ eq A B}.
Proof.
  unfold eq; revert B; induction A; intro; destruct B; simpl; auto; 
  try (right; unfold not; intros contra; now inversion contra).
  - destruct (IHA1 B1); destruct (IHA2 B2);
    try (right; unfold not; intros; inversion H; subst; contradiction); subst.
    f_equal; auto. 
  - destruct (IHA1 B1); destruct (IHA2 B2);
    try (right; unfold not; intros; inversion H; subst; contradiction); subst.
    f_equal; auto.
  - destruct (IHA1 B1); destruct (IHA2 B2); destruct (RS.eq_dec R R0);
    try (right; unfold not; intros; inversion H; subst; contradiction); subst.
    -- apply RS.eq_leibniz in e1; subst; auto.
    -- right; unfold not in *; intros; inversion H; subst; apply n; reflexivity.
Qed.

Lemma eq_dec' (A B: t): {A = B} + {A <> B}.
Proof. apply eq_dec. Qed.

Lemma eq_leibniz (A B: t): eq A B -> A = B. 
Proof. auto. Qed.

(** *** [shift] properties *)

Lemma shift_zero_refl (k: Lvl.t) (A: t):
  (shift k 0 A) = A.
Proof.
  induction A; simpl; f_equal; auto.
  apply RS.eq_leibniz; apply RS.shift_zero_refl.
Qed.

Lemma shift_wf_refl (lb k: Lvl.t) (A: t):
  Wf lb A -> shift lb k A = A.
Proof.
  intro Hv; induction Hv; subst; simpl; f_equal; auto.
  apply RS.eq_leibniz; now apply RS.shift_wf_refl.
Qed.

#[export] Instance shift_eq: Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.

Lemma shift_eq_iff (lb k: Lvl.t) (A B: t):
  A = B <-> (shift lb k A) = (shift lb k B).
Proof.
  split; intro Heq.
  - now subst.
  - revert B Heq; induction A; intros; destruct B; auto; 
    try (now inversion Heq); inversion Heq; f_equal; auto.
    apply Resources.eq_leibniz. 
    eapply Resources.shift_eq_iff.
    now rewrite H2.
Qed.

Lemma shift_trans (lb m n: Lvl.t) (A: t):
  shift lb m (shift lb n A) = shift lb (m + n) A.
Proof.
  induction A; simpl; f_equal; auto.
  apply RS.eq_leibniz; apply RS.shift_trans.
Qed.

Lemma shift_permute (lb m n: Lvl.t) (A: t):
  shift lb m (shift lb n A) = shift lb n (shift lb m A).
Proof.
  induction A; simpl; f_equal; auto.
  apply RS.eq_leibniz; apply RS.shift_permute.
Qed.

Lemma shift_permute_1 (lb m n: Lvl.t) (A: t):
  eq (shift lb m (shift lb n A)) (shift (lb + m) n (shift lb m A)).
Proof.
  unfold eq; induction A; intros; simpl; f_equal; auto.
  apply RS.eq_leibniz; apply RS.shift_permute_1.
Qed.

Lemma shift_permute_2 (lb k m n: Lvl.t) (A: t):
  lb <= k -> eq (shift lb m (shift k n A)) (shift (k + m) n (shift lb m A)).
Proof.
  unfold eq; induction A; intros; simpl; f_equal; auto.
  apply RS.eq_leibniz; now apply RS.shift_permute_2.
Qed.

Lemma shift_unfold (lb m n: Lvl.t) (A: t):
  eq (shift lb (m + n) A) (shift (lb + m) n (shift lb m A)). 
Proof.
  induction A; simpl; auto; try now rewrite IHA1; rewrite IHA2.
  rewrite IHA1; rewrite IHA2; unfold eq; f_equal. 
  apply RS.eq_leibniz.
  now apply RS.shift_unfold.
Qed.

Lemma shift_unfold_1 (k m n: Lvl.t) (A: t):
  k <= m -> m <= n -> eq (shift m (n - m) (shift k  (m - k) A)) (shift k (n - k) A).
Proof.
  induction A; simpl; intros Hlekm Hlemn; auto; 
  try now rewrite IHA1; auto; rewrite IHA2; auto.
  rewrite IHA1; auto; rewrite IHA2; auto; unfold eq; f_equal. 
  apply RS.eq_leibniz.
  now apply RS.shift_unfold_1.
Qed.

(** *** [Wf] properties *)

#[export] Instance Wf_iff: Proper (Logic.eq ==> eq ==> iff) Wf := _.

Lemma Wf_weakening (k n: Lvl.t) (A: t): (k <= n) -> Wf k A -> Wf n A.
Proof.
  unfold Wf; induction A; intros Hleq Hvτ; simpl in *; inversion Hvτ; subst; eauto.
  apply vΤ_reac; eauto. 
  eapply RS.Wf_weakening; eauto.
Qed.

Theorem shift_preserves_wf_1 (k m n: Lvl.t) (A: t):
  Wf m A -> Wf (m + n) (shift k n A).
Proof.
  unfold Wf; induction A; intro Hvτ; inversion Hvτ; subst; simpl; auto.
  apply vΤ_reac; auto. 
  now apply RS.shift_preserves_wf_1.
Qed.

Theorem shift_preserves_wf (m n: Lvl.t) (A: t):
  Wf m A -> Wf (m + n) (shift m n A).
Proof. now apply shift_preserves_wf_1. Qed.

Lemma shift_preserves_wf_zero (k: Lvl.t) (A: t): Wf k A -> Wf k (shift k 0 A).
Proof. 
  intro Hvα; replace k with (k + 0) by auto. 
  now apply shift_preserves_wf_1. 
Qed.

Lemma shift_preserves_wf_gen (lb k m n: Lvl.t) (A: t):
  m <= n -> lb <= k -> m <= lb -> n <= k -> n - m = k - lb -> 
  Wf lb A -> Wf k (shift m (n - m) A).
Proof.
  intros Hlemn Hlelbk Hlemlb Hlenk Heq. 
  induction A; intros; simpl; inversion H; subst; constructor; fold Wf; auto. 
  apply RS.shift_preserves_wf_gen with lb; auto.
Qed.

Lemma shift_preserves_wf_2 (m n: Lvl.t) (A: t):
  m <= n -> Wf m A -> Wf n (shift m (n - m) A).
Proof. intros Hle Hvα; eapply shift_preserves_wf_gen; eauto. Qed.

End Typ.

(** ---- *)

(** * Syntax - Pair of types 

  The resource context defined in [RContext.v] maps resource names to pair types. We define it co-domain here.
*)

Module PairTyp <: IsBdlLvlETWL.
  
(** ** Definitions *)

(** **** A pair of types *)
Definition t: Type := Typ.t * Typ.t.
Definition eq := @Logic.eq t.

#[export] Instance eq_equiv: Equivalence eq := _.

(** *** The shift function 

  It applies the shift function defined in [Typ] module on both elements of the pair.
*)
Definition shift (m n: Resource.t) (tp: t) :=
  let (p1,p2) := tp in 
  (Typ.shift m n p1,Typ.shift m n p2).

(** *** The well-formed property 

  A pair of types [tp] is well-formed under a level [m] if both types are well-formed under [m].
*)
Definition Wf (m: Resource.t) (tp: t) :=
  let (p1,p2) := tp in 
  Typ.Wf m p1 /\ Typ.Wf m p2.

(** ** Properties *)

(** *** [eq] properties *)

#[export] Hint Resolve eq_refl eq_sym eq_trans: core.

Lemma eq_dec (t1 t2: t): {eq t1 t2} + {~ eq t1 t2}.
Proof.
  unfold eq.
  destruct t1 as [p1 p2];
  destruct t2 as [p1' p2'].
  destruct (Typ.eq_dec p1 p1'); subst;
  destruct (Typ.eq_dec p2 p2'); 
  unfold Typ.eq in * ; subst; auto;
  right;
  intro c; inversion c; contradiction.
Qed.

Lemma eq_leibniz (t1 t2: t): eq t1 t2 -> t1 = t2. 
Proof. auto. Qed.

(** *** [shift] properties *)

Lemma shift_zero_refl (lb: Lvl.t) (t: t): shift lb 0 t = t.
Proof.
  destruct t as [p1 p2]; simpl.
  now do 2 rewrite Typ.shift_zero_refl.
Qed.

#[export] Instance shift_eq: Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.

Lemma shift_eq_iff (lb k: Lvl.t) (t t1: t) :
  t = t1 <-> (shift lb k t) = (shift lb k t1).
Proof.
  split; intro Heq.
  - now subst.
  - destruct t as [p1 p2];
    destruct t1 as [p1' p2'];
    simpl in *. 
    inversion Heq.
    rewrite <- Typ.shift_eq_iff in H0,H1; subst.
    reflexivity.
Qed.

Lemma shift_trans (lb k m: Lvl.t) (t: t) :
  shift lb k (shift lb m t) = shift lb (k + m) t.
Proof.
  destruct t as [p1 p2]; simpl.
  now do 2 rewrite Typ.shift_trans.
Qed.

Lemma shift_permute (lb k m: Lvl.t) (t: t) :
  shift lb k (shift lb m t) = shift lb m (shift lb k t).
Proof.
  destruct t as [p1 p2]; simpl.
  now f_equal; rewrite Typ.shift_permute.
Qed.

Lemma shift_permute_1 (lb k m: Lvl.t) (t: t) :
  (shift lb k (shift lb m t)) = (shift (lb + k) m (shift lb k t)).
Proof.
  destruct t as [p1 p2]; simpl.
  f_equal;
  now rewrite Typ.shift_permute_1.
Qed.

Lemma shift_permute_2 (lb k m n: Lvl.t) (t: t) :
  lb <= k -> (shift lb m (shift k n t)) = (shift (k + m) n (shift lb m t)).
Proof.
  intro Hle.
  destruct t as [p1 p2]; simpl.
  f_equal; rewrite Typ.shift_permute_2; auto.
Qed.

Lemma shift_unfold (lb k m: Lvl.t) (t: t) :
  (shift lb (k + m) t) = (shift (lb + k) m (shift lb k t)). 
Proof.
  destruct t as [p1 p2]; simpl.
  f_equal; now rewrite Typ.shift_unfold.
Qed.

Lemma shift_unfold_1 (k m n: Lvl.t) (t: t) :
  k <= m -> m <= n -> 
  (shift m (n - m) (shift k  (m - k) t)) = (shift k (n - k) t).
Proof.
  intros.
  destruct t as [p1 p2]; simpl.
  f_equal; rewrite Typ.shift_unfold_1; auto.
Qed.

Lemma shift_wf_refl m k t: Wf m t -> (shift m k t) = t.
Proof.
  destruct t as [p1 p2]; simpl.
  intros [Hwf1 Hwf2].
  now f_equal; apply Typ.shift_wf_refl.
Qed.

(** *** [Wf] properties *)

#[export] Instance Wf_iff: Proper (Logic.eq ==> eq ==> iff) Wf := _.

Lemma Wf_weakening (k m: Lvl.t) (t: t): (k <= m) -> Wf k t -> Wf m t.
Proof.
  unfold Wf.
  destruct t as [p1 p2].
  intros Hle [Hwfp1 Hwfp2].
  split; eapply Typ.Wf_weakening; eauto.
Qed.

Theorem shift_preserves_wf_1 (lb k m: Lvl.t) (t: t) :
  Wf k t -> Wf (k + m) (shift lb m t).
Proof.
  unfold Wf.
  destruct t as [p1 p2].
  intros [Hwfp1 Hwfp2].
  simpl.
  split; now apply Typ.shift_preserves_wf_1.
Qed.

Theorem shift_preserves_wf (k m: Lvl.t) (t: t) :
  Wf k t -> Wf (k + m) (shift k m t).
Proof. intros; now apply shift_preserves_wf_1. Qed. 

Theorem shift_preserves_wf_zero (k: Lvl.t) (t: t) :
  Wf k t -> Wf k (shift k 0 t).
Proof. 
  unfold Wf.
  destruct t as [p1 p2].
  intros [Hwfp1 Hwfp2].
  simpl.
  split; now apply Typ.shift_preserves_wf_zero.
Qed. 

Lemma shift_preserves_wf_gen (lb k m n: Lvl.t) (t: t) :
    m <= n -> lb <= k -> m <= lb -> n <= k -> n - m = k - lb -> 
    Wf lb t -> Wf k (shift m (n - m) t).
Proof.
  unfold Wf.
  destruct t as [p1 p2].
  intros.
  destruct H4 as [Hwfp1 Hwfp2].
  simpl.
  split; apply Typ.shift_preserves_wf_gen with (lb := lb); auto.
Qed.

Lemma shift_preserves_wf_2 (m n: Lvl.t) (t: t) :
  m <= n -> Wf m t -> Wf n (shift m (n - m) t).
Proof. 
  intros Hle Hvt. 
  eapply shift_preserves_wf_gen; eauto. 
Qed.

End PairTyp.