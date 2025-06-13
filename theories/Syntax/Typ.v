From Coq Require Import Classes.Morphisms.
From DeBrLevel Require Import LevelInterface Level PairLevel.
From Mecha Require Import Resource Resources.
Import ResourceNotations ResourcesNotations SetNotations.

(** * Syntax - Type

  Based on the arrow-calculus, the set of types is endowed with a new kind of arrow that represent signal functions. This new arrow carries a set of resources used by this signal function. Consequently, the definition of types relies on the module [Resources.v].
*)

(** ** Module - Type *)
Module Typ <: IsBdlLvlDTWL.

(** *** Definitions *)

Open Scope resource_scope.
Open Scope set_scope.
Open Scope resources_scope.

Module RS := Resources.

(** **** Type

  A type is either a ground type, named [unit], a function type, a product type or a reactive type, also named signal function type. The first three type are usual in the extended lambda-calculus. The last one is a type taken from the arrow-calculus and represent reactive expressions. In addition, it carries a set of resource names representing interaction with the environment done by the expression.
*)
Inductive raw : Type :=
  | ty_unit : raw
  | ty_arrow (α β : raw) : raw
  | ty_prod  (α β : raw) : raw
  | ty_reactive (α β : raw) (R : resources) : raw
.

Definition t := raw.
Definition eq := @Logic.eq t.

(** **** Shift function 

  The shift function impacts only the set of used resources. It takes a type goes through all sub-terms and applies the shift function defined for sets, in [Levels], on all used resource sets encountered. It is denoted [[⧐ _ – _] _].
*)
Fixpoint shift (lb : lvl) (k : lvl) (α : t) : t := 
  match α with
    | ty_arrow t1 t2 => ty_arrow (shift lb k t1) (shift lb k t2)    
    | ty_prod  t1 t2 => ty_prod  (shift lb k t1) (shift lb k t2)    
    | ty_reactive t1 t2 R => ty_reactive (shift lb k t1) (shift lb k t2) ([⧐ lb – k] R)
    | _ => α
  end
.

(** **** Multi shift function 

  As done in [Resource.v] and [Resources.v], we define a [multi_shift] function that applies [n] shifts for two lists [lbs] and [ks] of length [n].
*)
Definition multi_shift (lbs : list lvl) (ks : list lvl) (α : t) :=
  List.fold_right (fun lbk acc => shift (fst lbk) (snd lbk) acc) α (List.combine lbs ks).


(** **** Well-formedness

  The well-formed property, named [Wf] and denoted [(⊩)], takes a level [k] called the well-formedness level and states that all resource names in the type are well-formed under [k]. Recall that a resource name [r] is well-formed under [k] if [r < k] and a resource set [s] is well-formed under [k] if all
  [r] in [s] are well-formed under [k].
*)
Inductive Wf' : lvl -> t -> Prop :=
  | vΤ_unit (k : lvl): Wf' k ty_unit
  | vΤ_prod (k : lvl) (α β : t): Wf' k α -> Wf' k β -> Wf' k (ty_prod α β)
  | vΤ_func (k : lvl) (α β : t): Wf' k α -> Wf' k β -> Wf' k (ty_arrow α β)
  | vΤ_reac (k : lvl) (α β : t) (R : resources): 
                   Wf' k α -> Wf' k β -> k ⊩ R -> Wf' k (ty_reactive α β R)
.

Definition Wf := Wf'.

#[export] Hint Constructors Wf' : core.

(** *** Properties *)

(** **** [eq] properties *)

#[export] Instance eq_refl : Reflexive eq := _.

#[export] Instance eq_sym : Symmetric eq := _.

#[export] Instance eq_trans : Transitive eq := _.

#[export] Instance eq_equiv : Equivalence eq := _.

#[export] Instance eq_rr : RewriteRelation eq := {}.

#[export] Hint Resolve eq_refl eq_sym eq_trans : core.

Lemma eq_dec (α β : t): {eq α β} + {~ eq α β}.
Proof.
  unfold eq; revert β; induction α; intro; destruct β; simpl; auto; 
  try (right; unfold not; intros contra; now inversion contra).
  - destruct (IHα1 β1); destruct (IHα2 β2);
    try (right; unfold not; intros; inversion H; subst; contradiction); subst.
    f_equal; auto. 
  - destruct (IHα1 β1); destruct (IHα2 β2);
    try (right; unfold not; intros; inversion H; subst; contradiction); subst.
    f_equal; auto.
  - destruct (IHα1 β1); destruct (IHα2 β2); destruct (RS.eq_dec R R0);
    try (right; unfold not; intros; inversion H; subst; contradiction); subst.
    -- apply RS.eq_leibniz in e1; subst; auto.
    -- right; unfold not in *; intros; inversion H; subst; apply n; reflexivity.
Qed.

Lemma eq_dec' (α β : t): {α = β} + {α <> β}.
Proof. apply eq_dec. Qed.

Lemma eq_leibniz (α β : t): eq α β -> α = β. 
Proof. auto. Qed.

(** **** [shift] properties *)

Lemma shift_zero_refl (k : lvl) (α : t):
  (shift k 0 α) = α.
Proof.
  induction α; simpl; f_equal; auto.
  apply RS.eq_leibniz; apply RS.shift_zero_refl.
Qed.

Lemma shift_wf_refl (lb k : lvl) (α : t):
  Wf lb α -> shift lb k α = α.
Proof.
  intro Hv; induction Hv; subst; simpl; f_equal; auto.
  apply RS.eq_leibniz; now apply RS.shift_wf_refl.
Qed.

#[export] Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.

Lemma shift_eq_iff (lb k : lvl) (α β : t):
  α = β <-> (shift lb k α) = (shift lb k β).
Proof.
  split; intro Heq.
  - now subst.
  - revert β Heq; induction α; intros; destruct β; auto; 
    try (now inversion Heq); inversion Heq; f_equal; auto.
    apply Resources.eq_leibniz. 
    eapply Resources.shift_eq_iff.
    now rewrite H2.
Qed.

Lemma shift_trans (lb m n : lvl) (α : t):
  shift lb m (shift lb n α) = shift lb (m + n) α.
Proof.
  induction α; simpl; f_equal; auto.
  apply RS.eq_leibniz; apply RS.shift_trans.
Qed.

Lemma shift_permute (lb m n : lvl) (α : t):
  shift lb m (shift lb n α) = shift lb n (shift lb m α).
Proof.
  induction α; simpl; f_equal; auto.
  apply RS.eq_leibniz; apply RS.shift_permute.
Qed.

Lemma shift_permute_1 (lb m n : lvl) (α : t):
  eq (shift lb m (shift lb n α)) (shift (lb + m) n (shift lb m α)).
Proof.
  unfold eq; induction α; intros; simpl; f_equal; auto.
  apply RS.eq_leibniz; apply RS.shift_permute_1.
Qed.

Lemma shift_permute_2 (lb k m n : lvl) (α : t):
  lb <= k -> eq (shift lb m (shift k n α)) (shift (k + m) n (shift lb m α)).
Proof.
  unfold eq; induction α; intros; simpl; f_equal; auto.
  apply RS.eq_leibniz; now apply RS.shift_permute_2.
Qed.

Lemma shift_unfold (lb m n : lvl) (α : t):
  eq (shift lb (m + n) α) (shift (lb + m) n (shift lb m α)). 
Proof.
  induction α; simpl; auto; try now rewrite IHα1; rewrite IHα2.
  rewrite IHα1; rewrite IHα2; unfold eq; f_equal. 
  apply RS.eq_leibniz.
  now apply RS.shift_unfold.
Qed.

Lemma shift_unfold_1 (k m n : lvl) (α : t):
  k <= m -> m <= n -> eq (shift m (n - m) (shift k  (m - k) α)) (shift k (n - k) α).
Proof.
  induction α; simpl; intros Hlekm Hlemn; auto; 
  try now rewrite IHα1; auto; rewrite IHα2; auto.
  rewrite IHα1; auto; rewrite IHα2; auto; unfold eq; f_equal. 
  apply RS.eq_leibniz.
  now apply RS.shift_unfold_1.
Qed.

(** **** [Wf] properties *)

#[export] Instance Wf_iff : Proper (Logic.eq ==> eq ==> iff) Wf := _.

Lemma Wf_weakening (k n : lvl) (α : t): (k <= n) -> Wf k α -> Wf n α.
Proof.
  unfold Wf; induction α; intros Hleq Hvτ; simpl in *; inversion Hvτ; subst; eauto.
  apply vΤ_reac; eauto. 
  eapply RS.Wf_weakening; eauto.
Qed.

Theorem shift_preserves_wf_1 (k m n : lvl) (α : t):
  Wf m α -> Wf (m + n) (shift k n α).
Proof.
  unfold Wf; induction α; intro Hvτ; inversion Hvτ; subst; simpl; auto.
  apply vΤ_reac; auto. 
  now apply RS.shift_preserves_wf_1.
Qed.

Theorem shift_preserves_wf (m n : lvl) (α : t):
  Wf m α -> Wf (m + n) (shift m n α).
Proof. now apply shift_preserves_wf_1. Qed.

Lemma shift_preserves_wf_zero (k : lvl) (α : t): Wf k α -> Wf k (shift k 0 α).
Proof. 
  intro Hvα; replace k with (k + 0) by auto. 
  now apply shift_preserves_wf_1. 
Qed.

Lemma shift_preserves_wf_gen (lb k m n : lvl) (α : t):
  m <= n -> lb <= k -> m <= lb -> n <= k -> n - m = k - lb -> 
  Wf lb α -> Wf k (shift m (n - m) α).
Proof.
  intros Hlemn Hlelbk Hlemlb Hlenk Heq. 
  induction α; intros; simpl; inversion H; subst; constructor; fold Wf; auto. 
  apply RS.shift_preserves_wf_gen with lb; auto.
Qed.

Lemma shift_preserves_wf_2 (m n : lvl) (α : t):
  m <= n -> Wf m α -> Wf n (shift m (n - m) α).
Proof. intros Hle Hvα; eapply shift_preserves_wf_gen; eauto. Qed.

End Typ.

(** ---- *)

(** * Syntax - Pair of types 

  The resource context defined in [RContext.v] maps resource names to pair types. We define it co-domain here. Thanks to the [DeBrLevel] library, we do not have to prove properties that handle level because [PairLevel] already exists.
*)


(** ** Module - Pair of types *)
Module PairTyp <: IsBdlLvlETWL.
  
Definition t : Type := Typ.t * Typ.t.
Definition eq := @Logic.eq t.

#[export] Instance eq_equiv : Equivalence eq := _.


Definition shift (m n : resource) (tp : t) :=
  let (p1,p2) := tp in 
  (Typ.shift m n p1,Typ.shift m n p2).

Definition Wf (m : resource) (tp : t) :=
  let (p1,p2) := tp in 
  Typ.Wf m p1 /\ Typ.Wf m p2.


#[export] Hint Resolve eq_refl eq_sym eq_trans : core.

Lemma eq_dec (t1 t2: t) : {eq t1 t2} + {~ eq t1 t2}.
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

Lemma eq_leibniz (t1 t2: t) : eq t1 t2 -> t1 = t2. 
Proof. auto. Qed.

(** **** [shift] properties *)

Lemma shift_zero_refl (lb : lvl) (t : t) : shift lb 0 t = t.
Proof.
  destruct t as [p1 p2]; simpl.
  now do 2 rewrite Typ.shift_zero_refl.
Qed.

#[export] Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.

Lemma shift_eq_iff (lb k : lvl) (t t1 : t) :
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

Lemma shift_trans (lb k m : lvl) (t : t) :
  shift lb k (shift lb m t) = shift lb (k + m) t.
Proof.
  destruct t as [p1 p2]; simpl.
  now do 2 rewrite Typ.shift_trans.
Qed.

Lemma shift_permute (lb k m : lvl) (t : t) :
  shift lb k (shift lb m t) = shift lb m (shift lb k t).
Proof.
  destruct t as [p1 p2]; simpl.
  now f_equal; rewrite Typ.shift_permute.
Qed.

Lemma shift_permute_1 (lb k m : lvl) (t : t) :
  (shift lb k (shift lb m t)) = (shift (lb + k) m (shift lb k t)).
Proof.
  destruct t as [p1 p2]; simpl.
  f_equal;
  now rewrite Typ.shift_permute_1.
Qed.

Lemma shift_permute_2 (lb k m n : lvl) (t : t) :
  lb <= k -> (shift lb m (shift k n t)) = (shift (k + m) n (shift lb m t)).
Proof.
  intro Hle.
  destruct t as [p1 p2]; simpl.
  f_equal; rewrite Typ.shift_permute_2; auto.
Qed.

Lemma shift_unfold (lb k m : lvl) (t : t) :
  (shift lb (k + m) t) = (shift (lb + k) m (shift lb k t)). 
Proof.
  destruct t as [p1 p2]; simpl.
  f_equal; now rewrite Typ.shift_unfold.
Qed.

Lemma shift_unfold_1 (k m n : lvl) (t : t) :
  k <= m -> m <= n -> 
  (shift m (n - m) (shift k  (m - k) t)) = (shift k (n - k) t).
Proof.
  intros.
  destruct t as [p1 p2]; simpl.
  f_equal; rewrite Typ.shift_unfold_1; auto.
Qed.

Lemma shift_wf_refl m k t : Wf m t -> (shift m k t) = t.
Proof.
  destruct t as [p1 p2]; simpl.
  intros [Hwf1 Hwf2].
  now f_equal; apply Typ.shift_wf_refl.
Qed.

(** **** [Wf] properties *)

#[export] Instance Wf_iff : Proper (Logic.eq ==> eq ==> iff) Wf := _.

Lemma Wf_weakening (k m : lvl) (t : t) : (k <= m) -> Wf k t -> Wf m t.
Proof.
  unfold Wf.
  destruct t as [p1 p2].
  intros Hle [Hwfp1 Hwfp2].
  split; eapply Typ.Wf_weakening; eauto.
Qed.

Theorem shift_preserves_wf_1 (lb k m : lvl) (t : t) :
  Wf k t -> Wf (k + m) (shift lb m t).
Proof.
  unfold Wf.
  destruct t as [p1 p2].
  intros [Hwfp1 Hwfp2].
  simpl.
  split; now apply Typ.shift_preserves_wf_1.
Qed.

Theorem shift_preserves_wf (k m : lvl) (t : t) :
  Wf k t -> Wf (k + m) (shift k m t).
Proof. intros; now apply shift_preserves_wf_1. Qed. 

Theorem shift_preserves_wf_zero (k : lvl) (t : t) :
  Wf k t -> Wf k (shift k 0 t).
Proof. 
  unfold Wf.
  destruct t as [p1 p2].
  intros [Hwfp1 Hwfp2].
  simpl.
  split; now apply Typ.shift_preserves_wf_zero.
Qed. 

Lemma shift_preserves_wf_gen (lb k m n : lvl) (t : t) :
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

Lemma shift_preserves_wf_2 (m n : lvl) (t : t) :
  m <= n -> Wf m t -> Wf n (shift m (n - m) t).
Proof. 
  intros Hle Hvt. 
  eapply shift_preserves_wf_gen; eauto. 
Qed.

  
End PairTyp.

(** ---- *)

(** ** Notation - Types *)
Module TypNotations.

(** *** Scopes *)
Declare Scope typ_scope.
Declare Scope ptyp_scope.
Delimit Scope typ_scope with ty.
Delimit Scope ptyp_scope with pty.

(** *** Notations *)
Definition Τ := Typ.t.
Definition πΤ := PairTyp.t.
  
Notation "'𝟙'"       := Typ.ty_unit (in custom wh at level 0).
Notation "t1 '→' t2" := (Typ.ty_arrow t1 t2) (in custom wh at level 50, right associativity).
Notation "t1 '×' t2"   := (Typ.ty_prod t1 t2) 
                        (in custom wh at level 2, t1 custom wh, t2 custom wh at level 0).
Notation "t1 '⟿' t2 '∣' R" := (Typ.ty_reactive t1 t2 R)
                               (in custom wh at level 50, R constr, right associativity).
Notation "'[⧐' lb '–' k ']' t" := (Typ.shift lb k t) 
                                   (in custom wh at level 45, right associativity) : typ_scope.
Notation "'[⧐⧐' lb '–' k ']' t" := (Typ.multi_shift lb k t) 
                                    (in custom wh at level 45, right associativity) : typ_scope.
Notation "'[⧐' lb '–' k ']' t" := (PairTyp.shift lb k t) 
                                   (in custom wh at level 45, right associativity) : ptyp_scope.

Infix "⊩"  := Typ.Wf (at level 20, no associativity): typ_scope. 
Infix "⊩"  := PairTyp.Wf (at level 20, no associativity) : ptyp_scope. 
Infix "="  := Typ.eq : typ_scope.

(** *** Morphisms *)
Import Typ.

#[export] Instance typ_leibniz_eq : Proper Logic.eq Typ.eq := _.

#[export] Instance typ_wf_iff :  Proper (Level.eq ==> eq ==> iff) Wf := _.

#[export] Instance typ_shift_eq : Proper (Level.eq ==> Level.eq ==> eq ==> eq) shift := shift_eq.

#[export] Instance typ_multi_shift_eq : 
  Proper (Logic.eq ==> Logic.eq ==> eq ==> Logic.eq) multi_shift := _.

End TypNotations.