From Coq Require Import Classes.Morphisms.
From DeBrLevel Require Import LevelInterface Level PairLevel.
From Mecha Require Import Resource Resources.
Import ResourceNotations ResourcesNotations SetNotations.

(** * Syntax - Type

  Based on the arrow-calculus, the set of types is endowed with a new kind of arrow that represent signal functions. This new arrow carries a set of resources used by this signal function. Consequently, the definition of types relies on the module [Resources.v].
*)

(** ** Module - Type *)
Module Typ <: IsBdlLvlDTWL.

(** *** Definition *)

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


(** **** Valid property

  The well-formed property, named [valid] and denoted [(⊩)], takes a level [k] called the well-formedness level and states that all resource names in the type are well-formed under [k]. Recall that a resource name [r] is well-formed under [k] if [r < k] and a resource set [s] is well-formed under [k] if all
  [r] in [s] are well-formed under [k].
*)
Inductive valid' : lvl -> t -> Prop :=
  | vΤ_unit (k : lvl): valid' k ty_unit
  | vΤ_prod (k : lvl) (α β : t): valid' k α -> valid' k β -> valid' k (ty_prod α β)
  | vΤ_func (k : lvl) (α β : t): valid' k α -> valid' k β -> valid' k (ty_arrow α β)
  | vΤ_reac (k : lvl) (α β : t) (R : resources): 
                   valid' k α -> valid' k β -> k ⊩ R -> valid' k (ty_reactive α β R)
.

Definition valid := valid'.

#[export] Hint Constructors valid' : core.

(** *** Property *)

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

(** **** [shift] property *)

Lemma shift_zero_refl (k : lvl) (α : t):
  (shift k 0 α) = α.
Proof.
  induction α; simpl; f_equal; auto.
  apply RS.eq_leibniz; apply RS.shift_zero_refl.
Qed.

Lemma shift_valid_refl (lb k : lvl) (α : t):
  valid lb α -> shift lb k α = α.
Proof.
  intro Hv; induction Hv; subst; simpl; f_equal; auto.
  apply RS.eq_leibniz; now apply RS.shift_valid_refl.
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

(** **** [valid] property *)

#[export] Instance valid_eq : Proper (Logic.eq ==> eq ==> iff) valid := _.

Lemma valid_weakening (k n : lvl) (α : t): (k <= n) -> valid k α -> valid n α.
Proof.
  unfold valid; induction α; intros Hleq Hvτ; simpl in *; inversion Hvτ; subst; eauto.
  apply vΤ_reac; eauto. 
  eapply RS.valid_weakening; eauto.
Qed.

Theorem shift_preserves_valid_1 (k m n : lvl) (α : t):
  valid m α -> valid (m + n) (shift k n α).
Proof.
  unfold valid; induction α; intro Hvτ; inversion Hvτ; subst; simpl; auto.
  apply vΤ_reac; auto. 
  now apply RS.shift_preserves_valid_1.
Qed.

Theorem shift_preserves_valid (m n : lvl) (α : t):
  valid m α -> valid (m + n) (shift m n α).
Proof. now apply shift_preserves_valid_1. Qed.

Lemma shift_preserves_valid_zero (k : lvl) (α : t): valid k α -> valid k (shift k 0 α).
Proof. 
  intro Hvα; replace k with (k + 0) by auto. 
  now apply shift_preserves_valid_1. 
Qed.

Lemma shift_preserves_valid_gen (lb k m n : lvl) (α : t):
  m <= n -> lb <= k -> m <= lb -> n <= k -> n - m = k - lb -> 
  valid lb α -> valid k (shift m (n - m) α).
Proof.
  intros Hlemn Hlelbk Hlemlb Hlenk Heq. 
  induction α; intros; simpl; inversion H; subst; constructor; fold valid; auto. 
  apply RS.shift_preserves_valid_gen with lb; auto.
Qed.

Lemma shift_preserves_valid_2 (m n : lvl) (α : t):
  m <= n -> valid m α -> valid n (shift m (n - m) α).
Proof. intros Hle Hvα; eapply shift_preserves_valid_gen; eauto. Qed.

End Typ.

(** ---- *)

(** * Syntax - Pair of types 

  The resource context defined in [RContext.v] maps resource names to pair types. We define it co-domain here. Thanks to the [DeBrLevel] library, we do not have to prove properties that handle level because [PairLevel] already exists.
*)


(** ** Module - Pair of types *)
Module PairTyp <: IsBdlLvlETWL := IsBdlLvlPairETWL Typ Typ.

(** ---- *)

(** ** Notation - Types *)
Module TypNotations.

(** *** Scope *)
Declare Scope typ_scope.
Declare Scope ptyp_scope.
Delimit Scope typ_scope with ty.
Delimit Scope ptyp_scope with pty.

(** *** Notation *)
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

Infix "⊩"  := Typ.valid (at level 20, no associativity): typ_scope. 
Infix "⊩"  := PairTyp.valid (at level 20, no associativity) : ptyp_scope. 
Infix "="  := Typ.eq : typ_scope.

(** *** Morphism *)
Import Typ.

#[export] Instance typ_leibniz_eq : Proper Logic.eq Typ.eq := _.
#[export] Instance typ_valid_proper :  Proper (Level.eq ==> eq ==> iff) valid := _.
#[export] Instance typ_shift_proper : Proper (Level.eq ==> Level.eq ==> eq ==> eq) shift := shift_eq.
#[export] Instance typ_multi_shift_proper : Proper (Logic.eq ==> Logic.eq ==> eq ==> Logic.eq) multi_shift := _.

End TypNotations.