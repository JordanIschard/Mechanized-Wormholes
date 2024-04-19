From Coq Require Import Structures.OrdersEx Classes.RelationClasses Classes.Morphisms Bool.Bool Classical_Prop.
From Mecha Require Import Resource Resources.
From DeBrLevel Require Import LevelInterface.

Module Typ <: EqualityTypeWithLeibniz.

Module RS := Resources.

(** *** Definition *)

(** **** Type *)
Inductive raw : Type :=
  | ty_unit
  | ty_arrow : raw -> raw -> raw
  | ty_prod  : raw -> raw -> raw
  | ty_reactive : raw -> raw -> resources -> raw
.

Definition t := raw.

(** **** Equality *)
Definition eq := @Logic.eq t.

Lemma eq_refl : Reflexive eq.
Proof. unfold Reflexive, eq; now reflexivity. Qed.

Lemma eq_sym : Symmetric eq.
Proof. unfold Symmetric,eq; now symmetry. Qed.

Lemma eq_trans : Transitive eq.
Proof. unfold Transitive,eq; intros; now transitivity y. Qed.

#[global] 
Hint Resolve eq_refl eq_sym eq_trans : core.

#[global] 
Instance eq_rr : RewriteRelation eq := {}.
#[global] 
Instance eq_equiv : Equivalence eq. Proof. split; auto. Qed.

Lemma eq_dec : forall (τ τ' : t), {eq τ τ'} + {~ eq τ τ'}.
Proof.
  unfold eq; intros τ; induction τ; intros τ'; destruct τ'; simpl; auto; 
  try (right; unfold not; intros contra; now inversion contra).
  - destruct (IHτ1 τ'1); destruct (IHτ2 τ'2);
    try (right; unfold not; intros; inversion H; subst; contradiction); subst.
    f_equal; auto. 
  - destruct (IHτ1 τ'1); destruct (IHτ2 τ'2);
    try (right; unfold not; intros; inversion H; subst; contradiction); subst.
    f_equal; auto.
  - destruct (IHτ1 τ'1); destruct (IHτ2 τ'2); destruct (RS.eq_dec r r0);
    try (right; unfold not; intros; inversion H; subst; contradiction); subst.
    -- apply RS.eq_leibniz in e1; subst; auto.
    -- right; unfold not in *; intros; inversion H; subst; apply n; reflexivity.
Qed.

Lemma eq_dec' : forall (τ τ' : t), {τ = τ'} + {τ <> τ'}.
Proof.
  intros; destruct (eq_dec τ τ'). 
  - unfold eq in *; subst; auto.
  - unfold eq in *; auto.
Qed.

Lemma eq_leibniz : forall x y, eq x y -> x = y. Proof. auto. Qed.

End Typ.


Module PairTyp <: EqualityTypeWithLeibniz.

(** *** Definition *)
Section definition.

Definition t := (Typ.t * Typ.t)%type.

Definition eq := @Logic.eq t.

#[global]
Instance eq_equiv : Equivalence eq := _.

End definition.

(** *** Equality *)
Section equality.

Lemma eq_refl : Reflexive eq. 
Proof. 
  red; intros; destruct x; unfold eq; split;
  unfold RelationPairs.RelCompFun; simpl; reflexivity.
Qed.

Lemma eq_sym  : Symmetric eq.
Proof. 
  red; intros; destruct x,y; unfold eq in *; destruct H;
  unfold RelationPairs.RelCompFun in *; simpl in *; now symmetry.
Qed.

Lemma eq_trans   : Transitive eq.
Proof. 
  red; intros; destruct x,y,z; unfold eq in *; destruct H,H0;
  unfold RelationPairs.RelCompFun in *; simpl in *; etransitivity; eauto.
Qed.

Lemma eq_leibniz : forall x y, eq x y -> x = y. Proof. auto. Qed.

End equality.

End PairTyp.

(** *** Scope and Notations *)
Declare Scope typ_scope.
Delimit Scope typ_scope with typ.
Definition Τ := Typ.t.
Definition πΤ := PairTyp.t.
  
Notation "'𝟙'"       := Typ.ty_unit (in custom rsf at level 0).
Notation "T1 '→' T2" := (Typ.ty_arrow T1 T2) (in custom rsf at level 50, 
                                                                  right associativity).
Notation "X '×' Y"   := (Typ.ty_prod X Y) (in custom rsf at level 2, 
                                                        X custom rsf, 
                                                        Y custom rsf at level 0).
Notation "τ1 '⟿' τ2 '∣' R" := (Typ.ty_reactive τ1 τ2 R) (in custom rsf at level 50, 
                                                                  R constr, right associativity).

Infix "=" := Typ.eq : typ_scope.