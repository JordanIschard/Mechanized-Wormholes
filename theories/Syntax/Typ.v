From Coq Require Import Classes.RelationClasses Classes.Morphisms Bool.Bool Classical_Prop.
From DeBrLevel Require Import LevelInterface.

(** * Syntax -  Type

  Here is the definition of types based on the Wormholes language.
*)
Module Typ <: EqualityTypeWithLeibniz.


(** *** Definition *)

(** **** Type *)
Inductive raw : Type :=
  | ty_unit
  | ty_arrow : raw -> raw -> raw
  | ty_prod  : raw -> raw -> raw
  | ty_reactive : raw -> raw -> raw
.

Definition t := raw.

(** **** Equality *)
Definition eq := @Logic.eq t.

Fixpoint eqb' (τ τ' : t) : bool := 
  match (τ,τ') with
    | (ty_unit,ty_unit)                            => true
    | (ty_prod τ1 τ2,ty_prod τ1' τ2')              => (eqb' τ1 τ1') && (eqb' τ2 τ2')
    | (ty_arrow τ1 τ2,ty_arrow τ1' τ2')            => (eqb' τ1 τ1') && (eqb' τ2 τ2')
    | (ty_reactive τ1 τ2, ty_reactive τ1' τ2')     => (eqb' τ1 τ1') && (eqb' τ2 τ2')
    | _ => false
  end
.

Definition eqb := eqb'.

(** *** Equality *)

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

Lemma eqb_refl : forall τ, eqb τ τ = true.
Proof.
  induction τ; simpl; auto; try (rewrite andb_true_iff; split; now auto).
Qed.

Lemma eqb_eq : forall τ1 τ2, eqb τ1 τ2 = true <-> eq τ1 τ2.
Proof.
  intros; split.
  - revert τ2; unfold eq,eqb; induction τ1; intros; destruct τ2; inversion H; subst; auto.
    -- apply andb_true_iff in H1 as [H1 H1']; f_equal; auto.
    -- apply andb_true_iff in H1 as [H1 H1']; f_equal; auto.
    -- apply andb_true_iff in H1 as [H1 H1']; f_equal; auto.
  - intros; rewrite H; apply eqb_refl.
Qed.

Lemma eqb_neq : forall τ τ', eqb τ τ' = false <-> ~ eq τ τ'.
Proof.
  split.
  - unfold not; intros; apply eqb_eq in H0; rewrite H in *; inversion H0.
  - rewrite <- eqb_eq; intros; now apply not_true_is_false.
Qed.

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
  - destruct (IHτ1 τ'1); destruct (IHτ2 τ'2);
    try (right; unfold not; intros; inversion H; subst; contradiction); subst.
    f_equal; auto.
Qed.

Lemma eq_dec' : forall (τ τ' : t), {τ = τ'} + {τ <> τ'}.
Proof.
  intros; destruct (eq_dec τ τ'). 
  - unfold eq in *; subst; auto.
  - unfold eq in *; auto.
Qed.

Lemma eq_leibniz : forall x y, eq x y -> x = y. Proof. auto. Qed.

End Typ.

(** *** Scope and Notations *)
Declare Custom Entry arrow.
Declare Scope typ_scope.
Delimit Scope typ_scope with typ.
Definition Τ := Typ.t.
  
Notation "'𝟙'"       := Typ.ty_unit (in custom arrow at level 0, no associativity).
Notation "T1 '→' T2" := (Typ.ty_arrow T1 T2) (in custom arrow at level 50, 
                                                                  right associativity).
Notation "X '×' Y"   := (Typ.ty_prod X Y) (in custom arrow at level 2, 
                                                        X custom arrow, 
                                                        Y custom arrow at level 0).
Notation "τ1 '⟿' τ2" := (Typ.ty_reactive τ1 τ2) (in custom arrow at level 50, right associativity).


Infix "=" := Typ.eq : typ_scope.
Infix "=?" := Typ.eqb  (at level 70) : typ_scope.