From Coq Require Import Classical_Prop Classes.RelationClasses MSets Bool.Bool Lia.
From DeBrLevel Require Import LevelInterface.
Require Import Var Typ.

(** * Syntax - Term

  Here is the definition of terms based on the arrow language.
*)
Module Term <: EqualityTypeWithLeibniz.

(** *** Definition *)


(** **** Type *)
Inductive raw : Type :=
  | tm_var    : variable -> raw
  | tm_app    : raw -> raw -> raw
  | tm_abs    : variable -> Τ -> raw -> raw
  | tm_pair   : raw -> raw -> raw
  | tm_fst    : raw -> raw
  | tm_snd    : raw -> raw
  | tm_arr    : raw -> raw
  | tm_first  : Τ -> raw -> raw
  | tm_comp   : raw -> raw -> raw
  | tm_unit   : raw
  | tm_fix    : raw
.

Definition t := raw.

(** **** Equality *)

Definition eq := @eq t.

Fixpoint eqb (e e' : t) := 
  match (e,e') with
    | (tm_var x,tm_var y) => (x =? y)%v
    | (tm_app e1 e2,tm_app e1' e2') => (eqb e1 e1') && (eqb e2 e2')
    | (tm_abs x τ e,tm_abs y τ' e') => (x =? y)%v && (τ =? τ')%typ && (eqb e e')
    | (tm_pair e1 e2,tm_pair e1' e2') => (eqb e1 e1') && (eqb e2 e2')
    | (tm_fst e,tm_fst e') => eqb e e'
    | (tm_snd e,tm_snd e') => eqb e e'
    | (tm_arr e,tm_arr e') => eqb e e'
    | (tm_first τ e,tm_first τ' e') => (τ =? τ')%typ && eqb e e'
    | (tm_comp e1 e2,tm_comp e1' e2') => (eqb e1 e1') && (eqb e2 e2')
    | (tm_unit, tm_unit) => true
    | (tm_fix, tm_fix) => true
    | _ => false
  end
.

(** **** Others *)

Inductive appears_free_in : variable -> t -> Prop :=
  | afi_var : forall (x : variable), appears_free_in x (tm_var x)
  
  | afi_app1 :  forall x t1 t2, appears_free_in x t1 -> appears_free_in x (tm_app t1 t2)

  | afi_app2 :  forall x t1 t2, appears_free_in x t2 -> appears_free_in x (tm_app t1 t2)

  | afi_abs  :  forall x y τ t,
                  y <> x  -> appears_free_in x t -> appears_free_in x (tm_abs y τ t) 

  | afi_pair1 : forall x t1 t2, appears_free_in x t1 -> appears_free_in x (tm_pair t1 t2)

  | afi_pair2 : forall x t1 t2, appears_free_in x t2 -> appears_free_in x (tm_pair t1 t2)

  | afi_fst   : forall x t, appears_free_in x t -> appears_free_in x (tm_fst t)
  | afi_snd   : forall x t, appears_free_in x t -> appears_free_in x (tm_snd t)
  | afi_arr   : forall x t, appears_free_in x t -> appears_free_in x (tm_arr t)
  | afi_first : forall x τ t, appears_free_in x t -> appears_free_in x (tm_first τ t)
  
  | afi_comp1 : forall x t1 t2, appears_free_in x t1 -> appears_free_in x (tm_comp t1 t2)
  | afi_comp2 : forall x t1 t2, appears_free_in x t2 -> appears_free_in x (tm_comp t1 t2)
.

Definition closed (t : t) := forall x, ~ (appears_free_in x t).

Inductive value : t -> Prop :=
  | v_unit  : value tm_unit
  | v_fix  : value tm_fix

  | v_abs   : forall x τ t, value (tm_abs x τ t)

  | v_pair  : forall v1 v2, 
                value v1 -> value v2 -> value (tm_pair v1 v2)

  | v_arr   : forall t, value t -> value (tm_arr t)

  | v_first : forall τ t, value t -> value (tm_first τ t)

  | v_comp  : forall t1 t2, value t1 -> value t2 -> value (tm_comp t1 t2)
.


#[global] 
Hint Constructors value appears_free_in : core.

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

Lemma eqb_refl : forall e, eqb e e = true.
Proof.
  induction e; simpl; auto; try (rewrite andb_true_iff; split; now auto).
  - apply Var.eqb_refl.
  - repeat rewrite andb_true_iff; split; auto; split.
    -- apply Var.eqb_refl.
    -- apply Typ.eqb_refl.
  - rewrite andb_true_iff; split; try assumption. apply Typ.eqb_refl.
Qed.  

Lemma eqb_eq : forall e1 e2, eqb e1 e2 = true <-> eq e1 e2.
Proof.
  unfold eq,eqb; induction e1; intros; destruct e2; split; intro H; 
  try (now inversion H); fold eqb in *;
  try (apply andb_true_iff in H as [H H']; f_equal; rewrite IHe1_1 in *; 
        rewrite IHe1_2 in *; now auto);
  try (inversion H; subst; rewrite andb_true_iff in *; split; now apply eqb_refl);
  try (rewrite IHe1 in *; subst; now reflexivity);
  try (inversion H; subst; now apply eqb_refl).
  - f_equal; now rewrite Var.eqb_eq in *.
  - inversion H; subst; apply Var.eqb_refl.
  - repeat rewrite andb_true_iff in *; destruct H as [[H1 H2] H3].
    rewrite IHe1 in *; subst; rewrite Var.eqb_eq in H1; subst.
    rewrite Typ.eqb_eq in H2; rewrite H2; reflexivity. 
  - repeat rewrite andb_true_iff in *; inversion H; subst; repeat split.
    -- apply Var.eqb_refl.
    -- apply Typ.eqb_refl.
    -- apply eqb_refl.
  - rewrite andb_true_iff in *; destruct H; rewrite Typ.eqb_eq in H.
    rewrite H; apply IHe1 in H0; now subst.
  - rewrite andb_true_iff; inversion H; split.
    -- apply Typ.eqb_refl.
    -- apply eqb_refl.
Qed.

Lemma eqb_neq : forall e e', eqb e e' = false <-> ~ eq e e'.
Proof.
  split; intros.
  - unfold not; intros; apply eqb_eq in H0; rewrite H in *; inversion H0.
  - rewrite <- eqb_eq in *; intros; now apply not_true_is_false.
Qed.

Lemma eq_dec : forall (e e' : t), {eq e e'} + {~ eq e e'}.
Proof.
  unfold eq; intros e; induction e; intros e'; destruct e'; simpl; auto; 
  try (right; unfold not; intros contra; now inversion contra);
  try (destruct (IHe1 e'1); destruct (IHe2 e'2);
  try (right; unfold not; intros; inversion H; subst; contradiction); subst; f_equal; auto);
  try (destruct (IHe e'); subst; try (now left); right; intro c; 
        inversion c; subst; now contradiction).
  - destruct (Var.eqb_spec v v0); subst.
    -- now left.
    -- right; intro c; inversion c; subst; clear c; now contradiction n.
  - destruct (Typ.eq_dec τ τ0); destruct (Var.eqb_spec v v0); unfold Typ.eq in *; subst;
    destruct (IHe e'); subst; try (right; intro c; inversion c; subst; now contradiction).
    now left.
  - destruct (Typ.eq_dec τ τ0); destruct (IHe e'); unfold Typ.eq in *; subst; auto;
    try (right; intro c; inversion c; subst; now contradiction).
Qed.

Lemma eq_leibniz : forall x y, eq x y -> x = y. Proof. auto. Qed.

End Term.


(** *** Scope and Notations *)
Declare Scope term_scope.
Delimit Scope term_scope with tm.
Definition Λ := Term.t.

Coercion Term.tm_var : variable >-> Term.raw.
Notation "value( t )" := (Term.value t) (at level 20, no associativity).
Notation "clₜₘ( t )" := (Term.closed t) (at level 20, no associativity).
Notation "'isFV(' r ',' t ')'" := (Term.appears_free_in r t) (at level 40, t custom arrow).

Notation "x y"     := (Term.tm_app x y) (in custom arrow at level 70, left associativity).
Notation "\ x : t , y" := (Term.tm_abs x t y) (in custom arrow at level 90, 
                                                    x at level 99, t custom arrow at level 99, 
                                                    y custom arrow at level 99, 
                                                    left associativity).
Notation "'unit'" := (Term.tm_unit) (in custom arrow at level 0).
Notation "'Fix'" := (Term.tm_fix) (in custom arrow at level 0).
Notation "⟨ x ',' y ⟩" := (Term.tm_pair x y) (in custom arrow at level 0, 
                                                      x custom arrow at level 99, 
                                                      y custom arrow at level 99).
Notation "t '.fst'"  := (Term.tm_fst t) (in custom arrow at level 0).
Notation "t '.snd'"  := (Term.tm_snd t) (in custom arrow at level 0).
Notation "'arr(' f ')'"    := (Term.tm_arr f) (in custom arrow at level 0, 
                                                      f custom arrow at level 99,
                                                      no associativity).
Notation "'first(' τ ':' sf ')'" := (Term.tm_first τ sf) (in custom arrow at level 0).
Notation " sf1 '>>>' sf2 " := (Term.tm_comp sf1 sf2) (in custom arrow at level 60, 
                                                                          left associativity).

Infix "=" := Term.eq : term_scope.
Infix "=?" := Term.eqb  (at level 70) : term_scope.