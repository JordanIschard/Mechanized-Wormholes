From Coq Require Import Classes.Morphisms Bool.Bool Classical_Prop Classes.RelationClasses.
From DeBrLevel Require Import LevelInterface.
From Mecha Require Import Resource Term.

Module Cell <: EqualityTypeWithLeibniz.

(** *** Definition  *)

(** **** Type *)

(** 
  An element in the environment can be used only once. Thus the term is
  embedded in a type that differs unused and used value.
*)
Inductive raw : Type := 
  | inp  : Λ -> raw
  | out : Λ -> raw
. 

Definition t := raw.

(** **** Equality *)

Definition eq := @Logic.eq t.

(** **** Others *)

Definition embed (e : Λ) := inp e.

Definition extract (e : t) :=
  match e with
    | inp t => t
    | out t => t
  end
.

Definition unused (e : t) :=
  match e with
    | inp _ => True
    | _ => False
  end
.

Definition used (e : t) :=
  match e with
    | out _ => True
    | _ => False
  end
.

(** *** Equality *)

Lemma eq_refl : Reflexive eq.
Proof. unfold Reflexive, eq; intro x; destruct x; simpl; auto. Qed.

Lemma eq_sym : Symmetric eq.
Proof. 
  unfold Symmetric,eq; intros x y; destruct x,y; simpl; intro; auto. 
Qed.

Lemma eq_trans : Transitive eq.
Proof. 
  unfold Transitive,eq; intros x y z Hxy Hyz; destruct x,y,z; simpl in *;
  try now transitivity (inp λ0). now transitivity (out λ0). 
Qed.

#[global] 
Hint Resolve eq_refl eq_sym eq_trans : core.

#[global] 
Instance eq_rr : RewriteRelation eq := {}.
#[global] 
Instance eq_equiv : Equivalence eq.
          Proof. split; auto. Qed.

Lemma eq_dec : forall (p p' : t), {eq p p'} + {~ eq p p'}.
Proof.
  unfold eq; intros p p'; destruct p,p'; simpl;
  destruct (Term.eq_dec λ λ0); unfold Term.eq in *; subst; auto;
  try (right; intro; inversion H; subst; clear H; now apply n).
Qed.

Lemma eq_dec' : forall (p p' : t), {p = p'} + {p <> p'}.
Proof.
  intros p p'; destruct p,p'; destruct (Term.eq_dec λ λ0); unfold Term.eq in *;
  subst; auto;
  right; intro c; inversion c; subst; apply n; auto. 
Qed.

Lemma eq_leibniz : forall p p', eq p p' -> p = p'. 
Proof. intros; auto. Qed.

End Cell.

(** *** Scope and Notations *)

Declare Scope cell_scope.
Delimit Scope cell_scope with cl.
Definition 𝑣 := Cell.t.


Notation "⩽ v … ⩾" := (Cell.inp v) (at level 30, v custom rsf, no associativity).
Notation "⩽ … v ⩾" := (Cell.out v) (at level 30, v custom rsf, no associativity).

Infix "=" := Cell.eq : cell_scope.