From Coq Require Import Classes.Morphisms Bool.Bool Classical_Prop Classes.RelationClasses.
From DeBrLevel Require Import LevelInterface.
From Mecha Require Import Resource Term.

(** * Syntax - Cell 

  Resource environment is composed of cells with two possible pattern:
  - the first one is the input pattern. It represents the value mapped to the resource
    at the beginning of the instant and means that is not used yet;
  - the second one is the output pattern. It represents the value mapped to the resource
    after a resource signal function. It means that the initial value is consumed, the output
    is stocked for the update done at the end of this instant by the [temporal] transition and
    the resource is used.
*)
Module Cell <: IsLvlFullDTWL.

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

Definition eqb (p p' : t) := 
  match (p,p') with
    | (inp p1,inp p2) => (p1 =? p2)%tm
    | (out p1,out p2) => (p1 =? p2)%tm
    | _ => false
  end
.

(** **** Shift function 

  Cell carries a term then the [shift] function acts like a bind operator
  with the shift function of term.
*)
Definition shift (lb : Lvl.t) (k : Lvl.t) (c : t) : t := 
  match c with
    | inp tm => inp <[[⧐ₜₘ lb ≤ k] tm]>
    | out tm => out <[[⧐ₜₘ lb ≤ k] tm]>
  end.

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


(** **** Valid function 

 A cell is valid if the term encapsulated in it is valid.
*)
Definition valid (lb : Lvl.t) (c : t) : Prop := lb ⊩ₜₘ (extract c).
Definition validb (lb : Lvl.t) (c : t) : bool := lb ⊩?ₜₘ (extract c).

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

Lemma eqb_refl : forall p, eqb p p = true.
Proof. 
  intros; unfold eqb; destruct p; apply Term.eqb_refl. 
Qed.

Lemma eqb_eq : forall p p', eqb p p' = true <-> eq p p'.
Proof.
  intros; split.
  - unfold eq,eqb in *; destruct p,p'; simpl in *; intro; try (now inversion H);
    f_equal; now apply Term.eqb_eq.
  - unfold eq; intro; subst; apply eqb_refl.
Qed.

Lemma eqb_neq : forall p p', eqb p p' = false <-> ~ eq p p'.
Proof.
  split.
  - rewrite <- eqb_eq; intros. rewrite H; intro; inversion H0.
  - intros; apply not_true_is_false; intro; apply H; now rewrite <- eqb_eq.
Qed.

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


(** *** Shift *)

Lemma shift_refl : forall lb t, eq (shift lb 0 t) t.
Proof. intros; unfold shift,eq; destruct t0; f_equal; now apply Term.shift_refl. Qed.

#[global]
Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
Proof. repeat red; intros; subst. now rewrite H1. Qed.

Lemma shift_eq_iff : forall lb k t t1,
  t = t1 <-> (shift lb k t) = (shift lb k t1).
Proof.
  intros; destruct t0, t1; simpl in *; split;
  intro H; inversion H; subst; f_equal;
  eapply Term.shift_eq_iff; eauto.
Qed.

Lemma shift_trans : forall lb k k' t, 
  eq (shift lb k (shift lb k' t)) (shift lb (k + k') t).
Proof. intros; unfold shift,eq; destruct t0; f_equal; now apply Term.shift_trans. Qed.

Lemma shift_permute : forall lb k k' t, 
  eq (shift lb k (shift lb k' t)) (shift lb k' (shift lb k t)).
Proof. intros; unfold shift,eq; destruct t0; f_equal; now apply Term.shift_permute. Qed.

Lemma shift_unfold : forall lb k k' t,
  eq (shift lb (k + k') t) (shift (lb + k) k' (shift lb k t)). 
Proof.
  intros lb k k' t; unfold shift,eq; destruct t; f_equal; apply Term.shift_unfold.
Qed.

Lemma shift_unfold_1 : forall k k1 k2 t,
    k <= k1 -> k1 <= k2 -> eq (shift k1 (k2 - k1) (shift k  (k1 - k) t)) (shift k (k2 - k) t).
Proof.
  intros k k1 k2 t Hlt Hlt'; unfold shift,eq; destruct t; f_equal; 
  apply Term.shift_unfold_1; auto.
Qed.

(** *** Valid *)

Lemma validb_valid : forall k t, validb k t = true <-> valid k t.
Proof.
  split; unfold validb, valid; destruct t0; simpl; intros; now apply Term.validb_valid.
Qed.

Lemma validb_nvalid : forall k t, validb k t = false <-> ~ valid k t.
Proof.
  split; unfold validb, valid; destruct t0; simpl; intros; now apply Term.validb_nvalid.
Qed.

#[global]
Instance valid_eq : Proper (Logic.eq ==> eq ==> iff) valid.
Proof. repeat red; intros; subst; rewrite H0; auto. Qed.

#[global]
Instance validb_eq : Proper (Logic.eq ==> eq ==> Logic.eq) validb.
Proof. repeat red; intros; subst; rewrite H0; auto. Qed.

Lemma valid_weakening : forall k k' t, (k <= k') -> valid k t -> valid k' t.
Proof.
  intros; destruct t0; unfold valid in *; simpl in *; now apply Term.valid_weakening with k.
Qed.

Lemma shift_preserves_valid : forall k k' t, valid k t -> valid (k + k') (shift k k' t).
Proof.
  intros; destruct t0; unfold valid in *; simpl in *; now apply Term.shift_preserves_valid.
Qed.

Lemma shift_preserves_valid_1 : forall lb k k' t, valid k t -> valid (k + k') (shift lb k' t).
Proof.
  intros; destruct t0; unfold valid in *; simpl in *; now apply Term.shift_preserves_valid_1.
Qed.

Lemma shift_preserves_valid_2 : forall lb lb' k k' t,
  k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' -> k' - k = lb' - lb -> 
  valid lb t -> valid lb' (shift k (k' - k) t).
Proof.
  intros; destruct t0; unfold valid in *; simpl in *; 
  now apply Term.shift_preserves_valid_2 with lb.
Qed.

Lemma shift_preserves_valid_3 : forall lb lb' t,
  lb <= lb' -> valid lb t -> valid lb' (shift lb (lb' - lb) t).
Proof.
  intros; destruct t0; unfold valid in *; simpl in *; now apply Term.shift_preserves_valid_3.
Qed.

Lemma shift_preserves_valid_4 : forall k t, valid k t -> valid k (shift k 0 t).
Proof.
  intros; destruct t0; unfold valid in *; simpl in *; now apply Term.shift_preserves_valid_4.
Qed.

End Cell.

(** *** Scope and Notations *)

Declare Scope cell_scope.
Delimit Scope cell_scope with cl.
Definition 𝑣 := Cell.t.


Notation "⩽ v … ⩾" := (Cell.inp v) (at level 30, v custom wormholes, no associativity).
Notation "⩽ … v ⩾" := (Cell.out v) (at level 30, v custom wormholes, no associativity).
Notation "'[⧐ᵣₓ' lb '≤' k ']' t" := (Cell.shift lb k t) (at level 45, right associativity).

Infix "⊩ᵣₓ" := Cell.valid (at level 20, no associativity). 
Infix "⊩?ᵣₓ" := Cell.validb (at level 20, no associativity). 

Infix "=" := Cell.eq : cell_scope.
Infix "=?" := Cell.eqb  (at level 70) : cell_scope.