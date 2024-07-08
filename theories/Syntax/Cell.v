From Coq Require Import Classes.Morphisms Bool.Bool Classical_Prop Classes.RelationClasses.
From DeBrLevel Require Import LevelInterface.
From Mecha Require Import Resource Term.
Import ResourceNotations TermNotations.

(** * Syntax - Cell 

 A cell can have shape [<t .>] or [<. t>], for a term [t]. The first one is the
 unused form with a term that can be used during the instant. The second one is
 the used form which also contains a term but not usable during the instant.

*)
Module Cell <: IsLvlFullDTWL.

Open Scope term_scope.

(** ** Definition  *)

(** *** Type *)

Inductive raw : Type := 
  | inp  : Λ -> raw
  | out : Λ -> raw
. 

Definition t := raw.

(** **** Equality *)

Definition eq (p p' : t) := 
 match (p,p') with
    | (inp p1,inp p2) => (p1 = p2)%tm
    | (out p1,out p2) => (p1 = p2)%tm
    | _ => False
  end
.

Definition eqb (p p' : t) := 
  match (p,p') with
    | (inp p1,inp p2) => p1 =? p2
    | (out p1,out p2) => p1 =? p2
    | _ => false
  end
.

(** *** Shift function 

  Cell carries a term then the [shift] function acts like a bind operator
  with the shift function of term.

*)
Definition shift (lb : Lvl.t) (k : Lvl.t) (c : t) : t := 
  match c with
    | inp tm => inp <[[⧐ lb – k] tm]>
    | out tm => out <[[⧐ lb – k] tm]>
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


(** *** Extract *)

#[export] Instance extract_eq : Proper (eq ==> Term.eq) extract.
Proof. 
  repeat red; intros x y Heq; destruct x,y;
  simpl in *; unfold eq in *; try contradiction;
  now rewrite Heq.
Qed.

(** *** Valid function 

 A cell [c] is valid at level [lb] if its inner term is valid.
*)
Definition valid (lb : Lvl.t) (c : t) : Prop := lb ⊩ (extract c).
Definition validb (lb : Lvl.t) (c : t) : bool := lb ⊩? (extract c).

(** ** Property *)

(** *** Equality *)

#[export] Instance eq_refl : Reflexive eq.
Proof. repeat red; intros x; destruct x; reflexivity. Qed.

#[export] Instance eq_sym : Symmetric eq.
Proof. 
  repeat red; intros x y; destruct x,y; auto;
  intros; unfold eq in *; now symmetry.
Qed.

#[export] Instance eq_trans : Transitive eq.
Proof.
  repeat red; intros x y z; destruct x,y,z; auto;
  intros; unfold eq in *; try contradiction;
  now rewrite H.
Qed.

#[export] 
Hint Resolve eq_refl eq_sym eq_trans : core.

#[export] Instance eq_rr : RewriteRelation eq := {}.
#[export] Instance eq_equiv : Equivalence eq.
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
  - unfold eq; intro; subst. destruct p,p'; auto;
    rewrite H; apply eqb_refl.
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
Proof. 
  intros; unfold eq in *; destruct p,p'; try contradiction;
  now rewrite H.
Qed.


(** *** Shift *)

Lemma shift_zero_refl : forall lb t, eq (shift lb 0 t) t.
Proof. intros; unfold shift,eq; destruct t0; f_equal; now apply Term.shift_zero_refl. Qed.

#[export] Instance shift_eq : 
  Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
Proof.
  repeat red; intros; subst; destruct x1,y1; auto;
  unfold eq in *; simpl; now rewrite H1.
Qed.

Lemma shift_eq_iff : forall lb k t t1,
  eq t t1 <-> eq (shift lb k t) (shift lb k t1).
Proof.
  intros; destruct t0,t1; simpl in *; split;
  intro H; unfold eq in *; try contradiction;
  try (now rewrite H);
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

#[export] Instance valid_eq : Proper (Logic.eq ==> eq ==> iff) valid.
Proof.
  repeat red; intros; subst; destruct x0,y0; unfold eq in *;
  try contradiction; unfold valid; simpl; now rewrite H0.
Qed.

#[export] Instance validb_eq : Proper (Logic.eq ==> eq ==> Logic.eq) validb.
Proof.
  repeat red; intros; subst; destruct x0,y0; unfold eq in *;
  try contradiction; unfold valid; simpl; now rewrite H0.
Qed.

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

Lemma shift_preserves_valid_gen : forall lb lb' k k' t,
  k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' -> k' - k = lb' - lb -> 
  valid lb t -> valid lb' (shift k (k' - k) t).
Proof.
  intros; destruct t0; unfold valid in *; simpl in *; 
  now apply Term.shift_preserves_valid_gen with lb.
Qed.

Lemma shift_preserves_valid_2 : forall lb lb' t,
  lb <= lb' -> valid lb t -> valid lb' (shift lb (lb' - lb) t).
Proof.
  intros; destruct t0; unfold valid in *; simpl in *; now apply Term.shift_preserves_valid_2.
Qed.

Lemma shift_preserves_valid_zero : forall k t, valid k t -> valid k (shift k 0 t).
Proof.
  intros; destruct t0; unfold valid in *; simpl in *; now apply Term.shift_preserves_valid_zero.
Qed.

End Cell.


(** * Notation - Cell *)
Module CellNotations.

(** ** Scope *)
Declare Scope cell_scope.
Delimit Scope cell_scope with cl.

(** ** Notations *)
Definition 𝑣 := Cell.t.

Notation "⩽ v … ⩾" := (Cell.inp v) (at level 30, v custom wh, no associativity).
Notation "⩽ … v ⩾" := (Cell.out v) (at level 30, v custom wh, no associativity).
Notation "'[⧐' lb '–' k ']' t" := (Cell.shift lb k t) (at level 65, right associativity) : cell_scope.

Infix "⊩" := Cell.valid (at level 20, no associativity) : cell_scope. 
Infix "⊩?" := Cell.validb (at level 20, no associativity) : cell_scope. 

Infix "=" := Cell.eq : cell_scope.
Infix "=?" := Cell.eqb  (at level 70) : cell_scope.

End CellNotations.