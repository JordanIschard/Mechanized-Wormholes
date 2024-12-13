From Coq Require Import Classes.Morphisms Bool.Bool Classical_Prop Classes.RelationClasses.
From DeBrLevel Require Import LevelInterface Level.
From Mecha Require Import Resource Term.
Import ResourceNotations TermNotations.

(** * Syntax - Cell 

  A local memory cell is used in the resource environment, defined in [REnvironment.v]. It has two states: unused, used. For each states, the cell carries a term. However, its meaning differs. Indeed, when a cell is unused, then the term in it is the input term available during the instant. If the cell is used, then the term is the output term which will be given to the global environment at the end of the instant.
*)

(** ** Module - Cell *)
Module Cell <: IsLvlDTWL.

Open Scope term_scope.

(** *** Definitions  *)

(** **** Type

  A cell has two disjoints states structurally represented by  [<t .>], for unused state, and [<. t>], for used state, where [t] is a term.
*)
Inductive raw : Type := 
  | inp : Λ -> raw
  | out : Λ -> raw. 

Definition t := raw.
Definition eq := @eq t.

(** **** Shift function 

  A cell is a container for a term. Consequently, we apply the [shift] function for terms on the term carried while maintaining the shape of the cell.
*)
Definition shift (lb k : lvl) (c : t) : t := 
  match c with
    | inp tm => inp <[[⧐ lb – k] tm]>
    | out tm => out <[[⧐ lb – k] tm]>
  end.


(** **** Constructor 

  We define a function denoted [embed] which takes a term [t] and produces an unused cell which contains [t].
*)
Definition embed (t : Λ) := inp t.

(** **** Destructor 

  We define a function [extract] which opens the cell and returns its inner term.
*)
Definition extract (t : t) :=
  match t with
    | inp t => t
    | out t => t
  end.

(** **** Status checker *)
Definition unused (t : t) :=
  match t with
    | inp _ => True
    | _ => False
  end.

Definition used (t : t) :=
  match t with
    | out _ => True
    | _ => False
  end.

Definition opt_unused (ot : option t) :=
  match ot with Some t => unused t | _ => False end.

Definition opt_used (ot : option t) :=
  match ot with Some t => used t | _ => False end.

(** **** Well-formedness 

  A cell [c] is well-formed under a level [lb] if and only if its carried term [t] is well-formed under [lb].
*)
Definition Wf (lb : lvl) (c : t) : Prop := lb ⊩ (extract c).


(** *** Properties *)

(** **** [eq] properties *)

#[export] Instance eq_refl : Reflexive eq := _.

#[export] Instance eq_sym : Symmetric eq := _.

#[export] Instance eq_trans : Transitive eq := _.

#[export] Instance eq_rr : RewriteRelation eq := {}.

#[export] Instance eq_equiv : Equivalence eq := _.

#[export] Hint Resolve eq_refl eq_sym eq_trans : core.

Lemma eq_dec (c c' : t) : {eq c c'} + {~ eq c c'}.
Proof.
  unfold eq; destruct c,c'; simpl;
  destruct (Term.eq_dec λ λ0); unfold Term.eq in *; subst; auto;
  try (right; intro; inversion H; subst; clear H; now apply n).
Qed.

Lemma eq_dec' (c c' : t) : {c = c'} + {c <> c'}.
Proof.
  destruct c,c'; destruct (Term.eq_dec λ λ0); unfold Term.eq in *;
  subst; auto; right; intro c; inversion c; subst; apply n; auto. 
Qed.

Lemma eq_leibniz (c c' : t) : eq c c' -> c = c'. 
Proof. auto. Qed. 

#[export] Instance extract_eq : Proper (eq ==> Term.eq) extract.
Proof. now intros c' c Heq; rewrite Heq. Qed. 

(** **** [shift] properties *)

Lemma shift_zero_refl (lb : lvl) (c : t) : eq (shift lb 0 c) c.
Proof. 
  unfold eq; destruct c; simpl; f_equal;
  now apply Term.shift_zero_refl. 
Qed.

#[export] Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
Proof. intros m' m Heqm n' n Heqn c c' Heqc; subst; now rewrite Heqc. Qed.

Lemma shift_eq_iff (lb k : lvl) (c c' : t) :
  eq c c' <-> eq (shift lb k c) (shift lb k c').
Proof.
  destruct c,c'; simpl; unfold eq; split; intro Heq;
  inversion Heq; subst; auto; f_equal;
  eapply Term.shift_eq_iff; eauto.
Qed.

Lemma shift_trans (k m n : lvl) (c : t) : 
  eq (shift k m (shift k n c)) (shift k (m + n) c).
Proof. unfold shift,eq; destruct c; f_equal; now apply Term.shift_trans. Qed.

Lemma shift_permute (k m n : lvl) (c : t) : 
  eq (shift k m (shift k n c)) (shift k n (shift k m c)).
Proof. unfold shift,eq; destruct c; f_equal; now apply Term.shift_permute. Qed.

Lemma shift_unfold (k m n : lvl) (c : t) :
  eq (shift k (m + n) c) (shift (k + m) n (shift k m c)). 
Proof. unfold shift,eq; destruct c; f_equal; apply Term.shift_unfold. Qed.

Lemma shift_unfold_1 (k m n : lvl) (c : t) :
    k <= m -> m <= n -> 
    eq (shift m (n - m) (shift k  (m - k) c)) (shift k (n - k) c).
Proof.
  intros Hlt Hlt'; unfold shift,eq; destruct c; f_equal; 
  now apply Term.shift_unfold_1.
Qed.

(** **** [Wf] properties *)

#[export] Instance Wf_iff : Proper (Logic.eq ==> eq ==> iff) Wf.
Proof. intros k' k Heqk c c' Heqc; subst; now rewrite Heqc. Qed.

Lemma Wf_weakening (k n : lvl) (c : t) : (k <= n) -> Wf k c -> Wf n c.
Proof.
  destruct c; unfold Wf; simpl; intros Hlekn Hvc; 
  now apply Term.Wf_weakening with k.
Qed.

Lemma shift_preserves_wf (k n : lvl) (c : t) :
  Wf k c -> Wf (k + n) (shift k n c).
Proof.
  destruct c; unfold Wf; simpl; intro Hvc; 
  now apply Term.shift_preserves_wf.
Qed.

Lemma shift_preserves_wf_1 (lb k n : lvl) (c : t) : 
  Wf k c -> Wf (k + n) (shift lb n c).
Proof.
  destruct c; unfold Wf; simpl; intro Hvc; 
  now apply Term.shift_preserves_wf_1.
Qed.

Lemma shift_preserves_wf_gen (lb k m n : lvl) (c : t) :
  m <= n -> lb <= k -> m <= lb -> n <= k -> n - m = k - lb -> 
  Wf lb c -> Wf k (shift m (n - m) c).
Proof.
  destruct c; unfold Wf; simpl; intros; 
  now apply Term.shift_preserves_wf_gen with lb.
Qed.

Lemma shift_preserves_wf_2 (m n : lvl) (c : t) :
  m <= n -> Wf m c -> Wf n (shift m (n - m) c).
Proof.
  destruct c; unfold Wf; simpl; intros; 
  now apply Term.shift_preserves_wf_2.
Qed.

Lemma shift_preserves_wf_zero (k : lvl) (c : t) : 
  Wf k c -> Wf k (shift k 0 c).
Proof.
  destruct c; unfold Wf; simpl; intros; 
  now apply Term.shift_preserves_wf_zero.
Qed.

End Cell.

(** ---- *)

(** ** Notation - Cell *)
Module CellNotations.

(** ** Scope *)
Declare Scope cell_scope.
Delimit Scope cell_scope with cl.

(** ** Notations *)
Definition 𝑣 := Cell.t.

Notation "⩽ v … ⩾" := (Cell.inp v) (at level 30, v custom wh, no associativity).
Notation "⩽ … v ⩾" := (Cell.out v) (at level 30, v custom wh, no associativity).
Notation "'[⧐' lb '–' k ']' t" := (Cell.shift lb k t) (at level 65, right associativity) : cell_scope.

Infix "⊩" := Cell.Wf (at level 20, no associativity) : cell_scope. 
Infix "=" := Cell.eq : cell_scope.

(** ** Morphisms *)
Import Cell.

#[export] Instance cell_leibniz_eq : Proper Logic.eq Cell.eq := _.

#[export] Instance cell_wf_iff :  Proper (Level.eq ==> eq ==> iff) Wf := _.

#[export] Instance cell_shift_eq : Proper (Level.eq ==> Level.eq ==> eq ==> eq) shift := shift_eq.

End CellNotations.