From Coq Require Import Lia.
From Mecha Require Import Resource Term.
From DeBrLevel Require Import LevelInterface.
From MMaps Require Import MMaps.
Import ResourceNotations TermNotations.

(** * Syntax - Triplet

  In the functional transition definition, there is a triplet that saves locale resources with their initial value. We define it here.
*)

(** ** Module - Term *)
Module Triplet <: IsLvlET.

(** *** Definitions *)

(** **** The definition of a triplet 

  It contains the two local resources as well as the initial value.
*)
Definition t : Type := resource * resource * Λ.
Definition eq := @Logic.eq t.

#[export] Instance eq_equiv : Equivalence eq := _.

(** **** The shift function 

  As in the [PairTyp] module, the shift function applies the appropriate shift function on each elements.
*)
Definition shift (m n : resource) (tp : t) :=
  let '(rg,rs,v) := tp in 
  (([⧐ m – n] rg)%r,([⧐ m – n] rs)%r,(Term.shift m n v)%tm).

(** **** The well-formed property 

  A triplet is well-formed under a level [m] if each of its elements are well-formed under [m].
*)
Definition Wf (m : resource) (tp : t) :=
  let '(rg,rs,v) := tp in 
  Resource.Wf m rg /\ Resource.Wf m rs /\ Term.Wf m v.


(** *** Properties *)

(** **** [eq] properties *)

#[export] Hint Resolve eq_refl eq_sym eq_trans : core.

Lemma eq_dec (t1 t2: t) : {eq t1 t2} + {~ eq t1 t2}.
Proof.
  unfold eq.
  destruct t1 as [[rg1 rs1] v1];
  destruct t2 as [[rg2 rs2] v2].
  destruct (Resource.eq_dec rg1 rg2); subst;
  destruct (Resource.eq_dec rs1 rs2); subst;
  destruct (Term.eq_dec v1 v2); 
  try (unfold Term.eq in e); subst; auto;
  right;
  intro c; inversion c; contradiction.
Qed.

Lemma eq_leibniz (t1 t2: t) : eq t1 t2 -> t1 = t2. 
Proof. auto. Qed.

(** **** [shift] properties *)

Lemma shift_zero_refl (lb : lvl) (t : t) : shift lb 0 t = t.
Proof.
  destruct t as [[rg rs] v]; simpl.
  do 2 rewrite Resource.shift_zero_refl.
  now rewrite Term.shift_zero_refl.
Qed.

#[export] Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.

Lemma shift_eq_iff (lb k : lvl) (t t1 : t) :
  t = t1 <-> (shift lb k t) = (shift lb k t1).
Proof.
  split; intro Heq.
  - now subst.
  - destruct t as [[rg rs] v];
    destruct t1 as [[rg1 rs1] v1];
    simpl in *. 
    inversion Heq.
    rewrite <- Resource.shift_eq_iff in H0,H1; subst.
    rewrite <- Term.shift_eq_iff in H2; subst.
    reflexivity.
Qed.

Lemma shift_trans (lb k m : lvl) (t : t) :
  shift lb k (shift lb m t) = shift lb (k + m) t.
Proof.
  destruct t as [[rg rs] v]; simpl.
  do 2 rewrite Resource.shift_trans.
  now rewrite Term.shift_trans.
Qed.

Lemma shift_permute (lb k m : lvl) (t : t) :
  shift lb k (shift lb m t) = shift lb m (shift lb k t).
Proof.
  destruct t as [[rg rs] v]; simpl.
  f_equal; try (now rewrite Term.shift_permute).
  f_equal;
  now rewrite Resource.shift_permute.
Qed.

Lemma shift_permute_1 (lb k m : lvl) (t : t) :
  eq (shift lb k (shift lb m t)) (shift (lb + k) m (shift lb k t)).
Proof.
  unfold eq.
  destruct t as [[rg rs] v]; simpl.
  do 2 rewrite Resource.shift_permute_1.
  f_equal.
  now rewrite Term.shift_permute_1.
Qed.

Lemma shift_permute_2 (lb k m n : lvl) (t : t) :
  lb <= k -> eq (shift lb m (shift k n t)) (shift (k + m) n (shift lb m t)).
Proof.
  intro Hle.
  unfold eq.
  destruct t as [[rg rs] v]; simpl.
  rewrite Resource.shift_permute_2; auto.
  f_equal.
  - f_equal; rewrite Resource.shift_permute_2; auto.
  - now rewrite Term.shift_permute_2.
Qed.

Lemma shift_unfold (lb k m : lvl) (t : t) :
  eq (shift lb (k + m) t) (shift (lb + k) m (shift lb k t)). 
Proof.
  unfold eq.
  destruct t as [[rg rs] v]; simpl.
  do 2 (rewrite Resource.shift_unfold).
  f_equal.
  now rewrite Term.shift_unfold.
Qed.

Lemma shift_unfold_1 (k m n : lvl) (t : t) :
  k <= m -> m <= n -> 
  eq (shift m (n - m) (shift k  (m - k) t)) (shift k (n - k) t).
Proof.
  intros.
  unfold eq.
  destruct t as [[rg rs] v]; simpl.
  do 2 (rewrite Resource.shift_unfold_1; auto).
  f_equal.
  now rewrite Term.shift_unfold_1.
Qed.

(** **** [Wf] properties *)

#[export] Instance Wf_iff : Proper (Logic.eq ==> eq ==> iff) Wf := _.

Lemma Wf_weakening (k m : lvl) (t : t) : (k <= m) -> Wf k t -> Wf m t.
Proof.
  unfold Wf.
  destruct t as [[rg rs] v].
  intros Hle [Hwfrg [Hwfrs Hwfv]].
  repeat split; try (eapply Resource.Wf_weakening; eauto).
  eapply Term.Wf_weakening; eauto.
Qed.

Theorem shift_preserves_wf_1 (lb k m : lvl) (t : t) :
  Wf k t -> Wf (k + m) (shift lb m t).
Proof.
  unfold Wf.
  destruct t as [[rg rs] v].
  intros [Hwfrg [Hwfrs Hwfv]].
  simpl.
  repeat split; try (now apply Resource.shift_preserves_wf_1).
  now apply Term.shift_preserves_wf_1.
Qed.

Theorem shift_preserves_wf (k m : lvl) (t : t) :
  Wf k t -> Wf (k + m) (shift k m t).
Proof. intros; now apply shift_preserves_wf_1. Qed. 

Theorem shift_preserves_wf_zero (k : lvl) (t : t) :
  Wf k t -> Wf k (shift k 0 t).
Proof. 
  unfold Wf.
  destruct t as [[rg rs] v].
  intros [Hwfrg [Hwfrs Hwfv]].
  simpl.
  repeat split; try (now apply Resource.shift_preserves_wf_zero).
  now apply Term.shift_preserves_wf_zero.
Qed. 

Lemma shift_preserves_wf_gen (lb k m n : lvl) (t : t) :
    m <= n -> lb <= k -> m <= lb -> n <= k -> n - m = k - lb -> 
    Wf lb t -> Wf k (shift m (n - m) t).
Proof.
  unfold Wf.
  destruct t as [[rg rs] v].
  intros.
  destruct H4 as [Hwfrg [Hwfrs Hwfv]].
  simpl.
  repeat split.
  - apply Resource.shift_preserves_wf_gen with (m := lb); auto.
  - apply Resource.shift_preserves_wf_gen with (m := lb); auto.
  - apply Term.shift_preserves_wf_gen with (lb := lb); auto.
Qed.

Lemma shift_preserves_wf_2 (m n : lvl) (t : t) :
  m <= n -> Wf m t -> Wf n (shift m (n - m) t).
Proof. 
  intros Hle Hvt. 
  eapply shift_preserves_wf_gen; eauto. 
Qed.

End Triplet.