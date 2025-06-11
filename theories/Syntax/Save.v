From Coq Require Import Lia RelationClasses Classes.Morphisms.
From Mecha Require Import Resource Term Typ RContext.
From DeBrLevel Require Import LevelInterface.
Import ResourceNotations TermNotations TypNotations RContextNotations.

Module Save <: IsLvlET.

Definition t : Type := ℜ * Λ * Τ * Τ.

Definition eq (t t' : t) :=
  let '(Rc,v,ty,ty1) := t in
  let '(Rc',v',ty',ty1') := t' in 
  (Rc = Rc')%rc /\ v = v' /\ ty = ty' /\ ty1 = ty1'.

#[export] Instance eq_refl : Reflexive eq.
Proof.
  intros [[[Rc v] ty] ty1]; 
  repeat split.
Qed.

#[export] Instance eq_sym : Symmetric eq.
Proof.
  intros [[[Rc v] ty] ty1] [[[Rc' v'] ty'] ty1'] [HeqRc [Heqv []]]; subst.
  repeat split.
  now symmetry.
Qed.

#[export] Instance eq_trans : Transitive eq.
Proof.
  intros [[[Rc v] ty] ty1] 
         [[[Rc' v'] ty'] ty1'] 
         [[[Rc'' v''] ty''] ty1'']
         [HeqRc [Heqv []]] 
         [HeqRc' [Heqv' []]]; subst.
  repeat split.
  now rewrite HeqRc.
Qed. 

#[export] Instance eq_equiv : Equivalence eq.
Proof.
  split.
  - apply eq_refl.
  - apply eq_sym.
  - apply eq_trans.
Qed.


Definition shift (m n : resource) (tp : t) :=
  let '(Rc,v,ty,ty') := tp in 
  (([⧐ m – n] Rc)%rc,(Term.shift m n v)%tm,(Typ.shift m n ty)%ty,(Typ.shift m n ty')%ty).

Definition Wf (m : resource) (tp : t) :=
  let '(Rc,v,ty,ty') := tp in 
  RContext.Wf m Rc /\ Term.Wf m v /\ Typ.Wf m ty /\ Typ.Wf m ty'.


#[export] Hint Resolve eq_refl eq_sym eq_trans : core.

Lemma eq_dec (t1 t2: t) : {eq t1 t2} + {~ eq t1 t2}.
Proof. 
  (* needs to define RContext as an OrderedMaps in order to get eq_dec lemma *)
Admitted.

(** **** [shift] properties *)

Lemma shift_zero_refl (lb : lvl) (t : t) : eq (shift lb 0 t) t.
Proof.
  destruct t as [[[Rc v] ty] ty1]; simpl.
  rewrite RContext.shift_zero_refl.
  rewrite Term.shift_zero_refl.
  do 2 rewrite Typ.shift_zero_refl.
  repeat split.
Qed.

#[export] Instance shift_eq : 
  Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
Proof. Admitted.

Lemma shift_eq_iff (lb k : lvl) (t t1 : t) :
  eq t t1 <-> eq (shift lb k t) (shift lb k t1).
Proof.
Admitted.

Lemma shift_trans (lb k m : lvl) (t : t) :
  eq (shift lb k (shift lb m t)) (shift lb (k + m) t).
Proof.
Admitted.

Lemma shift_permute (lb k m : lvl) (t : t) :
  eq (shift lb k (shift lb m t)) (shift lb m (shift lb k t)).
Proof.
Admitted.

Lemma shift_permute_1 (lb k m : lvl) (t : t) :
  eq (shift lb k (shift lb m t)) (shift (lb + k) m (shift lb k t)).
Proof.
Admitted.

Lemma shift_permute_2 (lb k m n : lvl) (t : t) :
  lb <= k -> eq (shift lb m (shift k n t)) (shift (k + m) n (shift lb m t)).
Proof.
Admitted.

Lemma shift_unfold (lb k m : lvl) (t : t) :
  eq (shift lb (k + m) t) (shift (lb + k) m (shift lb k t)). 
Proof.
Admitted.

Lemma shift_unfold_1 (k m n : lvl) (t : t) :
  k <= m -> m <= n -> 
  eq (shift m (n - m) (shift k  (m - k) t)) (shift k (n - k) t).
Proof.
Admitted.

(** **** [Wf] properties *)

#[export] Instance Wf_iff : Proper (Logic.eq ==> eq ==> iff) Wf.
Admitted.

Lemma Wf_weakening (k m : lvl) (t : t) : (k <= m) -> Wf k t -> Wf m t.
Proof.
Admitted.

Theorem shift_preserves_wf_1 (lb k m : lvl) (t : t) :
  Wf k t -> Wf (k + m) (shift lb m t).
Proof.
Admitted.


Theorem shift_preserves_wf (k m : lvl) (t : t) :
  Wf k t -> Wf (k + m) (shift k m t).
Proof. intros; now apply shift_preserves_wf_1. Qed. 

Theorem shift_preserves_wf_zero (k : lvl) (t : t) :
  Wf k t -> Wf k (shift k 0 t).
Proof.
Admitted.

Lemma shift_preserves_wf_gen (lb k m n : lvl) (t : t) :
    m <= n -> lb <= k -> m <= lb -> n <= k -> n - m = k - lb -> 
    Wf lb t -> Wf k (shift m (n - m) t).
Proof.
Admitted.

Lemma shift_preserves_wf_2 (m n : lvl) (t : t) :
  m <= n -> Wf m t -> Wf n (shift m (n - m) t).
Proof. 
  intros Hle Hvt. 
  eapply shift_preserves_wf_gen; eauto. 
Qed.

End Save.