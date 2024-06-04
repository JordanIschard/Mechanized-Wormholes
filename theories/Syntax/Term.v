From Coq Require Import Classical_Prop Classes.RelationClasses Classes.Morphisms Bool.Bool Lia.
From DeBrLevel Require Import LevelInterface OptionLevel.
From Mecha Require Import Var Resource Typ.
Import ResourceNotations TypNotations.

(** * Syntax - Term

  The syntax of Wormholes consists in a typed lambda-calculus
  with pairs, recursion, arrow primitives and two additional 
  terms: rsf and wh. It is the first [Type] where levels can be
  bound.
*)
Module Term <: IsLvlFullDTWL.

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
  | tm_rsf    : resource -> raw
  | tm_wh     : raw -> raw -> raw
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
    | (tm_wh e1 e2,tm_wh e1' e2') => (eqb e1 e1') && (eqb e2 e2')
    | (tm_rsf r,tm_rsf r') => (r =? r')%r
    | (tm_unit, tm_unit) => true
    | (tm_fix, tm_fix) => true
    | _ => false
  end
.

(** **** Shift function 

  In terms, types and resource signal function are implied by the [shift] function.
  Then we recursively apply the appropriate shift on all types and resource contained
  in the term.
*)
Fixpoint shift (lb : nat) (k : nat) (e : t) : t := 
  match e with
  | tm_app t1 t2 => tm_app (shift lb k t1) (shift lb k t2)
  | tm_abs x τ t0 => tm_abs x <[[⧐ₜ lb ≤ k] τ]> (shift lb k t0)

  | tm_pair t1 t2 => tm_pair (shift lb k t1) (shift lb k t2)
  | tm_fst t0 => tm_fst (shift lb k t0)
  | tm_snd t0 => tm_snd (shift lb k t0)

  | tm_arr t0 => tm_arr (shift lb k t0)
  | tm_first τ t0 => tm_first <[[⧐ₜ lb ≤ k] τ]> (shift lb k t0)
  | tm_comp t1 t2 => tm_comp (shift lb k t1) (shift lb k t2)

  | tm_rsf r => tm_rsf ([⧐ᵣ lb ≤ k] r)
  | tm_wh t1 t2 => tm_wh (shift lb k t1) (shift lb k t2)

  | _ => e
  end
.

Definition multi_shift (lbs : list nat) (ks : list nat) (t : t) :=
  List.fold_right (fun (x : nat * nat) acc => let (lb,k) := x in shift lb k acc) t (List.combine lbs ks).


(** **** Valid function 

  A term is valid if all their types and resources contained in it are valid.
  However the lower bound is incremented by 2 when we go through a [wormhole] structure because
  2 virtuals resources exist in it. This is why we can define terms fully constained. Indeed, the lemma
  [shift_valid_refl] can be hold in this case.

<<
We can state that:

valid 0 wormhole(unit;rsf[0]) <-> valid 0 unit /\ valid 2 rsf[0]

but

            (shift 0 3 wormhole(unit;rsf[0])) != wormhole(unit;rsf[0])
wormhole((shift 0 3 unit);(shift 0 3 rsf[0])) != wormhole(unit;rsf[0])
                        wormhole(unit;rsf[3]) != wormhole(unit;rsf[0])
>>
*)
Inductive valid' : nat -> t -> Prop :=
  | vΛ_unit : forall k, valid' k tm_unit
  | vΛ_var : forall k x, valid' k (tm_var x)
  | vΛ_fix : forall k, valid' k tm_fix
  | vΛ_app : forall k t1 t2, valid' k t1 -> valid' k t2 -> valid' k (tm_app t1 t2)
  | vΛ_abs : forall k x τ t, k ⊩ₜ τ -> valid' k t -> valid' k (tm_abs x τ t)
  
  | vΛ_pair : forall k t1 t2, valid' k t1 -> valid' k t2 -> valid' k (tm_pair t1 t2)
  | vΛ_fst  : forall k t, valid' k t -> valid' k (tm_fst t) 
  | vΛ_snd  : forall k t, valid' k t -> valid' k (tm_snd t)
  
  | vΛ_arr   : forall k t, valid' k t -> valid' k (tm_arr t)
  | vΛ_first : forall k τ t, k ⊩ₜ τ -> valid' k t -> valid' k (tm_first τ t)
  | vΛ_comp  : forall k t1 t2, valid' k t1 -> valid' k t2 -> valid' k (tm_comp t1 t2)
  | vΛ_rsf : forall k r, k ⊩ᵣ r ->  valid' k (tm_rsf r)
  | vΛ_wh  : forall k t1 t2, valid' k t1 -> valid' (S (S k)) t2 -> valid' k (tm_wh t1 t2)
.

Fixpoint validb' (k : nat) (t : t) :=
  match t with
    | tm_unit => true
    | tm_fix => true
    | tm_var x => true
    | tm_app t1 t2 => (validb' k t1) && (validb' k t2) 
    | tm_abs x τ t1 => k ⊩?ₜ τ && (validb' k t1)
    | tm_pair t1 t2 => (validb' k t1) && (validb' k t2) 
    | tm_fst t1 => validb' k t1
    | tm_snd t1 => validb' k t1
    | tm_arr t1 => validb' k t1
    | tm_first τ t1 => k ⊩?ₜ τ && (validb' k t1)
    | tm_comp t1 t2 => (validb' k t1) && (validb' k t2) 
    | tm_rsf r => k ⊩?ᵣ r 
    | tm_wh t1 t2 => (validb' k t1) && (validb' (S (S k)) t2) 
  end
.

Definition valid := valid'.
Definition validb := validb'.

#[global] 
Hint Constructors valid' : core.

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

  | afi_wh1 : forall x t1 t2, appears_free_in x t1 -> appears_free_in x (tm_wh t1 t2)
  | afi_wh2 : forall x t1 t2, appears_free_in x t2 -> appears_free_in x (tm_wh t1 t2)
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

  | v_rsf   : forall r, value (tm_rsf r)

  | v_wh    : forall i t, value i -> value t -> value (tm_wh i t)
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
  - apply Resource.eqb_refl.
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
  - rewrite Resource.eqb_eq in *; subst; reflexivity.
  - inversion H; subst; apply Resource.eqb_refl.
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
  - destruct (Resource.eq_dec r r0); subst; try now left. right; intro c; inversion c; subst;
    contradiction.
Qed.

Lemma eq_leibniz : forall x y, eq x y -> x = y. Proof. auto. Qed.

(** *** Shift *)

Lemma shift_refl : forall (lb : nat) (t : t), shift lb 0 t = t.
Proof.
  intros lb t; induction t; simpl; f_equal; auto.
  - apply Typ.shift_refl.
  - apply Typ.shift_refl.
  - apply Resource.shift_refl.
Qed.

#[global]
Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
Proof. repeat red; intros; apply eq_leibniz; subst; now rewrite H1. Qed.

Lemma shift_eq_iff : forall lb k t t1,
  t = t1 <-> (shift lb k t) = (shift lb k t1).
Proof.
  split.
  - intros; now subst.
  - revert lb k t1; induction t0; intros lb k t' Heq; destruct t'; 
    simpl in *; try (now inversion Heq); try (inversion Heq;f_equal; eauto).
    -- eapply Typ.shift_eq_iff; eauto.
    -- eapply Typ.shift_eq_iff; eauto.
    -- eapply Resource.shift_eq_iff; eauto.
Qed.

Lemma shift_trans : forall lb k k' t,
  shift lb k (shift lb k' t) = shift lb (k + k') t.
Proof.
  intros lb k k' t; induction t; simpl; f_equal; auto.
  - apply Typ.shift_trans.
  - apply Typ.shift_trans.
  - apply Resource.shift_trans.
Qed.

Lemma shift_permute : forall lb k k' t,
  shift lb k (shift lb k' t) = shift lb k' (shift lb k t).
Proof.
  intros lb k k' t; induction t; simpl; f_equal; auto.
  - apply Typ.shift_permute.
  - apply Typ.shift_permute.
  - apply Resource.shift_permute.
Qed.

Lemma shift_not_fix_iff : forall t lb k,
  t <> tm_fix <-> (shift lb k t) <> tm_fix.
Proof.
  intro t; induction t; intros; split; simpl; intros; intro; inversion H0;
  try contradiction.
Qed.

Lemma shift_afi_iff : forall  t s lb k,
  appears_free_in s t <-> appears_free_in s (shift lb k t).
Proof. 
  intros t; induction t; intros x lb k; split; intros HFV; simpl in *; auto;
  try (inversion HFV; subst; constructor; auto; rewrite IHt in *; eauto);
  inversion HFV; subst; try (constructor; apply IHt1; now eauto);
  try (constructor; rewrite IHt1; now eauto).
  - apply afi_app2; rewrite <- IHt2; eauto.
  - apply afi_app2; rewrite IHt2; eauto.
  - apply afi_pair2; now rewrite <- IHt2.
  - apply afi_pair2; rewrite IHt2; eauto.
  - apply afi_comp2; now rewrite <- IHt2.
  - apply afi_comp2; rewrite IHt2; eauto.
  - apply afi_wh2; now rewrite <- IHt2.
  - apply afi_wh2; rewrite IHt2; eauto.
Qed.

Lemma shift_closed_iff : forall t lb k, closed t <-> closed (shift lb k t).
Proof. 
  unfold closed, not; intros; split; intros; apply (H x).
  - rewrite shift_afi_iff ; eauto.
  - rewrite shift_afi_iff in H0; eauto.
Qed.

Lemma shift_value_iff : forall t lb k, value t <-> value (shift lb k t).
Proof.
  intros t; induction t; split; intros; auto; simpl;
  try (now inversion H); try (inversion H; subst; constructor);
  try (erewrite IHt1; now eauto); try (erewrite <- IHt1; now eauto);
  try (erewrite IHt2; now eauto); try (erewrite <- IHt2; now eauto);
  try (now apply IHt); try (erewrite IHt; eauto).
Qed.

Lemma shift_permute_1 : forall t lb k k',
  eq (shift lb k (shift lb k' t)) (shift (lb + k) k' (shift lb k t)).
Proof.
  unfold eq; intro t; induction t; simpl; intros lb k k'; f_equal; auto.
  - apply Typ.shift_permute_1.
  - apply Typ.shift_permute_1.
  - apply Resource.shift_permute_1.
Qed.

Lemma shift_permute_2 : forall lb lb' k k' t,
  lb <= lb' -> eq (shift lb k (shift lb' k' t)) (shift (lb' + k) k' (shift lb k t)).
Proof.
  unfold eq; intros lb lb' k k' t; induction t; simpl; intros; f_equal; auto.
  - now apply Typ.shift_permute_2.
  - now apply Typ.shift_permute_2.
  - now apply Resource.shift_permute_2.
Qed.

Lemma shift_unfold : forall lb k k' t,
  eq (shift lb (k + k') t) (shift (lb + k) k' (shift lb k t)). 
Proof.
    intros lb k k' t; induction t; simpl; auto;
    try (rewrite IHt1; rewrite IHt2; now reflexivity);
    try (rewrite IHt; now reflexivity).
    - rewrite Typ.shift_unfold; now rewrite IHt.
    - rewrite Typ.shift_unfold; now rewrite IHt.
    - now rewrite Resource.shift_unfold.
Qed.

Lemma shift_unfold_1 : forall k k' k'' t,
    k <= k' -> k' <= k'' -> 
    eq (shift k' (k'' - k') (shift k  (k' - k) t)) (shift k (k'' - k) t).
Proof.
    intros k k' k'' t Hlt Hlt'; induction t; simpl; auto;
    try (rewrite IHt1; rewrite IHt2; now reflexivity);
    try (rewrite IHt; now reflexivity).
    - rewrite Typ.shift_unfold_1; auto; now rewrite IHt.
    - rewrite Typ.shift_unfold_1; auto; now rewrite IHt.
    - now rewrite Resource.shift_unfold_1.
Qed.

(** *** Valid *)

Lemma validb_valid : forall k t, validb k t = true <-> valid k t.
Proof.
  split.
  - revert k; induction t0; simpl; intros k H; constructor;
    try (repeat rewrite andb_true_iff in *; destruct H;
          fold valid; now auto); 
    try (repeat rewrite andb_true_iff in *; destruct H; now rewrite <- Typ.validb_valid);
    now rewrite <- Resource.validb_valid.
  - revert k; induction t0; simpl; intros k H; auto; inversion H; subst;
    fold valid in *; auto; try (rewrite andb_true_iff; split; auto);
    try (now rewrite Typ.validb_valid); now rewrite Resource.validb_valid.
Qed.

Lemma validb_nvalid : forall k t, validb k t = false <-> ~ valid k t.
Proof.
  intros; rewrite <- not_true_iff_false; split; intros; intro.
  - apply H; now rewrite validb_valid. 
  - apply H; now rewrite <- validb_valid.
Qed.

#[global]
Instance valid_eq : Proper (Logic.eq ==> eq ==> iff) valid.
Proof. repeat red; intros; apply eq_leibniz in H0; now subst. Qed.

#[global]
Instance validb_eq : Proper (Logic.eq ==> eq ==> Logic.eq) validb.
Proof. repeat red; intros; apply eq_leibniz in H0; now subst. Qed.

Lemma valid_weakening : forall k k' t, (k <= k') -> valid k t -> valid k' t.
Proof.
    unfold valid; intros k k' t; generalize k k'; clear k k'; induction t; 
    intros k k'; simpl; auto; intros Hlt Hv; try (inversion Hv; subst; now eauto).
    - inversion Hv; subst; apply vΛ_abs; eauto; eapply Typ.valid_weakening; eauto.
    - inversion Hv; subst; apply vΛ_first; eauto; eapply Typ.valid_weakening; eauto.
    - inversion Hv; subst; constructor; eapply Resource.valid_weakening; eauto.
    - inversion Hv; subst; apply vΛ_wh.
    -- eapply IHt1; eauto.
    -- apply IHt2 with (k := S (S k)); eauto; lia.
Qed.

Theorem shift_preserves_valid_1 : forall lb k k' t,
    valid k t -> valid (k + k') (shift lb k' t).
Proof.
    unfold valid; intros lb k k' t; revert lb k k'; induction t; intros lb k k' Hvt; 
    inversion Hvt; subst; simpl; auto.
    - constructor; auto; now apply Typ.shift_preserves_valid_1.
    - constructor; auto; now apply Typ.shift_preserves_valid_1.
    - constructor; now apply Resource.shift_preserves_valid_1.
    - apply vΛ_wh; auto. replace (S (S (k + k'))) with ((S (S k)) + k'); auto; lia.
Qed.

Theorem shift_preserves_valid : forall k k' t,
    valid k t -> valid (k + k') (shift k k' t).
Proof. intros; now apply shift_preserves_valid_1. Qed. 

Theorem shift_preserves_valid_4 : forall k t,
    valid k t -> valid k (shift k 0 t).
Proof. 
    intros. apply shift_preserves_valid with (k' := 0) in H. 
    replace (k + 0) with k in H; auto.
Qed. 

Lemma shift_preserves_valid_2 : forall lb lb' k k' t,
    k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' -> k' - k = lb' - lb -> 
    valid lb t -> valid lb' (shift k (k' - k) t).
Proof.
    intros lb lb' k k' t; revert k k' lb lb'; induction t; intros; simpl; inversion H4; subst; 
    constructor; eauto; try (apply IHt1 with lb; now auto);
    try (apply IHt2 with lb; now auto); try (apply IHt with lb; now auto).
    - apply Typ.shift_preserves_valid_2 with lb; auto.
    - apply Typ.shift_preserves_valid_2 with lb; auto.
    - apply Resource.shift_preserves_valid_2 with lb; auto.
    - apply IHt2 with (lb := S (S lb)); auto; lia.
Qed.

Lemma shift_preserves_valid_3 : forall lb lb' t,
    lb <= lb' -> valid lb t -> 
    valid lb' (shift lb (lb' - lb) t).
Proof. intros. eapply shift_preserves_valid_2; eauto. Qed.

(** *** Multi Shift *)

Lemma multi_shift_unit lbs ks :
  multi_shift lbs ks tm_unit = tm_unit.
Proof. 
  unfold multi_shift. revert ks.
  induction lbs.
  - simpl; intros; reflexivity.
  - simpl; intros; destruct ks.
    -- simpl; reflexivity.
    -- simpl. rewrite IHlbs. now simpl.
Qed.

Lemma multi_shift_fix lbs ks :
  multi_shift lbs ks tm_fix = tm_fix.
Proof. 
  unfold multi_shift. revert ks.
  induction lbs.
  - simpl; intros; reflexivity.
  - simpl; intros; destruct ks.
    -- simpl; reflexivity.
    -- simpl. rewrite IHlbs. now simpl.
Qed.

Lemma multi_shift_var lbs ks : forall x,
  multi_shift lbs ks (tm_var x) = tm_var x.
Proof. 
  unfold multi_shift. revert ks.
  induction lbs.
  - simpl; intros; reflexivity.
  - simpl; intros; destruct ks.
    -- simpl; reflexivity.
    -- simpl. rewrite IHlbs. now simpl.
Qed.

Lemma multi_shift_rsf lbs ks : forall r,
  multi_shift lbs ks (tm_rsf r) = tm_rsf ([⧐⧐ᵣ lbs ≤ ks] r).
Proof. 
  unfold multi_shift. revert ks.
  induction lbs.
  - simpl; intros; reflexivity.
  - simpl; intros; destruct ks.
    -- simpl; reflexivity.
    -- simpl. rewrite IHlbs. now simpl.
Qed.

Lemma multi_shift_app lbs ks : forall t1 t2,
  multi_shift lbs ks (tm_app t1 t2) = tm_app (multi_shift lbs ks t1) (multi_shift lbs ks t2).
Proof. 
  unfold multi_shift. revert ks.
  induction lbs.
  - simpl; intros; reflexivity.
  - simpl; intros; destruct ks.
    -- simpl; reflexivity.
    -- simpl. rewrite IHlbs. now simpl.
Qed.

Lemma multi_shift_pair lbs ks : forall t1 t2,
  multi_shift lbs ks (tm_pair t1 t2) = tm_pair (multi_shift lbs ks t1) (multi_shift lbs ks t2).
Proof. 
  unfold multi_shift. revert ks.
  induction lbs.
  - simpl; intros; reflexivity.
  - simpl; intros; destruct ks.
    -- simpl; reflexivity.
    -- simpl. rewrite IHlbs. now simpl.
Qed.

Lemma multi_shift_comp lbs ks : forall t1 t2,
  multi_shift lbs ks (tm_comp t1 t2) = tm_comp (multi_shift lbs ks t1) (multi_shift lbs ks t2).
Proof. 
  unfold multi_shift. revert ks.
  induction lbs.
  - simpl; intros; reflexivity.
  - simpl; intros; destruct ks.
    -- simpl; reflexivity.
    -- simpl. rewrite IHlbs. now simpl.
Qed.

Lemma multi_shift_wh lbs ks : forall t1 t2,
  multi_shift lbs ks (tm_wh t1 t2) = tm_wh (multi_shift lbs ks t1) (multi_shift lbs ks t2).
Proof. 
  unfold multi_shift. revert ks.
  induction lbs.
  - simpl; intros; reflexivity.
  - simpl; intros; destruct ks.
    -- simpl; reflexivity.
    -- simpl. rewrite IHlbs. now simpl.
Qed.

Lemma multi_shift_fst lbs ks : forall t1,
  multi_shift lbs ks (tm_fst t1) = tm_fst (multi_shift lbs ks t1).
Proof. 
  unfold multi_shift. revert ks.
  induction lbs.
  - simpl; intros; reflexivity.
  - simpl; intros; destruct ks.
    -- simpl; reflexivity.
    -- simpl. rewrite IHlbs. now simpl.
Qed.

Lemma multi_shift_snd lbs ks : forall t1,
  multi_shift lbs ks (tm_snd t1) = tm_snd (multi_shift lbs ks t1).
Proof. 
  unfold multi_shift. revert ks.
  induction lbs.
  - simpl; intros; reflexivity.
  - simpl; intros; destruct ks.
    -- simpl; reflexivity.
    -- simpl. rewrite IHlbs. now simpl.
Qed.

Lemma multi_shift_arr lbs ks : forall t1,
  multi_shift lbs ks (tm_arr t1) = tm_arr (multi_shift lbs ks t1).
Proof. 
  unfold multi_shift. revert ks.
  induction lbs.
  - simpl; intros; reflexivity.
  - simpl; intros; destruct ks.
    -- simpl; reflexivity.
    -- simpl. rewrite IHlbs. now simpl.
Qed.

Lemma multi_shift_abs lbs ks : forall x τ t1,
  multi_shift lbs ks (tm_abs x τ t1) = tm_abs x <[[⧐⧐ₜ lbs ≤ ks]  τ]> (multi_shift lbs ks t1).
Proof. 
  unfold multi_shift. revert ks.
  induction lbs.
  - simpl; intros; reflexivity.
  - simpl; intros; destruct ks.
    -- simpl; reflexivity.
    -- simpl. rewrite IHlbs. now simpl.
Qed.

Lemma multi_shift_first lbs ks : forall τ t1,
  multi_shift lbs ks (tm_first τ t1) = tm_first <[[⧐⧐ₜ lbs ≤ ks]  τ]> (multi_shift lbs ks t1).
Proof. 
  unfold multi_shift. revert ks.
  induction lbs.
  - simpl; intros; reflexivity.
  - simpl; intros; destruct ks.
    -- simpl; reflexivity.
    -- simpl. rewrite IHlbs. now simpl.
Qed.

Lemma multi_shift_nil_l ks : forall t,
  multi_shift nil ks t = t.
Proof. intro. unfold multi_shift; now simpl. Qed.

Lemma multi_shift_nil_r lbs : forall t,
  multi_shift lbs nil t = t.
Proof. 
  intro. unfold multi_shift; destruct lbs; reflexivity. 
Qed.

Lemma multi_shift_nil : forall t,
  multi_shift nil nil t = t.
Proof. 
  intro. unfold multi_shift; reflexivity. 
Qed.

Lemma multi_shift_cons lb k lbs ks t:
  multi_shift (lb :: lbs) (k :: ks) t = shift lb k (multi_shift lbs ks t).
Proof.
  unfold multi_shift; simpl; reflexivity.
Qed.

Lemma multi_shift_value_iff lbs ks t: 
  value t <-> value (multi_shift lbs ks t).
Proof.
  split.
  - revert ks t; induction lbs; intros;
    unfold multi_shift in *; simpl in *; auto.
    destruct ks; simpl in *; auto.
    apply shift_value_iff. now apply IHlbs.
  - revert ks t; induction lbs; intros;
    unfold multi_shift in *; simpl in *; auto.
    destruct ks; simpl in *; auto.
    apply shift_value_iff in H. 
    eapply IHlbs; eauto.
Qed.


End Term.

Module OptTerm <: IsLvlETWL := IsLvlOptETWL Term.

(** * Notation - Term *)
Module TermNotations.

(** ** Scope *)
Declare Scope term_scope.
Declare Scope opt_term_scope.
Delimit Scope term_scope with tm.
Delimit Scope opt_term_scope with otm.

(** ** Notations *)
Definition Λ := Term.t.
Definition Λₒ := OptTerm.t.

Coercion Term.tm_var : variable >-> Term.raw.
Notation "value( t )" := (Term.value t) (at level 20, no associativity).
Notation "clₜₘ( t )" := (Term.closed t) (at level 20, no associativity).
Notation "'isFV(' r ',' t ')'" := (Term.appears_free_in r t) (at level 40, t custom wh).

Notation "x y"     := (Term.tm_app x y) (in custom wh at level 70, left associativity).
Notation "\ x : t , y" := (Term.tm_abs x t y) (in custom wh at level 90, 
                                                    x at level 99, t custom wh at level 99, 
                                                    y custom wh at level 99, 
                                                    left associativity).
Notation "'unit'" := (Term.tm_unit) (in custom wh at level 0).
Notation "'Fix'" := (Term.tm_fix) (in custom wh at level 0).
Notation "⟨ x ',' y ⟩" := (Term.tm_pair x y) (in custom wh at level 0, 
                                                      x custom wh at level 99, 
                                                      y custom wh at level 99).
Notation "t '.fst'"  := (Term.tm_fst t) (in custom wh at level 0).
Notation "t '.snd'"  := (Term.tm_snd t) (in custom wh at level 0).
Notation "'arr(' f ')'"    := (Term.tm_arr f) (in custom wh at level 0, 
                                                      f custom wh at level 99,
                                                      no associativity).
Notation "'first(' τ ':' sf ')'" := (Term.tm_first τ sf) (in custom wh at level 0).
Notation " sf1 '>>>' sf2 " := (Term.tm_comp sf1 sf2) (in custom wh at level 60, 
                                                                          left associativity).
Notation "'rsf[' r ']'"    := (Term.tm_rsf r) (in custom wh at level 0,  
                                                      r constr, no associativity).
Notation "'wormhole(' i ';' sf ')'" :=  (Term.tm_wh i sf ) (in custom wh at level 23,
                                                                  i custom wh, 
                                                                  sf custom wh, 
                                                                  no associativity).

Notation "'[⧐ₜₘ' lb '≤' k ']' t" := (Term.shift lb k t) 
  (in custom wh at level 65, right associativity).
Notation "'[⧐⧐ₜₘ' lb '≤' k ']' t" := (Term.multi_shift lb k t) 
  (in custom wh at level 65, right associativity).
Notation "'[⧐ₒₜₘ' lb '≤' k ']' t" := (OptTerm.shift lb k t) 
  (in custom wh at level 65, right associativity).

Infix "⊩ₜₘ" := Term.valid (at level 20, no associativity).   
Infix "⊩ₒₜₘ" := OptTerm.valid (at level 20, no associativity).   
Infix "⊩?ₜₘ" := Term.validb (at level 20, no associativity). 

Infix "=" := Term.eq : term_scope.
Infix "=?" := Term.eqb  (at level 70) : term_scope.
Infix "=" := OptTerm.eq : opt_term_scope.

End TermNotations.