From Coq Require Import Classical_Prop Classes.RelationClasses Classes.Morphisms Bool.Bool Lia.
From DeBrLevel Require Import LevelInterface OptionLevel.
From Mecha Require Import Var Resource Typ.
Import VarNotations ResourceNotations TypNotations.


(** * Syntax - Term

  Wormholes's syntax is an extended version of the standard lambda calculus with pair, projections, fixpoint, ground value, denoted [()], and arrow primitives (arr,first and comp). In addition, the language introduces [rsf] and [wormhole]. The former access to the environment and allows interaction with it. The latter creates local resources.
*)

(** ** Module - Term *)
Module Term <: IsLvlDTWL.

(** *** Definition *)

Open Scope resource_scope.
Open Scope typ_scope.

(** **** Type 

  The syntax is an usual lambda-calculus, with arrow primitives (arr, first and comp) as well as two additional arrow primitives named [rsf] and [wormhole] that respectively represent an interaction with the environment and a [let...in] structure for resource names and reactive expression.
*)
Inductive raw : Type :=
  | tm_unit   : raw
  | tm_fix    : raw
  | tm_var (x : variable) : raw
  | tm_abs (x : variable) (t : raw) : raw
  | tm_app  (t1 t2 : raw) : raw
  | tm_pair (t1 t2 : raw) : raw
  | tm_fst   (t : raw) : raw
  | tm_snd   (t : raw) : raw
  | tm_arr   (t : raw) : raw
  | tm_first (t : raw) : raw
  | tm_rsf (r : resource) : raw
  | tm_comp (t1 t2 : raw) : raw
  | tm_wh   (t1 t2 : raw) : raw
.

Definition t := raw.
Definition eq := @eq t.

(** **** Shift function 

  The [shift] function takes a lower bound [lb] a natural [k] and a term [t], and produces a term [t'] where all resources [r] greater or equal to [lb] in [t] are incremented by [k]. The others are left unchanged.
*)
Fixpoint shift (lb : nat) (k : nat) (e : t) : t := 
  match e with
  | tm_rsf r => tm_rsf ([⧐ lb – k] r)

  | tm_abs x t0 => tm_abs x (shift lb k t0)
  | tm_fst t0   => tm_fst   (shift lb k t0)
  | tm_snd t0   => tm_snd   (shift lb k t0)
  | tm_arr t0   => tm_arr   (shift lb k t0)
  | tm_first t0 => tm_first (shift lb k t0)

  | tm_app  t1 t2 => tm_app  (shift lb k t1) (shift lb k t2)
  | tm_pair t1 t2 => tm_pair (shift lb k t1) (shift lb k t2)
  | tm_comp t1 t2 => tm_comp (shift lb k t1) (shift lb k t2)
  | tm_wh   t1 t2 => tm_wh   (shift lb k t1) (shift lb k t2)

  | _ => e
  end
.

(*========================= STOP ===============================*)

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

            (shift 0 3 wormhole(unit;rsf[0])) ≠ wormhole(unit;rsf[0])
wormhole((shift 0 3 unit);(shift 0 3 rsf[0])) ≠ wormhole(unit;rsf[0])
                        wormhole(unit;rsf[3]) ≠ wormhole(unit;rsf[0])
>>
*)
Inductive valid' : nat -> t -> Prop :=
  | vΛ_unit : forall k, valid' k tm_unit
  | vΛ_var : forall k x, valid' k (tm_var x)
  | vΛ_fix : forall k, valid' k tm_fix
  | vΛ_app : forall k t1 t2, valid' k t1 -> valid' k t2 -> valid' k (tm_app t1 t2)
  | vΛ_abs : forall k x t, valid' k t -> valid' k (tm_abs x t)
  
  | vΛ_pair : forall k t1 t2, valid' k t1 -> valid' k t2 -> valid' k (tm_pair t1 t2)
  | vΛ_fst  : forall k t, valid' k t -> valid' k (tm_fst t) 
  | vΛ_snd  : forall k t, valid' k t -> valid' k (tm_snd t)
  
  | vΛ_arr   : forall k t, valid' k t -> valid' k (tm_arr t)
  | vΛ_first : forall k t, valid' k t -> valid' k (tm_first t)
  | vΛ_comp  : forall k t1 t2, valid' k t1 -> valid' k t2 -> valid' k (tm_comp t1 t2)
  | vΛ_rsf : forall k r, (k ⊩ r)%r ->  valid' k (tm_rsf r)
  | vΛ_wh  : forall k t1 t2, valid' k t1 -> valid' (S (S k)) t2 -> valid' k (tm_wh t1 t2)
.

Definition valid := valid'.

#[export] Hint Constructors valid' : core.

(** **** Others *)

Inductive appears_free_in : variable -> t -> Prop :=
  | afi_var : forall (x : variable), appears_free_in x (tm_var x)
  
  | afi_app1 :  forall x t1 t2, appears_free_in x t1 -> appears_free_in x (tm_app t1 t2)

  | afi_app2 :  forall x t1 t2, appears_free_in x t2 -> appears_free_in x (tm_app t1 t2)

  | afi_abs  :  forall x y t,
                  y <> x  -> appears_free_in x t -> appears_free_in x (tm_abs y t) 

  | afi_pair1 : forall x t1 t2, appears_free_in x t1 -> appears_free_in x (tm_pair t1 t2)

  | afi_pair2 : forall x t1 t2, appears_free_in x t2 -> appears_free_in x (tm_pair t1 t2)

  | afi_fst   : forall x t, appears_free_in x t -> appears_free_in x (tm_fst t)
  | afi_snd   : forall x t, appears_free_in x t -> appears_free_in x (tm_snd t)
  | afi_arr   : forall x t, appears_free_in x t -> appears_free_in x (tm_arr t)
  | afi_first : forall x t, appears_free_in x t -> appears_free_in x (tm_first t)
  
  | afi_comp1 : forall x t1 t2, appears_free_in x t1 -> appears_free_in x (tm_comp t1 t2)
  | afi_comp2 : forall x t1 t2, appears_free_in x t2 -> appears_free_in x (tm_comp t1 t2)

  | afi_wh1 : forall x t1 t2, appears_free_in x t1 -> appears_free_in x (tm_wh t1 t2)
  | afi_wh2 : forall x t1 t2, appears_free_in x t2 -> appears_free_in x (tm_wh t1 t2)
.

Definition closed (t : t) := forall x, ~ (appears_free_in x t).

Inductive value : t -> Prop :=
  | v_unit  : value tm_unit
  | v_fix  : value tm_fix

  | v_abs   : forall x t, value (tm_abs x t)

  | v_pair  : forall v1 v2, 
                value v1 -> value v2 -> value (tm_pair v1 v2)

  | v_arr   : forall t, value t -> value (tm_arr t)

  | v_first : forall t, value t -> value (tm_first t)

  | v_comp  : forall t1 t2, value t1 -> value t2 -> value (tm_comp t1 t2)

  | v_rsf   : forall r, value (tm_rsf r)

  | v_wh    : forall i t, value i -> value t -> value (tm_wh i t)
.


#[global] 
Hint Constructors value appears_free_in : core.

(** *** Equality *)

#[export] Instance eq_refl : Reflexive eq := _.
#[export] Instance eq_sym : Symmetric eq := _.
#[export] Instance eq_trans : Transitive eq := _.
#[export] Instance eq_rr : RewriteRelation eq := {}.
#[export] Instance eq_equiv : Equivalence eq := _.

#[export] Hint Resolve eq_refl eq_sym eq_trans : core.

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
  - destruct (Var.eqb_spec v v0); subst;
    destruct (IHe e'); subst; try (right; intro c; inversion c; subst; now contradiction).
    now left.
  - destruct (Resource.eq_dec r r0); subst; try now left. right; intro c; inversion c; subst;
    contradiction.
Qed.

Lemma eq_leibniz : forall x y, eq x y -> x = y. Proof. auto. Qed.

(** *** Shift *)

Lemma shift_zero_refl : forall (lb : nat) (t : t), shift lb 0 t = t.
Proof.
  intros lb t; induction t; simpl; f_equal; auto.
  apply Resource.shift_zero_refl.
Qed.

#[export] Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.

Lemma shift_eq_iff : forall lb k t t1,
  t = t1 <-> (shift lb k t) = (shift lb k t1).
Proof.
  split.
  - intros; now subst.
  - revert lb k t1; induction t0; intros lb k t' Heq; destruct t'; 
    simpl in *; try (now inversion Heq); try (inversion Heq;f_equal; eauto).
    eapply Resource.shift_eq_iff; eauto.
Qed.

Lemma shift_trans : forall lb k k' t,
  shift lb k (shift lb k' t) = shift lb (k + k') t.
Proof.
  intros lb k k' t; induction t; simpl; f_equal; auto.
  apply Resource.shift_trans.
Qed.

Lemma shift_permute : forall lb k k' t,
  shift lb k (shift lb k' t) = shift lb k' (shift lb k t).
Proof.
  intros lb k k' t; induction t; simpl; f_equal; auto.
  apply Resource.shift_permute.
Qed.

Lemma shift_not_fix_iff : forall t lb k,
  t <> tm_fix <-> (shift lb k t) <> tm_fix.
Proof.
  intro t; induction t; intros; split; simpl; 
  intros; intro; inversion H0;
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
  apply Resource.shift_permute_1.
Qed.

Lemma shift_permute_2 : forall lb lb' k k' t,
  lb <= lb' -> eq (shift lb k (shift lb' k' t)) (shift (lb' + k) k' (shift lb k t)).
Proof.
  unfold eq; intros lb lb' k k' t; induction t; simpl; intros; f_equal; auto.
  now apply Resource.shift_permute_2.
Qed.

Lemma shift_unfold : forall lb k k' t,
  eq (shift lb (k + k') t) (shift (lb + k) k' (shift lb k t)). 
Proof.
    intros lb k k' t; induction t; simpl; auto;
    try (rewrite IHt1; rewrite IHt2; now reflexivity);
    try (rewrite IHt; now reflexivity).
    now rewrite Resource.shift_unfold.
Qed.

Lemma shift_unfold_1 : forall k k' k'' t,
    k <= k' -> k' <= k'' -> 
    eq (shift k' (k'' - k') (shift k  (k' - k) t)) (shift k (k'' - k) t).
Proof.
    intros k k' k'' t Hlt Hlt'; induction t; simpl; auto;
    try (rewrite IHt1; rewrite IHt2; now reflexivity);
    try (rewrite IHt; now reflexivity).
    now rewrite Resource.shift_unfold_1.
Qed.

(** *** Valid *)


#[export] Instance valid_eq : Proper (Logic.eq ==> eq ==> iff) valid := _.

Lemma valid_weakening : forall k k' t, (k <= k') -> valid k t -> valid k' t.
Proof.
    unfold valid; intros k k' t; generalize k k'; clear k k'; induction t; 
    intros k k'; simpl; auto; intros Hlt Hv; try (inversion Hv; subst; now eauto).
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
    - constructor; now apply Resource.shift_preserves_valid_1.
    - apply vΛ_wh; auto. replace (S (S (k + k'))) with ((S (S k)) + k'); auto; lia.
Qed.

Theorem shift_preserves_valid : forall k k' t,
    valid k t -> valid (k + k') (shift k k' t).
Proof. intros; now apply shift_preserves_valid_1. Qed. 

Theorem shift_preserves_valid_zero : forall k t,
    valid k t -> valid k (shift k 0 t).
Proof. 
    intros. apply shift_preserves_valid with (k' := 0) in H. 
    replace (k + 0) with k in H; auto.
Qed. 

Lemma shift_preserves_valid_gen : forall lb lb' k k' t,
    k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' -> k' - k = lb' - lb -> 
    valid lb t -> valid lb' (shift k (k' - k) t).
Proof.
    intros lb lb' k k' t; revert k k' lb lb'; induction t; intros; simpl; inversion H4; subst; 
    constructor; eauto; try (apply IHt1 with lb; now auto);
    try (apply IHt2 with lb; now auto); try (apply IHt with lb; now auto).
    - apply Resource.shift_preserves_valid_gen with lb; auto.
    - apply IHt2 with (lb := S (S lb)); auto; lia.
Qed.

Lemma shift_preserves_valid_2 : forall lb lb' t,
    lb <= lb' -> valid lb t -> 
    valid lb' (shift lb (lb' - lb) t).
Proof. intros. eapply shift_preserves_valid_gen; eauto. Qed.

(** *** Multi Shift *)

Lemma multi_shift_unit lbs ks :
  multi_shift lbs ks tm_unit = tm_unit.
Proof. 
  unfold multi_shift; revert ks.
  induction lbs; simpl; intros; auto.
  destruct ks; simpl; auto.
  now rewrite IHlbs.
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
  multi_shift lbs ks (tm_rsf r) = tm_rsf ([⧐⧐ lbs – ks] r).
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

Lemma multi_shift_abs lbs ks : forall x t1,
  multi_shift lbs ks (tm_abs x t1) = tm_abs x (multi_shift lbs ks t1).
Proof. 
  unfold multi_shift. revert ks.
  induction lbs.
  - simpl; intros; reflexivity.
  - simpl; intros; destruct ks.
    -- simpl; reflexivity.
    -- simpl. rewrite IHlbs. now simpl.
Qed.

Lemma multi_shift_first lbs ks : forall t1,
  multi_shift lbs ks (tm_first t1) = tm_first (multi_shift lbs ks t1).
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

(** ---- *)

(** * Syntax - Optional Term *)

(** ** Module - Optional Term *)
Module OptTerm <: IsLvlETWL := IsLvlOptETWL Term.

(** ---- *)

(** ** Notation - Term *)
Module TermNotations.

(** *** Scope *)
Declare Scope term_scope.
Declare Scope opt_term_scope.
Delimit Scope term_scope with tm.
Delimit Scope opt_term_scope with otm.

(** *** Notation *)
Definition Λ := Term.t.
Definition Λₒ := OptTerm.t.

Coercion Term.tm_var : variable >-> Term.raw.
Notation "value( t )" := (Term.value t) (at level 20, no associativity).
Notation "cl( t )" := (Term.closed t) (at level 20, no associativity).
Notation "'isFV(' r ',' t ')'" := (Term.appears_free_in r t) (at level 40, t custom wh).

Notation "x y"     := (Term.tm_app x y) (in custom wh at level 70, left associativity).
Notation "\ x , y" := (Term.tm_abs x y) (in custom wh at level 90, 
                                                    x at level 99, y custom wh at level 99, 
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
Notation "'first(' sf ')'" := (Term.tm_first sf) (in custom wh at level 0).
Notation " sf1 '>>>' sf2 " := (Term.tm_comp sf1 sf2) (in custom wh at level 60, 
                                                                          left associativity).
Notation "'rsf[' r ']'"    := (Term.tm_rsf r) (in custom wh at level 0,  
                                                      r constr, no associativity).
Notation "'wormhole(' i ';' sf ')'" :=  (Term.tm_wh i sf ) (in custom wh at level 23,
                                                                  i custom wh, 
                                                                  sf custom wh, 
                                                                  no associativity).

Notation "'[⧐' lb '–' k ']' t" := (Term.shift lb k t) 
  (in custom wh at level 45, right associativity) : term_scope.
Notation "'[⧐⧐' lb '–' k ']' t" := (Term.multi_shift lb k t) 
  (in custom wh at level 45, right associativity) : term_scope.
Notation "'[⧐' lb '–' k ']' t" := (OptTerm.shift lb k t) 
  (in custom wh at level 45, right associativity) : opt_term_scope.

Infix "⊩"  := Term.valid (at level 20, no associativity) : term_scope.   
Infix "⊩" := OptTerm.valid (at level 20, no associativity) : opt_term_scope.   

Infix "="  := Term.eq : term_scope.
Infix "="  := OptTerm.eq : opt_term_scope.


(** *** Morphism *)
#[export] Instance term_leibniz_eq : Proper Logic.eq Term.eq := _.

End TermNotations.