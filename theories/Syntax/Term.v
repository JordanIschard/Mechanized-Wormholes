From Coq Require Import Classes.Morphisms Lia.
From DeBrLevel Require Import LevelInterface Level OptionLevel.
From Mecha Require Import Var Resource Typ.
Import VarNotations ResourceNotations TypNotations.


(** * Syntax - Term

  Wormhole's terms are those of the arrow calculus with two additional arrow primitives named [rsf] and [wormhole] that respectively represent an interaction with the environment and a [let...in] structure for resource names and reactive expression. The definition relies on [Resource.v].
*)

(** ** Module - Term *)
Module Term <: IsLvlDTWL.

(** *** Definition *)

Open Scope resource_scope.
Open Scope typ_scope.

(** **** Type 

  Wormholes's syntax is an extended version of the standard lambda calculus with pair, projections, fixpoint, ground value, denoted [()], and arrow primitives (arr,first and comp). In addition, the language introduces [rsf] and [wormhole]. The former access to the environment and allows interaction with it. The latter creates local resources.
*)
Inductive raw : Type :=
  | tm_unit   : raw
  | tm_var (x : variable) : raw
  | tm_abs (x : variable) (t : raw) : raw
  | tm_app  (t1 t2 : raw) : raw
  | tm_pair (t1 t2 : raw) : raw
  | tm_fix   (t : raw) : raw
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

  The [shift] function takes a lower bound [lb] a natural [k] and a term [t], and produces a term [t'] where all resources [r] greater or equal to [lb] in [t] are incremented by [k]. The others are left unchanged. It is denoted [[⧐ lb – k] t].
*)
Fixpoint shift (lb k : lvl) (e : t) : t := 
  match e with
  | tm_rsf r => tm_rsf ([⧐ lb – k] r)

  | tm_abs x t0 => tm_abs x (shift lb k t0)
  | tm_fix t0   => tm_fix   (shift lb k t0)
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

(** **** Multi shift function 

  As done in [Resource.v], [Resources.v] and [Typ.v], we define a [multi_shift] function that applies [n] shifts for two lists [lbs] and [ks] of length [n].
*)
Definition multi_shift (lbs : list lvl) (ks : list lvl) (t : t) :=
  List.fold_right (fun lbk acc => shift (fst lbk) (snd lbk) acc) t (List.combine lbs ks).


(** **** Valid property 

  Defined as an inductive property and denoted [(⊩)], the well-formed property, named [valid], takes a level [k] called the well-formedness level and states that all resource names in the type are well-formed under [k]. Contrary to the property defined in [Typ.v], it is not exactly true because of bound resource names. Indeed, [k] may increase during the descent into the sub-term. It happens when
  we go through a [wormhole] term. It is the reactive binder that binds two resource names. If 
  [k ⊩ wormhole(t1;t2)] then its local resource names will be [k] and [S k]. Consequently, the
  well-formedness level [k] becomes [k + 2] in [t2]. A direct consequence the definition is that
 [shift_valid_refl] cannot hold anymore.
<<
We recall the lemma below.

Lemma shift_valid_refl (lb k : lvl) (t : t) : valid lb t -> (shift lb k t) = t.

Suppose t equals to wormhole(unit;rsf[0]), lb equals to 0 and k equals to 3. We know that: 

0 ⊩ wormhole(unit;rsf[0])

However, 

               ([⧐ 0 – 3] wormhole(unit;rsf[0])) ≠ wormhole(unit;rsf[0])
  wormhole(([⧐ 0 – 3] unit);([⧐ 0 – 3] rsf[0])) ≠ wormhole(unit;rsf[0])
                           wormhole(unit;rsf[3]) ≠ wormhole(unit;rsf[0])
>>
*)
Inductive valid' : lvl -> t -> Prop :=
  | vΛ_unit (k : lvl) : valid' k tm_unit
  | vΛ_var  (k : lvl) (x : variable) : valid' k (tm_var x)
  | vΛ_abs  (k : lvl) (x : variable) (t : t) : valid' k t -> valid' k (tm_abs x t)

  | vΛ_app  (k : lvl) (t1 t2 : t) : valid' k t1 -> valid' k t2 -> valid' k (tm_app t1 t2)
  | vΛ_pair (k : lvl) (t1 t2 : t) : valid' k t1 -> valid' k t2 -> valid' k (tm_pair t1 t2)

  | vΛ_fix   (k : lvl) (t : t) : valid' k t -> valid' k (tm_fix t) 
  | vΛ_fst   (k : lvl) (t : t) : valid' k t -> valid' k (tm_fst t) 
  | vΛ_snd   (k : lvl) (t : t) : valid' k t -> valid' k (tm_snd t)
  | vΛ_arr   (k : lvl) (t : t) : valid' k t -> valid' k (tm_arr t)
  | vΛ_first (k : lvl) (t : t) : valid' k t -> valid' k (tm_first t)

  | vΛ_rsf (k : lvl) (r : resource) : (k ⊩ r)%r ->  valid' k (tm_rsf r)

  | vΛ_comp (k : lvl) (t1 t2 : t) : valid' k t1 -> valid' k t2 -> valid' k (tm_comp t1 t2)
  | vΛ_wh   (k : lvl) (t1 t2 : t) : valid' k t1 -> valid' (S (S k)) t2 -> valid' k (tm_wh t1 t2)
.

Definition valid := valid'.

#[export] Hint Constructors valid' : core.

(** **** Value property 

  The evaluation transition definition, available in [ET_Definition.v], needs to differentiate terms and values. Ground values are [()], abstractions and [rsf]. We also consider as value
  pairs, and reactive terms only if all of their sub-terms are also values.
*)
Inductive value : t -> Prop :=
  | v_unit : value tm_unit
  | v_rsf (r : resource) : value (tm_rsf r)
  | v_abs (x : variable) (t : t) : value (tm_abs x t)

  | v_arr   (v : t) : value v -> value (tm_arr v)
  | v_first (v : t) : value v -> value (tm_first v)

  | v_pair (v1 v2 : t) : value v1 -> value v2 -> value (tm_pair v1 v2)
  | v_comp (v1 v2 : t) : value v1 -> value v2 -> value (tm_comp v1 v2)
  | v_wh   (v1 v2 : t) : value v1 -> value v2 -> value (tm_wh v1 v2)
.

#[export] Hint Constructors value valid' : core.

(** *** Property *)

#[export] Instance eq_refl : Reflexive eq := _.
#[export] Instance eq_sym : Symmetric eq := _.
#[export] Instance eq_trans : Transitive eq := _.
#[export] Instance eq_rr : RewriteRelation eq := {}.
#[export] Instance eq_equiv : Equivalence eq := _.

#[export] Hint Resolve eq_refl eq_sym eq_trans : core.

Lemma eq_dec (t1 t2 : t) : {eq t1 t2} + {~ eq t1 t2}.
Proof.
  unfold eq; revert t2; induction t1; intro; destruct t2; simpl; auto; 
  try (right; unfold not; intros contra; now inversion contra);
  try (destruct (IHt1_1 t2_1); destruct (IHt1_2 t2_2);
  try (right; unfold not; intros; inversion H; subst; contradiction); subst; f_equal; auto);
  try (destruct (IHt1 t2); subst; try (now left); right; intro c; 
        inversion c; subst; now contradiction).
  - destruct (Var.eqb_spec x x0); subst.
    -- now left.
    -- right; intro c; inversion c; subst; clear c; now contradiction n.
  - destruct (Var.eqb_spec x x0); subst;
    destruct (IHt1 t2); subst; try (right; intro c; inversion c; subst; now contradiction).
    now left.
  - destruct (Resource.eq_dec r r0); subst; try now left. right; intro c; inversion c; subst;
    contradiction.
Qed.

Lemma eq_leibniz (t1 t2 : t) : eq t1 t2 -> t1 = t2. 
Proof. auto. Qed.

(** **** [shift] property *)

Lemma shift_zero_refl (lb : lvl) (t : t) : shift lb 0 t = t.
Proof.
  induction t; simpl; f_equal; auto.
  apply Resource.shift_zero_refl.
Qed.

#[export] Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.

Lemma shift_eq_iff (lb k : lvl) (t t1 : t) :
  t = t1 <-> (shift lb k t) = (shift lb k t1).
Proof.
  split; intro Heq.
  - now subst.
  - revert t1 Heq; induction t; intros t' Heq; destruct t'; 
    simpl in *; try (now inversion Heq); try (inversion Heq;f_equal; eauto).
    eapply Resource.shift_eq_iff; eauto.
Qed.

Lemma shift_trans (lb k m : lvl) (t : t) :
  shift lb k (shift lb m t) = shift lb (k + m) t.
Proof.
  induction t; simpl; f_equal; auto.
  apply Resource.shift_trans.
Qed.

Lemma shift_permute (lb k m : lvl) (t : t) :
  shift lb k (shift lb m t) = shift lb m (shift lb k t).
Proof.
  induction t; simpl; f_equal; auto.
  apply Resource.shift_permute.
Qed.

Lemma shift_value_iff (lb k : lvl) (t : t) : value t <-> value (shift lb k t).
Proof.
  induction t; split; intros; auto; simpl;
  try (now inversion H); try (inversion H; subst; constructor);
  try (erewrite IHt1; now eauto); try (erewrite <- IHt1; now eauto);
  try (erewrite IHt2; now eauto); try (erewrite <- IHt2; now eauto);
  try (now apply IHt); try (erewrite IHt; eauto).
Qed.

Lemma shift_permute_1 (lb k m : lvl) (t : t) :
  eq (shift lb k (shift lb m t)) (shift (lb + k) m (shift lb k t)).
Proof.
  unfold eq; induction t; simpl; f_equal; auto.
  apply Resource.shift_permute_1.
Qed.

Lemma shift_permute_2 (lb k m n : lvl) (t : t) :
  lb <= k -> eq (shift lb m (shift k n t)) (shift (k + m) n (shift lb m t)).
Proof.
  unfold eq; induction t; simpl; intros; f_equal; auto.
  now apply Resource.shift_permute_2.
Qed.

Lemma shift_unfold (lb k m : lvl) (t : t) :
  eq (shift lb (k + m) t) (shift (lb + k) m (shift lb k t)). 
Proof.
  induction t; simpl; auto;
  try (rewrite IHt1; rewrite IHt2; now reflexivity);
  try (rewrite IHt; now reflexivity).
  now rewrite Resource.shift_unfold.
Qed.

Lemma shift_unfold_1 (k m n : lvl) (t : t) :
  k <= m -> m <= n -> 
  eq (shift m (n - m) (shift k  (m - k) t)) (shift k (n - k) t).
Proof.
  intros Hlekm Hlemn; induction t; simpl; auto;
  try (rewrite IHt1; rewrite IHt2; now reflexivity);
  try (rewrite IHt; now reflexivity).
  now rewrite Resource.shift_unfold_1.
Qed.

(** **** [valid] property *)

#[export] Instance valid_eq : Proper (Logic.eq ==> eq ==> iff) valid := _.

Lemma valid_weakening (k m : lvl) (t : t) : (k <= m) -> valid k t -> valid m t.
Proof.
  unfold valid; revert k m; induction t; simpl; intros k m Hle Hvt; 
  auto; try (inversion Hvt; subst; now eauto).
  - inversion Hvt; subst; constructor; eapply Resource.valid_weakening; eauto.
  - inversion Hvt; subst; apply vΛ_wh.
    -- eapply IHt1; eauto.
    -- apply IHt2 with (k := S (S k)); eauto; lia.
Qed.

Theorem shift_preserves_valid_1 (lb k m : lvl) (t : t) :
  valid k t -> valid (k + m) (shift lb m t).
Proof.
  unfold valid; revert lb k m; induction t; intros lb k m Hvt; 
  inversion Hvt; subst; simpl; auto.
  - constructor; now apply Resource.shift_preserves_valid_1.
  - apply vΛ_wh; auto. 
    replace (S (S (k + m))) with ((S (S k)) + m); auto; lia.
Qed.

Theorem shift_preserves_valid (k m : lvl) (t : t) :
  valid k t -> valid (k + m) (shift k m t).
Proof. intros; now apply shift_preserves_valid_1. Qed. 

Theorem shift_preserves_valid_zero (k : lvl) (t : t) :
  valid k t -> valid k (shift k 0 t).
Proof. 
  intro Hvt. 
  apply shift_preserves_valid with (m := 0) in Hvt. 
  replace (k + 0) with k in Hvt; auto.
Qed. 

Lemma shift_preserves_valid_gen (lb k m n : lvl) (t : t) :
    m <= n -> lb <= k -> m <= lb -> n <= k -> n - m = k - lb -> 
    valid lb t -> valid k (shift m (n - m) t).
Proof.
  revert lb k m n; induction t; 
  intros lb k m n Hlemn Hlelbk Hlemlb Hlenk Heq Hvt; simpl; 
  inversion Hvt; subst; constructor;
  try (apply IHt1 with lb; now auto);
  try (apply IHt2 with lb; now auto); try (apply IHt with lb; now auto).
  - apply Resource.shift_preserves_valid_gen with lb; auto.
  - apply IHt2 with (lb := S (S lb)); auto; lia.
Qed.

Lemma shift_preserves_valid_2 (m n : lvl) (t : t) :
  m <= n -> valid m t -> valid n (shift m (n - m) t).
Proof. 
  intros Hle Hvt. 
  eapply shift_preserves_valid_gen; eauto. 
Qed.

(** **** [multi_shift] property *)

Lemma multi_shift_unit (lbs ks : list lvl) :
  multi_shift lbs ks tm_unit = tm_unit.
Proof. 
  unfold multi_shift; revert ks.
  induction lbs; simpl; intros; auto.
  destruct ks; simpl; auto.
  now rewrite IHlbs.
Qed.

Lemma multi_shift_var (lbs ks : list lvl) (x : variable) :
  multi_shift lbs ks (tm_var x) = tm_var x.
Proof. 
  unfold multi_shift; revert ks.
  induction lbs; simpl; intro ks; auto.
  destruct ks; simpl; auto.
  now rewrite IHlbs. 
Qed.

Lemma multi_shift_rsf (lbs ks : list lvl) (r : resource) :
  multi_shift lbs ks (tm_rsf r) = tm_rsf ([⧐⧐ lbs – ks] r).
Proof. 
  unfold multi_shift; revert ks.
  induction lbs; simpl; intro ks; auto.
  destruct ks; simpl; auto.
  now rewrite IHlbs.
Qed.

Lemma multi_shift_app (lbs ks : list lvl) (t1 t2 : t) :
  multi_shift lbs ks (tm_app t1 t2) = tm_app (multi_shift lbs ks t1) (multi_shift lbs ks t2).
Proof. 
  unfold multi_shift; revert ks; induction lbs; intro ks; simpl; auto.
  destruct ks; simpl; auto; now rewrite IHlbs.
Qed.

Lemma multi_shift_pair (lbs ks : list lvl) (t1 t2 : t) :
  multi_shift lbs ks (tm_pair t1 t2) = tm_pair (multi_shift lbs ks t1) (multi_shift lbs ks t2).
Proof. 
  unfold multi_shift; revert ks; induction lbs; intro ks; simpl; auto.
  destruct ks; simpl; auto; now rewrite IHlbs.
Qed.

Lemma multi_shift_comp (lbs ks : list lvl) (t1 t2 : t) :
  multi_shift lbs ks (tm_comp t1 t2) = tm_comp (multi_shift lbs ks t1) (multi_shift lbs ks t2).
Proof. 
  unfold multi_shift; revert ks; induction lbs; intro ks; simpl; auto.
  destruct ks; simpl; auto; now rewrite IHlbs.
Qed.

Lemma multi_shift_wh (lbs ks : list lvl) (t1 t2 : t) :
  multi_shift lbs ks (tm_wh t1 t2) = tm_wh (multi_shift lbs ks t1) (multi_shift lbs ks t2).
Proof. 
  unfold multi_shift; revert ks; induction lbs; intro ks; simpl; auto.
  destruct ks; simpl; auto; now rewrite IHlbs.
Qed.

Lemma multi_shift_fix (lbs ks : list lvl) (t : t) :
  multi_shift lbs ks (tm_fix t) = tm_fix (multi_shift lbs ks t).
Proof. 
  unfold multi_shift; revert ks; induction lbs; intro ks; simpl; auto.
  destruct ks; simpl; auto; now rewrite IHlbs.
Qed.

Lemma multi_shift_fst (lbs ks : list lvl) (t : t) :
  multi_shift lbs ks (tm_fst t) = tm_fst (multi_shift lbs ks t).
Proof. 
  unfold multi_shift; revert ks; induction lbs; intro ks; simpl; auto.
  destruct ks; simpl; auto; now rewrite IHlbs.
Qed.

Lemma multi_shift_snd (lbs ks : list lvl) (t : t) :
  multi_shift lbs ks (tm_snd t) = tm_snd (multi_shift lbs ks t).
Proof. 
  unfold multi_shift; revert ks; induction lbs; intro ks; simpl; auto.
  destruct ks; simpl; auto; now rewrite IHlbs.
Qed.

Lemma multi_shift_arr (lbs ks : list lvl) (t : t) :
  multi_shift lbs ks (tm_arr t) = tm_arr (multi_shift lbs ks t).
Proof. 
  unfold multi_shift; revert ks; induction lbs; intro ks; simpl; auto.
  destruct ks; simpl; auto; now rewrite IHlbs.
Qed.

Lemma multi_shift_abs (lbs ks : list lvl) (x : variable) (t : t) :
  multi_shift lbs ks (tm_abs x t) = tm_abs x (multi_shift lbs ks t).
Proof. 
  unfold multi_shift; revert ks; induction lbs; intro ks; simpl; auto.
  destruct ks; simpl; auto; now rewrite IHlbs.
Qed.

Lemma multi_shift_first (lbs ks : list lvl) (t : t) :
  multi_shift lbs ks (tm_first t) = tm_first (multi_shift lbs ks t).
Proof. 
  unfold multi_shift; revert ks; induction lbs; intro ks; simpl; auto.
  destruct ks; simpl; auto; now rewrite IHlbs.
Qed.

Lemma multi_shift_nil_l (ks : list lvl) (t : t) : multi_shift nil ks t = t.
Proof. now unfold multi_shift; simpl. Qed.

Lemma multi_shift_nil_r (lbs : list lvl) (t : t) : multi_shift lbs nil t = t.
Proof. now unfold multi_shift; destruct lbs. Qed.

Lemma multi_shift_nil (t : t) : multi_shift nil nil t = t.
Proof. now unfold multi_shift. Qed.

Lemma multi_shift_cons (lb k : lvl) (lbs ks : list lvl) (t : t) :
  multi_shift (lb :: lbs) (k :: ks) t = shift lb k (multi_shift lbs ks t).
Proof. now unfold multi_shift. Qed.

Lemma multi_shift_value_iff (lbs ks : list lvl) (t : t) : 
  value t <-> value (multi_shift lbs ks t).
Proof.
  split; revert ks t; induction lbs; simpl; intros ks t Hvt; auto.
  - destruct ks; simpl in *; auto.
    rewrite multi_shift_cons.
    apply shift_value_iff. 
    now apply IHlbs.
  - destruct ks; simpl in *; auto.
    rewrite multi_shift_cons in Hvt.
    apply shift_value_iff in Hvt. 
    now apply IHlbs in Hvt.
Qed.

End Term.

(** ---- *)

(** * Syntax - Optional Term 

  In the temporal transition, we need to represent potential output. Thanks to the [DeBrLevel] library, we do not have to prove properties that handle level because [OptionLevel] already exists.
*)

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
(* Notation "cl( t )" := (Term.closed t) (at level 20, no associativity). *)
(* Notation "'isFV(' r ',' t ')'" := (Term.appears_free_in r t) (at level 40, t custom wh). *)

Notation "t1 t2"     := (Term.tm_app t1 t2) (in custom wh at level 70, left associativity).
Notation "\ x , t" := (Term.tm_abs x t) 
                      (in custom wh at level 90, x at level 99, t custom wh at level 99, 
                       left associativity).
Notation "'unit'" := (Term.tm_unit) (in custom wh at level 0).
Notation "⟨ t1 ',' t2 ⟩" := (Term.tm_pair t1 t2) 
                          (in custom wh at level 0, t1 custom wh at level 99, 
                           t2 custom wh at level 99).

Notation "'Fix' t"   := (Term.tm_fix t) (in custom wh at level 0).
Notation "'fst.' t"  := (Term.tm_fst t) (in custom wh at level 0).
Notation "'snd.' t"  := (Term.tm_snd t) (in custom wh at level 0).

Notation "'rsf[' r ']'" := (Term.tm_rsf r) (in custom wh at level 0, r constr, no associativity).

Notation "'arr(' t ')'"   := (Term.tm_arr t) 
                             (in custom wh at level 0, t custom wh at level 99, no associativity).
Notation "'first(' t ')'" := (Term.tm_first t) (in custom wh at level 0).
Notation " t1 '>>>' t2 "  := (Term.tm_comp t1 t2) (in custom wh at level 60, left associativity).
Notation "'wormhole(' t1 ';' t2 ')'" := (Term.tm_wh t1 t2) 
                                        (in custom wh at level 23, t1 custom wh, t2 custom wh, 
                                         no associativity).

Notation "'[⧐' lb '–' k ']' t"   := (Term.shift lb k t) 
                                     (in custom wh at level 45, right associativity) : term_scope.
Notation "'[⧐⧐' lb '–' k ']' t" := (Term.multi_shift lb k t) 
                                    (in custom wh at level 45, right associativity) : term_scope.
Notation "'[⧐' lb '–' k ']' t" := (OptTerm.shift lb k t) 
                                   (in custom wh at level 45, right associativity) : opt_term_scope.

Infix "⊩" := Term.valid (at level 20, no associativity) : term_scope.   
Infix "⊩" := OptTerm.valid (at level 20, no associativity) : opt_term_scope.   
Infix "=" := Term.eq : term_scope.
Infix "=" := OptTerm.eq : opt_term_scope.


(** *** Morphism *)
Import Term.

#[export] Instance term_leibniz_eq : Proper Logic.eq Term.eq := _.
#[export] Instance term_valid_proper :  Proper (Level.eq ==> eq ==> iff) valid := _.
#[export] Instance term_shift_proper : Proper (Level.eq ==> Level.eq ==> eq ==> eq) shift := shift_eq.
#[export] Instance term_multi_shift_proper : Proper (Logic.eq ==> Logic.eq ==> eq ==> Logic.eq) multi_shift := _.

End TermNotations.