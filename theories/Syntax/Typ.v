From Coq Require Import Classes.RelationClasses Classes.Morphisms Bool.Bool Classical_Prop.
From DeBrLevel Require Import LevelInterface PairLevel.
From Mecha Require Import Resource Resources.

(** * Syntax -  Type

  Here is the definition of types based on the Wormholes language.
*)
Module Typ <: IsBdlLvlFullDTWL.

Module RS := Resources.

(** *** Definition *)

(** **** Type *)
Inductive raw : Type :=
  | ty_unit
  | ty_arrow : raw -> raw -> raw
  | ty_prod  : raw -> raw -> raw
  | ty_reactive : raw -> raw -> resources -> raw
.

Definition t := raw.

(** **** Equality *)
Definition eq := @Logic.eq t.

Fixpoint eqb' (τ τ' : t) : bool := 
  match (τ,τ') with
    | (ty_unit,ty_unit)                            => true
    | (ty_prod τ1 τ2,ty_prod τ1' τ2')              => (eqb' τ1 τ1') && (eqb' τ2 τ2')
    | (ty_arrow τ1 τ2,ty_arrow τ1' τ2')            => (eqb' τ1 τ1') && (eqb' τ2 τ2')
    | (ty_reactive τ1 τ2 R,ty_reactive τ1' τ2' R') => (eqb' τ1 τ1') && (eqb' τ2 τ2') && 
                                                      (R =? R')%rs
    | _ => false
  end
.

Definition eqb := eqb'.

(** **** Shift function 

  The only elements that can be shift are sets on reactive arrow types.
*)
Fixpoint shift (lb : Lvl.t) (k : Lvl.t) (τ : t) : t := 
  match τ with
    | ty_arrow t1 t2 => ty_arrow (shift lb k t1) (shift lb k t2)    
    | ty_prod t1 t2 => ty_prod (shift lb k t1) (shift lb k t2)    
    | ty_reactive t1 t2 R => ty_reactive (shift lb k t1) (shift lb k t2) ([⧐ᵣₛ lb ≤ k] R)
    | _ => τ
  end
.

(** **** Valid function

  In the same way than the [shift] function, the valid function scan the entire type and
  verify the property if all carried sets satisfied the property of validity.
*)
Inductive valid' : Lvl.t -> t -> Prop :=
  | vΤ_unit : forall k, valid' k ty_unit
  | vΤ_prod : forall k τ1 τ2, valid' k τ1 -> valid' k τ2 -> valid' k (ty_prod τ1 τ2)
  | vΤ_func : forall k τ1 τ2, valid' k τ1 -> valid' k τ2 -> valid' k (ty_arrow τ1 τ2)
  | vΤ_reac : forall k τ1 τ2 R, valid' k τ1 -> valid' k τ2 -> k ⊩ᵣₛ R -> valid' k (ty_reactive τ1 τ2 R)
.

Fixpoint validb' (k : Lvl.t) (τ : t) :=
  match τ with
    | ty_unit => true
    | ty_arrow t1 t2 =>  (validb' k t1) && (validb' k t2)   
    | ty_prod t1 t2 =>  (validb' k t1) && (validb' k t2)   
    | ty_reactive t1 t2 R =>  (validb' k t1) && (validb' k t2) && (k ⊩?ᵣₛ R)
  end
.

Definition valid := valid'.
Definition validb := validb'.

#[global]
Hint Constructors valid' : core.

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

Lemma eqb_refl : forall τ, eqb τ τ = true.
Proof.
  induction τ; simpl; auto; try (rewrite andb_true_iff; split; now auto).
  repeat (rewrite andb_true_iff; split); auto. apply RS.eqb_refl.
Qed.

Lemma eqb_eq : forall τ1 τ2, eqb τ1 τ2 = true <-> eq τ1 τ2.
Proof.
  intros; split.
  - revert τ2; unfold eq,eqb; induction τ1; intros; destruct τ2; inversion H; subst; auto.
    -- apply andb_true_iff in H1 as [H1 H1']; f_equal; auto.
    -- apply andb_true_iff in H1 as [H1 H1']; f_equal; auto.
    -- apply andb_true_iff in H1 as [H1 H1'']; 
        apply andb_true_iff in H1 as [H1 H1']; f_equal; auto.
        apply RS.equal_spec in H1''; now apply RS.eq_leibniz.
  - intros; rewrite H; apply eqb_refl.
Qed.

Lemma eqb_neq : forall τ τ', eqb τ τ' = false <-> ~ eq τ τ'.
Proof.
  split.
  - unfold not; intros; apply eqb_eq in H0; rewrite H in *; inversion H0.
  - rewrite <- eqb_eq; intros; now apply not_true_is_false.
Qed.

Lemma eq_dec : forall (τ τ' : t), {eq τ τ'} + {~ eq τ τ'}.
Proof.
  unfold eq; intros τ; induction τ; intros τ'; destruct τ'; simpl; auto; 
  try (right; unfold not; intros contra; now inversion contra).
  - destruct (IHτ1 τ'1); destruct (IHτ2 τ'2);
    try (right; unfold not; intros; inversion H; subst; contradiction); subst.
    f_equal; auto. 
  - destruct (IHτ1 τ'1); destruct (IHτ2 τ'2);
    try (right; unfold not; intros; inversion H; subst; contradiction); subst.
    f_equal; auto.
  - destruct (IHτ1 τ'1); destruct (IHτ2 τ'2); destruct (RS.eq_dec r r0);
    try (right; unfold not; intros; inversion H; subst; contradiction); subst.
    -- apply RS.eq_leibniz in e1; subst; auto.
    -- right; unfold not in *; intros; inversion H; subst; apply n; reflexivity.
Qed.

Lemma eq_dec' : forall (τ τ' : t), {τ = τ'} + {τ <> τ'}.
Proof.
  intros; destruct (eq_dec τ τ'). 
  - unfold eq in *; subst; auto.
  - unfold eq in *; auto.
Qed.

Lemma eq_leibniz : forall x y, eq x y -> x = y. Proof. auto. Qed.

(** *** Shift *)

Lemma shift_refl : forall (lb : Lvl.t) (τ : t),
  (shift lb 0 τ) = τ.
Proof.
  intros lb τ; induction τ; simpl; f_equal; auto.
  apply RS.eq_leibniz; apply RS.shift_refl.
Qed.

Lemma shift_valid_refl : forall lb k τ,
  valid lb τ -> shift lb k τ = τ.
Proof.
  intros; induction H; subst; simpl; f_equal; auto.
  apply RS.eq_leibniz; now apply RS.shift_valid_refl.
Qed.

#[global]
Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift.
Proof. repeat red; intros; subst; apply eq_leibniz; now rewrite H1. Qed.

Lemma shift_eq_iff : forall lb k τ τ1,
  τ = τ1 <-> (shift lb k τ) = (shift lb k τ1).
Proof.
  split.
  - intros; now subst.
  - revert τ1; induction τ; intros τ1' Heq; destruct τ1'; auto; 
    try (now inversion Heq); inversion Heq; f_equal; auto.
    apply Resources.eq_leibniz. eapply Resources.shift_eq_iff.
    now rewrite H2.
Qed.

Lemma shift_trans : forall lb k k' τ,
  shift lb k (shift lb k' τ) = shift lb (k + k') τ.
Proof.
  intros; induction τ; simpl; f_equal; auto.
  apply RS.eq_leibniz; apply RS.shift_trans.
Qed.

Lemma shift_permute : forall lb k k' τ,
  shift lb k (shift lb k' τ) = shift lb k' (shift lb k τ).
Proof.
  intros; induction τ; simpl; f_equal; auto.
  apply RS.eq_leibniz; apply RS.shift_permute.
Qed.

Lemma shift_permute_1 : forall t lb k k',
  eq (shift lb k (shift lb k' t)) (shift (lb + k) k' (shift lb k t)).
Proof.
  unfold eq; intro t; induction t; intros; simpl; f_equal; auto.
  apply RS.eq_leibniz; apply RS.shift_permute_1.
Qed.

Lemma shift_permute_2 : forall t lb lb' k k',
  lb <= lb' -> eq (shift lb k (shift lb' k' t)) (shift (lb' + k) k' (shift lb k t)).
Proof.
  unfold eq; intro t; induction t; intros; simpl; f_equal; auto.
  apply RS.eq_leibniz; now apply RS.shift_permute_2.
Qed.

Lemma shift_unfold : forall lb k k' t,
  eq (shift lb (k + k') t) (shift (lb + k) k' (shift lb k t)). 
Proof.
  intros lb k k' t; induction t; simpl; auto.
  - rewrite IHt1; rewrite IHt2; reflexivity.
  - rewrite IHt1; rewrite IHt2; reflexivity.
  - rewrite IHt1; rewrite IHt2. 
    assert ([⧐ᵣₛ lb ≤ k + k'] r = [⧐ᵣₛ lb + k ≤ k'] [⧐ᵣₛ lb ≤ k] r)%rs by apply Resources.shift_unfold.
    apply Resources.eq_leibniz in H; rewrite H; reflexivity.
Qed.

Lemma shift_unfold_1 : forall k k' k'' t,
  k <= k' -> k' <= k'' -> eq (shift k' (k'' - k') (shift k  (k' - k) t)) (shift k (k'' - k) t).
Proof.
  intros k k' k'' t; induction t; simpl; intros; auto.
  - rewrite IHt1; auto; rewrite IHt2; auto; reflexivity.
  - rewrite IHt1; auto; rewrite IHt2; auto; reflexivity.
  - rewrite IHt1; auto; rewrite IHt2; auto. 
    assert ([⧐ᵣₛ k' ≤ k'' - k'] [⧐ᵣₛ k ≤ k' - k] r = [⧐ᵣₛ k ≤ k'' - k] r )%rs.
    -- apply Resources.shift_unfold_1; auto.
    -- apply Resources.eq_leibniz in H1; rewrite H1; reflexivity.
Qed.

(** *** Valid *)


Lemma validb_valid : forall k t, validb k t = true <-> valid k t.
Proof.
  intros k t; induction t; simpl; split; intros; auto.
  - now constructor.
  - rewrite andb_true_iff in *; destruct H; constructor; 
    try (now rewrite <- IHt1); now rewrite <- IHt2.
  - rewrite andb_true_iff in *; inversion H; subst; split; try (now rewrite IHt1);
    now rewrite IHt2.
  - rewrite andb_true_iff in *; destruct H; constructor; 
    try (now rewrite <- IHt1); now rewrite <- IHt2.
  - rewrite andb_true_iff in *; inversion H; subst; split; try (now rewrite IHt1);
    now rewrite IHt2.
  - repeat rewrite andb_true_iff in *; destruct H; destruct H; constructor;
    try (now rewrite <- IHt1); try (now rewrite <- IHt2); now rewrite <- Resources.validb_valid.
  - repeat rewrite andb_true_iff in *; inversion H; subst; repeat split; try (now rewrite IHt1);
    try (now rewrite IHt2); now rewrite Resources.validb_valid.
Qed.

Lemma validb_nvalid : forall k t, validb k t = false <-> ~ valid k t.
Proof.
  intros; rewrite <- not_true_iff_false; split; intros; intro.
  - apply H; now rewrite validb_valid. 
  - apply H; now rewrite <- validb_valid.
Qed.

#[global]
Instance valid_eq : Proper (Logic.eq ==> eq ==> iff) valid.
Proof. repeat red; intros; apply eq_leibniz in H0; subst; auto. Qed.

#[global]
Instance validb_eq : Proper (Logic.eq ==> eq ==> Logic.eq) validb.
Proof. repeat red; intros; apply eq_leibniz in H0; subst; auto. Qed.

Lemma valid_weakening: forall k k' τ,
  (k <= k') -> valid k τ -> valid k' τ.
Proof.
  unfold valid; intros k k' τ; induction τ; intros Hleq Hvτ; simpl in *;
  inversion Hvτ; subst; eauto.
  apply vΤ_reac; eauto. eapply RS.valid_weakening; eauto.
Qed.

Theorem shift_preserves_valid_1 : forall lb k k' τ,
  valid k τ -> valid (k + k') (shift lb k' τ).
Proof.
  unfold valid; intros lb k k' τ; induction τ; intro Hvτ; inversion Hvτ; subst; simpl; auto.
  apply vΤ_reac; auto. now apply RS.shift_preserves_valid_1.
Qed.

Theorem shift_preserves_valid : forall k k' τ,
  valid k τ -> valid (k + k') (shift k k' τ).
Proof. intros; now apply shift_preserves_valid_1. Qed.

Lemma shift_preserves_valid_4 : forall k t, valid k t -> valid k (shift k 0 t).
Proof. intros; replace k with (k + 0); auto; now apply shift_preserves_valid_1. Qed.

Lemma shift_preserves_valid_2 : forall lb lb' k k' t,
  k <= k' -> lb <= lb' -> k <= lb -> k' <= lb' -> k' - k = lb' - lb -> 
  valid lb t -> valid lb' (shift k (k' - k) t).
Proof.
  intros lb lb' k k' t; induction t; intros; simpl; inversion H4; subst; 
  constructor; eauto; try (apply IHt1; now auto); try (apply IHt2; now auto).
  apply RS.shift_preserves_valid_2 with lb; auto.
Qed.

Lemma shift_preserves_valid_3 : forall lb lb' t,
  lb <= lb' -> valid lb t -> valid lb' (shift lb (lb' - lb) t).
Proof. intros. eapply shift_preserves_valid_2; eauto. Qed.

End Typ.

(** * Syntax - Pair of types 

  Resource context needs a pair of types. Knowing that the context
  can be shifted, its elements need to implement shift, valid functions 
  and their associated lemmas.
*)
Module PairTyp <: IsBdlLvlFullETWL := IsBdlLvlFullPairETWL Typ Typ.

(** *** Scope and Notations *)
Declare Scope typ_scope.
Delimit Scope typ_scope with typ.
Definition Τ := Typ.t.
Definition πΤ := PairTyp.t.

(* #[export] Hint Constructors Raw_Typ.lt' : core.
#[export] Hint Resolve Raw_Typ.eq_refl Raw_Typ.eq_sym Raw_Typ.eq_trans : core. *)
(* #[export] Instance rtyp_eq_rr : RewriteRelation Raw_Typ.eq := {}.   
#[export] Instance rtyp_eq_equiv : Equivalence Raw_Typ.eq. Proof. split; auto. Qed.
#[export] Instance rtyp_lt_strorder : StrictOrder Raw_Typ.lt. 
          Proof. apply Raw_Typ.lt_strorder. Qed.
#[export] Instance rtyp_lt_compat : Proper (Raw_Typ.eq ==> Raw_Typ.eq ==> iff) Raw_Typ.lt. 
          Proof. apply Raw_Typ.lt_compat. Qed. *)
  
Notation "'𝟙'"       := Typ.ty_unit (in custom wormholes at level 0).
Notation "T1 '→' T2" := (Typ.ty_arrow T1 T2) (in custom wormholes at level 50, 
                                                                  right associativity).
Notation "X '×' Y"   := (Typ.ty_prod X Y) (in custom wormholes at level 2, 
                                                        X custom wormholes, 
                                                        Y custom wormholes at level 0).
Notation "τ1 '⟿' τ2 '∣' R" := (Typ.ty_reactive τ1 τ2 R) (in custom wormholes at level 50, 
                                                                  R constr, right associativity).


Notation "'[⧐ₜ' lb '≤' k ']' t" := (Typ.shift lb k t) (in custom wormholes at level 45, 
right associativity).
Notation "'[⧐ₚₜ' lb '≤' k ']' t" := (PairTyp.shift lb k t) (in custom wormholes at level 45, 
right associativity).

Infix "⊩ₜ" := Typ.valid (at level 20, no associativity). 
Infix "⊩?ₜ" := Typ.validb (at level 20, no associativity). 
Infix "⊩ₚₜ" := PairTyp.valid (at level 20, no associativity). 
Infix "⊩?ₚₜ" := PairTyp.valid (at level 20, no associativity). 

Infix "=" := Typ.eq : typ_scope.
Infix "=?" := Typ.eqb  (at level 70) : typ_scope.