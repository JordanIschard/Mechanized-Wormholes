From Coq Require Import Classes.Morphisms Relations.Relation_Operators.
From Mecha Require Import Term REnvironment Resource Cell.
From DeBrLevel Require Import SetLevelInterface SetLevel Level Levels.
Import ResourceNotations REnvironmentNotations TermNotations CellNotations.

(** * Environment - Virtual Resource Environment - Writer

  W, defined in [Stock.v], is in charge of keeping bound resources
  and initial terms of each removed wh term. In the original paper,
  W is a set of triplets, which can be cumbersome to treat. We decide
  to split W into two data structures: a map and a set. The latter,
  defined here, contains resources.

*)
Module WriteStock <: IsBdlLvlFullSetOTWLInterface Level.

Include Levels.

(** *** Definition *)

Definition init_virtual (st : WriteStock.t) (V : REnvironment.t) :=
  fold (fun r acc => ⌈ r ⤆ ⩽ unit … ⩾ ⌉ᵣᵦ acc) st V.


(** *** Initialize *)

Lemma proper_init_virtual : 
  Proper (Logic.eq ==> REnvironment.eq ==> REnvironment.eq)
  (fun (r : elt) (acc : REnvironment.t) => ⌈ r ⤆ ⩽ unit … ⩾ ⌉ᵣᵦ acc).
Proof.
  red; red; red; intros; subst. intro z; now rewrite H0.
Qed.

Lemma transpose_init_virtual :
  SetoidList.transpose REnvironment.eq
  (fun (r : elt) (acc : REnvironment.t) => ⌈ r ⤆ ⩽ unit … ⩾ ⌉ᵣᵦ acc).
Proof.
  red; intros. destruct (Resource.eq_dec x y); subst.
  - reflexivity.
  - rewrite REnvironment.add_add_2; auto; reflexivity.
Qed.

#[export] 
Hint Resolve proper_init_virtual transpose_init_virtual REnvironment.Equal_equiv : core.

Lemma init_virtual_unused : forall wsk V,
  forall r, In r wsk -> REnvironment.unused r (init_virtual wsk V).
Proof.
  intro wsk; induction wsk using set_induction; intros V r HIn.
  - unfold Empty in H; exfalso; now apply (H r).
  - apply Add_inv in H0; subst. rewrite add_spec in HIn; 
    destruct HIn as [Heq | HIn]; subst.
    -- exists <[unit]>; unfold init_virtual; rewrite fold_add; auto.
       rewrite REnvironment.add_eq_o; auto.
    -- destruct (Resource.eq_dec x r); subst.
       + exists <[unit]>; unfold init_virtual; 
         rewrite fold_add with (eqA := REnvironment.eq); auto;
         rewrite REnvironment.add_eq_o; auto.
       + apply IHwsk1 with (V := V) in HIn.
         destruct HIn. exists x0.
         unfold init_virtual; rewrite fold_add with (eqA := REnvironment.eq);
         auto; rewrite REnvironment.add_neq_o; auto.
Qed.

Lemma init_virtual_find_spec : forall wsk V r v,
  (init_virtual wsk V) ⌈ r ⩦ v ⌉ᵣᵦ -> In r wsk \/ V ⌈ r ⩦ v ⌉ᵣᵦ.
Proof.
  intros wsk; induction wsk using set_induction; intros.
  - unfold init_virtual in *. apply empty_is_empty_1 in H; 
    apply eq_leibniz in H; subst. rewrite fold_empty in H0; auto.
  - unfold init_virtual in H1. apply Add_inv in H0; subst. 
    rewrite fold_add in H1; eauto.
    rewrite REnvironment.add_o in H1. destruct (Resource.eq_dec x r); subst.
    -- inversion H1. left. rewrite add_spec; now left.
    -- apply IHwsk1 in H1; destruct H1; auto.
       left; rewrite add_spec; now right.
Qed. 
       
Lemma init_virtual_Forall_unused : forall wsk V,
  REnvironment.For_all (fun _ v => Cell.unused v) V ->
  REnvironment.For_all (fun _ v => Cell.unused v) (init_virtual wsk V).
Proof.
  unfold REnvironment.For_all in *; intros.
  apply init_virtual_find_spec in H0 as H0'; destruct H0'; auto.
  - eapply init_virtual_unused in H1; eauto.
    destruct H1; rewrite H0 in H1; inversion H1. now simpl.
  - eapply H; eauto.
Qed.

Lemma valid_in_spec_1 : forall (wsk : t) lb k r,
  valid lb wsk -> In r (shift lb k wsk) <-> In r wsk.
Proof.
  intro wsk. induction wsk using set_induction; intros lb k r Hv; split.
  - intro HIn; rewrite shift_Empty_spec in *; auto; inversion HIn.
  - intro HIn; unfold Empty in *; exfalso; now apply (H r).
  - intro HIn; apply Add_inv in H0; subst. rewrite shift_add_notin_spec in *; auto.
    apply valid_add_spec in Hv as [Hvr Hv]. rewrite add_spec in HIn; destruct HIn; subst.
    -- rewrite Resource.shift_valid_refl; auto; rewrite add_spec; now left.
    -- rewrite add_spec; right. rewrite <- IHwsk1; eauto.
  - intro HIn; apply Add_inv in H0; subst. rewrite shift_add_notin_spec in *; auto.
    apply valid_add_spec in Hv as [Hvr Hv]. rewrite add_spec in HIn; destruct HIn; subst.
    -- rewrite Resource.shift_valid_refl; auto; rewrite add_spec; now left.
    -- rewrite add_spec; right. rewrite IHwsk1; eauto.
Qed.

Lemma halts_init_virtual : forall k W V,
  REnvironment.halts k V ->
  REnvironment.halts k (init_virtual W V).
Proof.
  intros k W; induction W using set_induction; intros.
  - unfold init_virtual.
    apply empty_is_empty_1 in H. apply eq_leibniz in H. 
    rewrite H. now rewrite fold_empty.
  - unfold init_virtual in *.
    apply Add_inv in H0. subst.
    rewrite fold_add; auto. unfold REnvironment.halts; intros.
    destruct (Resource.eq_dec x r); subst.
    -- rewrite REnvironment.add_eq_o in H0; auto.
       inversion H0; subst; simpl. exists <[unit]>.
       split; auto. apply rt1n_refl.
    -- unfold REnvironment.halts in *. 
       rewrite REnvironment.add_neq_o in H0; auto.
       apply (IHW1 V) with (r := r); auto.
Qed.

End WriteStock.

(** * Notation - Writing Virtual Resource Environment *)
Module WriteStockNotations.

(** ** Scope *)
Declare Scope wstock_scope.
Delimit Scope wstock_scope with wk.

(** ** Notations *)
Definition 𝐖ₔ := WriteStock.t.

Notation "∅ₔₖ" := (WriteStock.empty).
Infix "∉" := (fun x s => ~ WriteStock.In x s) (at level 75) : wstock_scope.
Infix "∈" := (WriteStock.In)  (at level 60, no associativity) : wstock_scope.
Infix "+:" := (WriteStock.add)  (at level 60, no associativity) : wstock_scope.
Infix "∪" := (WriteStock.union) (at level 50, left associativity) : wstock_scope.
Infix "∩" := (WriteStock.inter) (at level 50, left associativity) : wstock_scope.
Infix "\" := (WriteStock.diff) (at level 50, left associativity) : wstock_scope.
Infix "⊆" := WriteStock.Subset (at level 60, no associativity) : wstock_scope.
Infix "⊈" := (fun s s' => ~ (WriteStock.Subset s s')) (at level 60, no associativity) : wstock_scope.
Infix "<"  := WriteStock.lt : wstock_scope.
Infix "<?"  := WriteStock.ltb : wstock_scope.
Infix "=" := WriteStock.eq : wstock_scope.
Infix "=?" := WriteStock.equal : wstock_scope.

Notation "'[⧐ₔₖ' lb '≤' k ']' t" := (WriteStock.shift lb k t) (at level 65, right associativity).
Infix "⊩ₔₖ" := WriteStock.valid (at level 20, no associativity). 
Infix "⊩?ₔₖ" := WriteStock.validb (at level 20, no associativity). 

(** ** Morphisms *)

#[export] 
Instance valid_wk : Proper (Logic.eq ==> WriteStock.eq ==> iff) WriteStock.valid.
Proof. apply WriteStock.valid_eq. Qed.

#[export] 
Instance validb_wk : Proper (Logic.eq ==> WriteStock.eq ==> Logic.eq) WriteStock.validb.
Proof. apply WriteStock.validb_eq. Qed.

#[export] 
Instance shift_wk : 
  Proper (Logic.eq ==> Logic.eq ==> WriteStock.eq ==> WriteStock.eq) WriteStock.shift.
Proof. apply WriteStock.shift_eq. Qed.

End WriteStockNotations.