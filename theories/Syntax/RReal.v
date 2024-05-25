From Coq Require Import Lists.List Structures.Equalities Classes.Morphisms.
From Mecha Require Import Term Typ Evaluation Resource VContext RContext Typing.
From DeBrLevel Require Import LevelInterface PairLevel ListLevel.
Import ListNotations.

Module RRealI <: IsLvlETWL.

Include IsLvlListETWL Term.

Definition halts k t := 
  forall x, In x t -> Evaluation.halts k x.

Definition well_typed (Γ : Γ) (Re : ℜ) (t : t) (τ : Τ) :=
  forall x, In x t -> Γ ⋅ Re ⊫ x ∈ τ.

#[export]
Instance wt_eq :
  Proper (VContext.eq ==> RContext.eq ==> eq ==> Typ.eq ==> iff) well_typed.
Proof.
  repeat red; intros G G' HeqVC R R' HeqRC st st' Heqst ty ty' Heqty; split.
  - unfold well_typed; intros. rewrite Heqst in *.
    apply H in H0. rewrite <- HeqVC; rewrite <- HeqRC; now rewrite <- Heqty.
  -  unfold well_typed; intros. rewrite Heqst in *.
    apply H in H0. rewrite HeqVC; rewrite HeqRC; now rewrite Heqty.
Qed.

End RRealI.

Module RRealO <: IsLvlETWL.

Include IsLvlListETWL OptTerm.

Definition prop_opt (P: Λ -> Prop) ot :=
  match ot with
    | Some t => P t
    | _ => True
  end.

Definition halts k t := 
  forall x, In x t -> prop_opt (halts k) x.

Definition well_typed (Γ : Γ) (Re : ℜ) (t : t) (τ : Τ) :=
  forall x, In x t -> prop_opt (fun v => Γ ⋅ Re ⊫ v ∈ τ) x.

#[export]
Instance wt_eq :
  Proper (VContext.eq ==> RContext.eq ==> eq ==> Typ.eq ==> iff) well_typed.
Proof.
  repeat red; intros G G' HeqVC R R' HeqRC st st' Heqst ty ty' Heqty; split.
  - unfold well_typed; intros. rewrite Heqst in *.
    apply H in H0. unfold prop_opt in *; destruct x; auto. 
    rewrite <- HeqVC; rewrite <- HeqRC; now rewrite <- Heqty.
  - unfold well_typed; intros. rewrite Heqst in *.
    apply H in H0. unfold prop_opt in *; destruct x; auto. 
    rewrite HeqVC; rewrite HeqRC; now rewrite Heqty.
Qed.

End RRealO.

Module RReal <: IsLvlETWL.

(** *** Definition *)

Include IsLvlPairETWL RRealI RRealO.

Definition next (rr : t) : option Λ := hd_error (fst rr).

Definition put (v : option Λ) (rr : t) : t := (tl (fst rr),v :: (snd rr)).

Definition update (rr : t) : t := (tl (fst rr),snd rr).

Definition halts k (rr : t) := 
  RRealI.halts k (fst rr) /\ RRealO.halts k (snd rr).

Definition well_typed (Γ : Γ) (Re : ℜ) (s : t) (α β : Τ) :=
  RRealI.well_typed Γ Re (fst s) α /\ RRealO.well_typed Γ Re (snd s) β.

Definition prop_opt (P: Λ -> Prop) ot :=
  match ot with
    | Some t => P t
    | _ => True
  end.

(** *** Halts *)


Lemma halts_next k t : 
  halts k t -> prop_opt (Evaluation.halts k) (next t).
Proof.  Admitted.

Lemma halts_put_Some k t v :
  halts k t -> Evaluation.halts k v -> halts k (put (Some v) t).
Proof.
  intros; unfold put; destruct t; destruct H; split; simpl in *.
  - unfold RRealI.halts in *; intros. apply H.
    destruct l; simpl in *; auto.
  - unfold RRealO.halts in *; intros. destruct H2; subst.
    -- now unfold RRealO.prop_opt.
    -- now apply H1.
Qed. 

Lemma halts_put_None k t :
  halts k t -> halts k (put None t).
Proof.
  intros; unfold put; destruct t; destruct H; split; simpl in *.
  - unfold RRealI.halts in *; intros. apply H.
    destruct l; simpl in *; auto.
  - unfold RRealO.halts in *; intros. destruct H1; subst.
    -- now unfold RRealO.prop_opt.
    -- now apply H0.
Qed. 

#[export]
Instance wt_rflow :
  Proper (VContext.eq ==> RContext.eq ==> eq ==> Typ.eq ==> Typ.eq ==> iff) well_typed.
Proof.
  repeat red; intros; unfold well_typed; split; intros [].
  - split.
    -- eapply RRealI.wt_eq; try symmetry; eauto.
       destruct H1. unfold RelationPairs.RelCompFun in *; auto.
    -- eapply RRealO.wt_eq; try symmetry; eauto.
       destruct H1. unfold RelationPairs.RelCompFun in *; auto.
  - split.
    -- eapply RRealI.wt_eq; eauto.
       destruct H1. unfold RelationPairs.RelCompFun in *; auto.
    -- eapply RRealO.wt_eq; eauto.
       destruct H1. unfold RelationPairs.RelCompFun in *; auto.
Qed.

Lemma well_typed_next : forall Γ Re s α β,
  well_typed Γ Re s α β ->
  prop_opt (fun v => Γ ⋅ Re ⊫ v ∈ α) (next s).
Proof.
  intros. unfold well_typed in H. destruct H as [H _].
  unfold prop_opt,next; destruct s; simpl in *.
  destruct l; simpl in *; auto.
  unfold RRealI.well_typed in *. apply H. simpl; now left.
Qed.

Lemma well_typed_None : forall Γ Re s α β,
  well_typed Γ Re s α β ->
  well_typed Γ Re (RReal.put None s) α β.
Proof.
  intros. unfold well_typed in *; destruct s; unfold put.
  destruct H; split; simpl in *.
  - unfold RRealI.well_typed in *; intros.
    destruct l; simpl in *; auto.
  - unfold RRealO.well_typed in *; intros.
    destruct H1; subst; auto. now unfold RRealO.prop_opt.
Qed.

Lemma well_typed_Some : forall Γ Re s v α β,
  well_typed Γ Re s α β ->
  Γ ⋅ Re ⊫ v ∈ β ->
  well_typed Γ Re (RReal.put (Some v) s) α β.
Proof.
  intros. unfold well_typed in *; destruct s; unfold put.
  destruct H; split. simpl in *.
  - unfold RRealI.well_typed in *; intros.
    destruct l; simpl in *; auto.
  - simpl in *. unfold RRealO.well_typed in *; intros.
    destruct H2; subst; auto.
Qed.

End RReal.