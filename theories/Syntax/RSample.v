From Coq Require Import Lists.List Structures.Equalities Classes.Morphisms.
From Mecha Require Import Term Typ ET_Definition Resource VContext RContext Typing.
From DeBrLevel Require Import LevelInterface PairLevel.
Import ListNotations.

Module RSampleI <: IsLvlETWL := Term.

Module RSampleO <: IsLvlETWL.

Include OptTerm.

Definition prop_opt (P: Λ -> Prop) ot :=
  match ot with
    | Some t => P t
    | _ => True
  end.

Definition halts k t := prop_opt (halts k) t.

Definition well_typed (Γ : Γ) (Re : ℜ) (t : t) (τ : Τ) :=
  prop_opt (fun v => Γ ⋅ Re ⊫ v ∈ τ) t.

#[export]
Instance wt_eq :
  Proper (VContext.eq ==> RContext.eq ==> eq ==> Typ.eq ==> iff) well_typed.
Proof.
  repeat red; intros G G' HeqVC R R' HeqRC st st' Heqst ty ty' Heqty; split.
  - unfold well_typed; intros; destruct st; destruct st'; simpl in *; auto;
    inversion Heqst; subst;
    rewrite <- HeqVC; rewrite <- HeqRC; now rewrite <- Heqty.
  - unfold well_typed; intros; destruct st; destruct st'; simpl in *; auto;
    inversion Heqst; subst;
    rewrite HeqVC; rewrite HeqRC; now rewrite Heqty.
Qed.

End RSampleO.

(** * Syntax - Sample

  In the temporal transition each resources is associated to a value via a next and a put function.
  We formalize it by a pair term and optional term, because the resource can be unused.
*)
Module RSample <: IsLvlETWL.

(** *** Definition *)

Include IsLvlPairETWL RSampleI RSampleO.

Definition next (rr : t) : Λ := fst rr.

Definition put (v : option Λ) (rr : t) : t := (fst rr,v).

Definition halts k (rr : t) := 
  halts k (fst rr) /\ RSampleO.halts k (snd rr).

Definition well_typed (Γ : Γ) (Re : ℜ) (s : t) (α β : Τ) :=
  well_typed Γ Re (fst s) α /\ RSampleO.well_typed Γ Re (snd s) β.

(** *** Halts *)


Lemma halts_next k t : 
  halts k t -> ET_Definition.halts k (next t).
Proof.
  unfold halts,next; now intros [].
Qed.

Lemma halts_put_Some k t v :
  halts k t -> ET_Definition.halts k v -> halts k (put (Some v) t).
Proof.
  intros; unfold put; destruct t; destruct H; split; simpl in *; auto.
Qed. 

Lemma halts_put_None k t :
  halts k t -> halts k (put None t).
Proof.
  intros; unfold put; destruct t; destruct H; split; simpl in *; auto.
Qed. 

#[export]
Instance wt_rflow :
  Proper (VContext.eq ==> RContext.eq ==> eq ==> Typ.eq ==> Typ.eq ==> iff) well_typed.
Proof.
  repeat red; intros; unfold well_typed; split; intros [].
  - split.
    -- rewrite <- H1; rewrite <- H2; rewrite <- H; now rewrite <- H0.
    -- eapply RSampleO.wt_eq; try symmetry; eauto.
       destruct H1. unfold RelationPairs.RelCompFun in *; auto.
  - split.
    -- rewrite H1; rewrite H2; rewrite H; now rewrite H0.
    -- eapply RSampleO.wt_eq; eauto.
       destruct H1. unfold RelationPairs.RelCompFun in *; auto.
Qed.

Lemma well_typed_next : forall Γ Re s α β,
  well_typed Γ Re s α β -> Γ ⋅ Re ⊫ {next s} ∈ α.
Proof.
  intros. unfold well_typed in H. destruct H as [H _].
  destruct s; now simpl in *.
Qed.

Lemma well_typed_None : forall Γ Re s α β,
  well_typed Γ Re s α β ->
  well_typed Γ Re (RSample.put None s) α β.
Proof.
  intros. unfold well_typed in *; destruct s; unfold put.
  destruct H; split; simpl in *; auto.
Qed.

Lemma well_typed_Some : forall Γ Re s v α β,
  well_typed Γ Re s α β ->
  Γ ⋅ Re ⊫ v ∈ β ->
  well_typed Γ Re (RSample.put (Some v) s) α β.
Proof.
  intros. unfold well_typed in *; destruct s; unfold put.
  destruct H; split. simpl in *; auto.
  now simpl in *.
Qed.

End RSample.