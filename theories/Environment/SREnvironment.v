From Coq Require Import Lia Arith.PeanoNat Morphisms.
From Mecha Require Import Resource Term REnvironment Cell SyntaxNotation.
From DeBrLevel Require Import LevelInterface MapLevelInterface MapLevelLVLD MapExtInterface MapExt.

(** * Environment - Simple Resource Environment

  For the temporal transition, we need to define a map that binds global resources with terms. Indeed, it simulates the information that come from the external environment.
*)

Module SREnvironment <: IsLvlET.

Include MakeLvlMapLVLD Term.
Import Raw Ext.

Module RE := REnvironment.

(** ** Definitions *)

(** *** Initialize an environment

  For each instant, global resources are initialized with a certain term. Consequently, we define [init_globals] that takes a simple environment [sr] and an environement [V] and produces an environment where all resource names in [sr] are initialized.
*)
Definition init_func (r: resource) (v: Λ) (V: RE.t) := RE.Raw.add r (Cell.inp v) V.

Definition init_g (sr: t) (V: RE.t) := fold init_func sr V.

Definition init_globals (sr: t) : RE.t := init_g sr RE.Raw.empty.

(** ** Properties *)

(** *** [extend] properties *)
 
Lemma extend_Empty_left (sr sr' : t) :
  Empty sr -> eq (extend sr sr') sr'.
Proof.
  intro HEmp; unfold extend.
  apply Empty_eq in HEmp.
  rewrite fold_init; eauto.
  - apply fold_identity.
  - repeat red; intros; subst; now rewrite H1.
Qed.

Lemma extend_Empty_right (sr sr' : t) :
  Empty sr' -> eq (extend sr sr') sr.
Proof. intro HEmp; unfold extend; now rewrite fold_Empty; eauto. Qed.

Lemma extend_add_right (r: resource) (v: Λ) (sr sr' : t) :
  ~ (In r sr') -> eq (extend sr (add r v sr')) (add r v (extend sr sr')).
Proof.
  intro HnIn; unfold extend; rewrite fold_Add; eauto.
  - reflexivity.
  - intros k' k Heqk d' d Heqd c c' Heqc; subst; now rewrite Heqc.
  - apply diamond_add.
  - unfold SREnvironment.Add; reflexivity.
Qed.

Lemma Wf_extend (k : lvl) (sr sr' : t) :
  Wf k sr -> Wf k sr' -> Wf k (extend sr sr').
Proof.
  revert sr; induction sr' using map_induction; intros sr Hvrs Hvrs'.
  - rewrite extend_Empty_right; auto.
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    rewrite extend_add_right; auto.
    apply Wf_add_notin in Hvrs' as [Hvx [Hve Hvrs'1]]; auto.
    apply Wf_add; auto.
Qed.

Lemma extend_new_key (sr sr': t) :
  new_key (extend sr sr') = max (new_key sr) (new_key sr').
Proof.
  revert sr.
  induction sr' using map_induction; intro sr.
  - rewrite extend_Empty_right; auto.
    rewrite (new_key_Empty sr'); auto; lia.
  - unfold SREnvironment.Add in H0; rewrite H0; clear H0.
    rewrite extend_add_right; auto.
    do 2 rewrite new_key_add_max.
    rewrite IHsr'1; lia.
Qed.

(** *** [new_key] properties *)

Lemma new_key_Wf (k: lvl) (sr: t) : Wf k sr -> new_key sr <= k.
Proof.
  induction sr using map_induction; intro Hwf.
  - rewrite new_key_Empty; auto; lia.
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    apply Wf_add_notin in Hwf as [Hwfx [_ Hwf]]; auto.
    apply IHsr1 in Hwf.
    unfold Resource.Wf in Hwfx.
    rewrite new_key_add_max; lia.
Qed.

(** *** Morphisms *)

#[export] Instance srenvironment_in_iff : Proper (Logic.eq ==> eq ==> iff) In.
Proof. intros k' k Heqk sr sr' Heqrs; subst; now rewrite Heqrs. Qed.

#[export] Instance srenvironment_Add_iff : 
  Proper (Resource.eq ==> Term.eq ==> eq ==> eq ==> iff) (@SREnvironment.Add Term.t).
Proof.
  intros k' k Heqk d d' Heqd sr sr' Heqrs rs1 rs1' Heqrs1; unfold SREnvironment.Add.
  now rewrite Heqk, Heqd, Heqrs, Heqrs1. 
Qed.

#[export] Instance srenvironment_for_all_iff :
  Proper (Logic.eq ==> eq ==> iff) For_all.
Proof.
  intros P' P HeqP t t' Heqt; subst.
  split; intros HFa r v Hfi.
  - rewrite <- Heqt in Hfi.
    now apply HFa.
  - rewrite Heqt in Hfi.
    now apply HFa.
Qed.

End SREnvironment.