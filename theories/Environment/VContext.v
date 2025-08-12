From Coq Require Import Classes.Morphisms.
From Mecha Require Import Var Typ SyntaxNotation.
From DeBrLevel Require Import LevelInterface MapLevelInterface MapLevelD.

(** * Context - Variable Context 

  The type system, defined in [Type_System.v], requires two contexts: a variable context and a resource context. The former is defined here and the latter is defined in [RContext.v]. It is a map which binds variable names with types. We use the module [MapD] defined by the library [DeBrLevel].
*)

Module VContext <: IsBdlLvlET.

Include MakeBdlLvlMapD Var Typ.
Import Raw Ext.

(** ** Properties *)

#[export] Instance vcontext_in_iff : Proper (Logic.eq ==> eq ==> iff) In.
Proof. intros x y Heqx c c' Heqc; subst; now rewrite Heqc. Qed.

#[export] Instance vcontext_find_eq : Proper (Logic.eq ==> eq ==> Logic.eq) find.
Proof. repeat red; intros; subst. now rewrite H0. Qed.

#[export] Instance vcontext_Empty_iff : Proper (eq ==> iff) Empty.
Proof. intros c c' Heq; now rewrite Heq. Qed.

#[export] Instance vcontext_add_eq : Proper (Var.eq ==> Typ.eq ==> eq ==> eq) (@add Typ.t).
Proof.
  intros x x' HeqV ty ty' HeqT c c' Heq.
  now rewrite HeqV; rewrite HeqT; rewrite Heq.
Qed. 

#[export] Instance vcontext_Add_eq : Proper (Var.eq ==> Typ.eq ==> eq ==> eq ==> iff) (@Add Typ.t).
Proof. 
  intros x x' HeqV ty ty' HeqT c c' Heq c1 c1' Heq1.
  rewrite HeqV; rewrite HeqT.
  unfold Add.
  now rewrite Heq,Heq1.
Qed.

End VContext.