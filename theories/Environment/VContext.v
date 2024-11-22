From Coq Require Import Classes.Morphisms.
From Mecha Require Import Resource Typ Var.
From DeBrLevel Require Import LevelInterface MapLevelInterface MapLevel.

(** * Context - Variable Context 

  The type system, defined in [Type_System.v], requires two contexts: a variable context and a resource context. The former is defined here and the latter is defined in [RContext.v]. It is a map which binds variable names with types. We use the module [MapD] defined by the library [DeBrLevel].
*)

(** ** Module - Variable Context *)
Module VContext <: IsBdlLvlET.

(** *** Definition *)

Include MapD.MakeBdlLvlMapD Var Typ.
Import Raw Ext.

(** *** Property *)

#[export] Instance in_vctx : Proper (Logic.eq ==> eq ==> iff) In.
Proof. intros x y Heqx c c' Heqc; subst; now rewrite Heqc. Qed.

#[export] Instance find_vctx : Proper (Logic.eq ==> eq ==> Logic.eq) find.
Proof. repeat red; intros; subst. now rewrite H0. Qed.

#[export] Instance Empty_vctx : Proper (eq ==> iff) Empty.
Proof. intros c c' Heq; now rewrite Heq. Qed.

#[export] Instance add_vctx : Proper (Var.eq ==> Typ.eq ==> eq ==> eq) (@add Typ.t).
Proof.
  intros x x' HeqV ty ty' HeqT c c' Heq.
  now rewrite HeqV; rewrite HeqT; rewrite Heq.
Qed. 

#[export] Instance Add_vctx : Proper (Var.eq ==> Typ.eq ==> eq ==> eq ==> iff) (@Add Typ.t).
Proof. 
  intros x x' HeqV ty ty' HeqT c c' Heq c1 c1' Heq1.
  rewrite HeqV; rewrite HeqT.
  unfold Add.
  now rewrite Heq,Heq1.
Qed.

End VContext.

(** ---- *)

(** ** Notation - Variable Context *)
Module VContextNotations.

(** *** Scope *)
Declare Scope vcontext_scope.
Delimit Scope vcontext_scope with vc.

(** *** Notation *)
Definition Γ := VContext.t.

Notation "r '∉' t" := (~ (VContext.Raw.In r t)) (at level 75, no associativity) : vcontext_scope. 
Notation "∅" := VContext.Raw.empty (at level 0, no associativity) : vcontext_scope. 
Notation "'isEmpty(' t ')'" := (VContext.Empty t) 
                                (at level 20, no associativity) : vcontext_scope. 
Notation "'Add'" := (VContext.Add) (at level 20, no associativity) : vcontext_scope. 
Notation "t '⌊' x '⌋'"  := (VContext.Raw.find x t) (at level 15, x constr) : vcontext_scope.
Notation "⌈ x ⤆ v '⌉' t"  := (VContext.Raw.add x v t) 
                             (at level 15, x constr, v constr) : vcontext_scope.
Notation "'[⧐' lb '–' k ']' t" := (VContext.shift lb k t) 
                                   (at level 65, right associativity) : vcontext_scope.

Infix "⊆" := VContext.Submap (at level 60, no associativity) : vcontext_scope. 
Infix "∈" := VContext.Raw.In (at level 60, no associativity) : vcontext_scope. 
Infix "=" := VContext.eq : vcontext_scope.

Infix "⊩" := VContext.valid (at level 20, no associativity) : vcontext_scope.

(** *** Morphism *)

Import VContext.

#[export] Instance eq_equiv_vctx : Equivalence eq := _.
#[export] Instance in_vctx : Proper (Logic.eq ==> eq ==> iff) (Raw.In) := _.
#[export] Instance find_vctx : Proper (Logic.eq ==> eq ==> Logic.eq) (Raw.find) := _.
#[export] Instance Empty_vctx : Proper (eq ==> iff) (Empty) := _.
#[export] Instance Add_vctx : 
  Proper (Var.eq ==> Typ.eq ==> eq ==> eq ==> iff) (@VContext.Add Typ.t) := _.
#[export] Instance add_vctx : Proper (Var.eq ==> Typ.eq ==> eq ==> eq) (@Raw.add Typ.t) := _.
#[export] Instance Submap_vctx : Proper (eq ==> eq ==> iff) Submap := _.
#[export] Instance valid_vctx : Proper (Logic.eq ==> eq ==> iff) valid := _.
#[export] Instance shift_vctx : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.
#[export] Instance Submap_vctx_po : PreOrder Submap := _.

End VContextNotations.