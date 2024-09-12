From Coq Require Import Structures.Equalities Lists.List Classes.Morphisms Logic.FunctionalExtensionality.
From Mecha Require Import Resource Typ Var.
From DeBrLevel Require Import LevelInterface MapLevelInterface MapLevel.

(** * Context - Variable Context 

 A Wormholes term is typed by a type defined in [Typ.v] regards of two contexts:
 the common variable context and the resource context. The former is defined here.
 It is the usual context, however types carry resources thus it implements one of
 the interface for level management.

*)
Module VContext <: IsBdlLvlET.

Include MapD.MakeBdlLvlMapD Var Typ.
Import Raw Ext.

(** *** Morphism *)

#[export] Instance in_vctx : 
  Proper (Logic.eq ==> eq ==> iff) In.
Proof.
  repeat red; intros; split; intros;
  apply Equal_Eqdom in H0; eapply In_m in H0; eauto;
  apply H0; eauto. 
Qed.

#[export] Instance find_vctx : Proper (Logic.eq ==> eq ==> Logic.eq) find.
Proof. repeat red; intros; subst. now rewrite H0. Qed.

#[export] Instance Empty_vctx : Proper (eq ==> iff) Empty.
Proof. intros c c' Heq; now rewrite Heq. Qed.

#[export] Instance add_vctx : 
  Proper (Var.eq ==> Typ.eq ==> eq ==> eq) (@add Typ.t).
Proof.
  intros x x' HeqV ty ty' HeqT c c' Heq.
  rewrite HeqV; rewrite HeqT.
  now rewrite Heq.
Qed. 

#[export] Instance Add_vctx : 
  Proper (Var.eq ==> Typ.eq ==> eq ==> eq ==> iff) (@Add Typ.t).
Proof. 
  intros x x' HeqV ty ty' HeqT c c' Heq c1 c1' Heq1.
  rewrite HeqV; rewrite HeqT.
  unfold Add.
  now rewrite Heq,Heq1.
Qed.

End VContext.


(** * Notation - Variable Context *)
Module VContextNotations.

(** ** Scope *)
Declare Scope vcontext_scope.
Delimit Scope vcontext_scope with vc.

(** ** Notations *)
Definition Γ := VContext.t.

Infix "⊆" := VContext.Submap (at level 60, no associativity) : vcontext_scope. 
Infix "∈" := VContext.Raw.In (at level 60, no associativity) : vcontext_scope. 
Notation "r '∉' Re" := (~ (VContext.Raw.In r Re)) (at level 75, no associativity) : vcontext_scope. 
Notation "∅" := VContext.Raw.empty (at level 0, no associativity) : vcontext_scope. 
Notation "'isEmpty(' Re ')'" := (VContext.Empty Re) (at level 20, no associativity) : vcontext_scope. 
Notation "'Add'" := (VContext.Add) (at level 20, no associativity) : vcontext_scope. 
Notation "R '⌊' x '⌋'"  := (VContext.Raw.find x R) (at level 15, x constr) : vcontext_scope.
Notation "⌈ x ⤆ v '⌉' R"  := (VContext.Raw.add x v R) (at level 15, x constr, 
                                                                                v constr) : vcontext_scope.
                                                                                (*
Notation "R ⌈ x ⩦ v '⌉'"  := (VContext.Raw.find x R = Some v) (at level 15, 
                                                                          x constr, v constr).
Notation "R ⌈ x ⩦ ⊥ '⌉'"  := (VContext.Raw.find x R = None) (at level 15, 
                                                                                x constr).
*)
Infix "=" := VContext.eq : vcontext_scope.

Notation "'[⧐' lb '–' k ']' t" := (VContext.shift lb k t) (at level 65, right associativity) : vcontext_scope.
Infix "⊩" := VContext.valid (at level 20, no associativity) : vcontext_scope.

(** ** Morphism *)

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