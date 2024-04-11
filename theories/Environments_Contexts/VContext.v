From Coq Require Import Structures.Equalities Lists.List Classes.Morphisms Logic.FunctionalExtensionality.
Require Import Resource Typ Var.
From DeBrLevel Require Import MapExt MapExtInterface.

(** * Context between variables and types *)
Module VContext <: EqualityType.

Module Raw := MMaps.OrdList.Make Var.
Module Ext := MapET Var Typ Raw.

Include Ext.
Import Raw OP.P.

(** *** Morphism *)

#[global] 
Instance in_vctx : 
  Proper (Logic.eq ==> eq ==> iff) In.
Proof.
  repeat red; intros; split; intros;
  apply Equal_Eqdom in H0; eapply In_m in H0; eauto;
  apply H0; eauto. 
Qed.

#[global] 
Instance find_vctx : Proper (Logic.eq ==> eq ==> Logic.eq) find.
Proof. repeat red; intros; subst. now rewrite H0. Qed.

#[global] 
Instance Empty_vctx : Proper (eq ==> iff) Empty.
Proof. red; red; intros; now apply Empty_eq_spec. Qed.

#[export] 
Instance Add_vctx : 
Proper (Var.eq ==> Typ.eq ==> eq ==> eq ==> iff) (@Add Typ.t).
Proof. 
  red; red; red; red; red; intros. unfold Typ.eq in *; subst.
  rewrite H. unfold Add in *. rewrite H1; rewrite H2. 
  split; intros; auto.
Qed.

#[global] 
Instance add_vctx : 
Proper (Var.eq ==> Typ.eq ==> eq ==> eq) (@add Typ.t).
Proof. 
 red; red; red; red; red; intros; subst; unfold Typ.eq in H0; subst.
 rewrite H1; now rewrite H. 
Qed. 

#[global] 
Instance Submap_vctx : Proper (eq ==> eq ==> iff) Submap.
Proof. 
  repeat red; intros; split; intros.
  - rewrite Submap_eq_left_spec in H1; eauto.
    rewrite Submap_eq_right_spec in H1; eauto.
  - rewrite <- Submap_eq_left_spec in H1; eauto.
    rewrite <- Submap_eq_right_spec in H1; eauto.
Qed.

End VContext.

(** *** Scope and Notations *)

Definition Γ := VContext.t.
Declare Scope vcontext_scope.
Delimit Scope vcontext_scope with vc.

Infix "⊆ᵥᵪ" := VContext.Submap (at level 20, no associativity). 
Infix "∈ᵥᵪ" := VContext.Raw.In (at level 20, no associativity). 
Notation "r '∉ᵥᵪ' Re" := (~ (VContext.Raw.In r Re)) (at level 20, no associativity). 
Notation "∅ᵥᵪ" := VContext.Raw.empty (at level 20, no associativity). 
Notation "'isEmptyᵥᵪ(' Re ')'" := (VContext.OP.P.Empty Re) (at level 20, no associativity). 
Notation "'Addᵥᵪ'" := (VContext.OP.P.Add) (at level 20, no associativity). 
Notation "R '⌊' x '⌋ᵥᵪ'"  := (VContext.Raw.find x R) (at level 15, x constr).
Notation "⌈ x ⤆ v '⌉ᵥᵪ' R"  := (VContext.Raw.add x v R) (at level 15, x constr, 
                                                                                v constr).
Notation "R ⌈ x ⩦ v '⌉ᵥᵪ'"  := (VContext.Raw.find x R = Some v) (at level 15, 
                                                                          x constr, v constr).
Notation "R ⌈ x ⩦ ⊥ '⌉ᵥᵪ'"  := (VContext.Raw.find x R = None) (at level 15, 
                                                                                x constr).

Infix "=" := VContext.eq : vcontext_scope.

(** *** Morphism *)


#[global] Instance eq_equiv_vctx : Equivalence VContext.eq.
          Proof. apply VContext.OP.P.Equal_equiv. Qed.

#[global] 
Instance in_vctx : 
  Proper (Logic.eq ==> VContext.eq ==> iff) (VContext.Raw.In).
Proof. apply VContext.in_vctx. Qed.

#[global] 
Instance find_vctx : 
  Proper (Logic.eq ==> VContext.eq ==> Logic.eq) (VContext.Raw.find).
Proof. apply VContext.find_vctx. Qed.

#[global] 
Instance Empty_vctx : Proper (VContext.eq ==> iff) (VContext.OP.P.Empty).
Proof. apply VContext.Empty_vctx. Qed.

#[global] 
Instance Add_vctx : 
Proper (Var.eq ==> Typ.eq ==> VContext.eq ==> VContext.eq ==> iff) 
                                                  (@VContext.OP.P.Add Typ.t).
Proof. apply VContext.Add_vctx. Qed. 

#[global] 
Instance add_vctx : 
Proper (Var.eq ==> Typ.eq ==> VContext.eq ==> VContext.eq) 
                                                          (@VContext.Raw.add Typ.t).
Proof. apply VContext.add_vctx. Qed. 

#[global] 
Instance Submap_vctx : 
  Proper (VContext.eq ==> VContext.eq ==> iff) VContext.Submap.
Proof. apply VContext.Submap_vctx. Qed.

#[global] 
Instance Submap_vctx_po : PreOrder VContext.Submap.
Proof. apply VContext.Submap_po. Qed. 