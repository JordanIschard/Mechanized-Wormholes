From Coq Require Import Structures.Equalities Lists.List Classes.Morphisms Logic.FunctionalExtensionality.
Require Import Typ Var.
From DeBrLevel Require Import MapExt.
From MMaps Require Import MMaps.

(** * Context between variables and types *)
Module Context.

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

End Context.

(** *** Scope and Notations *)

Definition Γ := Context.t.
Declare Scope context_scope.
Delimit Scope context_scope with γ.

Infix "⊆ᵧ" := Context.Submap (at level 20, no associativity). 
Infix "∈ᵧ" := Context.Raw.In (at level 20, no associativity). 
Notation "r '∉ᵧ' Re" := (~ (Context.Raw.In r Re)) (at level 20, no associativity). 
Notation "∅ᵧ" := Context.Raw.empty (at level 20, no associativity). 
Notation "'isEmptyᵧ(' Re ')'" := (Context.OP.P.Empty Re) (at level 20, no associativity). 
Notation "'Addᵧ'" := (Context.OP.P.Add) (at level 20, no associativity). 
Notation "R '⌊' x '⌋ᵧ'"  := (Context.Raw.find x R) (at level 15, x constr).
Notation "⌈ x ⤆ v '⌉ᵧ' R"  := (Context.Raw.add x v R) (at level 15, x constr, 
                                                                                v constr).
Notation "R ⌈ x ⩦ v '⌉ᵧ'"  := (Context.Raw.find x R = Some v) (at level 15, 
                                                                          x constr, v constr).
Notation "R ⌈ x ⩦ ⊥ '⌉ᵧ'"  := (Context.Raw.find x R = None) (at level 15, 
                                                                                x constr).

Infix "=" := Context.eq : context_scope.

(** *** Morphism *)


#[global] Instance eq_equiv_vctx : Equivalence Context.eq.
          Proof. apply Context.OP.P.Equal_equiv. Qed.

#[global] 
Instance in_vctx : 
  Proper (Logic.eq ==> Context.eq ==> iff) (Context.Raw.In).
Proof. apply Context.in_vctx. Qed.

#[global] 
Instance find_vctx : 
  Proper (Logic.eq ==> Context.eq ==> Logic.eq) (Context.Raw.find).
Proof. apply Context.find_vctx. Qed.

#[global] 
Instance Empty_vctx : Proper (Context.eq ==> iff) (Context.OP.P.Empty).
Proof. apply Context.Empty_vctx. Qed.

#[global] 
Instance Add_vctx : 
Proper (Var.eq ==> Typ.eq ==> Context.eq ==> Context.eq ==> iff) 
                                                  (@Context.OP.P.Add Typ.t).
Proof. apply Context.Add_vctx. Qed. 

#[global] 
Instance add_vctx : 
Proper (Var.eq ==> Typ.eq ==> Context.eq ==> Context.eq) 
                                                          (@Context.Raw.add Typ.t).
Proof. apply Context.add_vctx. Qed. 

#[global] 
Instance Submap_vctx : 
  Proper (Context.eq ==> Context.eq ==> iff) Context.Submap.
Proof. apply Context.Submap_vctx. Qed.

#[global] 
Instance Submap_vctx_po : PreOrder Context.Submap.
Proof. apply Context.Submap_po. Qed. 