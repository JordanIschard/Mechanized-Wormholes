From Coq Require Import Lia.
Require Import Typ Resource.
From DeBrLevel Require Import MapExtInterface MapExt.
From MMaps Require Import MMaps.

(** * Context between resources and pairs of types *)
Module RContext <: EqualityType.

Module Raw := MMaps.OrdList.Make Resource.
Module Ext := MapET Resource PairTyp Raw.

Include Ext.
Import Raw OP.P.

#[global] 
Instance in_rctx : 
  Proper (Logic.eq ==> eq ==> iff) In.
Proof.
  repeat red; intros; split; intros;
  apply Equal_Eqdom in H0; eapply In_m in H0; eauto;
  apply H0; eauto. 
Qed.

#[global] 
Instance find_rctx : Proper (Logic.eq ==> eq ==> Logic.eq) find.
Proof. repeat red; intros; subst. now rewrite H0. Qed.

#[global] 
Instance Empty_rctx : Proper (eq ==> iff) Empty.
Proof. red; red; intros; now apply Empty_eq_spec. Qed.

#[export] 
Instance Add_rctx : 
Proper (Resource.eq ==> PairTyp.eq ==> eq ==> eq ==> iff) (@Add PairTyp.t).
Proof. 
  red; red; red; red; red; intros. apply PairTyp.eq_leibniz in H0; subst.
  rewrite H. unfold OP.P.Add in *. rewrite H1; rewrite H2. split; intros; auto.
Qed.

#[global] 
Instance add_rctx : 
Proper (Resource.eq ==> PairTyp.eq ==> eq ==> eq) (@add PairTyp.t).
Proof. 
 red; red; red; red; red; intros; subst; apply PairTyp.eq_leibniz in H0; subst.
 rewrite H1; now rewrite H. 
Qed. 

#[global] 
Instance Submap_rctx : 
  Proper (eq ==> eq ==> iff) Submap.
Proof. 
  repeat red; intros; split; intros.
  - rewrite Submap_eq_left_spec in H1; eauto.
    rewrite Submap_eq_right_spec in H1; eauto.
  - rewrite <- Submap_eq_left_spec in H1; eauto.
    rewrite <- Submap_eq_right_spec in H1; eauto.
Qed.

End RContext.

(** *** Scope and Notations *)
Declare Scope rcontext_scope.
Delimit Scope rcontext_scope with rc.

Definition ℜ := RContext.t.

Infix "⊆ᵣᵪ" := RContext.Submap (at level 20, no associativity). 
Infix "∈ᵣᵪ" := RContext.Raw.In (at level 20, no associativity). 
Notation "r '∉ᵣᵪ' Re" := (~ (RContext.Raw.In r Re)) (at level 20, no associativity). 
Notation "∅ᵣᵪ" := RContext.Raw.empty (at level 20, no associativity). 
Notation "'isEmptyᵣᵪ(' Re ')'" := (RContext.OP.P.Empty Re) (at level 20, no associativity). 
Notation "'Addᵣᵪ'" := (RContext.OP.P.Add) (at level 20, no associativity). 
Notation "R '⌊' x '⌋ᵣᵪ'"  := (RContext.Raw.find x R) (at level 15, x constr).
Notation "⌈ x ⤆ v '⌉ᵣᵪ' R"  := (RContext.Raw.add x v R) (at level 15, x constr, 
                                                                                v constr).
Notation "R ⌈ x ⩦ v '⌉ᵣᵪ'"  := (RContext.Raw.find x R = Some v) (at level 15, 
                                                                          x constr, v constr).
Notation "R ⌈ x ⩦ ⊥ '⌉ᵣᵪ'"  := (RContext.Raw.find x R = None) (at level 15, 
                                                                                x constr).

Infix "=" := RContext.eq : rcontext_scope.

(** *** Morphisms *)

#[global] Instance eq_equiv : Equivalence RContext.eq.
          Proof. apply RContext.OP.P.Equal_equiv. Qed.

#[global] 
Instance in_rctx : 
  Proper (Logic.eq ==> RContext.eq ==> iff) (RContext.Raw.In).
Proof. apply RContext.in_rctx. Qed.

#[global] 
Instance find_rctx : Proper (Logic.eq ==> RContext.eq ==> Logic.eq) 
                                                      (RContext.Raw.find).
Proof. apply RContext.find_rctx. Qed.

#[global] 
Instance Empty_rctx : Proper (RContext.eq ==> iff) (RContext.OP.P.Empty).
Proof. apply RContext.Empty_rctx. Qed.

#[global] 
Instance Add_rctx : 
Proper (Resource.eq ==> PairTyp.eq ==> RContext.eq ==> RContext.eq ==> iff) 
                                                  (@RContext.OP.P.Add PairTyp.t).
Proof. apply RContext.Add_rctx. Qed. 

#[global] 
Instance add_rctx : 
Proper (Resource.eq ==> PairTyp.eq ==> RContext.eq ==> RContext.eq) 
                                                          (@RContext.Raw.add PairTyp.t).
Proof. apply RContext.add_rctx. Qed. 

#[global] 
Instance Submap_rctx : 
  Proper (RContext.eq ==> RContext.eq ==> iff) RContext.Submap.
Proof. apply RContext.Submap_rctx. Qed.

#[global] 
Instance Submap_po : PreOrder RContext.Submap.
Proof. apply RContext.Submap_po. Qed. 