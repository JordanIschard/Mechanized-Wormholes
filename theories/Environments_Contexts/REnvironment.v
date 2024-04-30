From Coq Require Import Lia Arith.PeanoNat Classical_Prop.
From Mecha Require Import Resource Term Cell Evaluation (* RealResource *).
From DeBrLevel Require Import MapExtInterface MapExt.
From MMaps Require Import MMaps.


(** * Environment between resources and cells *)
Module REnvironment <: EqualityType.

Module Raw := MMaps.OrdList.Make Resource.
Module Ext := MapETLVL Cell Raw.

Include Ext.
Import Raw OP.P.

(** *** Definition *)


Definition For_all (P : resource -> Cell.t -> Prop) (V : REnvironment.t) := 
  forall r v, find r V = Some v -> P r v. 

Definition halts (V : REnvironment.t) := forall (r : resource) (v : 𝑣), 
 find r V = Some v -> halts (Cell.extract v).

Definition used r (V : REnvironment.t) := exists v, find r V = Some (⩽ … v ⩾).
Definition unused r (V : REnvironment.t) := exists v, find r V = Some (⩽ v … ⩾).

(** *** Halts *)

Lemma halts_add_spec : forall m x v,
  (Evaluation.halts (Cell.extract v)) /\ halts m -> halts (add x v m).
Proof.
  intros m x v [Hltv Hltm]; unfold halts; intros r v' Hfi.
  rewrite OP.P.add_o in Hfi; destruct (Resource.eq_dec x r); subst; inversion Hfi; subst; auto.
  apply Hltm in Hfi; auto.
Qed.

#[export]
Instance halts_eq : Proper (eq ==> iff) halts.
Proof.
  repeat red; intros; unfold halts; split; intros; apply (H0 r).
  - now rewrite H.
  - now rewrite <- H.
Qed.

(** *** Morphism *)

#[global] 
Instance in_renv : 
  Proper (Logic.eq ==> REnvironment.eq ==> iff) In.
Proof.
  repeat red; intros; split; intros;
  apply OP.P.Equal_Eqdom in H0; eapply OP.P.In_m in H0; eauto;
  apply H0; eauto. 
Qed.

#[global] 
Instance find_renv : Proper (Logic.eq ==> REnvironment.eq ==> Logic.eq) find.
Proof. repeat red; intros; subst. now rewrite H0. Qed.

#[global] 
Instance Empty_renv : Proper (REnvironment.eq ==> iff) OP.P.Empty.
Proof. red; red; intros; now apply Empty_eq_spec. Qed.

#[export] 
Instance Add_renv : 
Proper (Resource.eq ==> Cell.eq ==> REnvironment.eq ==> REnvironment.eq ==> iff) (@OP.P.Add Cell.t).
Proof. 
  red; red; red; red; red; intros. apply Cell.eq_leibniz in H0; subst. unfold Resource.eq in H.
  rewrite H. unfold OP.P.Add in *. split; intros; auto.
  - unfold Equal in *; intros. rewrite <- H2. rewrite H0. rewrite OP.P.add_m; eauto.
  - unfold Equal in *; intros. rewrite H2. rewrite H0. rewrite OP.P.add_m; eauto.
    now symmetry.
Qed.

#[global] 
Instance add_renv : 
Proper (Resource.eq ==> Cell.eq ==> REnvironment.eq ==> REnvironment.eq) 
                                                          (@add Cell.t).
Proof. 
 red; red; red; red; red; intros; subst; apply Cell.eq_leibniz in H0; subst.
 unfold Equal; intros; rewrite OP.P.add_m; eauto.
Qed. 

#[global] 
Instance Submap_env : 
  Proper (REnvironment.eq ==> REnvironment.eq ==> iff) Submap.
Proof. 
  repeat red; intros; split; intros.
  - rewrite Submap_eq_left_spec in H1; eauto.
    rewrite Submap_eq_right_spec in H1; eauto.
  - rewrite <- Submap_eq_left_spec in H1; eauto.
    rewrite <- Submap_eq_right_spec in H1; eauto.
Qed.

End REnvironment.


(** *** Scope and Notations *)

Declare Scope renvironment_scope.
Delimit Scope renvironment_scope with re.

Definition 𝓥 := REnvironment.t.

Infix "⊆ᵣᵦ" := REnvironment.Submap (at level 20, no associativity). 
Infix "∈ᵣᵦ" := REnvironment.Raw.In (at level 20, no associativity). 
Notation "r '∉ᵣᵦ' Re" := (~ (REnvironment.Raw.In r Re)) (at level 20, 
                                                                        no associativity). 
Notation "∅ᵣᵦ" := REnvironment.Raw.empty (at level 20, no associativity). 
Notation "'isEmptyᵣᵦ(' Re ')'" := (REnvironment.OP.P.Empty Re) (at level 20, no associativity). 
Notation "'Addᵣᵦ'" := (REnvironment.OP.P.Add) (at level 20, no associativity). 
Notation "'maxᵣᵦ(' R ')'"  := (REnvironment.Ext.max_key R) (at level 15).
Notation "'newᵣᵦ(' R ')'"  := (REnvironment.Ext.new_key R) (at level 15).
Notation "R '⌊' x '⌋ᵣᵦ'"  := (REnvironment.Raw.find x R) (at level 15, x constr).
Notation "⌈ x ⤆ v '⌉ᵣᵦ' R"  := (REnvironment.Raw.add x v R) (at level 15, 
                                                                          x constr, v constr).
Notation "R ⌈ x ⩦ v '⌉ᵣᵦ'"  := (REnvironment.Raw.find x R = Some v) (at level 15, 
                                                                                  x constr, 
                                                                                  v constr).
Notation "R ⌈ x ⩦ ⊥ '⌉ᵣᵦ'"  := (REnvironment.Raw.find x R = None) (at level 15, 
                                                                                    x constr).

Infix "=" := REnvironment.eq : renvironment_scope.

#[global]
Instance eq_equiv_re : Equivalence REnvironment.eq.
Proof. apply REnvironment.OP.P.Equal_equiv. Qed.

#[global] Instance max_re : Proper (REnvironment.eq ==> Logic.eq) (REnvironment.Ext.max_key).
          Proof. apply REnvironment.Ext.max_key_eq. Qed.

#[global] Instance new_re : Proper (REnvironment.eq ==> Logic.eq) (REnvironment.Ext.new_key).
          Proof. apply REnvironment.Ext.new_key_eq. Qed.
          
#[global] 
Instance in_renv : 
  Proper (Logic.eq ==> REnvironment.eq ==> iff) (REnvironment.Raw.In).
Proof. apply REnvironment.in_renv. Qed.

#[global] 
Instance find_renv : Proper (Logic.eq ==> REnvironment.eq ==> Logic.eq) 
                                                      (REnvironment.Raw.find).
Proof. apply REnvironment.find_renv. Qed.

#[global] 
Instance Empty_renv : Proper (REnvironment.eq ==> iff) (REnvironment.OP.P.Empty).
Proof. apply REnvironment.Empty_renv. Qed.

#[global] 
Instance Add_renv : 
Proper (Resource.eq ==> Cell.eq ==> REnvironment.eq ==> REnvironment.eq ==> iff) 
                                                  (@REnvironment.OP.P.Add Cell.t).
Proof. apply REnvironment.Add_renv. Qed. 

#[global] 
Instance add_renv : 
Proper (Resource.eq ==> Cell.eq ==> REnvironment.eq ==> REnvironment.eq) 
                                                          (@REnvironment.Raw.add Cell.t).
Proof. apply REnvironment.add_renv. Qed. 

#[global] 
Instance Submap_env : 
  Proper (REnvironment.eq ==> REnvironment.eq ==> iff) REnvironment.Submap.
Proof. apply REnvironment.Submap_env. Qed.

#[global] 
Instance Submap_env_po : PreOrder REnvironment.Submap.
Proof. apply REnvironment.Submap_po. Qed. 