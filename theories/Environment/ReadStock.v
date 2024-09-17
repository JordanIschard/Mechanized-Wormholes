From Coq Require Import Lia Arith.PeanoNat Morphisms.
From Mecha Require Import Resource Resources Term REnvironment Cell OverlayMap.
From DeBrLevel Require Import LevelInterface MapLevelInterface MapLevel MapExtInterface MapExt.
Import ResourceNotations TermNotations REnvironmentNotations CellNotations
       ResourcesNotations SetNotations.


(** * Environment - Virtual Resource Environment - Reader

  In the functional transition there are two kind of environment: the resource environment and the stock. The former, defined in [REnvironment.v], represents the local memory during an instant. The latter, defined in [Stock.v], keeps local resource names with their initial value. [ReadStock] is a part of the stock. It maps resource names with terms, i.e, it binds local resource names, used for a reading interaction, with their initial value.
*)

(** ** Module - Virtual Resource Environment - Reader *)
Module ReadStock <: IsLvlET.

Include OverlayMap Term.
Import Raw Ext.

Module ET := Evaluation_Transition.
Module RE := REnvironment.

(** *** Definition *)

(** **** Initialize an environment

  For each instant, local resource names that represent a reading interaction have their memory cells initialized as unused with a certain term. This function takes a reader environment [rs] and an environement [V] and produces an environment where all resource names in [rs] are initialized.
*)
Definition init_read_func (r : resource) (v : Λ) (V : 𝐕) := (⌈ r ⤆ ⩽ v … ⩾ ⌉ V)%re.

Definition init_read (rs : t) (V : 𝐕) := fold init_read_func rs V.

(** **** Halts 

  In the functional transition proofs, we assume that all elements in the virtual resource environment [W] halts. Thus, we define this property here with [For_all].
  An environment has the halting property if and only if each term in it halts. 
*)
Definition halts (k : lvl) := For_all (fun _ d => ET.halts k d).

(** *** Property *)

(** **** [extend] property *)
 
Lemma extend_Empty_left_spec (rs rs' : t) :
  Empty rs -> eq (extend rs rs') rs'.
Proof.
  intro HEmp; unfold extend.
  apply Empty_eq_spec in HEmp.
  rewrite fold_init; eauto.
  - apply fold_identity.
  - repeat red; intros; subst; now rewrite H1.
Qed.

Lemma extend_Empty_right_spec (rs rs' : t) :
  Empty rs' -> eq (extend rs rs') rs.
Proof. intro HEmp; unfold extend; now rewrite fold_Empty; eauto. Qed.

Lemma extend_add_right_spec (r : resource) (v : Λ) (rs rs' : t) :
  ~ (In r rs') -> eq (extend rs (add r v rs')) (add r v (extend rs rs')).
Proof.
  intro HnIn; unfold extend; rewrite fold_Add; eauto.
  - reflexivity.
  - intros k' k Heqk d' d Heqd c c' Heqc; subst; now rewrite Heqc.
  - apply diamond_add.
  - unfold ReadStock.Add; reflexivity.
Qed.

Lemma valid_extend_spec (k : lvl) (rs rs' : t) :
  valid k rs -> valid k rs' -> valid k (extend rs rs').
Proof.
  revert rs; induction rs' using map_induction; intros rs Hvrs Hvrs'.
  - rewrite extend_Empty_right_spec; auto.
  - unfold ReadStock.Add in H0; rewrite H0 in *; clear H0.
    rewrite extend_add_right_spec; auto.
    apply valid_add_notin_spec in Hvrs' as [Hvx [Hve Hvrs'1]]; auto.
    apply valid_add_spec; auto.
Qed.


(** **** [init_read] property *)

#[export] Instance init_read_func_proper :
 Proper (Logic.eq ==> Logic.eq ==> RE.eq ==> RE.eq) init_read_func.
Proof.
  intros k' k Heqk d' d Heqd V V' HeqV; subst; unfold init_read_func.
  now rewrite HeqV.
Qed.

Lemma init_read_func_diamond : Diamond RE.eq init_read_func.
Proof.
  unfold init_read_func; intros k k' d d' rs rs1 rs' Hneq Heq Heq'.
  rewrite <- Heq; rewrite <- Heq'.
  now rewrite RE.add_add_2; auto.
Qed.

#[local] Hint Resolve init_read_func_proper init_read_func_diamond RE.Equal_equiv : core.

Lemma init_read_Empty_spec (rs : t) (V : 𝐕) :
  Empty rs -> RE.eq (init_read rs V) V.
Proof.
  intro Hemp; unfold init_read.
  rewrite fold_Empty with (eqA := RE.eq); now auto.
Qed.

Lemma init_read_add_spec (r : resource) (v : Λ) (rs : t) (V : 𝐕) :
  ~ (In r rs) ->
  RE.eq (init_read (add r v rs) V) (⌈ r ⤆ (⩽ v … ⩾)⌉ (init_read rs V))%re. 
Proof.
  unfold init_read; intro HnIn.
  rewrite fold_Add with (eqA := RE.eq); eauto.
  - unfold init_read_func at 1; reflexivity.
  - red; reflexivity.
Qed.

#[export] Instance init_read_proper : Proper (eq ==> RE.eq ==> RE.eq) init_read.
Proof.
  intros rs rs' Heqrs V V' HeqV; unfold init_read.
  eapply fold_Proper with (eqA := RE.eq); now eauto.
Qed.  

Lemma init_read_find_spec (rs : t) (V : 𝐕) (r : resource) (v : 𝑣) :
  ((init_read rs V)⌊r⌋)%re = Some v -> In r rs \/ V⌊r⌋%re = Some v.
Proof.
  revert r v; induction rs using map_induction; intros r v Hfi.
  - rewrite init_read_Empty_spec in Hfi; auto.
  - unfold ReadStock.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_read_add_spec in Hfi; auto.
    rewrite RE.add_o in Hfi; destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- now rewrite add_in_iff; repeat left.
    -- rewrite add_in_iff.
       apply IHrs1 in Hfi as [HIn | Hfi]; auto.
Qed. 

Lemma init_read_in_iff  (rs : t) (V : 𝐕) (r : resource) :
  (r ∈ (init_read rs V))%re <-> In r rs \/ (r ∈ V)%re.
Proof.
  revert r; induction rs using map_induction; intro r; split.
  - rewrite init_read_Empty_spec; auto.
  - intros [HIn | HIn].
    -- destruct HIn as [v HM].
       exfalso; now apply (H r v).
    -- rewrite init_read_Empty_spec; auto.
  - intro HIn.
    unfold ReadStock.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_read_add_spec in HIn; auto.
    rewrite add_in_iff.
    apply RE.add_in_iff in HIn as [| HIn]; subst; auto.
    apply IHrs1 in HIn as [HIn | HIn]; auto.
  - unfold ReadStock.Add in H0; rewrite H0 in *; clear H0.
    rewrite add_in_iff.
    rewrite init_read_add_spec; auto.
    rewrite RE.add_in_iff.
    intros [[Heq | HIn] | HIn]; subst; auto; 
    right; rewrite IHrs1; auto.
Qed. 

Lemma init_read_unused (rs : t) (V : 𝐕) (r : resource) :
  In r rs -> REnvironment.unused r (init_read rs V).
Proof.
  revert r; induction rs using map_induction; intros r HIn.
  - exfalso; destruct HIn as [v HM]; now apply (H r v).
  - unfold ReadStock.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_read_add_spec; auto; 
    apply add_in_iff in HIn as [| HIn]; subst.
    -- apply RE.unused_add_eq_spec; now red.
    -- assert (Hneq : r <> x) by (intro; subst; contradiction).
       apply RE.unused_add_neq_spec; auto.
Qed.

(* Lemma init_read_Forall_unused : forall rsk V,
  REnvironment.For_all (fun _ v => Cell.unused v) V ->
  REnvironment.For_all (fun _ v => Cell.unused v) (init_read rsk V).
Proof.
  unfold REnvironment.For_all in *; intros.
  apply init_read_find_spec in H0 as H0'; destruct H0'; auto.
  - eapply init_read_unused in H1; eauto.
    destruct H1; rewrite H0 in H1; inversion H1. now simpl.
  - eapply H; eauto.
Qed. *)


(** **** [halts] property *)

Lemma halts_union_spec (k : lvl) (rs rs': t) :
  halts k rs /\ halts k rs' -> halts k (extend rs rs').
Proof.
  unfold halts; intros [HFa HFa'] r v Hfi.
  apply find_2 in Hfi. 
  apply extend_mapsto_iff in Hfi as [HM | [HM _]]; apply find_1 in HM.
  - now apply (HFa' r).
  - now apply (HFa r).
Qed.

Lemma halts_add_spec (k : lvl) (r : resource) (v : Λ) (rs : t) :
  (ET.halts k v) /\ halts k rs -> halts k (add r v rs).
Proof.
  intros [Hltv Hlts] r' v' Hfi.
  rewrite add_o in Hfi; destruct (Resource.eq_dec r r') as [| Hneq]; subst.
  - inversion Hfi; subst; auto.
  - apply Hlts in Hfi; auto.
Qed.

Lemma halts_add_iff (k : lvl) (r : resource) (v : Λ) (rs : t) :
  ~ (In r rs) -> 
  halts k (add r v rs) <-> (ET.halts k v) /\ halts k rs.
Proof.
  intros HIn; split.
  - unfold halts; intro HFa.
    apply For_all_add_notin_spec in HFa; auto.
  - apply halts_add_spec.
Qed.

Lemma halts_weakening (m n : lvl) (rs : t) : 
  m <= n -> halts m rs -> halts n (shift m (n - m) rs).
Proof.
  intros Hle Hlt r v Hfi. 
  apply shift_find_e_spec_1 in Hfi as HI.
  destruct HI as [[r' Heqr'] [v' Heqv']]; subst.
  rewrite <- shift_find_iff in Hfi. 
  apply ET.halts_weakening; auto; apply Hlt in Hfi; now simpl in *.
Qed.

Lemma halts_weakening_1 (m n : lvl) (rs : t) : 
  halts m rs -> halts (m + n) (shift m n rs).
Proof.
  intro Hlt; replace n with ((m + n) - m) at 2 by lia.
  apply halts_weakening; auto; lia.
Qed.

Lemma halts_init_read (k : lvl) (rs : t) (V : 𝐕) :
  halts k rs -> RE.halts k V -> RE.halts k (init_read rs V).
Proof.
  induction rs using map_induction; intros Hltrs HltV.
  - now rewrite init_read_Empty_spec.
  - unfold ReadStock.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_read_add_spec; auto.
    apply RE.halts_add_spec; simpl.
    apply halts_add_iff in Hltrs as [Hkte Htlrs1]; auto. 
Qed.

(** **** Morphism *)

#[export] Instance in_readstock : Proper (Logic.eq ==> eq ==> iff) In.
Proof. intros k' k Heqk rs rs' Heqrs; subst; now rewrite Heqrs. Qed.

#[export] Instance Add_readstock : 
  Proper (Resource.eq ==> Term.eq ==> eq ==> eq ==> iff) (@ReadStock.Add Term.t).
Proof.
  intros k' k Heqk d d' Heqd rs rs' Heqrs rs1 rs1' Heqrs1; unfold ReadStock.Add.
  now rewrite Heqk, Heqd, Heqrs, Heqrs1. 
Qed.

#[export] Instance halts_readstock : Proper (Logic.eq ==> eq ==> iff) halts. 
Proof. unfold halts; intros m n Heqm rs rs' Heqrs; subst; now rewrite Heqrs. Qed.

End ReadStock.

(** ---- *)

(** ** Notation - Virtual Resource Environment - Reader *)

Module ReadStockNotations.

(** *** Scope *)
Declare Scope rstock_scope.
Delimit Scope rstock_scope with rk.

(** *** Notation *)
Definition 𝐖ᵣ := ReadStock.t.

Notation "V '⁺'" := (ReadStock.Ext.new_key V) (at level 16) : rstock_scope.
Notation "∅" := ReadStock.Raw.empty (at level 0, no associativity) : rstock_scope. 
Notation "r '∉' Re" := (~ (ReadStock.Raw.In r Re)) (at level 75, no associativity) : rstock_scope. 
Notation "'isEmpty(' Re ')'" := (ReadStock.Empty Re) (at level 20, no associativity) : rstock_scope. 
Notation "'Add'" := (ReadStock.Add) (at level 20, no associativity) : rstock_scope. 
Notation "R '⌊' x '⌋'"  := (ReadStock.Raw.find x R) (at level 15, x constr) : rstock_scope.
Notation "'max(' R ')'"  := (ReadStock.Ext.max_key R) (at level 15) : rstock_scope.
Notation "⌈ x ⤆ v '⌉' R" := (ReadStock.Raw.add x v R) 
                             (at level 15, x constr, v constr) : rstock_scope.
Notation "'[⧐' lb '–' k ']' t" := (ReadStock.shift lb k t) 
                                   (at level 65, right associativity) : rstock_scope.

Infix "⊆" := ReadStock.Submap (at level 60, no associativity) : rstock_scope. 
Infix "∈" := ReadStock.Raw.In (at level 60, no associativity) : rstock_scope. 
Infix "=" := ReadStock.eq : rstock_scope.
Infix "∪" := ReadStock.extend : rstock_scope.
Infix "⊩" := ReadStock.valid (at level 20, no associativity) : rstock_scope.

(** *** Morphism *)

Import ReadStock.

#[export] Instance max_rk : Proper (eq ==> Logic.eq) (Ext.max_key) := Ext.max_key_eq.
#[export] Instance new_rk : Proper (eq ==> Logic.eq) (Ext.new_key) := Ext.new_key_eq.
#[export] Instance in_rk : Proper (Logic.eq ==> ReadStock.eq ==> iff) (ReadStock.Raw.In) := _.
#[export] Instance find_rk : Proper (Logic.eq ==> eq ==> Logic.eq) (Raw.find) := _.
#[export] Instance Empty_rk : Proper (ReadStock.eq ==> iff) (ReadStock.Empty) := _.
#[export] Instance Add_rk : 
  Proper (Resource.eq ==> Term.eq ==> eq ==> eq ==> iff) (@ReadStock.Add Term.t) := _.
#[export] Instance add_rk : 
  Proper (Resource.eq ==> Term.eq ==> eq ==> eq) (@Raw.add Term.t) := _.
#[export] Instance Submap_rk : Proper (eq ==> eq ==> iff) Submap := _.
#[export] Instance Submap_rk_po : PreOrder ReadStock.Submap := Submap_po.
#[export] Instance valid_rk : Proper (Logic.eq ==> ReadStock.eq ==> iff) ReadStock.valid := _.
#[export] Instance shift_rk : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.
#[export] Instance halts_rk: Proper (Logic.eq ==> ReadStock.eq ==> iff) ReadStock.halts := _.

End ReadStockNotations.