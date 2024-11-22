From Coq Require Import Lia Arith.PeanoNat Classical_Prop Morphisms SetoidList.
From Mecha Require Import Resource Resources Term Cell REnvironment SREnvironment.
From Mecha Require Evaluation_Transition.
From DeBrLevel Require Import LevelInterface MapLevelInterface MapLevel MapExtInterface MapExt.
Import ResourceNotations TermNotations CellNotations SREnvironmentNotations
       ResourcesNotations SetNotations REnvironmentNotations.

(** * Environment - Optional Resource Environment *)

(** ** Module - Optional Resource Environment *)

Module OREnvironment <: IsLvlET.

(** *** Definition *)

Include MapLvlD.MakeLvlMapLVLD OptTerm.
Import Raw Ext.

Module RE := REnvironment.
Module SRE := SREnvironment.
Module ET := Evaluation_Transition.
Open Scope renvironment_scope.

(** **** Update Resource environment *)

Definition update_globals_func (V : 𝐕) (r : resource) (_v : Λ) (or : t) : t :=
  match (V⌊r⌋)%re with 
    | Some (⩽ … v' ⩾) =>  add r (Some v') or
    |  _ => add r None or
  end.

Definition update_globals (e : 𝐄) (V : 𝐕) : t := 
  SRE.Raw.fold (update_globals_func V) e empty.

(** **** Halts *)
Definition halts (k : lvl) := For_all (fun _ d => OptTerm.prop_opt (ET.halts k) d).


(** *** Property *)


(** **** [update_globals] property *)

#[export] Instance update_globals_func_eq :
  Proper (RE.eq ==> Logic.eq ==> Logic.eq ==> eq ==> eq) update_globals_func.
Proof.
  intros V V' HeqV r' r Heqr v' v Heqv t t' Heqt; subst.
  unfold update_globals_func; rewrite HeqV.
  destruct (V' ⌊r⌋); try (destruct r0); now rewrite Heqt.
Qed.

#[export] Instance update_globals_func_eq' (V : 𝐕) :
  Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) (update_globals_func V).
Proof. intros r' r Heqr v' v Heqv t t' Heqt; subst; now rewrite Heqt. Qed.

Lemma update_globals_func_diamond (V : 𝐕) : SRE.Diamond eq (update_globals_func V).
Proof.
  intros r r' v v' t t1 t2 Hneq Heq1 Heq2.
  rewrite <- Heq1, <- Heq2; unfold update_globals_func.
  destruct (V ⌊r⌋); destruct (V ⌊r'⌋); try (destruct r0); try (destruct r1);
  now rewrite add_add_2. 
Qed.

Hint Resolve update_globals_func_eq update_globals_func_eq' 
              update_globals_func_diamond eq_equiv: core.

Lemma update_globals_Empty (e : 𝐄) (V : 𝐕) : 
  SRE.Empty e -> eq (update_globals e V) empty.
Proof. 
  intro HEmp; unfold update_globals. 
  rewrite SRE.fold_Empty; now auto.
Qed.

Lemma update_globals_Add_spec (r : resource) (v : Λ) (e e' : 𝐄) (V : 𝐕) : 
  ~ (r ∈ e)%sr -> SRE.Add r v e e' -> 
  eq (update_globals e' V) ((update_globals_func V) r v (update_globals e V)).
Proof. 
  intros HnIn HA; unfold update_globals. 
  now rewrite SRE.fold_Add; eauto. 
Qed.

Lemma update_globals_add_notin_spec (r : resource) (v : Λ) (e : 𝐄) (V : 𝐕) : 
  (r ∉ e)%sr -> 
  eq (update_globals (SRE.Raw.add r v e) V) ((update_globals_func V) r v (update_globals e V)).
Proof. 
  intros HnIn; rewrite update_globals_Add_spec; eauto.
  - reflexivity.
  - now unfold SRE.Add.
Qed.

#[export] Instance update_globals_eq : Proper (SRE.eq ==> RE.eq ==> eq) update_globals.
Proof.
  intros t t' Heqt V V' HeqV; revert t' Heqt V V' HeqV.
  induction t using SRE.map_induction; intros t' Heqt V V' HeqV.
  - rewrite update_globals_Empty; auto.
    rewrite Heqt in H.
    now rewrite update_globals_Empty; auto.
  - rewrite update_globals_Add_spec; eauto.
    assert (SRE.Add x e t1 t') by (unfold SRE.Add in *; now rewrite <- Heqt).
    symmetry; rewrite update_globals_Add_spec; eauto.
    rewrite (IHt1 t1) with (V' := V); try reflexivity.
    -- unfold update_globals_func.
       now rewrite HeqV.
    -- now symmetry.
Qed.

Lemma update_globals_keys (e : 𝐄) (V : 𝐕) : 
  forall (r : resource), (r ∈ e)%sr <-> In r (update_globals e V).
Proof.
  induction e using SRE.map_induction; intro r.
  - split.
    -- intros [v HM]; exfalso.
       apply (H r v HM).
    -- intro HIn.
       rewrite update_globals_Empty in HIn; auto.
       inversion HIn; inversion H0.
  - split.
    -- unfold SRE.Add in H0; rewrite H0; clear H0.
       rewrite SRE.add_in_iff; intros [Heq | HIn]; subst.
       + rewrite update_globals_add_notin_spec; auto.
         unfold update_globals_func.
         destruct (V ⌊r⌋); simpl.
         ++ destruct r0; rewrite add_in_iff; auto.
         ++ rewrite add_in_iff; auto.
       + rewrite update_globals_add_notin_spec; auto.
         unfold update_globals_func.
         destruct (V ⌊x⌋); simpl.
         ++ destruct r0; rewrite add_in_iff; right;
            now rewrite <- IHe1.
         ++ rewrite add_in_iff; right; now rewrite <- IHe1.
    -- unfold SRE.Add in H0; rewrite H0; clear H0.
       rewrite update_globals_add_notin_spec; auto.
       rewrite SRE.add_in_iff.
       unfold update_globals_func.
       destruct (V ⌊x⌋); simpl.
       + destruct r0; rewrite add_in_iff; intros [| HIn];
         auto; right; now rewrite IHe1.
       + rewrite add_in_iff; intros [| HIn];
         auto; right; now rewrite IHe1.
Qed.



(*
Lemma puts_Add_spec_1 (r : resource) (v : σ) (V : 𝐕) (t t' : t) : 
  ~ In r t -> Samples.Add r v t t' -> 
  Samples.Add r (puts_core_func r v V) (puts V t) (puts V t').
Proof.
  intros HIn HA; unfold Samples.Add in *.
  rewrite HA in *; rewrite puts_add_notin_spec; now auto. 
Qed.

Lemma puts_find_spec (r : resource) (v : σ) (V : 𝐕) (t : t) :
 find r t = Some v -> find r (puts V t) = Some (puts_core_func r v V).
Proof.
  revert r v; induction t using map_induction; intros r v Hfi.
  - exfalso; apply (H r v); now apply find_2.
  - unfold Samples.Add in H0; rewrite H0 in *; clear H0.
    rewrite puts_add_notin_spec; auto.
    destruct (Resource.eq_dec r x); subst.
    -- rewrite add_eq_o in Hfi; auto; inversion Hfi; subst; clear Hfi.
       unfold puts_func,puts_core_func.
       rewrite add_eq_o; auto. 
    -- unfold puts_func.
       rewrite add_neq_o in *; auto. 
Qed.

Lemma puts_Empty_iff (V : 𝐕) (t : t) : Empty t <-> Empty (puts V t).
Proof.
  split; intros HEmp.
  - apply puts_Empty with (V := V) in HEmp; rewrite HEmp.
    apply empty_1.
  - intros r v HM; apply find_1 in HM.
    apply puts_find_spec with (V := V) in HM.
    apply (HEmp r (puts_core_func r v V)).
    now apply find_2.
Qed.

Lemma puts_is_empty_iff (V : 𝐕) (t : t) : is_empty t = is_empty (puts V t).
Proof.
  destruct (is_empty t) eqn:H.
  - symmetry. apply is_empty_2 in H. apply is_empty_1. 
    now apply puts_Empty_iff.
  - destruct (is_empty (puts V t)) eqn:H1; auto.
    apply is_empty_2 in H1.
    rewrite <- puts_Empty_iff in H1.
    apply is_empty_1 in H1; rewrite H in *.
    inversion H1.
Qed.

Lemma puts_In_iff r (V : 𝐕) (t : t) : In r t <-> In r (puts V t).
Proof.
  revert r V; induction t using map_induction; intros r V.
  - split; intro HIn.
    -- exfalso; destruct HIn as [v HMap]. 
       now apply (H r v).
    -- exfalso; destruct HIn as [v HMap].
       rewrite puts_Empty_iff with (V := V) in H.
       now apply (H r v).
  - split; intro HIn;
    unfold Samples.Add in *; rewrite H0 in *; clear H0.
    -- rewrite puts_add_notin_spec; auto; unfold puts_func.
       rewrite add_in_iff in *.
       destruct HIn as [| HIn]; subst; auto.
       right; now rewrite <- IHt1.
    -- rewrite puts_add_notin_spec in HIn; auto.
       unfold puts_func in HIn. 
       rewrite add_in_iff in *.
       destruct HIn as [| HIn]; subst; auto.
       right; now rewrite (IHt1 r V).
Qed. 

Lemma puts_max_spec (V : 𝐕) (t : t) : max_key t = max_key (puts V t).
Proof.
  revert V; induction t using map_induction; intro V.
  - rewrite max_key_Empty_spec; auto.
    rewrite puts_Empty; auto.
  - unfold Samples.Add in *; rewrite H0 in *; clear H0.
    rewrite puts_add_notin_spec; auto; unfold puts_func.
    apply max_key_add_spec with (v := e) in H as HI; auto.
    destruct HI as [[Heq Hle] | [Heq Hgt]]; subst.
    -- rewrite max_key_add_ge_spec; auto.
       rewrite (IHt1 V) in Hle.
       rewrite max_key_add_ge_spec; auto.
       now rewrite <- puts_In_iff.
    -- rewrite max_key_add_lt_spec; auto.
       rewrite (IHt1 V) in Hgt.
       rewrite max_key_add_lt_spec; auto.
       now rewrite <- puts_In_iff.
Qed.

Lemma puts_new_spec (V : 𝐕) (t : t) : new_key t = new_key (puts V t).
Proof.
  unfold new_key; destruct (is_empty t) eqn:Hempt.
  - rewrite puts_is_empty_iff with (V := V) in Hempt.
    rewrite Hempt; reflexivity.
  - rewrite puts_is_empty_iff with (V := V) in Hempt.
    rewrite Hempt; f_equal; apply puts_max_spec.
Qed. *)

(** **** [halts] property *)

Lemma halts_update_globals (k : lvl) (e : 𝐄) (V : 𝐕) :
  SRE.halts k e -> RE.halts k V -> halts k (update_globals e V).
Proof.
  induction e using SRE.map_induction; intros Hlt HlV.
  - rewrite update_globals_Empty; auto.
    now apply For_all_Empty_spec.
  - unfold SRE.Add in *; rewrite H0 in *; clear H0.
    rewrite update_globals_add_notin_spec; auto; unfold update_globals_func.
    apply SRE.halts_add_iff in Hlt as [Hlt Hlt']; auto.
    destruct (V ⌊x⌋) eqn:Hfi; try (destruct r).
    -- apply For_all_add_spec; split; simpl; auto.
       now apply IHe1.
    -- apply For_all_add_spec; split; simpl.
       + apply HlV in Hfi; now simpl in *. 
       + now apply IHe1.
    -- apply For_all_add_spec; split; simpl; auto.
       now apply IHe1.
Qed.


(** **** Morphism *)

#[export] Instance in_ore : Proper (Logic.eq ==> eq ==> iff) In.
Proof. intros k' k Heqk rs rs' Heqrs; subst; now rewrite Heqrs. Qed.

#[export] Instance Add_ore : 
  Proper (Resource.eq ==> OptTerm.eq ==> eq ==> eq ==> iff) (@OREnvironment.Add OptTerm.t).
Proof.
  intros k' k Heqk d d' Heqd rs rs' Heqrs rs1 rs1' Heqrs1; unfold OREnvironment.Add.
  rewrite Heqk, Heqrs, Heqrs1.
  destruct d, d'; try inversion Heqd; subst; simpl in *; now auto.
Qed.

#[export] Instance add_sr : 
  Proper (Resource.eq ==> OptTerm.eq ==> eq ==> eq) (@OREnvironment.Raw.add OptTerm.t).
Proof.
  intros k' k Heqk d d' Heqd t t' Heqt; subst.
  rewrite Heqk, Heqt. destruct d,d'; now inversion Heqd.
Qed.

#[export] Instance halts_ore : Proper (Logic.eq ==> eq ==> iff) halts. 
Proof. unfold halts; intros m n Heqm rs rs' Heqrs; subst; now rewrite Heqrs. Qed.

End OREnvironment.

(** ---- *)

(** ** Notation - Virtual Resource Environment - Reader *)

Module OREnvironmentNotations.

(** *** Scope *)
Declare Scope orenv_scope.
Delimit Scope orenv_scope with or.

(** *** Notation *)
Definition o𝐄 := OREnvironment.t.

Notation "t '⁺'" := (OREnvironment.Ext.new_key t) (at level 16) : orenv_scope.
Notation "∅" := OREnvironment.Raw.empty (at level 0, no associativity) : orenv_scope. 
Notation "r '∉' t" := (~ (OREnvironment.Raw.In r t)) (at level 75, no associativity) : orenv_scope. 
Notation "'isEmpty(' t ')'" := (OREnvironment.Empty t) (at level 20, no associativity) : orenv_scope. 
Notation "'Add'" := (OREnvironment.Add) (at level 20, no associativity) : orenv_scope. 
Notation "t '⌊' x '⌋'"  := (OREnvironment.Raw.find x t) (at level 15, x constr) : orenv_scope.
Notation "'max(' t ')'"  := (OREnvironment.Ext.max_key t) (at level 15) : orenv_scope.
Notation "⌈ x ⤆ v '⌉' t" := (OREnvironment.Raw.add x v t) 
                             (at level 15, x constr, v constr) : orenv_scope.
Notation "'[⧐' lb '–' k ']' t" := (OREnvironment.shift lb k t) 
                                   (at level 65, right associativity) : orenv_scope.

Infix "⊆" := OREnvironment.Submap (at level 60, no associativity) : orenv_scope. 
Infix "∈" := OREnvironment.Raw.In (at level 60, no associativity) : orenv_scope. 
Infix "=" := OREnvironment.eq : orenv_scope.
Infix "∪" := OREnvironment.extend : orenv_scope.
Infix "⊩" := OREnvironment.valid (at level 20, no associativity) : orenv_scope.

(** *** Morphism *)

Import OREnvironment.

#[export] Instance equiv_or : Equivalence OREnvironment.eq := _.
#[export] Instance max_or : Proper (eq ==> Logic.eq) (Ext.max_key) := Ext.max_key_eq.
#[export] Instance new_or : Proper (eq ==> Logic.eq) (Ext.new_key) := Ext.new_key_eq.
#[export] Instance in_or : Proper (Logic.eq ==> OREnvironment.eq ==> iff) (OREnvironment.Raw.In) := _.
#[export] Instance find_or : Proper (Logic.eq ==> eq ==> Logic.eq) (Raw.find) := _.
#[export] Instance Empty_or : Proper (OREnvironment.eq ==> iff) (OREnvironment.Empty) := _.
#[export] Instance Add_or : 
  Proper (Resource.eq ==> OptTerm.eq ==> eq ==> eq ==> iff) (@OREnvironment.Add OptTerm.t) := _.
#[export] Instance add_or : 
  Proper (Resource.eq ==> OptTerm.eq ==> eq ==> eq) (@Raw.add OptTerm.t) := _.
#[export] Instance Submap_or : Proper (eq ==> eq ==> iff) Submap := _.
#[export] Instance Submap_or_po : PreOrder OREnvironment.Submap := Submap_po.
#[export] Instance valid_or : Proper (Logic.eq ==> OREnvironment.eq ==> iff) OREnvironment.valid := _.
#[export] Instance shift_or : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.
#[export] Instance halts_or: Proper (Logic.eq ==> OREnvironment.eq ==> iff) OREnvironment.halts := _.

End OREnvironmentNotations.