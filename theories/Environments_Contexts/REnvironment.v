From Coq Require Import Lia Arith.PeanoNat Classical_Prop.
From Mecha Require Import Resource Term Cell Evaluation RealResource.
From DeBrLevel Require Import MapExtInterface MapExt.
From MMaps Require Import MMaps.


(** * Environment between resources and cells *)
Module REnvironment <: EqualityType.

Module Raw := MMaps.OrdList.Make Resource.
Module Ext := MapETLVL Cell Raw.

Include Ext.
Import Raw OP.P.

(** *** Definition *)

Definition embeds_func V v := add (new_key V) (⩽ v … ⩾) V.

Definition embeds_func_revert v V := embeds_func V v. 

Definition embeds_gen (V : REnvironment.t) (l : list Λ) := 
  List.fold_left embeds_func l V.

Definition For_all (P : resource -> Cell.t -> Prop) (V : REnvironment.t) := 
  forall r v, find r V = Some v -> P r v. 

Definition embeds := embeds_gen empty. 

Definition extracts (V : REnvironment.t) : list (option Λ) :=
  List.map (fun x =>  match (find x V) with
                        | Some (⩽ … v ⩾) => Some v
                        | Some _ => None
                        | None   => None
                      end) (seq 0 (max_key V)).

Definition halts (V : REnvironment.t) := forall (r : resource) (v : 𝑣), 
 find r V = Some v -> halts (Cell.extract v).

Definition used r (V : REnvironment.t) := exists v, find r V = Some (⩽ … v ⩾).
Definition unused r (V : REnvironment.t) := exists v, find r V = Some (⩽ v … ⩾).

(** *** Embedding *)

Lemma embedding_func_new_spec : forall V v,
 new_key (embeds_func_revert v V) = S (new_key V).
Proof.
  unfold embeds_func_revert, embeds_func; intros.
  rewrite new_key_add_spec_1; auto; apply new_key_notin_spec; lia.
Qed.

Lemma embedding_func_in_spec : forall V v r,
  In r (embeds_func_revert v V) <-> r = (new_key V) \/ In r V.
Proof. 
  split; intros; unfold embeds_func_revert,embeds_func in *.
  - rewrite add_in_iff in H; destruct H; auto.
  - destruct H; rewrite add_in_iff; subst; auto.
Qed.

Lemma embedding_func_unused_spec : forall r x V,
  unused r V -> unused r (embeds_func_revert x V).
Proof.
  intros; unfold embeds_func_revert,embeds_func.
  destruct (Resource.eq_dec r (new_key V)); subst.
  - simpl. exists x; rewrite add_eq_o; auto.
  - destruct H; exists x0. rewrite add_neq_o; auto.
Qed.

Lemma embedding_gen_new_spec : forall l V,
  (length l) + new_key V = new_key (embeds_gen V l).
Proof.
  intros; unfold embeds_gen; rewrite <- fold_left_rev_right. 
  fold embeds_func_revert. revert V.
  induction l using rev_ind; intro; simpl; auto.
  rewrite rev_unit; simpl. rewrite app_length; simpl.
  rewrite embedding_func_new_spec; rewrite <- IHl; lia.
Qed.

Lemma embedding_gen_find_eq_spec : forall V x,
  find (new_key V) (embeds_func_revert x V) = Some (⩽ x … ⩾).
Proof.
  unfold embeds_func_revert, embeds_func; intros.
  rewrite add_eq_o; auto.
Qed.

Lemma embedding_gen_unused : forall l V,
  (forall r, In r V -> unused r V) ->
  forall r, In r (embeds_gen V l) -> unused r (embeds_gen V l).
Proof.
  intros; unfold embeds_gen in *; rewrite <- fold_left_rev_right in *.
  fold embeds_func_revert in *. revert V r H H0.
  induction l using rev_ind; intros V r H HIn; simpl in *; auto.
  rewrite rev_unit in *; simpl in *.
  rewrite embedding_func_in_spec in HIn. destruct HIn; subst.
  - exists x. apply embedding_gen_find_eq_spec.
  - apply IHl in H0 as H0'; auto. now apply embedding_func_unused_spec.
Qed.

Lemma embedding_unused : forall l,
  forall r, In r (embeds l) -> unused r (embeds l).
Proof. 
  intros; unfold embeds in *; apply embedding_gen_unused; auto.
  intros; inversion H0; inversion H1.
Qed.


Lemma embedding_Forall_unused : forall l V,
  For_all (fun _ v => Cell.unused v) V ->
  For_all (fun _ v => Cell.unused v) (embeds_gen V l).
Proof.
  unfold For_all; intros. assert (In r (embeds_gen V l)).
  { exists v; now apply find_2. }
  apply embedding_gen_unused in H1.
  - destruct H1. rewrite H0 in H1; now inversion H1.
  - intros. destruct H2. apply find_1 in H2. apply H in H2 as H2'.
    destruct x eqn:Heq.
    -- now exists λ.
    -- contradiction.
Qed. 


(** *** Halts *)

Lemma halts_add_spec : forall m x v,
  (Evaluation.halts (Cell.extract v)) /\ halts m -> halts (add x v m).
Proof.
  intros m x v [Hltv Hltm]; unfold halts; intros r v' Hfi.
  rewrite OP.P.add_o in Hfi; destruct (Resource.eq_dec x r); subst; inversion Hfi; subst; auto.
  apply Hltm in Hfi; auto.
Qed.

Lemma halts_next_gen l V :
  halts V -> RealResources.halts l -> 
  halts (embeds_gen V (RealResources.nexts l)).
Proof.
  intros; unfold embeds_gen; rewrite <- fold_left_rev_right; fold embeds_func_revert.
  revert V H H0; induction l using rev_ind; intros; simpl in *; auto.
  unfold RealResources.nexts; rewrite map_app; simpl. rewrite rev_unit in *; simpl.
  unfold embeds_func_revert,embeds_func; simpl.
  apply halts_add_spec; split.
  - simpl. unfold RealResources.halts in *; rewrite Forall_app in H0; destruct H0.
    apply Forall_cons_iff in H1; destruct H1. now apply RealResource.halts_next.
  - unfold RealResources.nexts in *; apply IHl; auto. unfold RealResources.halts in *.
    rewrite Forall_app in H0; now destruct H0.
Qed.

Lemma halts_nexts l :
  RealResources.halts l ->  halts (embeds (RealResources.nexts l)).
Proof.
  intros; unfold embeds; apply halts_next_gen; auto; unfold halts; intros; inversion H0.
Qed.

Lemma halts_extract V : 
  halts V -> 
  List.Forall (fun v => match v with Some v => Evaluation.halts v | _ => True end) (extracts V).
Proof. Admitted.

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