From Coq Require Import Lia Morphisms Lists.List Arith Lists.Streams.
From Mecha Require Import Resource Resources Term Typ Cell VContext RContext  
                          Type_System Evaluation_Transition Functional_Transition 
                          REnvironment SREnvironment ResourcesMap Stock OREnvironment.
Import ResourceNotations TermNotations TypNotations CellNotations ListNotations
       VContextNotations RContextNotations REnvironmentNotations OREnvironmentNotations
       SREnvironmentNotations ResourcesNotations SetNotations StockNotations ResourcesMapNotations.

(** * Semantics - Temporal

  Wormholes’s dynamic semantics is split in three sets of transition rules: the evaluation transition, defined in [Evaluation_Transition.v], which extends standard β-reduction; the functional transition which performs the logical instant, defined in [Functional_Transition.v], and the temporal transition which corresponds to the reactivity of the program: it initializes the resources values, performs the instant via the functional transition and updates the system. In this file, we focus on the temporal transition.
*)


(** ** Definition - Temporal *)

Module RE := REnvironment.
Module SRE := SREnvironment.
Module RM := ResourcesMap.
Module ORE := OREnvironment.
Module ST := Stock.
Module RC := RContext.


(** *** Well-formed environments-context *)

Definition well_formed_in_ec (Rc : ℜ) (S : 𝐄) (W : 𝐖) :=
  (forall (r : resource), (r ∈ Rc)%rc <->  (r ∈ W)%sk \/ (r ∈ S)%sr) /\ 
  (forall (r : resource), ((r ∈ W)%sk -> (r ∉ S)%sr) /\ ((r ∈ S)%sr -> (r ∉ W)%sk)) /\
  (Rc⁺ ⊩ Rc)%rc /\ (S⁺ ⊩ S)%sr /\ (W⁺ ⊩ W)%sk /\
  (forall (r : resource) (α : πΤ) (v : Λ), Rc⌊r⌋%rc = Some α -> 
           (S⌊r⌋%sr = Some v -> 
            (∅)%vc ⋅ Rc ⊢ {Term.shift (S⁺)%sr ((max (S⁺)%sr (W⁺)%sk) - (S⁺)%sr) v} ∈ {snd α}) /\
           (W⌊r⌋%sk = Some v -> (∅)%vc ⋅ Rc ⊢ v ∈ {snd α})) /\
  (~ ST.Empty W -> (W⁺)%sk = (Rc⁺)%rc /\ (W⁺)%sk > (S⁺)%sr) /\
  (forall (r : resource) (α : πΤ), 
                    (r ∈ (ST.writers W))%rm -> Rc⌊r⌋%rc = Some α -> (snd α) = <[𝟙]>) /\ 
  (forall r : resource, (r ∈ ST.readers W)%sr -> exists r' : resource, ((ST.writers W ⌊ r' ⌋)%rm = Some r))%type .


Definition well_formed_out_ec (Rc : ℜ) (S : o𝐄) (W : 𝐖) :=
  (forall (r : resource), (r ∈ Rc)%rc <-> (r ∈ W)%sk \/ (r ∈ S)%or) /\
  (forall (r : resource), ((r ∈ W)%sk -> (r ∉ S)%or) /\ ((r ∈ S)%or -> (r ∉ W)%sk)) /\
  (Rc⁺ ⊩ Rc)%rc /\ ((Rc⁺)%rc ⊩ S)%or /\ (W⁺ ⊩ W)%sk /\ 
  (~ ST.Empty W -> (W⁺)%sk = (Rc⁺)%rc) /\ 
  (forall (r : resource) (α : πΤ) (v : Λ), Rc⌊r⌋%rc = Some α -> 
                                           (W⌊r⌋%sk = Some v -> (∅)%vc ⋅ Rc ⊢ v ∈ {snd α})) /\
  (forall (r : resource) (α : πΤ), 
                    (r ∈ (ST.writers W))%rm -> Rc⌊r⌋%rc = Some α -> (snd α) = <[𝟙]>) /\ 
  (forall r : resource, (r ∈ ST.readers W)%sr -> exists r' : resource, ((ST.writers W ⌊ r' ⌋)%rm = Some r))%type .


Notation "'WFᵢₙ(' Rc , S , W )" := (well_formed_in_ec Rc S W) (at level 50).
Notation "'WFₒᵤₜ(' Rc , S , W )" := (well_formed_out_ec Rc S W) (at level 50).


(** *** Temporal transition *)

(** **** Initialize the input resource environment 

  The input resource environment consists of locals resources (from W) and global resources (from S). Global resources, at the first instant, are well formed under S. After that, they must be shift in order to be well formed under the maximum between W⁺ and S⁺ because W may contains local resources which are, by construction, greater than global resources. 
*)
Definition init_input_env (S : 𝐄) (W : 𝐖) : 𝐕 :=
  ST.init_locals W (SRE.init_globals (SRE.shift (S⁺)%sr ((max (S⁺)%sr (W⁺)%sk) - (S⁺)%sr) S)).

Definition temporal (S : 𝐄) (S' : o𝐄) (P P' : Λ) (W W' : 𝐖) :=

  (** (1) Initialize the local memory [Vin] with global and local resources. *)
  let Vin := init_input_env S W in

  exists (Vout : 𝐕) Wnew _tv,
  (** (2) Perform the instant with the functional transition. *)                  
  ⪡ Vin ; unit ; P ⪢ ⭆ ⪡ Vout ; _tv ; P' ; Wnew ⪢ /\

  (** (3) Update the global and local resources. *)               
  (S' = ORE.update_globals ([⧐ (S⁺)%sr – (Vout⁺ - (S⁺)%sr)%re] S)%sr Vout)%or /\
  (W' = (ST.update_locals (([⧐ (W⁺)%sk – (Vout⁺ - (W⁺)%sk)%re] W) ∪ Wnew) Vout))%sk.

Notation "'⟦' S ';' W ';' P '⟧' '⟾' '⟦' S1 ';' W1 ';' P1 '⟧'" := (temporal S S1 P P1 W W1) 
(at level 30, S constr, S1 constr, P custom wh, P1 custom wh, W constr, W1 constr, no associativity).

(** ---- *)

(** ** Property - Temporal *)

Lemma temporal_preserves_global_keys (S : 𝐄) (S' : o𝐄) (P P' : Λ) (W W' : 𝐖) :
  ⟦S ; W ; P⟧ ⟾ ⟦S' ; W' ; P'⟧ -> (forall (k : resource), (k ∈ S)%sr <-> (k ∈ S')%or). 
Proof.
  intros [Vin [Wnew [_tv [_ [Heq _]]]]] k.
  rewrite Heq; rewrite <- ORE.update_globals_in_iff.
  now rewrite SRE.shift_in_new_key.
Qed.

Lemma temporal_preserves_local_keys (S : 𝐄) (S' : o𝐄) (P P' : Λ) (W W' : 𝐖) :
  ⟦S ; W ; P⟧ ⟾ ⟦S' ; W' ; P'⟧ -> (forall (k : resource), (k ∈ W)%sk -> (k ∈ W')%sk).
Proof. 
  intros [Vout [Wnew [_tv [HfT [_ Heq]]]]] k HIn.
  rewrite Heq; clear Heq.
  rewrite ST.update_locals_in_iff.
  rewrite ST.union_in_iff; left.
  rewrite ST.shift_new_key_in_iff; auto.
Qed.

(** *** [init_input_env] property *)

Lemma init_input_env_in_iff (S: 𝐄) (W: 𝐖) (r: resource) : 
  (r ∈ W)%sk \/ (r ∈ S)%sr <-> r ∈ init_input_env S W.
Proof.
  unfold init_input_env.
  rewrite ST.init_locals_in_iff.
  rewrite SRE.init_globals_in_iff.
  now rewrite SRE.shift_in_new_key.
Qed.

Lemma init_input_env_new_key (S: 𝐄) (W: 𝐖) :
  (init_input_env S W)⁺ = max (S⁺)%sr (W⁺)%sk.
Proof.
  unfold init_input_env.
  rewrite ST.init_locals_new_key.
  replace (Nat.max (S ⁺)%sr (W ⁺)%sk) with (Nat.max (W ⁺)%sk (S ⁺)%sr) by lia.
  f_equal.
  rewrite SRE.init_globals_new_key.
  rewrite SRE.shift_new_refl; auto.
Qed.

(** *** [eqDom] properties *)


Lemma TT_EqDom_Empty (Rc : ℜ) (S : 𝐄) (W : 𝐖) :
  (forall r : resource, (r ∈ Rc)%rc <-> (r ∈ W)%sk \/ (r ∈ S)%sr) -> 
  RC.Empty Rc <-> (SRE.Empty S) /\ (ST.Empty W).
Proof.
  intro HIn; split.
  - intros HEmp; split.
    -- intros k v HM.
       assert ((k ∈ W)%sk \/ (k ∈ S)%sr).
       + right; now exists v.
       + rewrite <- HIn in H.
         destruct H as [v' HM'].
         apply (HEmp k v' HM').
    -- apply ST.Empty_notin; intros r HIn'.
       assert ((r ∈ W)%sk \/ (r ∈ S)%sr) by now left.
       rewrite <- HIn in H.
       destruct H as [v' HM'].
       apply (HEmp r v' HM').
  - intros [HEmpS HEmpW] k v HM.
    assert (k ∈ Rc)%rc by now exists v.
    rewrite HIn in H.
    destruct H as [HIn' | [v' HM']].
    -- revert HIn'.
       now apply ST.Empty_notin_1.
    -- apply (HEmpS k v' HM').
Qed. 

Lemma TT_EqDom_new (Rc : ℜ) (S : 𝐄) (W : 𝐖) :
  (forall r : resource, (r ∈ Rc)%rc <-> (r ∈ W)%sk \/ (r ∈ S)%sr) ->  
  (Rc⁺)%rc = max (S⁺)%sr (W⁺)%sk.
Proof.
  revert S W.
  induction Rc using RC.map_induction; intros S W HeqDom.
  - rewrite RC.Ext.new_key_Empty; auto.
    rewrite (TT_EqDom_Empty Rc S W HeqDom) in H.
    destruct H as [HEmp HEmp'].
    rewrite SRE.Ext.new_key_Empty; auto.
    rewrite ST.new_key_Empty; auto.
  - unfold RC.Add in H0; rewrite H0 in *.
    rewrite RC.Ext.new_key_add_max; auto.
    assert (HIn: (x ∈ Rc2)%rc).
    { rewrite H0, RC.add_in_iff; now left. }
    destruct (SRE.In_dec S x) as [HInS | HnInS].
    -- destruct (ST.In_dec x W) as [HInW | HnInW]. 
       + destruct HInS as [v Hfi].
         apply SRE.find_1 in Hfi.
         apply SRE.add_id in Hfi as Heq.
         rewrite <- Heq; clear Heq.
         rewrite <- SRE.add_remove_1.
         rewrite SRE.Ext.new_key_add_max.
         destruct W as [rW wW].
         destruct HInW as [HInrW | HInwW].
         ++ destruct (RM.In_dec wW x) as [[v1 HM] | HnInwW].
            * simpl in HInrW; unfold ST.new_key in *;
              simpl (Stock.readers (rW,wW));
              simpl (Stock.writers (rW,wW)).
              destruct HInrW as [v' Hfi'].
              apply SRE.find_1 in Hfi'.
              apply SRE.add_id in Hfi' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- SRE.add_remove_1.
              rewrite SRE.Ext.new_key_add_max.
              apply RM.find_1 in HM.
              apply RM.add_id in HM as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- RM.add_remove_1.
              rewrite RM.Ext.new_key_add_max.
              rewrite (IHRc1 (SRE.Raw.remove x S) (SRE.Raw.remove x rW,RM.Raw.remove x wW)).
              ** unfold ST.new_key. 
                 simpl (Stock.readers (SRE.Raw.remove x rW, RM.Raw.remove x wW));
                 simpl (Stock.writers (SRE.Raw.remove x rW, RM.Raw.remove x wW)); lia.
              ** intro r; split.
                 {
                  intro HInRc1.
                  destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                  - contradiction.
                  - rewrite <- RC.add_neq_in_iff in HInRc1; eauto.
                    unfold ST.In in *; simpl in *.
                    do 2 rewrite SRE.remove_in_iff.
                    rewrite RM.remove_in_iff.
                    specialize (HeqDom r); rewrite H0 in *; clear H0.
                    apply HeqDom in HInRc1 as [[HIn' | HIn'] | HIn'].
                    -- do 2 left; split; auto.
                    -- left; right; split; auto.
                    -- right; split; auto.
                 }
                 {
                  specialize (HeqDom r); rewrite H0 in *; clear H0.
                  unfold ST.In in *; simpl in *.
                  do 2 rewrite SRE.remove_in_iff.
                  rewrite RM.remove_in_iff.
                  intros [[[Hneq HIn'] | [HIn' Hneq]] | [Hneq HIn']];
                  rewrite <- RC.add_neq_in_iff; eauto;
                  rewrite HeqDom; auto.
                 }
            * simpl in HInrW; unfold ST.new_key in *;
              simpl (Stock.readers (rW,wW));
              simpl (Stock.writers (rW,wW)).
              destruct HInrW as [v' Hfi'].
              apply SRE.find_1 in Hfi'.
              apply SRE.add_id in Hfi' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- SRE.add_remove_1.
              rewrite SRE.Ext.new_key_add_max.
              rewrite (IHRc1 (SRE.Raw.remove x S) (SRE.Raw.remove x rW,wW)).
              ** simpl (Stock.readers (SRE.Raw.remove x rW, wW));
                 simpl (Stock.writers (SRE.Raw.remove x rW, wW)); lia.
              ** intro r; split.
                 {
                  intro HInRc1.
                  destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                  - contradiction.
                  - rewrite <- RC.add_neq_in_iff in HInRc1; eauto.
                    unfold ST.In in *; simpl in *.
                    do 2 rewrite SRE.remove_in_iff.
                    specialize (HeqDom r); rewrite H0 in *; clear H0.
                    apply HeqDom in HInRc1 as [[HIn' | HIn'] | HIn'].
                    -- do 2 left; split; auto.
                    -- left; right; auto.
                    -- right; split; auto.
                 }
                 {
                  specialize (HeqDom r); rewrite H0 in *; clear H0.
                  unfold ST.In in *; simpl in *.
                  do 2 rewrite SRE.remove_in_iff.
                  intros [[[Hneq HIn'] | HIn'] | [Hneq HIn']].
                  - rewrite <- RC.add_neq_in_iff; eauto.
                    rewrite HeqDom; auto.
                  - destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                    -- contradiction.
                    -- rewrite <- RC.add_neq_in_iff; eauto.
                       rewrite HeqDom; auto.
                  - rewrite <- RC.add_neq_in_iff; eauto.
                    rewrite HeqDom; auto.
                 }
         ++ destruct (SRE.In_dec rW x) as [HInrW | HnInrW].
            * simpl in HInwW; unfold ST.new_key in *;
              simpl (Stock.readers (rW,wW));
              simpl (Stock.writers (rW,wW)).
              destruct HInrW as [v' Hfi'].
              apply SRE.find_1 in Hfi'.
              apply SRE.add_id in Hfi' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- SRE.add_remove_1.
              rewrite SRE.Ext.new_key_add_max.
              destruct HInwW as [v'' Hfi''].
              apply RM.find_1 in Hfi''.
              apply RM.add_id in Hfi'' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- RM.add_remove_1.
              rewrite RM.Ext.new_key_add_max.
              rewrite (IHRc1 (SRE.Raw.remove x S) (SRE.Raw.remove x rW,RM.Raw.remove x wW)).
              ** unfold ST.new_key. 
                 simpl (Stock.readers (SRE.Raw.remove x rW, RM.Raw.remove x wW));
                 simpl (Stock.writers (SRE.Raw.remove x rW, RM.Raw.remove x wW)); lia.
              ** intro r; split.
                 {
                  intro HInRc1.
                  destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                  - contradiction.
                  - rewrite <- RC.add_neq_in_iff in HInRc1; eauto.
                    unfold ST.In in *; simpl in *.
                    do 2 rewrite SRE.remove_in_iff.
                    rewrite RM.remove_in_iff.
                    specialize (HeqDom r); rewrite H0 in *; clear H0.
                    apply HeqDom in HInRc1 as [[HIn' | HIn'] | HIn'].
                    -- do 2 left; split; auto.
                    -- left; right; split; auto.
                    -- right; split; auto.
                 }
                 {
                  specialize (HeqDom r); rewrite H0 in *; clear H0.
                  unfold ST.In in *; simpl in *.
                  do 2 rewrite SRE.remove_in_iff.
                  rewrite RM.remove_in_iff.
                  intros [[[Hneq HIn'] | [HIn' Hneq]] | [Hneq HIn']];
                  rewrite <- RC.add_neq_in_iff; eauto;
                  rewrite HeqDom; auto.
                 }
            * simpl in HInwW; unfold ST.new_key in *;
              simpl (Stock.readers (rW,wW));
              simpl (Stock.writers (rW,wW)).
              destruct HInwW as [v'' Hfi''].
              apply RM.find_1 in Hfi''.
              apply RM.add_id in Hfi'' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- RM.add_remove_1.
              rewrite RM.Ext.new_key_add_max.
              rewrite (IHRc1 (SRE.Raw.remove x S) (rW,RM.Raw.remove x wW)).
              ** simpl (Stock.readers (rW, RM.Raw.remove x wW));
                 simpl (Stock.writers (rW, RM.Raw.remove x wW)); lia.
              ** intro r; split.
                 {
                  intro HInRc1.
                  destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                  - contradiction.
                  - rewrite <- RC.add_neq_in_iff in HInRc1; eauto.
                    unfold ST.In in *; simpl in *.
                    rewrite SRE.remove_in_iff.
                    rewrite RM.remove_in_iff.
                    specialize (HeqDom r); rewrite H0 in *; clear H0.
                    apply HeqDom in HInRc1 as [[HIn' | HIn'] | HIn'].
                    -- do 2 left; auto.
                    -- left; right; split; auto.
                    -- right; split; auto.
                 }
                 {
                  specialize (HeqDom r); rewrite H0 in *; clear H0.
                  unfold ST.In in *; simpl in *.
                  rewrite SRE.remove_in_iff.
                  rewrite RM.remove_in_iff.
                  intros [[HIn' | [Hneq HIn']] | [Hneq HIn']].
                  - destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                    -- contradiction.
                    -- rewrite <- RC.add_neq_in_iff; eauto.
                       rewrite HeqDom; auto.
                  - rewrite <- RC.add_neq_in_iff; eauto.
                    rewrite HeqDom; auto.
                  - rewrite <- RC.add_neq_in_iff; eauto.
                    rewrite HeqDom; auto.
                 }
       + destruct HInS as [v Hfi].
         apply SRE.find_1 in Hfi.
         apply SRE.add_id in Hfi as Heq.
         rewrite <- Heq; clear Heq.
         rewrite <- SRE.add_remove_1.
         rewrite SRE.Ext.new_key_add_max.
         rewrite (IHRc1 (SRE.Raw.remove x S) W); try lia.
         intro r; split.
         ++ intro HInRc1.
            destruct (Resource.eq_dec r x) as [| Hneq]; subst.
            * contradiction.
            * rewrite SRE.remove_neq_in_iff; auto.
              rewrite <- HeqDom.
              rewrite H0, RC.add_in_iff; auto.
         ++ intros [HInW | HInS]; auto.
            * destruct (Resource.eq_dec r x) as [| Hneq]; subst.
              ** contradiction.
              ** rewrite <- RC.add_neq_in_iff; eauto.
                 specialize (HeqDom r).
                 rewrite H0 in HeqDom.
                 rewrite HeqDom; auto.
            * apply SRE.remove_in_iff in HInS as [Hneq HInS].
              rewrite <- RC.add_neq_in_iff; eauto.
              specialize (HeqDom r).
              rewrite H0 in HeqDom.
              rewrite HeqDom; auto.
    -- destruct (ST.In_dec x W) as [HInW | HnInW]. 
       + destruct W as [rW wW].
         destruct HInW as [HInrW | HInwW].
         ++ destruct (RM.In_dec wW x) as [HInwW | HnInwW].
            * simpl in HInrW; unfold ST.new_key in *;
              simpl (Stock.readers (rW,wW));
              simpl (Stock.writers (rW,wW)).
              destruct HInrW as [v' Hfi'].
              apply SRE.find_1 in Hfi'.
              apply SRE.add_id in Hfi' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- SRE.add_remove_1.
              rewrite SRE.Ext.new_key_add_max.
              destruct HInwW as [v'' Hfi''].
              apply RM.find_1 in Hfi''.
              apply RM.add_id in Hfi'' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- RM.add_remove_1.
              rewrite RM.Ext.new_key_add_max.
              rewrite (IHRc1 S (SRE.Raw.remove x rW,RM.Raw.remove x wW)).
              ** unfold ST.new_key. 
                 simpl (Stock.readers (SRE.Raw.remove x rW, RM.Raw.remove x wW));
                 simpl (Stock.writers (SRE.Raw.remove x rW, RM.Raw.remove x wW)); lia.
              ** intro r; split.
                 {
                  intro HInRc1.
                  destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                  - contradiction.
                  - rewrite <- RC.add_neq_in_iff in HInRc1; eauto.
                    unfold ST.In in *; simpl in *.
                    rewrite SRE.remove_in_iff.
                    rewrite RM.remove_in_iff.
                    specialize (HeqDom r); rewrite H0 in *; clear H0.
                    apply HeqDom in HInRc1 as [[HIn' | HIn'] | HIn'].
                    -- do 2 left; split; auto.
                    -- left; right; split; auto.
                    -- right; auto.
                 }
                 {
                  specialize (HeqDom r); rewrite H0 in *; clear H0.
                  unfold ST.In in *; simpl in *.
                  rewrite SRE.remove_in_iff.
                  rewrite RM.remove_in_iff.
                  intros [[[Hneq HIn'] | [HIn' Hneq]] | HIn'].
                  - rewrite <- RC.add_neq_in_iff; eauto.
                    rewrite HeqDom; auto.
                  - rewrite <- RC.add_neq_in_iff; eauto.
                    rewrite HeqDom; auto.
                  - destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                    -- contradiction.
                    -- rewrite <- RC.add_neq_in_iff; eauto.
                       rewrite HeqDom; auto.
                 }
            * simpl in HInrW; unfold ST.new_key in *;
              simpl (Stock.readers (rW,wW));
              simpl (Stock.writers (rW,wW)).
              destruct HInrW as [v' Hfi'].
              apply SRE.find_1 in Hfi'.
              apply SRE.add_id in Hfi' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- SRE.add_remove_1.
              rewrite SRE.Ext.new_key_add_max.
              rewrite (IHRc1 S (SRE.Raw.remove x rW,wW)).
              ** simpl (Stock.readers (SRE.Raw.remove x rW, wW));
                 simpl (Stock.writers (SRE.Raw.remove x rW, wW)); lia.
              ** intro r; split.
                 {
                  intro HInRc1.
                  destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                  - contradiction.
                  - rewrite <- RC.add_neq_in_iff in HInRc1; eauto.
                    unfold ST.In in *; simpl in *.
                    rewrite SRE.remove_in_iff.
                    specialize (HeqDom r); rewrite H0 in *; clear H0.
                    apply HeqDom in HInRc1 as [[HIn' | HIn'] | HIn'].
                    -- do 2 left; split; auto.
                    -- left; right; auto.
                    -- right; auto.
                 }
                 {
                  specialize (HeqDom r); rewrite H0 in *; clear H0.
                  unfold ST.In in *; simpl in *.
                  rewrite SRE.remove_in_iff.
                  intros [[[Hneq HIn'] | HIn'] | HIn'].
                  - rewrite <- RC.add_neq_in_iff; eauto.
                    rewrite HeqDom; auto.
                  - destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                    -- contradiction.
                    -- rewrite <- RC.add_neq_in_iff; eauto.
                       rewrite HeqDom; auto.
                  - destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                    -- contradiction.
                    -- rewrite <- RC.add_neq_in_iff; eauto.
                       rewrite HeqDom; auto.
                 }
         ++ destruct (SRE.In_dec rW x) as [HInrW | HnInrW].
            * simpl in HInwW; unfold ST.new_key in *;
              simpl (Stock.readers (rW,wW));
              simpl (Stock.writers (rW,wW)).
              destruct HInrW as [v' Hfi'].
              apply SRE.find_1 in Hfi'.
              apply SRE.add_id in Hfi' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- SRE.add_remove_1.
              rewrite SRE.Ext.new_key_add_max.
              destruct HInwW as [v'' Hfi''].
              apply RM.find_1 in Hfi''.
              apply RM.add_id in Hfi'' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- RM.add_remove_1.
              rewrite RM.Ext.new_key_add_max.
              rewrite (IHRc1 S (SRE.Raw.remove x rW,RM.Raw.remove x wW)).
              ** unfold ST.new_key. 
                 simpl (Stock.readers (SRE.Raw.remove x rW, RM.Raw.remove x wW));
                 simpl (Stock.writers (SRE.Raw.remove x rW, RM.Raw.remove x wW)); lia.
              ** intro r; split.
                 {
                  intro HInRc1.
                  destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                  - contradiction.
                  - rewrite <- RC.add_neq_in_iff in HInRc1; eauto.
                    unfold ST.In in *; simpl in *.
                    rewrite SRE.remove_in_iff.
                    rewrite RM.remove_in_iff.
                    specialize (HeqDom r); rewrite H0 in *; clear H0.
                    apply HeqDom in HInRc1 as [[HIn' | HIn'] | HIn'].
                    -- do 2 left; split; auto.
                    -- left; right; split; auto.
                    -- right; auto.
                 }
                 {
                  specialize (HeqDom r); rewrite H0 in *; clear H0.
                  unfold ST.In in *; simpl in *.
                  rewrite SRE.remove_in_iff.
                  rewrite RM.remove_in_iff.
                  intros [[[Hneq HIn'] | [HIn' Hneq]] | HIn'].
                  - rewrite <- RC.add_neq_in_iff; eauto;
                    rewrite HeqDom; auto.
                  - rewrite <- RC.add_neq_in_iff; eauto;
                    rewrite HeqDom; auto.
                  - destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                    -- contradiction.
                    -- rewrite <- RC.add_neq_in_iff; eauto.
                       rewrite HeqDom; auto.
                 }
            * simpl in HInwW; unfold ST.new_key in *;
              simpl (Stock.readers (rW,wW));
              simpl (Stock.writers (rW,wW)).
              destruct HInwW as [v'' Hfi''].
              apply RM.find_1 in Hfi''.
              apply RM.add_id in Hfi'' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- RM.add_remove_1.
              rewrite RM.Ext.new_key_add_max.
              rewrite (IHRc1 S (rW,RM.Raw.remove x wW)).
              ** simpl (Stock.readers (rW, RM.Raw.remove x wW));
                 simpl (Stock.writers (rW, RM.Raw.remove x wW)); lia.
              ** intro r; split.
                 {
                  intro HInRc1.
                  destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                  - contradiction.
                  - rewrite <- RC.add_neq_in_iff in HInRc1; eauto.
                    unfold ST.In in *; simpl in *.
                    rewrite RM.remove_in_iff.
                    specialize (HeqDom r); rewrite H0 in *; clear H0.
                    apply HeqDom in HInRc1 as [[HIn' | HIn'] | HIn'].
                    -- do 2 left; auto.
                    -- left; right; split; auto.
                    -- right; auto.
                 }
                 {
                  specialize (HeqDom r); rewrite H0 in *; clear H0.
                  unfold ST.In in *; simpl in *.
                  rewrite RM.remove_in_iff.
                  intros [[HIn' | [Hneq HIn']] | HIn'].
                  - destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                    -- contradiction.
                    -- rewrite <- RC.add_neq_in_iff; eauto.
                       rewrite HeqDom; auto.
                  - rewrite <- RC.add_neq_in_iff; eauto.
                    rewrite HeqDom; auto.
                  - destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                    -- contradiction.
                    -- rewrite <- RC.add_neq_in_iff; eauto.
                       rewrite HeqDom; auto.
                 }
       + exfalso.
         apply HeqDom in HIn as [|]; auto.
Qed. 
  

(** *** [well_formed_in_ec] properties *)

Lemma WF_in_ec_empty_locals (Rc: ℜ) (S: 𝐄) :
  (
    (forall (r : resource), (r ∈ Rc)%rc <-> (r ∈ S)%sr) /\ 
    (Rc⁺ ⊩ Rc)%rc /\  (S⁺ ⊩ S)%sr /\
    (forall (r : resource) (α : πΤ) (v : Λ), Rc⌊r⌋%rc = Some α -> 
                                             S⌊r⌋%sr = Some v -> (∅)%vc ⋅ Rc ⊢ v ∈ {snd α})
  ) 
  <-> 
   WFᵢₙ(Rc, S, (∅)%sk).
Proof.
  split.
  - intros [HeqDom [HvRc [HvS Hwt]]].
    unfold well_formed_in_ec.
    split.
    -- intro r; split.
       + rewrite HeqDom; auto.
       + intros [Hc | HIn].
         ++ exfalso; revert Hc.
            apply ST.empty_in.
         ++ rewrite HeqDom; auto.
    -- split.
       + intro r; split.
         ++ intros Hc HIn; revert Hc.
            apply ST.empty_in.
         ++ intro Hc.
            apply ST.empty_in.
       + do 2 (split; auto); split.
         ++ apply ST.Wf_empty.
         ++ split.
            * intros r πα v HfRc.
              split; intro Hfi.
              ** replace (Nat.max (S⁺)%sr (∅⁺)%sk - (S⁺)%sr) with 0.
                 { 
                  rewrite Term.shift_zero_refl.
                  apply (Hwt r); auto.
                 }
                 { rewrite ST.new_key_empty; lia. }
              ** inversion Hfi.
            * split.
              ** intro Hc; exfalso.
                 apply Hc.
                 apply ST.Empty_empty.
              ** split. 
                 { 
                  simpl; intros r πα HIn.
                  inversion HIn.
                  apply RM.empty_mapsto_iff in H.
                  contradiction.
                 }
                 { 
                  simpl; intros r [v HM].
                  apply SRE.empty_mapsto_iff in HM.
                  contradiction.
                 }
  - intros [HeqDom [_ [HvRc [HvS [_ [Hwt _]]]]]].
    split.
    -- intro r; split; intro HIn.
       + rewrite HeqDom in HIn.
         destruct HIn as [HIn |]; auto.
         exfalso; revert HIn.
         apply ST.empty_in.
       + rewrite HeqDom; auto.
    -- do 2 (split; auto).
       intros r πα v HfRc HfS.
       apply (Hwt _ _ v) in HfRc as HI.
       destruct HI as [Hwt' _].
       replace (Nat.max (S⁺)%sr (∅⁺)%sk - (S⁺)%sr) with 0 in Hwt'.
       { 
        rewrite Term.shift_zero_refl in Hwt'.
        apply Hwt'; auto.
       }
       { rewrite ST.new_key_empty; lia. }
Qed.

#[export] Instance WF_in_eq : Proper (RContext.eq ==> SRE.eq ==> ST.eq ==> iff) well_formed_in_ec.
Proof.
  intros Rc Rc1 HeqRe S S' HeqS W W' HeqW; split.
  - intros [HeqDom [HDisj [HvRc [HvS [HvW [Hwt [Hgt [Hwt' Hcorr]]]]]]]].  
    split.
    -- intro r; rewrite <- HeqS, <- HeqW, <- HeqRe; auto.
    -- split.
       + intro r; rewrite <- HeqS, <- HeqW; auto.
       + split; try (now rewrite <- HeqRe).
         split; try (now rewrite <- HeqS).
         split; try (now rewrite <- HeqW).
         split.
         ++ intros r πα v.
            rewrite <- HeqW.
            rewrite <- HeqS.
            rewrite <- HeqRe.
            auto.
         ++ split.
            * intros HnEmp.
              rewrite <- HeqW in HnEmp.
              apply Hgt in HnEmp as [].
              rewrite <- HeqW, <- HeqS, <- HeqRe; auto.
            * split.
              ** intros r πα. 
                 rewrite <- HeqW.
                 rewrite <- HeqRe.
                 apply (Hwt' r πα).
              ** intro r.
                 rewrite <- HeqW.
                 intro HIn.
                 apply Hcorr in HIn as [r' Hfi].
                 exists r'.
                 now rewrite <- HeqW.
  - intros [HeqDom [HDisj [HvRc [HvS [HvW [Hwt [Hgt [Hwt' Hcorr]]]]]]]].  
    split.
    -- intro r; rewrite HeqS, HeqW, HeqRe; auto.
    -- split.
       + intro r; rewrite HeqS, HeqW; auto.
       + split; try (now rewrite HeqRe).
         split; try (now rewrite HeqS).
         split; try (now rewrite HeqW).
         split.
         ++ intros r πα v.
            rewrite HeqW.
            rewrite HeqS.
            rewrite HeqRe.
            auto.
         ++ split.
            * intro HnEmp.
              rewrite HeqW in *.
              apply Hgt in HnEmp.
              now rewrite HeqS, HeqRe.
            * split.
              ** intros r πα. 
                 rewrite HeqW.
                 rewrite HeqRe.
                 apply (Hwt' r πα).
              ** intro r.
                 rewrite HeqW.
                 intro HIn.
                 apply Hcorr in HIn as [r' Hfi].
                 exists r'.
                 now rewrite HeqW.
Qed.

Lemma WF_in_ec_new (Rc : ℜ) (S : 𝐄) (W : 𝐖) :
  WFᵢₙ(Rc, S, W) -> (Rc⁺)%rc = max (S⁺)%sr (W⁺)%sk.
Proof.
  intros [HeqDom _].
  now apply TT_EqDom_new.
Qed.

Lemma WF_in_ec_Wf (Rc : ℜ) (S : 𝐄) (W : 𝐖) :
  WFᵢₙ(Rc, S, W) -> (Rc⁺ ⊩ Rc)%rc /\ (S⁺ ⊩ S)%sr /\ (W⁺ ⊩ W)%sk.
Proof.
  intros [_ [_ [HwfRc [HwfS [HwfW _]]]]]; auto.
Qed.

Lemma WF_in_ec_to_WF_ec (Rc : ℜ) (S : 𝐄) (W : 𝐖) :
  WFᵢₙ(Rc, S, W) -> WF(Rc,init_input_env S W).
Proof.
  intros [HeqDom [HneqDom [HvRe [HvS [HvW [Hwt [HnInW HeqWw]]]]]]]; split.
  { intro x; rewrite <- init_input_env_in_iff; auto. }
  do 2 (split; auto).
  {
   rewrite init_input_env_new_key.
   unfold init_input_env.
   apply ST.init_locals_Wf; split.
   - destruct (ST.is_empty W) eqn:Heq.
     -- apply ST.Empty_is_empty in Heq.
        now apply ST.Wf_Empty.
     -- rewrite <- ST.not_Empty_is_empty in Heq.
        apply HnInW in Heq.
        replace (Init.Nat.max (S⁺) (W⁺)%sk)%sr with (W⁺)%sk by lia.
        assumption.
   - apply SRE.init_globals_Wf.
     destruct (ST.is_empty W) eqn:Heq.
     -- apply ST.Empty_is_empty in Heq.
        rewrite ST.new_key_Empty; auto.
        replace (Init.Nat.max (S⁺) 0)%sr with (S⁺)%sr by lia.
        replace (S⁺ - S⁺)%sr with 0 by lia.
        rewrite SRE.shift_zero_refl; assumption.
     -- rewrite <- ST.not_Empty_is_empty in Heq.
        apply HnInW in Heq.
        replace (Init.Nat.max (S⁺) (W⁺)%sk)%sr with (W⁺)%sk by lia.
        apply SRE.shift_preserves_wf_2; auto; lia.
  }
  { 
   intros r α β v Hfi HfV.
   apply ST.init_locals_find_inp in HfV as H.
   - destruct H as [v' Heq]; subst.
     apply ST.init_locals_find_1 in HfV as [HfW | HfW].
     -- simpl in *.
        apply Hwt with (v := v') in Hfi as H.
        destruct H as [_ HwtW].
        apply HwtW in HfW; auto.
     -- apply RM.init_writers_find in HfW as H.
        destruct H as [HInW | HfS].
        + apply HeqWw with (α := (α,β)) in HInW as Heq; auto.
          simpl in *; subst.
          rewrite RM.init_writers_in in HfW; auto.
          inversion HfW; subst; constructor.
        + rewrite SRE.init_globals_shift in HfS. 
          apply RE.shift_find_e_1 in HfS as H.
          destruct H as [[r' Heq] [d Heqd]]; subst.
          destruct d as [t | t]; simpl in *; inversion Heqd; subst; clear Heqd.
          replace (Cell.inp <[[⧐{(S ⁺)%sr} – {(max (S⁺)%sr (W⁺)%sk) - (S ⁺)%sr}] t]>)
          with (Cell.shift (S⁺)%sr ((max (S⁺)%sr (W⁺)%sk) - (S⁺)%sr) (Cell.inp t)) 
          in HfS by now simpl.
          rewrite <- RE.shift_find_iff in HfS.
          rewrite SRE.init_globals_find_iff in HfS.
          rewrite Resource.shift_wf_refl in Hfi.
          ++ apply Hwt with (v := t) in Hfi.
              destruct Hfi as [HwtS _].
              apply HwtS in HfS; auto.
          ++ apply (SRE.Wf_find (S⁺)%sr) in HfS as [H _]; auto.
   - intros r' HfS.
     now apply SRE.init_globals_find_e in HfS.
  }
Qed.

(** ---- *)

(** ** Preservation - Temporal *)

Section props.


Hypothesis all_arrow_halting : forall Rc t α β,
  ∅%vc ⋅ Rc ⊢ arr(t) ∈ (α ⟿ β ∣ ∅%s) -> forall v, ∅%vc ⋅ Rc ⊢ v ∈ α -> halts (Rc⁺)%rc <[t v]>.

Theorem temporal_preserves_typing (Rc : ℜ) (S : 𝐄) (S' : o𝐄) (W W' : 𝐖) (P P' : Λ) (R : resources) :

         halts (Rc⁺)%rc P -> SRE.halts (S⁺)%sr S -> ST.halts (W⁺)%sk W -> 
                  WFᵢₙ(Rc,S,W) -> ∅%vc ⋅ Rc ⊢ P ∈ (𝟙 ⟿ 𝟙 ∣ R) -> 
                      
                      ⟦ S ; W ; P ⟧ ⟾ ⟦ S' ; W' ; P' ⟧ ->
  (* ------------------------------------------------------------------------ *)
       exists (Rc1 : ℜ) (R' : resources),
          (R ⊆ R')%s /\ (Rc ⊆ Rc1)%rc /\ WFₒᵤₜ(Rc1,S',W') /\
          (~ ST.Empty W' -> (W'⁺)%sk > (S⁺)%sr) /\
          
          ∅%vc ⋅ Rc1 ⊢ P' ∈ (𝟙 ⟿ 𝟙 ∣ R') /\ 
     
          halts (Rc1⁺)%rc P' /\ ORE.halts (Rc1⁺)%rc S' /\ ST.halts (W'⁺)%sk W'.
Proof.
  intros HltP HltS HltW HWF HwtP HTT.
  destruct HTT as [Vout [Wnew [_tv [fT [HeqS' HeqW']]]]].

  (* clean *)
  move Vout before R; move Wnew before W'; 
  move _tv before P'; move fT before HwtP.
  (* clean *)

  apply WF_in_ec_to_WF_ec in HWF as HWF'.
  apply (functional_preserves_typing_gen 
              all_arrow_halting Rc _ _ _ _ _ _ _ <[𝟙]> <[𝟙]> R) in fT as IH; auto.
  - 
    destruct IH as [Hunsd [Hlcl [Rc' [R' [HsubRc [HsubR [[HltVout [HltWnew [_ HltP']]] [Hwtv'
                   [HwtP' [HWF'' [HwtW1 [HInR Husd1]]]]]]]]]]]].

    (* clean *)
    move Rc' before Rc; move R' before R; move HltVout before HltP;
    move HltWnew before HltW; move HltP' before HltP; move Hwtv' before HwtP;
    move HwtP' before HwtP.
    (* clean *)

    exists Rc', R'.

    do 2 (split; auto); split.
    {
      apply functional_W_props in fT as H.
      apply WF_in_ec_new in HWF as Hnew'.
      apply WF_in_ec_Wf in HWF as HI.
      destruct HI as [HwfRc [HwfS HwfW]].
      destruct H as [HInWnew [Hdisj [HeqDom [HnEmpnew [Hcorr Hcorr']]]]].
      apply (WF_ec_Wf Rc' Vout) in HWF'' as HI.
      destruct HI as [HwfRc' HwfVout].
      apply (WF_ec_Wf) in HWF' as HI.
      destruct HI as [_ Hwfinp].

      apply functional_preserves_Wf in fT as H; auto;
      try (now constructor); 
      try (rewrite <- (WF_ec_new _ _ HWF'); 
           apply well_typed_implies_Wf in HwtP as []; auto).
      destruct H as [_ [_ [_ [HwfWnew Hle]]]].
      split.
      {
        intro r.
        rewrite HeqS', HeqW'.
        rewrite ST.update_locals_in_iff.
        rewrite ST.union_in_iff.
        rewrite ST.shift_new_key_in_iff.
        rewrite <- ORE.update_globals_in_iff.
        rewrite SRE.shift_in_new_key.
        destruct HWF as [HeqD _].
        specialize (HeqD r).
        specialize (HeqDom r).
        rewrite <- HeqDom.
        assert (Heq: r ∈ RE.diff Vout (init_input_env S W) <-> (r ∈ RC.diff Rc' Rc)%rc).
        - rewrite RE.diff_in_iff, RC.diff_in_iff.
          rewrite (WF_ec_In _ Vout HWF'').
          rewrite (WF_ec_In _ _ HWF').
          reflexivity.
        - rewrite Heq.
          rewrite RC.diff_Submap_in; eauto.
          rewrite HeqD; split.
          -- intros [|[|]]; auto.
          -- intros [[|]|]; auto.
      }
      split.
      { 
        intro r. 
        rewrite HeqS', HeqW'.
        rewrite ST.update_locals_in_iff.
        rewrite ST.union_in_iff.
        rewrite ST.shift_new_key_in_iff.
        rewrite <- ORE.update_globals_in_iff.
        rewrite SRE.shift_in_new_key.

        destruct HWF as [_ [HInWS _]].
        specialize (HInWS r).
        destruct HInWS as [HInWS HInSW].
           
        split. 
        - intros [| HIn]; auto.
          apply HInWnew in HIn as H.
          destruct H as [HnIn _].
          rewrite <- init_input_env_in_iff in HnIn.
          intro; apply HnIn; now right.
        - intros HIn [HInW | HInWnew'].
          -- revert HInW.
             now apply HInSW.
          -- apply HInWnew in HInWnew' as H.
             destruct H as [HnIn _].
             rewrite <- init_input_env_in_iff in HnIn.
             apply HnIn; now right.
      }
      do 2 (split; auto).
      {
        rewrite HeqS'.
        apply (WF_ec_new Rc' Vout) in HWF'' as Hnew.
        apply ORE.update_globals_Wf; split.
        - rewrite <- Hnew.
          apply SRE.shift_preserves_wf_2; auto.
          apply RC.Ext.new_key_Submap in HsubRc; lia.
        - now rewrite Hnew.
      }
      split.
      {
        rewrite HeqW'.
        destruct (Stock.is_empty W) eqn:Hemp'.
        - destruct (Stock.is_empty Wnew) eqn:Hemp.
          -- apply Stock.Empty_is_empty in Hemp, Hemp'.
             apply ST.Wf_Empty.
             apply ST.update_locals_Empty.
             apply ST.Empty_union; split; auto.
             apply ST.shift_Empty_iff; auto.

          -- apply ST.Empty_is_empty in Hemp'.
             apply ST.not_Empty_is_empty in Hemp.
             apply HnEmpnew in Hemp as [Heq _].

             rewrite ST.update_locals_new_key.
             rewrite ST.new_key_union.
             rewrite ST.shift_new_refl; auto.
             rewrite ST.new_key_Empty at 1; auto.
             simpl (max 0 (Wnew⁺)%sk).
             rewrite <- Heq.
             apply ST.update_locals_Wf; split; auto.
             apply ST.Wf_union; split; auto.
             apply ST.shift_preserves_wf_2; auto.
             rewrite <- (WF_ec_new Rc' Vout); auto.
             apply RC.Ext.new_key_Submap in HsubRc; lia.
        - apply ST.not_Empty_is_empty in Hemp'.
          rewrite ST.update_locals_new_key.
          rewrite ST.new_key_union.
          rewrite ST.shift_new_refl; auto.
          destruct (Stock.is_empty Wnew) eqn:Hemp.
          -- apply Stock.Empty_is_empty in Hemp.
             rewrite (Stock.new_key_Empty Wnew); auto.
             rewrite Resource.max_l; try lia.

             assert (forall r, r ∈ Rc <-> r ∈ Rc')%rc.
             {
              intro r; split; intro HIn.
              - apply (RC.Submap_in _ Rc); auto.
              -  destruct (RC.In_dec Rc r) as [| HnIn]; auto.
                exfalso.
                apply Stock.Empty_unfold in Hemp.
                apply Hemp.
                exists r.
                rewrite <- HeqDom.
                rewrite RE.diff_in_iff; auto.
                rewrite <- (WF_ec_In _ _ HWF'). 
                rewrite <- (WF_ec_In _ _ HWF''); auto. 
             }
             assert (Vout⁺ = (init_input_env S W)⁺).
             {  
              apply RE.new_key_in_eqDom.
              intro r.
              rewrite <- (WF_ec_In Rc' Vout); auto.
              rewrite <- (WF_ec_In Rc); auto.
              symmetry; auto.
             }
             rewrite H0.
             rewrite init_input_env_new_key.

             destruct HWF as [_ [_ [_ [_ [_ [_ [Hgt _]]]]]]].
             apply Hgt in Hemp'.
             rewrite Resource.max_r by lia.
             replace (W⁺ - W⁺)%sk with 0 by lia.
             apply ST.update_locals_Wf; split.

             + apply ST.Wf_union; split. 
               ++ rewrite ST.shift_zero_refl; auto.
               ++ now apply ST.Wf_Empty.
             + rewrite init_input_env_new_key in H0.
               rewrite Resource.max_r in H0 by lia.
               rewrite <- H0; auto.
          -- apply ST.not_Empty_is_empty in Hemp.
             apply HnEmpnew in Hemp as [Heq _].
             rewrite <- Heq.
             rewrite init_input_env_new_key in Hle.
             rewrite max_r by lia.
             apply ST.update_locals_Wf; split; auto.
             apply ST.Wf_union; split; auto.
             apply ST.shift_preserves_wf_2; auto; lia.
      }
      split.
      { 
        intro HnEmp. 
        rewrite HeqW' in *.
        rewrite ST.update_locals_Empty in HnEmp.
        rewrite ST.Empty_union in HnEmp.
        rewrite ST.update_locals_new_key.
        rewrite ST.new_key_union.
        rewrite ST.shift_new_refl by lia.
        rewrite <- ST.shift_Empty_iff in HnEmp.
        apply Classical_Prop.not_and_or in HnEmp as [HnEmp | HnEmp].
        - destruct HWF as [_ [_ [_ [_ [_ [_ HnEmpW]]]]]].
          apply HnEmpW in HnEmp as H.
          destruct H as [Heq Hgt].
          destruct (ST.is_empty Wnew) eqn:Hemp.
          -- apply ST.Empty_is_empty in Hemp.
             rewrite (ST.new_key_Empty Wnew); auto.
             rewrite max_l by lia.
             rewrite (RC.new_key_diff _ _ HsubRc); auto.
             rewrite Heq.
             rewrite (RC.Ext.new_key_Empty (RC.diff Rc' Rc)); try lia.
             assert ((forall r, r ∉ RC.diff Rc' Rc)%rc -> RC.Empty (RC.diff Rc' Rc)).
             + intros HIn r v HM.
               apply (HIn r).
               now exists v.
             + apply H; intros r HIn.
               apply (ST.Empty_notin_1 r) in Hemp.
               apply Hemp.
               rewrite <- HeqDom.
               rewrite RE.diff_in_iff.  
               rewrite RC.diff_in_iff in *.
               rewrite <- (WF_ec_In _ _ HWF').  
               now rewrite <- (WF_ec_In _ _ HWF'').
          -- apply ST.not_Empty_is_empty in Hemp.
             apply HnEmpnew in Hemp as H.
             destruct H as [Heq' Hgt'].
             rewrite <- Heq' in *.
             rewrite init_input_env_new_key in Hgt'.
             rewrite (WF_ec_new _ _ HWF''); lia.
        - apply HnEmpnew in HnEmp as H.
          destruct H as [Heq Hgt].
          rewrite init_input_env_new_key in Hgt.
          rewrite <- Heq.  
          rewrite (WF_ec_new _ _ HWF''); lia.
      }
      split.
      { 
        intros r [α β] v Hfi Hfi'.
        rewrite HeqW' in Hfi'.
        apply ST.update_locals_find in Hfi' as [Hfi' | Hfi'].
        - rewrite ST.find_union in Hfi'.
      }
      { admit. }
    }
    split.
    {
      apply functional_W_props in fT as H.
      destruct H as [_ [_ [_ [HnEmpnew _]]]].
      rewrite HeqW'.
      intros HnEmp.
      rewrite ST.update_locals_Empty in HnEmp.
      rewrite ST.Empty_union in HnEmp.
      apply Classical_Prop.not_and_or in HnEmp as [HnEmp | HnEmp].
      - rewrite ST.update_locals_new_key.
        rewrite ST.new_key_union.
        rewrite ST.shift_new_refl; auto.
        destruct HWF as [_ [_ [_ [_ [_ [_ [H _]]]]]]].
        rewrite <- ST.shift_Empty_iff in HnEmp.
        apply H in HnEmp; lia.
      - rewrite ST.update_locals_new_key.
        rewrite ST.new_key_union.
        rewrite ST.shift_new_refl; auto.
        apply HnEmpnew in HnEmp as [Heq Hgt].
        rewrite init_input_env_new_key in Hgt; lia.
    }
    do 2 (split; auto); split.
    {
     rewrite HeqS'.
     apply ORE.halts_update_globals; auto.
     rewrite <- (WF_ec_new Rc' Vout); auto.
     apply SRE.halts_weakening; auto.
     apply RC.Ext.new_key_Submap in HsubRc.
     rewrite (TT_EqDom_new _ S W) in HsubRc; try lia;
     destruct HWF as [HIn [Hdisj _]]; auto.
    }
    {
     rewrite HeqW'.
     rewrite ST.update_locals_new_key.
     rewrite ST.new_key_union.
     rewrite ST.shift_new_refl; auto.
     apply functional_W_props in fT as H.
     destruct H as [_ [_ [HeqD [HnEmpnew _]]]].
     destruct (Stock.is_empty W) eqn:Hemp'.
     - apply ST.Empty_is_empty in Hemp'.
       rewrite ST.new_key_Empty at 1; simpl; auto. 
       destruct (Stock.is_empty Wnew) eqn:Hemp.
       -- apply ST.Empty_is_empty in Hemp.
          apply ST.halts_Empty.
          apply ST.update_locals_Empty.
          apply ST.Empty_union; split; auto.
          apply ST.shift_Empty_iff; auto.
       -- apply ST.not_Empty_is_empty in Hemp.
          apply HnEmpnew in Hemp as [Heq Hgt].
          rewrite <- Heq.
          rewrite <- (WF_ec_new Rc' Vout); auto.
          apply ST.halts_update_locals; auto.
          apply ST.halts_union; split; auto.
          apply ST.halts_weakening; auto.

          apply RC.Ext.new_key_Submap in HsubRc.
          rewrite (WF_ec_new Rc _ HWF') in HsubRc; auto.
          rewrite init_input_env_new_key in HsubRc; lia.
     - apply ST.not_Empty_is_empty in Hemp'.
       destruct (Stock.is_empty Wnew) eqn:Hemp.
       + apply ST.Empty_is_empty in Hemp.
         rewrite (Stock.new_key_Empty Wnew); auto.
         rewrite Resource.max_l; try lia.

         assert (forall r, r ∈ Rc <-> r ∈ Rc')%rc.
         {
           intro r; split; intro HIn.
           - apply (RC.Submap_in _ Rc); auto.
           -  destruct (RC.In_dec Rc r) as [| HnIn]; auto.
             exfalso.
             apply Stock.Empty_unfold in Hemp.
             apply Hemp.
             exists r.
             rewrite <- HeqD.
             rewrite RE.diff_in_iff.
             rewrite <- (WF_ec_In Rc _ HWF'). 
             rewrite <- (WF_ec_In Rc' _ HWF'').
             split; auto. 
         }
         assert (Vout⁺ = (init_input_env S W)⁺).
         {  
           apply RE.new_key_in_eqDom.
           intro r.
           rewrite <- (WF_ec_In Rc' Vout); auto.
           rewrite <- (WF_ec_In Rc); auto.
           symmetry; auto.
         }
         rewrite H0.
         rewrite init_input_env_new_key. 

         destruct HWF as [_ [_ [_ [_ [_ [_ [Hgt _]]]]]]].
         apply Hgt in Hemp'.
         rewrite Resource.max_r by lia.
         replace (W⁺ - W⁺)%sk with 0 by lia.
         apply ST.halts_update_locals.
         ++ rewrite init_input_env_new_key in H0.
            rewrite Resource.max_r in H0 by lia.
            rewrite <- H0; auto.
            rewrite <- (WF_ec_new Rc'); auto.
         ++ apply ST.halts_union; split. 
            { rewrite ST.shift_zero_refl; auto. }
            { now apply ST.halts_Empty. }
        + apply ST.not_Empty_is_empty in Hemp.
          apply HnEmpnew in Hemp as [Heq Hgt].
          rewrite <- Heq.
          assert ((W ⁺)%sk <= (Rc' ⁺)%rc).
          ++ apply RC.Ext.new_key_Submap in HsubRc.
              rewrite (WF_ec_new Rc _ HWF') in HsubRc; auto.
              rewrite init_input_env_new_key in HsubRc; lia.
          ++ rewrite <- (WF_ec_new Rc' Vout); auto.
             rewrite Resource.max_r by lia.
             apply ST.halts_update_locals; auto.
             apply ST.halts_union; split; auto.
             apply ST.halts_weakening; auto.
    }
  - repeat split; auto.
    -- unfold init_input_env.
       apply ST.halts_init_locals; auto.
       + rewrite (TT_EqDom_new _ S W); auto;
         destruct HWF as [HIn [Hdisj [_ [_ [HvW [_ [HEmp _]]]]]]]; auto.
         destruct (ST.is_empty W) eqn:Heq.
         ++ apply ST.Empty_is_empty in Heq.
            now apply ST.halts_Empty.
         ++ apply ST.not_Empty_is_empty in Heq.
            apply HEmp in Heq.
            replace (Init.Nat.max (S⁺)%sr (W⁺)%sk) with (W⁺)%sk by lia.
            assumption.
       + apply SRE.halts_init_globals.
         rewrite (TT_EqDom_new Rc S W) in * by (destruct HWF as [HIn [Hdisj _]]; auto).
         apply SRE.halts_weakening; auto; lia.
    -- exists <[unit]>; split; auto; reflexivity.
Qed.


(** ---- *)


(** ** Progress - Temporal *)

Theorem temporal_progress (Rc : ℜ) (S : 𝐄) (W: 𝐖) (P : Λ) (R : resources) :

         halts (Rc⁺)%rc P -> SRE.halts (S⁺)%sr S -> ST.halts (W⁺)%sk W -> 
                WFᵢₙ(Rc,S,W) -> ∅%vc ⋅ Rc ⊢ P ∈ (𝟙 ⟿ 𝟙 ∣ R) ->
  (* ------------------------------------------------------------------------ *)
       exists (S' : o𝐄) (P': Λ) (W': 𝐖), ⟦ S ; W ; P ⟧ ⟾ ⟦ S' ; W' ; P' ⟧.
Proof.
  intros HltP HltS HltW HWF Hwt.
  eapply progress_of_functional 
  with (V := init_input_env S W) (tv := <[unit]>) in Hwt as HI; auto.
  - destruct HI as [V1 [_tv [P' [Wnew [fT _]]]]].
    exists (ORE.update_globals ([⧐ (S⁺)%sr – (V1⁺ - (S⁺)%sr)%re] S)%sr V1)%or.
    exists P'.
    exists (ST.update_locals (([⧐ (W⁺)%sk – (V1⁺ - (W⁺)%sk)%re] W) ∪ Wnew)%sk V1).
    unfold temporal.
    exists V1, Wnew, _tv; split; auto.
    split; try reflexivity.
  - repeat split; auto.
    -- unfold init_input_env.
       apply ST.halts_init_locals; auto.
       + rewrite (TT_EqDom_new _ S W); auto;
         destruct HWF as [HIn [Hdisj [_ [_ [HvW [_ [HEmp _]]]]]]]; auto.
         destruct (ST.is_empty W) eqn:Heq.
         ++ apply ST.Empty_is_empty in Heq.
            now apply ST.halts_Empty.
         ++ apply ST.not_Empty_is_empty in Heq.
            apply HEmp in Heq.
            replace (Init.Nat.max (S⁺)%sr (W⁺)%sk) with (W⁺)%sk by lia.
            assumption.
       + apply SRE.halts_init_globals.
         rewrite (TT_EqDom_new Rc S W) in * by (destruct HWF as [HIn [Hdisj _]]; auto).
         apply SRE.halts_weakening; auto; lia.
    -- exists <[unit]>; split; auto; reflexivity.
  - now apply WF_in_ec_to_WF_ec.
  - intros r HIn.
    apply WF_in_ec_to_WF_ec in HWF.
    apply WF_ec_Wf in HWF as H.
    destruct H as [HvRe HvV].
    destruct HltP as [P' [HmeT HvP']].
    apply multi_preserves_typing with (t' := P') in Hwt; auto.
    apply typing_Re_R with (r := r) in Hwt; auto.
    rewrite (WF_ec_In Rc (init_input_env S W)) in Hwt; auto.
    unfold init_input_env in *.
    apply ST.init_locals_in_iff in Hwt as [HIn' | HIn'].
    -- now apply ST.init_locals_in_unused.
    -- apply ST.init_locals_unused.
       apply SRE.init_globals_in_unused.
       now rewrite <- SRE.init_globals_in_iff.
Qed.

End props.