From Coq Require Import Lists.List Lia Classes.Morphisms Bool.Bool.
From Mecha Require Import RFlows REnvironment Term Functional Resource Cell Typing VContext Typ
               Resources Evaluation RContext RFlow.

(** * Transition - Temporal

rsf's semantics are divided in three sub semantics:
- evaluation transition
- functional transition
- temporal transition <--

*)

Module RE := REnvironment.
Reserved Notation "'Wfₜₜ(' Re , Rf )" (at level 50).

(** *** Definition *)

Inductive temporal : 𝐅 -> 𝐅 -> Λ -> Λ -> Prop :=
  | TT_instant : forall Vin Vout _tv (R R' : 𝐅) (P P' : Λ),

                    (Vin = RFlows.nexts R)%re ->
                    ⪡ Vin ; unit ; P ⪢ ⭆ ⪡ Vout ; _tv ; P' ⪢ ->
                    (R' = RFlows.puts Vout R) -> 
                    
                    temporal R R' P P'
  | TT_trans : forall R R' R'' (P P' P'' : Λ), 
                  temporal R R' P P' -> 
                  temporal R' R'' P' P'' -> 
                  temporal R R'' P P''.

Notation "'⟦' R ';' P '⟧' '⟾' '⟦' R1 ';' P1 '⟧'" := (temporal R R1 P P1) 
                                                     (at level 30, R constr, R1 constr,
                                                         P custom rsf, P1 custom rsf, 
                                                        no associativity).

Inductive wf_env_TT : ℜ -> 𝐅 -> Prop :=
  | wfTT_empty  : forall (Re : ℜ) (Fl : 𝐅), 
                     isEmptyᵣᵪ(Re) -> 
                     isEmptyᵣₔ(Fl) -> Wfₜₜ(Re,Fl)

  | wfTT_add   : forall (Re Re' : ℜ) (Fl Fl' : 𝐅) (τ τ' : Τ) (r : RFlow.t),
      Wfₜₜ(Re,Fl) ->
      Addᵣᵪ (newᵣᵪ(Re)) (τ,τ') Re Re' ->
      Addᵣₔ (newᵣₔ(Fl)) r Fl Fl' ->
      RFlow.well_typed_rflow (∅ᵥᵪ) Re r τ' τ ->
      Wfₜₜ(Re',Fl')

where "'Wfₜₜ(' Re , Fl )" := (wf_env_TT Re Fl).

(** *** wf_env_TT *)

Lemma wf_env_TT_is_empty_spec : forall (Re : ℜ) Fl,
  Wfₜₜ(Re,Fl) -> RC.Raw.is_empty Re = RFlows.Raw.is_empty Fl.
Proof.
  intros Re V Hinst; induction Hinst.
  - rewrite RC.OP.P.is_empty_1; auto; 
    now rewrite RFlows.OP.P.is_empty_1.
  - apply RC.notEmpty_Add_spec in H.
    apply RFlows.notEmpty_Add_spec in H0.
    destruct (RC.Raw.is_empty Re') eqn:HEmp.
    -- apply RC.OP.P.is_empty_2 in HEmp; contradiction.
    -- destruct (RFlows.Raw.is_empty Fl') eqn:HEmp'; auto.
        apply RFlows.OP.P.is_empty_2 in HEmp'; contradiction.
Qed.

Lemma wf_env_TT_Empty_spec : forall (Re : ℜ) Fl,
  Wfₜₜ(Re,Fl) -> isEmptyᵣᵪ(Re) <-> isEmptyᵣₔ(Fl).
Proof.
  intros Re V Hinst; induction Hinst.
  - split; intros; assumption.
  - split; intros.
    -- now apply RC.notEmpty_Add_spec in H.
    -- now apply RFlows.notEmpty_Add_spec in H0.
Qed.

Lemma wf_env_TT_max : forall (Re : ℜ) Fl,
  Wfₜₜ(Re,Fl) -> maxᵣᵪ(Re) = maxᵣₔ(Fl).
Proof.
  intros Re V inst; induction inst.
  - rewrite RC.Ext.max_key_Empty_spec; auto.
    now rewrite RFlows.Ext.max_key_Empty_spec.
  - apply RC.Ext.max_key_Add_spec in H as [[H H'] | [H H']]; auto.
    -- rewrite H. 
        apply RFlows.Ext.max_key_Add_spec in H0 as [[H0 H0'] | [H0 H0']].
        + rewrite H0; apply wf_env_TT_is_empty_spec in inst as HEmp.
          unfold RC.Ext.new_key,RFlows.Ext.new_key; rewrite HEmp.
          destruct (RFlows.Raw.is_empty Fl); auto.
        + assert (newᵣₔ(Fl) >= maxᵣₔ(Fl)). { apply RFlows.Ext.new_key_geq_max_key. }
          lia.
        + apply RFlows.new_key_notin_spec; auto.
    -- unfold RC.Ext.new_key in H'. 
        destruct (RC.Raw.is_empty Re) eqn:HEmp; try lia.
        rewrite RC.Ext.max_key_Empty_spec in H'; try lia.
        now apply RC.OP.P.is_empty_2.
    -- apply RC.Ext.new_key_notin_spec; lia.
Qed.

Lemma wf_env_TT_new : forall (Re : ℜ) Fl,
  Wfₜₜ(Re,Fl) -> newᵣᵪ(Re) = newᵣₔ(Fl).
Proof.
  intros Re Fl Hwf; unfold RC.Ext.new_key,RFlows.Ext.new_key.
  apply wf_env_TT_is_empty_spec in Hwf as HisEmp.
  destruct (RC.Raw.is_empty Re) eqn:HEmp.
  - now rewrite <- HisEmp.
  - rewrite <- HisEmp; f_equal; now apply wf_env_TT_max.
Qed.

Lemma wf_env_TT_domains_match: forall (Re : ℜ) Fl (k : resource) (πτ : πΤ),
  Wfₜₜ(Re,Fl) -> Re ⌈k ⩦ πτ⌉ᵣᵪ -> exists v, Fl ⌈k ⩦ v⌉ᵣₔ.
Proof.
  intros Re Fl k πτ wf; revert k πτ; induction wf; intros k' πτ' Hfin.
  - apply RC.notEmpty_find_spec in Hfin; auto; contradiction.
  - rewrite H0 in *; destruct (Resource.eq_dec (newᵣᵪ(Re)) k'); subst.
    -- exists r. 
       apply wf_env_TT_new in wf as Hnew; rewrite Hnew.
       now apply RFlows.OP.P.add_eq_o.
    -- rewrite H in Hfin. rewrite RC.OP.P.add_neq_o in Hfin; try assumption.
        apply IHwf in Hfin as [v' Hfin]; exists v'. 
        rewrite RFlows.OP.P.add_neq_o; auto.
        apply wf_env_TT_new in wf; now rewrite <- wf.
Qed.

#[export] 
Instance wfTT_eq : Proper (RC.eq ==> RFlows.eq ==> iff) (wf_env_TT).
Proof.
  repeat red; split; intros.
  - revert y y0 H0 H; induction H1; subst; intros y y0 Heq Heq'.
    -- apply wfTT_empty; try (now rewrite <- Heq); now rewrite <- Heq'.
    -- eapply wfTT_add; eauto; try (now rewrite <- Heq); now rewrite <- Heq'.
  - revert x x0 H0 H; induction H1; subst; intros x x0 Heq Heq'.
    -- apply wfTT_empty; try (now rewrite Heq'); now rewrite Heq.
    -- eapply wfTT_add; eauto; try (now rewrite Heq); now rewrite Heq'.
Qed.

Lemma wf_env_TT_in : forall (Re : ℜ) Fl (r : resource),
  Wfₜₜ(Re,Fl) -> r ∈ᵣᵪ Re <-> r ∈ᵣₔ Fl.
Proof.
  split.
  - intros; destruct H0; apply RC.OP.P.find_1 in H0. 
    eapply wf_env_TT_domains_match in H0; eauto;
    destruct H0. exists x0; now apply RFlows.OP.P.find_2.
  - revert r; induction H.
    -- intros. unfold RE.OP.P.Empty in *; exfalso.
       destruct H1. now apply (H0 r x).
    -- intros. unfold RFlows.OP.P.Add in *. rewrite H1 in *.
       unfold RC.OP.P.Add in *. rewrite H0.
       apply RFlows.OP.P.add_in_iff in H3; destruct H3; subst.
       + apply wf_env_TT_new in H; rewrite H.
         rewrite RC.OP.P.add_in_iff; now left.
       + rewrite RC.OP.P.add_in_iff; right; now apply IHwf_env_TT.
Qed.


Lemma wf_env_TT_well_typed : forall (Re : ℜ) Fl (r : resource) v (τ τ' : Τ),
  Wfₜₜ(Re,Fl) -> Re ⌈r ⩦ (τ,τ')⌉ᵣᵪ -> Fl ⌈r ⩦ v⌉ᵣₔ -> 
  RFlow.well_typed_rflow (∅ᵥᵪ) Re v τ' τ.
Proof.
  intros Re V r v τ τ' wf; revert r v τ τ'; induction wf;
  intros r' v' τ1 τ1' HfRe HfFl.
  - apply RC.notEmpty_find_spec in HfRe; auto; contradiction.
  - rewrite H in HfRe; rewrite H0 in HfFl.
    apply wf_env_TT_new in wf as Hnew. 
    destruct (Resource.eq_dec (newᵣᵪ(Re)) r'); subst.
    -- rewrite Hnew in HfFl. rewrite RC.OP.P.add_eq_o in HfRe; auto; 
        inversion HfRe; clear HfRe; subst.
        rewrite RFlows.OP.P.add_eq_o in HfFl; auto; inversion HfFl; 
        subst; clear HfFl. apply RFlow.rflow_weakening_ℜ with (Re := Re); auto.
        unfold RC.OP.P.Add in H. rewrite H. apply RC.Ext.Submap_add_spec_1.
        + apply RC.Ext.new_key_notin_spec; lia.
        + reflexivity.
    -- rewrite <- Hnew in HfFl. rewrite RC.OP.P.add_neq_o in HfRe; auto.
        rewrite RFlows.OP.P.add_neq_o in HfFl; auto. eapply IHwf in HfFl; eauto.
        apply RFlow.rflow_weakening_ℜ with (Re := Re); auto.
        unfold RC.OP.P.Add in H. rewrite H. apply RC.Ext.Submap_add_spec_1.
        + apply RC.Ext.new_key_notin_spec; lia.
        + reflexivity.
Qed.

Lemma wf_env_TT_to_fT Re Fl : 
  Wfₜₜ(Re,Fl) -> Wfᵣₜ(Re,RFlows.nexts Fl).
Proof. 
  intros. induction H.
  - apply wfFT_empty; auto. rewrite RFlows.nexts_Empty; auto.
    apply RFlows.OP.P.empty_1.
  - apply (wfFT_add Re Re' (RFlows.nexts Fl) (RFlows.nexts Fl')
                     τ τ' (RFlow.next r)); auto.
    -- unfold RE.OP.P.Add. apply RFlows.nexts_Add_spec; auto;
       rewrite <- RFlows.nexts_new_key.
       + apply RFlows.new_key_notin_spec; auto.
       + assumption.
    -- destruct r; simpl in *; apply H2.
Qed.

Lemma wf_env_fT_update (Re : ℜ) V (Fl Fl' : 𝐅): 
  Wfₜₜ(Re,Fl) ->  Wfᵣₜ(Re,V) ->
  (Fl' = (RFlows.puts V Fl))%rf -> Wfₜₜ(Re,Fl').
Proof.
  intros wftt; revert Fl' V; induction wftt; intros Fl1 V Hwfrt Heq.
  - rewrite RFlows.puts_Empty_eq with (V := V) in H0.
    apply wfTT_empty; auto; rewrite Heq; auto.
  -
    rename H into HAddRe; rename H0 into HAddFl; move Fl1 before Fl;
    move V before Re'; move IHwftt before r; move Hwfrt before wftt;
    rename H1 into Hwtr; move Hwtr before IHwftt.

    assert(HInRe': (newᵣᵪ(Re)) ∈ᵣᵪ Re').
    { exists (τ,τ'). apply RC.OP.P.find_2. rewrite HAddRe. now rewrite RC.OP.P.add_eq_o. }

    move HInRe' before HAddFl.
    
    assert (Hnm: newᵣᵪ(Re) = maxᵣᵦ(V)).
    { 
     apply wf_env_fT_max in Hwfrt as Hmax. rewrite <- Hmax.
     apply RC.max_key_Add_spec in HAddRe.
     - destruct HAddRe as [[Heq' Hle] | [Heq' Hle]]; try lia.
       assert (newᵣᵪ(Re) >= maxᵣᵪ(Re)) by apply RC.Ext.new_key_geq_max_key.
       lia.
     - apply RC.Ext.new_key_notin_spec; auto. 
    }

    assert (Hnew: maxᵣᵦ(V) = newᵣᵦ(RE.Raw.remove (maxᵣᵦ(V)) V)).
    { admit. }
       
    remember (RE.Raw.remove (maxᵣᵦ(V)) V) as V0.
    rewrite Hnew in HeqV0. move V0 before Re'.

    assert (HAddV: exists v, RE.OP.P.Add (newᵣᵦ(V0)) v V0 V).
    {
      rewrite wf_env_fT_in in HInRe'; eauto.
      rewrite Hnm in HInRe'. rewrite Hnew in HInRe'. 
      destruct HInRe' as [v HM]. apply RE.OP.P.find_1 in HM. exists v. 
      unfold RE.OP.P.Add. apply RE.OP.P.add_id in HM. rewrite <- HM. 
      rewrite <- RE.OP.P.add_remove_1. now rewrite <- HeqV0.
    }

    destruct HAddV as [v HAddV]. move v before r; move HAddV before HAddRe.
    eapply wf_env_fT_weakening_bis in Hwfrt as Hwfrt0; eauto.
    rewrite Hnew in Hwfrt0. rewrite <- HeqV0 in Hwfrt0.
    assert (RC.Raw.remove (maxᵣᵪ( Re')) Re' = Re)%rc.
    { admit. }
    rewrite <- Hnm in Hnew; clear Hnm. rewrite Heq. rewrite H in *. clear H.
    assert (Hnew': newᵣₔ(Fl) = newᵣᵦ(V0)).
    { apply wf_env_TT_new in wftt. rewrite <- Hnew; now rewrite <- wftt. }
    eapply RFlows.puts_Add_spec_2 with (V := V0) (v := v) (V' := V) in HAddFl.
    -- apply (wfTT_add Re Re' (RFlows.puts V0 Fl) (RFlows.puts V Fl') 
                     τ τ' (RFlows.puts_func_1 V0 (newᵣₔ(Fl)) r)); auto.
       + apply IHwftt with (V := V0); auto; reflexivity.
       + rewrite <- RFlows.puts_new_spec with (V := V0); assumption.
       + unfold RFlows.puts_func_1; rewrite Hnew'.
         replace (V0⌊newᵣᵦ(V0)⌋ᵣᵦ) with (@None Cell.t).
         ++ now apply RFlow.rflow_well_typed_None.
         ++ symmetry. apply RE.OP.P.not_in_find.
            apply RE.Ext.new_key_notin_spec; lia.
    -- apply RFlows.Ext.new_key_notin_spec; lia.
    -- rewrite Hnew'. apply RE.Ext.new_key_notin_spec; lia.
    -- now rewrite Hnew'.
Admitted.

(** *** Initialization *)

Lemma resource_used_init_unused : forall Re t α β R l V,
  ∅ᵥᵪ ⋅ Re ⊫ t ∈ (α ⟿ β ∣ R) ->
  halts t ->
  Wfᵣₜ(Re,V) ->
  (V = (RFlows.nexts l))%re ->
  
  (forall r, (r ∈ R)%rs -> RE.unused r V).
Proof.
  intros. destruct H0 as [t' [HmeT Hvt']].
  apply multi_preserves_typing with (t' := t') in H; auto.
  apply typing_Re_R with (r := r) in H; auto.
  apply wf_env_fT_in with (V := V) in H; auto.
  rewrite H2 in *. destruct H; apply RE.OP.P.find_1 in H.
  assert (r ∈ᵣₔ l). { rewrite RFlows.nexts_in_iff. exists x. now apply RE.OP.P.find_2. }
  apply RFlows.nexts_unused in H0. destruct H0. rewrite <- H2 in H0.
  now exists x0.
Qed. 

Section safety.

Hypothesis all_arrow_halting : forall Re t α β,
  ∅ᵥᵪ ⋅ Re ⊫ arr(t) ∈ (α ⟿ β ∣ ∅ᵣₛ) -> forall v, ∅ᵥᵪ ⋅ Re ⊫ v ∈ α -> halts <[t v]>.


(** *** Proof of typing preservation through the temporal transition *)
Theorem temporal_preserves_typing (Re : ℜ) Rf Rf' (P P' : Λ) (R : resources) :

    (* (1) *) halts P -> (* (2) *) RFlows.halts Rf ->

    (* (1) *) ∅ᵥᵪ ⋅ Re ⊫ P ∈ (𝟙 ⟿ 𝟙 ∣ R) ->
    (* (3) *) ⟦ Rf ; P ⟧ ⟾ ⟦ Rf' ; P' ⟧ ->
              Wfₜₜ(Re,Rf) ->

  (*----------------------------------------------------*)
      ∅ᵥᵪ ⋅ Re ⊫ P' ∈ (𝟙 ⟿ 𝟙 ∣ R) /\ Wfₜₜ(Re,Rf') /\ 
       (* (7) *) halts P' /\ (* (8) *) RFlows.halts Rf'.
Proof.
  intros HltP HltRf HwP HTT; revert Re R HltP HltRf HwP. 
  induction HTT; subst; intros Re R1 HlP HlRf HwP Hwf.
  - apply wf_env_TT_to_fT in Hwf as Hwf'.
    eapply functional_preserves_typing in H0; eauto.
    -- destruct H0 as [_ [_ [HwfV [_ [_ [HwP' [HltP' [_ HltVout]]]]]]]].
       split; auto; split.
       + eapply wf_env_fT_update; eauto. reflexivity.
       + split; auto. apply RFlows.halts_puts; auto.
    -- exists <[unit]>; split; auto.
    -- apply RFlows.halts_nexts in HlRf. eapply RE.halts_eq; eauto.
    -- now rewrite H.
  - apply IHHTT1 in HwP as IH; auto. destruct IH as [HwP' [Hwf' [HlP' HlR']]].
    apply IHHTT2; assumption.
Qed. 


Theorem progress_of_temporal (Re : ℜ) (Rf : 𝐅) (P : Λ) (R : resources) :

  (* (1) *) halts P -> (* (2) *) RFlows.halts Rf ->

  (* (4) *) ∅ᵥᵪ ⋅ Re ⊫ P ∈ (𝟙 ⟿ 𝟙 ∣ R) -> (* (5) *) Wfₜₜ(Re,Rf) ->
  
  (*-------------------------------------------------------------------------------------------------*)
    exists Rf' P',  (* (6) *) ⟦ Rf ; P ⟧ ⟾ ⟦ Rf' ; P' ⟧ /\ 
                    (* (7) *) halts P' /\ (* (8) *) RFlows.halts Rf'.
Proof.
  intros HltP HltRf HwP Hinst. 
  assert (HwU : ∅ᵥᵪ ⋅ Re ⊫ unit ∈ 𝟙). { now constructor. }
  remember (RFlows.nexts Rf) as Vin.

  eapply progress_of_functional with (V := Vin) in HwU; eauto.
  - destruct HwU as [Vout [tv' [P' [HfT [HltP' [Hltv' HltVout]]]]]].
    exists (RFlows.puts Vout Rf); exists P'; split.
    -- econstructor; eauto; subst; reflexivity.
    -- split; auto. apply RFlows.halts_puts; auto.
  - exists <[unit]>; split; auto.
  - apply RFlows.halts_nexts in HltRf; now subst.
  - subst. now apply wf_env_TT_to_fT.
  - apply wf_env_TT_to_fT in Hinst.
    destruct HltP as [P' [HmeT HltP']].
    eapply multi_preserves_typing in HwP; eauto.
    intros. apply typing_Re_R with (r := r) in HwP; auto.
    rewrite wf_env_fT_in in HwP; eauto; subst.
    apply RFlows.nexts_unused. now rewrite RFlows.nexts_in_iff.
Qed.

End safety.