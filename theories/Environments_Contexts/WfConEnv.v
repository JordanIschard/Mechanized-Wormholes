From Coq Require Import Classes.Morphisms Lia.
From Mecha Require Import Resource Typ Typing VContext RContext Cell REnvironment RFlows RFlow.

(** * Well formed properties between environments *)

Module RC := RContext.
Module RE := REnvironment.
Module RF := RFlows.

(** ** Well formed property between the resource context and environment *)

(** *** Definition *)

Definition wf_env_fT (Re : ℜ) (V : 𝓥) :=
  (forall r, r ∈ᵣᵪ Re <-> r ∈ᵣᵦ V) /\
  (forall r τ τ' v, 
    Re ⌈ r ⩦ (τ,τ') ⌉ᵣᵪ -> 
    V ⌈ r ⩦ v ⌉ᵣᵦ -> 
    match v with
      | (⩽ v' … ⩾) => ∅ᵥᵪ ⋅ Re ⊫ v' ∈ τ'
      | (⩽ … v' ⩾) => ∅ᵥᵪ ⋅ Re ⊫ v' ∈ τ
    end
  ).

Notation "'Wfᵣₜ(' Re , V )" := (wf_env_fT Re V) (at level 50).

(** *** Property *)

Fact fT_eqDom_Empty (Re : ℜ) (V : 𝓥):
 (forall r, r ∈ᵣᵪ Re <-> r ∈ᵣᵦ V) -> isEmptyᵣᵪ(Re) <-> isEmptyᵣᵦ(V).
Proof.
  intro HeqDom. split; intros HEmp.
  - intro r. 
    assert (r ∉ᵣᵪ Re).
    { intro. destruct H. now apply (HEmp r x). }
    intro v. intro Hc.
    apply H. rewrite HeqDom. now exists v.
  - intro r.
    assert (r ∉ᵣᵦ V).
    { intro. destruct H. now apply (HEmp r x). }
    rewrite <- HeqDom in H.
    intro v. intro Hc.
    apply H. now exists v.
Qed.
  
Fact fT_eqDom_is_empty (Re : ℜ) (V : 𝓥):
  (forall r, r ∈ᵣᵪ Re <-> r ∈ᵣᵦ V) -> RC.Raw.is_empty Re = RE.Raw.is_empty V.
Proof.
  intro HeqDom.
  destruct (RC.Raw.is_empty Re) eqn:HisEmp;
  destruct (RE.Raw.is_empty V) eqn:HisEmp';
  try reflexivity.
  - exfalso.  
    apply RC.OP.P.is_empty_2 in HisEmp.
    rewrite fT_eqDom_Empty in HisEmp; eauto.
    apply RE.OP.P.is_empty_1 in HisEmp.
    rewrite HisEmp' in *. inversion HisEmp.
  - exfalso.  
    apply RE.OP.P.is_empty_2 in HisEmp'.
    rewrite <- fT_eqDom_Empty in HisEmp'; eauto.
    apply RC.OP.P.is_empty_1 in HisEmp'.
    rewrite HisEmp in *. inversion HisEmp'.
Qed.

Fact fT_eqDom_max (Re : ℜ) (V : 𝓥):
  (forall r, r ∈ᵣᵪ Re <-> r ∈ᵣᵦ V) -> maxᵣᵪ(Re) = maxᵣᵦ(V).
Proof.
  revert V.
  induction Re using RC.OP.P.map_induction; intros V HeqDom.
  - rewrite RC.Ext.max_key_Empty_spec; auto.
    rewrite (fT_eqDom_Empty Re V HeqDom) in H.
    rewrite RE.Ext.max_key_Empty_spec; auto.
  - assert (HAddV: exists v, Addᵣᵦ x v (RE.Raw.remove x V) V). 
    {
      assert (x ∈ᵣᵦ V). { 
        rewrite <- HeqDom. unfold RC.OP.P.Add in *; rewrite H0.
        rewrite RC.OP.P.add_in_iff; auto. 
      }
      destruct H1 as [v HM].
      exists v. unfold RE.OP.P.Add.
      rewrite RE.OP.P.add_remove_1.
      symmetry. rewrite RE.OP.P.add_id.
      now apply RE.OP.P.find_1.
    }
    destruct HAddV as [v HAddV]. remember (RE.Raw.remove x V) as V0.
    assert (HeqDom': forall r : RContext.Raw.key, r ∈ᵣᵪ Re1 <-> r ∈ᵣᵦ V0).
    { 
      intro r; split; intro HIn.
      - assert (r ∈ᵣᵪ Re2). 
        { unfold RC.OP.P.Add in *; rewrite H0. rewrite RC.OP.P.add_in_iff; auto. }
        rewrite HeqDom in H1.
        unfold RE.OP.P.Add in *; rewrite HAddV in *.
        rewrite RE.OP.P.add_in_iff in H1; destruct H1; subst; auto.
        contradiction.
      - assert (r ∈ᵣᵦ V). 
        { unfold RE.OP.P.Add in *; rewrite HAddV. rewrite RE.OP.P.add_in_iff; auto. }
        rewrite <- HeqDom in H1.
        unfold RC.OP.P.Add in *. rewrite H0 in *.
        rewrite RC.OP.P.add_in_iff in H1; destruct H1; subst; auto.
        rewrite RE.OP.P.remove_in_iff in HIn; destruct HIn; contradiction.
    }
    apply IHRe1 in HeqDom' as Hmax.
    unfold RC.OP.P.Add in *. rewrite H0. 
    unfold RE.OP.P.Add in *. rewrite HAddV.
    destruct (Resource.ltb_spec0 x (maxᵣᵪ(Re1))).
    -- rewrite RC.Ext.max_key_add_spec_2; auto.
       rewrite RE.Ext.max_key_add_spec_2; auto.
       + subst. intro Hc. 
        rewrite RE.OP.P.remove_in_iff in Hc. 
        destruct Hc; contradiction.
       + now rewrite Hmax in *.
    -- rewrite RC.Ext.max_key_add_spec_1; auto; try lia.
       rewrite Hmax in n.
       rewrite RE.Ext.max_key_add_spec_1; auto; try lia.
       subst. intro Hc. 
       rewrite RE.OP.P.remove_in_iff in Hc. 
       destruct Hc; contradiction.
Qed.

Corollary wf_env_fT_Empty (Re : ℜ) (V : 𝓥):
  Wfᵣₜ(Re,V) -> isEmptyᵣᵪ(Re) <-> isEmptyᵣᵦ(V).
Proof.
  intros [HeqDom _]. now apply fT_eqDom_Empty.
Qed.

Corollary wf_env_fT_is_empty (Re : ℜ) (V : 𝓥):
  Wfᵣₜ(Re,V) -> RC.Raw.is_empty Re = RE.Raw.is_empty V.
Proof.
  intros [HeqDom _]. now apply fT_eqDom_is_empty.
Qed.

Fact wf_env_fT_in (Re : ℜ) (V : 𝓥):
  Wfᵣₜ(Re,V) -> forall r, r ∈ᵣᵪ Re <-> r ∈ᵣᵦ V.
Proof. now intros [HeqDom _]. Qed.

Fact wf_env_fT_find (Re : ℜ) (V : 𝓥):
  Wfᵣₜ(Re,V) -> forall r τ τ', 
  Re ⌈ r ⩦ (τ, τ') ⌉ᵣᵪ -> exists v, V ⌈r ⩦ v⌉ᵣᵦ.
Proof. 
  intros [HeqDom _] r τ τ' HfRe.
  assert (r ∈ᵣᵪ Re).
  { exists (τ,τ'). now apply RC.OP.P.find_2. }
  rewrite HeqDom in *. destruct H.
  exists x. now apply RE.OP.P.find_1.
Qed.


Fact wf_env_fT_well_typed (Re : ℜ) (V : 𝓥):
  Wfᵣₜ(Re,V) -> 
  forall (r : resource) (v : 𝑣) (τ τ' : Τ),
  Re ⌈ r ⩦ (τ,τ') ⌉ᵣᵪ -> V ⌈ r ⩦ v ⌉ᵣᵦ -> 
  match v with
    | (⩽ v' … ⩾) => ∅ᵥᵪ ⋅ Re ⊫ v' ∈ τ'
    | (⩽ … v' ⩾) => ∅ᵥᵪ ⋅ Re ⊫ v' ∈ τ
  end.
Proof. intros [_ Hwt] r v τ τ' HfRe HfV. apply (Hwt r); assumption. Qed.

Fact wf_env_fT_max (Re : ℜ) (V : 𝓥):
  Wfᵣₜ(Re,V) -> maxᵣᵪ(Re) = maxᵣᵦ(V).
Proof.
  intros [HeqDom _]. now apply fT_eqDom_max.
Qed.

Corollary wf_env_fT_new (Re : ℜ) (V : 𝓥):
  Wfᵣₜ(Re,V) -> newᵣᵪ(Re) = newᵣᵦ(V).
Proof.
  intro wf; unfold RC.Ext.new_key,RE.Ext.new_key.
  apply wf_env_fT_is_empty in wf as HisEmp.
  destruct (RC.Raw.is_empty Re) eqn:HEmp.
  - now rewrite <- HisEmp.
  - rewrite <- HisEmp; f_equal; now apply wf_env_fT_max.
Qed.

#[export] 
Instance wfFT_eq : Proper (RC.eq ==> RE.eq ==> iff) (wf_env_fT).
Proof.
  repeat red; split; intros [HeqDom Hwt].
  - split.
    -- split; intros.
       + rewrite <- H0. rewrite <- HeqDom. now rewrite H.
       + rewrite <- H. rewrite HeqDom. now rewrite H0.
    -- intros. rewrite <- H in *. rewrite <- H0 in *.
       apply (Hwt r τ τ' v) in H2; auto.
       destruct v; now rewrite <- H.
  - split.
    -- split; intros.
       + rewrite H0. rewrite <- HeqDom. now rewrite <- H.
       + rewrite H. rewrite HeqDom. now rewrite <- H0.
    -- intros. rewrite H in *. rewrite H0 in *.
       apply (Hwt r τ τ' v) in H2; auto.
       destruct v; now rewrite H.
Qed.



(** ** Well formed property between the resource context and real resource environment *)

Reserved Notation "'Wfₜₜ(' Re , Fl )" (at level 50).

(** *** Definition *)

Definition wf_env_TT (Re : ℜ) (Fl : 𝐅) :=
  (forall r, r ∈ᵣᵪ Re <-> r ∈ᵣₔ Fl) /\
  (forall r τ τ' rf, 
    Re ⌈ r ⩦ (τ,τ') ⌉ᵣᵪ -> 
    Fl ⌈ r ⩦ rf ⌉ᵣₔ -> 
    RFlow.well_typed_rflow (∅ᵥᵪ) Re rf τ' τ
  ).

Notation "'Wfₜₜ(' Re , Fl )" := (wf_env_TT Re Fl) (at level 50).

(** *** Property *)

Fact tT_eqDom_Empty (Re : ℜ) (Fl : 𝐅):
 (forall r, r ∈ᵣᵪ Re <-> r ∈ᵣₔ Fl) -> isEmptyᵣᵪ(Re) <-> isEmptyᵣₔ(Fl).
Proof.
  intro HeqDom. split; intros HEmp.
  - intro r. 
    assert (r ∉ᵣᵪ Re).
    { intro. destruct H. now apply (HEmp r x). }
    intro v. intro Hc.
    apply H. rewrite HeqDom. now exists v.
  - intro r.
    assert (r ∉ᵣₔ Fl).
    { intro. destruct H. now apply (HEmp r x). }
    rewrite <- HeqDom in H.
    intro v. intro Hc.
    apply H. now exists v.
Qed.
  
Fact tT_eqDom_is_empty (Re : ℜ) (Fl : 𝐅):
  (forall r, r ∈ᵣᵪ Re <-> r ∈ᵣₔ Fl) -> RC.Raw.is_empty Re = RF.Raw.is_empty Fl.
Proof.
  intro HeqDom.
  destruct (RC.Raw.is_empty Re) eqn:HisEmp;
  destruct (RF.Raw.is_empty Fl) eqn:HisEmp';
  try reflexivity.
  - exfalso.  
    apply RC.OP.P.is_empty_2 in HisEmp.
    rewrite tT_eqDom_Empty in HisEmp; eauto.
    apply RF.OP.P.is_empty_1 in HisEmp.
    rewrite HisEmp' in *. inversion HisEmp.
  - exfalso.  
    apply RF.OP.P.is_empty_2 in HisEmp'.
    rewrite <- tT_eqDom_Empty in HisEmp'; eauto.
    apply RC.OP.P.is_empty_1 in HisEmp'.
    rewrite HisEmp in *. inversion HisEmp'.
Qed.

Fact tT_eqDom_max (Re : ℜ) (Fl : 𝐅):
  (forall r, r ∈ᵣᵪ Re <-> r ∈ᵣₔ Fl) -> maxᵣᵪ(Re) = maxᵣₔ(Fl).
Proof.
  revert Fl.
  induction Re using RC.OP.P.map_induction; intros Fl HeqDom.
  - rewrite RC.Ext.max_key_Empty_spec; auto.
    rewrite (tT_eqDom_Empty Re Fl HeqDom) in H.
    rewrite RF.Ext.max_key_Empty_spec; auto.
  - assert (HAddV: exists v, Addᵣₔ x v (RF.Raw.remove x Fl) Fl). 
    {
      assert (x ∈ᵣₔ Fl). { 
        rewrite <- HeqDom. unfold RC.OP.P.Add in *; rewrite H0.
        rewrite RC.OP.P.add_in_iff; auto. 
      }
      destruct H1 as [v HM].
      exists v. unfold RF.OP.P.Add.
      rewrite RF.OP.P.add_remove_1.
      symmetry. rewrite RF.OP.P.add_id.
      now apply RF.OP.P.find_1.
    }
    destruct HAddV as [v HAddV]. remember (RF.Raw.remove x Fl) as V0.
    assert (HeqDom': forall r : RContext.Raw.key, r ∈ᵣᵪ Re1 <-> r ∈ᵣₔ V0).
    { 
      intro r; split; intro HIn.
      - assert (r ∈ᵣᵪ Re2). 
        { unfold RC.OP.P.Add in *; rewrite H0. rewrite RC.OP.P.add_in_iff; auto. }
        rewrite HeqDom in H1.
        unfold RF.OP.P.Add in *; rewrite HAddV in *.
        rewrite RF.OP.P.add_in_iff in H1; destruct H1; subst; auto.
        contradiction.
      - assert (r ∈ᵣₔ Fl). 
        { unfold RF.OP.P.Add in *; rewrite HAddV. rewrite RF.OP.P.add_in_iff; auto. }
        rewrite <- HeqDom in H1.
        unfold RC.OP.P.Add in *. rewrite H0 in *.
        rewrite RC.OP.P.add_in_iff in H1; destruct H1; subst; auto.
        rewrite RF.OP.P.remove_in_iff in HIn; destruct HIn; contradiction.
    }
    apply IHRe1 in HeqDom' as Hmax.
    unfold RC.OP.P.Add in *. rewrite H0. 
    unfold RF.OP.P.Add in *. rewrite HAddV.
    destruct (Resource.ltb_spec0 x (maxᵣᵪ(Re1))).
    -- rewrite RC.Ext.max_key_add_spec_2; auto.
       rewrite RF.Ext.max_key_add_spec_2; auto.
       + subst. intro Hc. 
        rewrite RF.OP.P.remove_in_iff in Hc. 
        destruct Hc; contradiction.
       + now rewrite Hmax in *.
    -- rewrite RC.Ext.max_key_add_spec_1; auto; try lia.
       rewrite Hmax in n.
       rewrite RF.Ext.max_key_add_spec_1; auto; try lia.
       subst. intro Hc. 
       rewrite RF.OP.P.remove_in_iff in Hc. 
       destruct Hc; contradiction.
Qed.

Corollary wf_env_TT_Empty (Re : ℜ) (Fl : 𝐅):
  Wfₜₜ(Re,Fl) -> isEmptyᵣᵪ(Re) <-> isEmptyᵣₔ(Fl).
Proof.
  intros [HeqDom _]. now apply tT_eqDom_Empty.
Qed.

Corollary wf_env_TT_is_empty (Re : ℜ) (Fl : 𝐅):
  Wfₜₜ(Re,Fl) -> RC.Raw.is_empty Re = RF.Raw.is_empty Fl.
Proof.
  intros [HeqDom _]. now apply tT_eqDom_is_empty.
Qed.

Fact wf_env_TT_in (Re : ℜ) (Fl : 𝐅):
  Wfₜₜ(Re,Fl) -> forall r, r ∈ᵣᵪ Re <-> r ∈ᵣₔ Fl.
Proof. now intros [HeqDom _]. Qed.

Fact wf_env_TT_find (Re : ℜ) (Fl : 𝐅):
  Wfₜₜ(Re,Fl) -> forall r τ τ', 
  Re ⌈ r ⩦ (τ, τ') ⌉ᵣᵪ -> exists v, Fl ⌈r ⩦ v⌉ᵣₔ.
Proof. 
  intros [HeqDom _] r τ τ' HfRe.
  assert (r ∈ᵣᵪ Re).
  { exists (τ,τ'). now apply RC.OP.P.find_2. }
  rewrite HeqDom in *. destruct H.
  exists x. now apply RF.OP.P.find_1.
Qed.

Fact wf_env_TT_well_typed (Re : ℜ) (Fl : 𝐅):
  Wfₜₜ(Re,Fl) -> 
  forall (r : resource) rf (τ τ' : Τ),
  Re ⌈ r ⩦ (τ,τ') ⌉ᵣᵪ -> Fl ⌈r ⩦ rf⌉ᵣₔ -> 
  RFlow.well_typed_rflow (∅ᵥᵪ) Re rf τ' τ.
Proof. intros [_ Hwt] r v τ τ' HfRe HfV. apply (Hwt r); assumption. Qed.

Fact wf_env_TT_max (Re : ℜ) (Fl : 𝐅):
  Wfₜₜ(Re,Fl) -> maxᵣᵪ(Re) = maxᵣₔ(Fl).
Proof.
  intros [HeqDom _]. now apply tT_eqDom_max.
Qed.

Corollary wf_env_TT_new (Re : ℜ) (Fl : 𝐅):
  Wfₜₜ(Re,Fl) -> newᵣᵪ(Re) = newᵣₔ(Fl).
Proof.
  intro wf; unfold RC.Ext.new_key,RF.Ext.new_key.
  apply wf_env_TT_is_empty in wf as HisEmp.
  destruct (RC.Raw.is_empty Re) eqn:HEmp.
  - now rewrite <- HisEmp.
  - rewrite <- HisEmp; f_equal; now apply wf_env_TT_max.
Qed.

Lemma wf_env_TT_to_fT Re Fl : 
  Wfₜₜ(Re,Fl) -> Wfᵣₜ(Re,RFlows.nexts Fl).
Proof.
  intros [HeqDom Hwt]; split.
  - intro r. split; intro HIn.
    -- apply RF.nexts_in_iff.
       now apply HeqDom.
    -- apply HeqDom.
       now apply RF.nexts_in_iff.
  - intros r τ τ' v HfRe HfV. 
    apply RFlows.nexts_find_e_spec in HfV as Hrf.
    destruct Hrf as [rf Heq]; subst.
    apply (wf_env_TT_find Re Fl) in HfRe as HfFl;
    try (now split).
    destruct HfFl as [rf' HfFl].
    apply RFlows.nexts_find_spec in HfFl as HfnFl.
    rewrite HfnFl in HfV. inversion HfV; subst; clear HfV.
    unfold RFlows.nexts_func_1. rewrite <- H0. clear H0.
    eapply Hwt in HfFl; eauto.
    now apply RFlow.rflow_well_typed_next with (β := τ).
Qed.

Lemma wf_env_fT_update (Re : ℜ) V (Fl : 𝐅): 
  Wfₜₜ(Re,Fl) ->  Wfᵣₜ(Re,V) -> Wfₜₜ(Re,(RFlows.puts V Fl)).
Proof.
  intros [HeqDomTT HwtTT] [HeqDomfT HwtfT]. split.
  - intro r; split; intro HIn.
    -- apply RF.puts_In_spec.
       now apply HeqDomTT.
    -- apply HeqDomTT.
       now apply RF.puts_In_spec in HIn.
  - intros r τ τ' rf HfRe HfpFl.
    apply wf_env_fT_find with (V := V) in HfRe as HfV;
    try (now split).
    destruct HfV as [v HfV].
    apply wf_env_TT_find with (Fl := Fl) in HfRe as HfFl;
    try (now split).
    destruct HfFl as [rf1 HfFl].

    move HeqDomfT before HeqDomTT; move r after Re;
    move τ before r; move τ' before τ; move rf before r;
    move rf1 before rf; move v before r.

    apply RF.puts_find_spec with (V := V) in HfFl as tmp.
    rewrite HfpFl in tmp; inversion tmp; subst; clear tmp.
    eapply HwtTT in HfFl as HwTT; eauto; clear HwtTT.
    eapply HwtfT in HfV as HwfT; eauto; clear HwtfT.
    unfold RF.puts_func_1; rewrite HfV.
    destruct v.
    -- now apply RFlow.rflow_well_typed_None.
    -- now apply RFlow.rflow_well_typed_Some.  
Qed.