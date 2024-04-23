From Coq Require Import Lists.List.
From Mecha Require Import RealResource REnvironment Term Functional Resource Cell Typing VContext Typ
               Resources Evaluation RContext.

(** * Transition - Temporal

rsf's semantics are divided in three sub semantics:
- evaluation transition
- functional transition
- temporal transition <--

*)

Module RE := REnvironment.
Reserved Notation "'Wfₜₜ(' Re , Rf )" (at level 50).

(** *** Definition *)

Inductive temporal : RealResources.t -> RealResources.t -> Λ -> Λ -> Prop :=
 TT_instant : forall Vin Vout _tv (R R' : RealResources.t) (P P' : Λ),

                    (Vin = RE.embeds (RealResources.nexts R))%re ->
                    ⪡ Vin ; unit ; P ⪢ ⭆ ⪡ Vout ; _tv ; P' ⪢ ->
                    R' = RealResources.puts (RE.extracts Vout) R -> 
                    
                    temporal R R' P P'.

Notation "'⟦' R ';' P '⟧' '⟾' '⟦' R1 ';' P1 '⟧'" := (temporal R R1 P P1) 
                                                     (at level 30, R constr, R1 constr,
                                                         P custom rsf, P1 custom rsf, 
                                                        no associativity).

Inductive multi_temporal : RealResources.t -> RealResources.t -> Λ -> Λ -> Prop :=
  TT_step : forall R R' R'' (P P' P'' : Λ), 
                  ⟦ R ; P ⟧ ⟾ ⟦ R' ; P' ⟧ -> 
                  multi_temporal R' R'' P' P'' -> 
                  multi_temporal R R'' P P''.

Notation "'⟦' R ';' P '⟧' '⟾⋆' '⟦' R1 ';' P1 '⟧'" := (multi_temporal R R1 P P1) 
                                                     (at level 30, R constr, R1 constr,
                                                         P custom rsf, P1 custom rsf, 
                                                        no associativity).

Inductive wf_env_TT : ℜ -> RealResources.t -> Prop :=
  | wfTT_empty  : forall (Re : ℜ) (Fl : RealResources.t), 
                     isEmptyᵣᵪ(Re) -> Wfₜₜ(Re,nil)

  | wfTT_init   : forall (Re Re' : ℜ) (Fl : RealResources.t) (τ τ' : Τ) (r : RealResource.t),
      Wfₜₜ(Re,Fl) ->
      Addᵣᵪ (newᵣᵪ(Re)) (τ,τ') Re Re' ->
      Streams.ForAll (fun v => ∅ᵥᵪ ⋅ Re ⊫ {Streams.hd v} ∈ τ') (fst r) -> 
      Streams.ForAll (fun v => ∅ᵥᵪ ⋅ Re ⊫ {Streams.hd v} ∈ τ) (snd r) -> 
      Wfₜₜ(Re',Fl ++ (r :: nil))

  | wfTT_update : forall (Re : ℜ) (V : 𝓥) Rf,
                    Wfᵣₜ(Re,V) -> 
                    Wfₜₜ(Re,Rf) ->
                    Wfₜₜ(Re,RealResources.puts (RE.extracts V) Rf)
where "'Wfₜₜ(' Re , Fl )" := (wf_env_TT Re Fl).

Lemma wf_env_TT_to_fT Re Fl : 
  Wfₜₜ(Re,Fl) -> Wfᵣₜ(Re,RE.embeds (RealResources.nexts Fl)).
Proof.
  intro inst; induction inst; simpl.
  - unfold RE.embeds; simpl; apply wfFT_empty; auto.
    apply RE.OP.P.empty_1.
  - destruct r; simpl in *. unfold RealResources.nexts.
    rewrite map_app; simpl. unfold RE.embeds.
    unfold RE.embeds_gen; rewrite <- fold_left_rev_right. 
    fold RE.embeds_func_revert. rewrite rev_unit; simpl.
    rewrite fold_left_rev_right. unfold RE.embeds_func_revert.
    replace (fold_left (fun (x : RE.t) (y : Λ) => RE.embeds_func x y) (map RealResource.next Fl) (∅ᵣᵦ))
    with (RE.embeds (RealResources.nexts Fl)); auto.
    unfold RE.embeds_func.
    
    destruct s; simpl in *. inversion H0; simpl in *.
    eapply wfFT_init with (v := λ); eauto.
    unfold RE.OP.P.Add; reflexivity.
  - admit.
Admitted.

(** *** Initialization *)

Theorem initialization_unused : forall l,
  RE.For_all (fun _ v => Cell.unused v) (RE.embeds l).
Proof.
  intros. apply RE.embedding_Forall_unused.
  unfold RE.For_all; intros. inversion H.
Qed.

Lemma resource_used_init_unused : forall Re t α β R l V,
  ∅ᵥᵪ ⋅ Re ⊫ t ∈ (α ⟿ β ∣ R) ->
  halts t ->
  Wfᵣₜ(Re,V) ->
  (V = (RE.embeds l))%re ->
  
  (forall r, (r ∈ R)%rs -> RE.unused r V).
Proof.
  intros. destruct H0 as [t' [HmeT Hvt']].
  apply multi_preserves_typing with (t' := t') in H; auto.
  apply typing_Re_R with (r := r) in H; auto.
  apply wf_env_fT_in with (V := V) in H; auto.
  rewrite H2 in *. destruct H; apply RE.OP.P.find_1 in H.
  apply initialization_unused in H as H'; destruct x; inversion H'.
  exists λ. now rewrite H2.
Qed. 


(** *** Proof of typing preservation through the temporal transition *)
Theorem temporal_preserves_typing (Re : ℜ) Rf Rf' (P P' : Λ) (R : resources) :

    (* (1) *) halts P -> (* (2) *) RealResources.halts Rf -> (* (3) *) all_arrow_halting ->

    (* (1) *) ∅ᵥᵪ ⋅ Re ⊫ P ∈ (𝟙 ⟿ 𝟙 ∣ R) ->
    (* (3) *) ⟦ Rf ; P ⟧ ⟾ ⟦ Rf' ; P' ⟧ ->
              Wfₜₜ(Re,Rf) ->

  (*----------------------------------------------------*)
      ∅ᵥᵪ ⋅ Re ⊫ P' ∈ (𝟙 ⟿ 𝟙 ∣ R) /\ Wfₜₜ(Re,Rf') /\ 
       (* (7) *) halts P' /\ (* (8) *) RealResources.halts Rf'.
Proof.
  intros HltP HltRf HlAll HwP HTT Hinst; inversion HTT; subst.
  apply wf_env_TT_to_fT in Hinst as Hinst'.
  eapply functional_preserves_typing in H0; eauto.
  - repeat split; destruct H0 as [_ [_ [HinstV [_ [_ [HwP' [HltP' [_ HltVout]]]]]]]]; auto.
    -- constructor; auto.
    -- apply RealResources.halts_puts; auto. now apply RE.halts_extract.
  - exists <[unit]>; split; auto.
  - apply REnvironment.halts_nexts in HltRf. unfold RE.halts; intros. rewrite H in *.
    eapply HltRf; eauto. 
  - now rewrite H.
Qed.

(** *** Proof of typing preservation through multi temporal transitions *)
Theorem multi_temporal_preserves_typing (Re : ℜ) Rf Rf' (P P' : Λ) (R : resources) :
    (* (1) *) halts P -> (* (2) *) RealResources.halts Rf -> (* (3) *) all_arrow_halting ->

    (* (1) *) ∅ᵥᵪ ⋅ Re ⊫ P ∈ (𝟙 ⟿ 𝟙 ∣ R) ->
    (* (3) *) ⟦ Rf ; P ⟧ ⟾⋆ ⟦ Rf' ; P' ⟧ ->
              Wfₜₜ(Re,Rf) ->

  (*----------------------------------------------------*)
      ∅ᵥᵪ ⋅ Re ⊫ P' ∈ (𝟙 ⟿ 𝟙 ∣ R) /\ Wfₜₜ(Re,Rf') /\ 
       (* (7) *) halts P' /\ (* (8) *) RealResources.halts Rf'.
Proof.
  intros HltP HltRf HAll HwP HTT; induction HTT; subst; intros.
  eapply temporal_preserves_typing in H as [HwP' [HWf [HltP' HlR0]]]; eauto.
Qed.


Theorem progress_of_temporal (Re : ℜ) (Rf : RealResources.t) (P : Λ) (R : resources) :

  (* (1) *) halts P -> (* (2) *) RealResources.halts Rf -> (* (3) *) all_arrow_halting ->

  (* (4) *) ∅ᵥᵪ ⋅ Re ⊫ P ∈ (𝟙 ⟿ 𝟙 ∣ R) -> (* (5) *) Wfₜₜ(Re,Rf) ->
  
  (*-------------------------------------------------------------------------------------------------*)
    exists Rf' P',  (* (6) *) ⟦ Rf ; P ⟧ ⟾ ⟦ Rf' ; P' ⟧ /\ 
                    (* (7) *) halts P' /\ (* (8) *) RealResources.halts Rf'.
Proof.
  intros HltP HltRf HlAll HwP Hinst. 
  assert (HwU : ∅ᵥᵪ ⋅ Re ⊫ unit ∈ 𝟙). { now constructor. }
  remember (RE.embeds (RealResources.nexts Rf)) as Vin.

  eapply progress_of_functional with (V := Vin) in HwU; eauto.
  - destruct HwU as [Vout [tv' [P' [HfT [HltP' [Hltv' HltVout]]]]]].
    exists (RealResources.puts (RE.extracts Vout) Rf); exists P'; repeat split; auto.
    -- econstructor; eauto; subst; reflexivity.
    -- apply RealResources.halts_puts; auto. now apply RE.halts_extract.
  - exists <[unit]>; split; auto.
  - apply REnvironment.halts_nexts in HltRf. unfold RE.halts; intros. rewrite HeqVin in *.
    eapply HltRf; eauto. 
  - subst. now apply wf_env_TT_to_fT.
  - apply wf_env_TT_to_fT in Hinst.
    destruct HltP as [P' [HmeT HltP']].
    eapply multi_preserves_typing in HwP; eauto.
    intros. apply typing_Re_R with (r := r) in HwP; auto.
    rewrite wf_env_fT_in in HwP; eauto.
    unfold RE.unused. 
    assert (RE.For_all (fun _ v => Cell.unused v) (RE.embeds (RealResources.nexts Rf))).
    { apply initialization_unused. }
    unfold RE.For_all in *. destruct HwP. apply RE.OP.P.find_1 in H1.
    apply H0 in H1 as Hunsd. destruct x; inversion Hunsd. exists λ.
    now rewrite HeqVin.
Qed.