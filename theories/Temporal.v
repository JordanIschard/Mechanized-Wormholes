From Coq Require Import Lists.List Lia Classes.Morphisms Bool.Bool.
From Mecha Require Import RFlows REnvironment Term Functional Resource Cell Typing VContext Typ
               Resources Evaluation RContext RFlow WfConEnv.

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
       + eapply wf_env_fT_update; eauto.
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