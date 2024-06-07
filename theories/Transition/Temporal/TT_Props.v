From Mecha Require Import Resource Term ReadStock WriteStock Stock REnvironment
                          Sample Samples RContext VContext Typing Typ
                          ET_Definition ET_Preservation FT_Definition FT_Props TT_Definition.
Import ResourceNotations TermNotations StockNotations REnvironmentNotations
       SamplesNotations RContextNotations VContextNotations TypNotations.

Module RE := REnvironment.


(** * Transition - Temporal - Properties *)

Lemma resource_used_init_unused : forall Re t α β R W Sa V,
  ∅ᵥᵪ ⋅ Re ⊫ t ∈ (α ⟿ β ∣ R) ->
  halts (Re⁺ᵣᵪ) t ->
  Wfᵣₜ(Re,V) ->
  (V = Stock.init_virtual W (Samples.nexts Sa))%re ->
  
  (forall r, (r ∈ R)%rs -> RE.unused r V).
Proof.
  intros Re t α β R W Sa V Hwt Hlt Hwf Heq r HInR.
  destruct Hlt as [t' [HmeT Hvt']].
  apply multi_preserves_typing with (t' := t') in Hwt; auto.
  - apply typing_Re_R with (r := r) in Hwt as HInRe; auto.
    rewrite (wf_env_fT_in Re V Hwf) in HInRe.
    rewrite Heq in *. 
    destruct HInRe as [v HfV].
    apply RE.OP.P.find_1 in HfV.
    apply Stock.init_virtual_unused_1 in HfV as Hunsd.
    -- destruct v; simpl in *.
       + now exists λ.
       + contradiction.
    -- intros r1 v1 HfSa.
       assert (r1 ∈ᵣₔ Sa). 
       { rewrite Samples.nexts_in_iff. exists v1. now apply RE.OP.P.find_2. }
       apply Samples.nexts_unused in H; destruct H.
       apply RE.OP.P.find_2 in HfSa, H. 
       eapply RE.OP.P.mapsto_fun in HfSa; eauto.
       subst; now simpl.
  - eapply (wf_env_fT_valid Re V Hwf). 
Qed.

Lemma wf_env_TT_to_fT Re Sa W : 
  Wfₜₜ(Re,Sa,W) -> Wfᵣₜ(Re,Stock.init_virtual W (Samples.nexts Sa)).
Proof. Admitted.