From Coq Require Import  Classes.Morphisms.
From Mecha Require Import Resource Term ReadStock Stock REnvironment
                          Resources Sample Samples RContext VContext Typing Typ
                          ET_Definition ET_Preservation FT_Definition FT_Props TT_Definition.
Import ResourceNotations TermNotations StockNotations REnvironmentNotations
       SamplesNotations RContextNotations VContextNotations TypNotations
       ResourcesNotations SetNotations.

Module RE := REnvironment.


(** * Transition - Temporal - Properties *)

Lemma resource_used_init_unused : forall Re t α β R W Sa V,
  ∅%vc ⋅ Re ⊫ t ∈ (α ⟿ β ∣ R) ->
  halts (Re⁺)%rc t ->
  Wfᵣₜ(Re,V) ->
  (V = Stock.env_from_stock W (Samples.nexts Sa))%re ->
  
  (forall r, (r ∈ R)%s -> RE.unused r V).
Proof.
  intros Re t α β R W Sa V Hwt Hlt Hwf Heq r HInR.
  destruct Hlt as [t' [HmeT Hvt']].
  apply multi_preserves_typing with (t' := t') in Hwt; auto.
  - apply typing_Re_R with (r := r) in Hwt as HInRe; auto.
    rewrite (wf_env_fT_in Re V Hwf) in HInRe.
    rewrite Heq in *. 
    destruct HInRe as [v HfV].
    apply RE.OP.P.find_1 in HfV.
    apply Stock.env_from_stock_unused_1 in HfV as Hunsd.
    -- destruct v; simpl in *.
       + now exists λ.
       + contradiction.
    -- intros r1 v1 HfSa.
       assert (r1 ∈ Sa)%rf. 
       { rewrite Samples.nexts_in_iff. exists v1. now apply RE.OP.P.find_2. }
       apply Samples.nexts_unused in H; destruct H.
       apply RE.OP.P.find_2 in HfSa, H. 
       eapply RE.OP.P.mapsto_fun in HfSa; eauto.
       subst; now simpl.
  - eapply (wf_env_fT_valid Re V Hwf). 
Qed.

Lemma wf_env_TT_to_fT Re Sa W : 
  Wfₜₜ(Re,Sa,W) -> Wfᵣₜ(Re,Stock.env_from_stock W (Samples.nexts Sa)).
Proof. 
  intros [HeqDom [HvRe [HvSa [HwtSa HwtW]]]].
  repeat split; auto.
  - intro HIn.
    apply Stock.env_from_stock_in_iff.
    apply HeqDom in HIn as [HIn |]; auto.
    right; now apply Samples.nexts_in_iff.
  - intro HIn.
    apply HeqDom; auto.
    apply Stock.env_from_stock_in_iff in HIn as [| HIn]; auto.
    left; now apply Samples.nexts_in_iff.
  - admit.
  - intros r τ τ' v HfRe HfW.
    apply Stock.env_from_stock_find_spec in HfW as HI;
    destruct HI as  [HIn | HfSa].
    -- admit. 
    -- apply Samples.nexts_find_e_spec in HfSa as Heq.
       destruct Heq as [rf Heq]; subst. 
       destruct rf; simpl in *.
       assert (r ∈ Sa)%rf. 
       { 
        rewrite Samples.nexts_in_iff. 
        exists (Samples.nexts_func_1 (r0, o)). 
        now apply REnvironment.find_2.
       }
       destruct H; apply Samples.find_1 in H.
       apply Samples.nexts_find_spec in H as H'.
       rewrite HfSa in H'; destruct x; inversion H'; subst.
       clear H'.
       eapply HwtSa in H; eauto. destruct H; now simpl in *.
Admitted.

#[export]
Instance wfTT_eq : Proper (RContext.eq ==> Samples.eq ==> Stock.eq ==> iff) wf_env_tT.
Proof. Admitted.