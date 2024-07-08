From Coq Require Import Relations.Relation_Operators.
From Mecha Require Import Resource Term ReadStock Stock REnvironment
                          Sample Samples RContext VContext Typing Typ
                          ET_Definition ET_Preservation FT_Definition FT_Props 
                          FT_Preservation TT_Definition TT_Props Resources.
Import ResourceNotations TermNotations StockNotations REnvironmentNotations
       SamplesNotations RContextNotations VContextNotations TypNotations
       ResourcesNotations SetNotations.

Section preservation.

Hypothesis all_arrow_halting : forall Re t α β,
  ∅%vc ⋅ Re ⊫ arr(t) ∈ (α ⟿ β ∣ ∅%s) -> forall v, ∅%vc ⋅ Re ⊫ v ∈ α -> halts (Re⁺)%rc <[t v]>.

Theorem temporal_preserves_typing (Re : ℜ) (Sa Sa' : 𝐒) (W W' : 𝐖) (P P' : Λ) (R : resources) :

    (* (1) *) halts (Re⁺)%rc P -> (* (2) *) Samples.halts (Re⁺)%rc Sa -> Stock.halts (Re⁺)%rc W ->
              Wfₜₜ(Re,Sa,W) ->

    (* (1) *) ∅%vc ⋅ Re ⊫ P ∈ (𝟙 ⟿ 𝟙 ∣ R) ->
    (* (3) *) ⟦ Sa ; W ; P ⟧ ⟾ ⟦ Sa' ; W' ; P' ⟧ ->

(*----------------------------------------------------*)
   exists Re1 R1,
    (R ⊆ R1)%s /\ (Re ⊆ Re1)%rc /\
    ∅%vc ⋅ Re1 ⊫ P' ∈ (𝟙 ⟿ 𝟙 ∣ R1) /\ 
    Wfₜₜ(Re1,Sa',W') /\ 
    (* (7) *) halts (Re1⁺)%rc P' /\ (* (8) *) Samples.halts (Re1⁺)%rc Sa' /\ Stock.halts (Re1⁺)%rc W'.
Proof.
  intros HlP HlSa HlW HwfTT HwP HTT.
  destruct HTT as [Vin [Vout [Wnew [_tv [HeqVin [fT [HeqSa' HeqW']]]]]]].

  move Vin before R; move Vout before Vin; move Wnew before W'; move _tv before P'.
  move fT before HwP.

  apply wf_env_TT_to_fT in HwfTT as HwfFT.
  rewrite <- HeqVin in HwfFT.

  apply (functional_preserves_typing_gen 
              all_arrow_halting Re _ _ _ _ _ _ _ Typ.ty_unit Typ.ty_unit R) 
              in fT as IH; 
  auto.
  - destruct IH as 
    [Hunsd [Hunc [Re1 [R1 [HsubRe [HsubR [HwfFT1 
    [HwtW [HW [Husd [_ [HwtP' [HlP' [_ [HlVout HlWnew]]]]]]]]]]]]]]].
    exists Re1; exists R1.
    split; auto; split; auto; split; auto.
    split.
    -- rewrite HeqW'; rewrite HeqSa'. 
       admit.
    -- split; auto; split.
       + rewrite HeqSa'. apply Samples.halts_puts; auto.
         rewrite <- (wf_env_fT_new Re Vin HwfFT).
         rewrite <- (wf_env_fT_new Re1 Vout HwfFT1).
         apply Samples.halts_weakening; auto.
         apply RContext.Ext.new_key_Submap_spec; assumption.
       + rewrite HeqW'. apply Stock.halts_update; auto.
  - exists <[unit]>; split; auto; apply rt1n_refl.
  - rewrite HeqVin. apply Stock.halts_env_from_stock; auto.
    now apply Samples.halts_nexts.
Admitted.

End preservation.