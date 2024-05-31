From Coq Require Import Program Lia Relations.Relation_Definitions Classes.RelationClasses PeanoNat
                        Classical_Prop Classical_Pred_Type Bool.Bool Lists.List Classes.Morphisms.
From Mecha Require Import Resource Resources Term Typ Var ReadStock WriteStock Typing VContext RContext 
                          Cell REnvironment Stock ET_Definition ET_Props ET_Preservation 
                          FT_Definition FT_Props FT_Preservation FT_Progress.

Section safety.

Hypothesis all_arrow_halting : forall Re t α β,
  ∅ᵥᵪ ⋅ Re ⊫ arr(t) ∈ (α ⟿ β ∣ ∅ᵣₛ) -> forall v, ∅ᵥᵪ ⋅ Re ⊫ v ∈ α -> halts (Re⁺ᵣᵪ) <[t v]>.

(** * Proof of Resource safety *)

Theorem safety_resources_interaction (Re : ℜ) (V : 𝓥) (t : Λ) (τ τ' : Τ) (R : resources) :

    (* (1) *) halts (Re⁺ᵣᵪ) t -> (* (2) *) RE.halts (Re⁺ᵣᵪ) V ->

    (* (3) *) Wfᵣₜ(Re,V) -> (* (4) *) (forall (r : resource), (r ∈ R)%rs -> RE.unused r V) ->

    (* (5) *) ∅ᵥᵪ ⋅ Re ⊫ t ∈ (τ ⟿ τ' ∣ R) -> 

  (*-----------------------------------------------------------------------------------------------*)
    forall (tv : Λ), (* (6) *) halts (Re⁺ᵣᵪ) tv -> (* (7) *) ∅ᵥᵪ ⋅ Re ⊫ tv ∈ τ -> 

    exists (R' : resources) (V1 : 𝓥) (tv' t' : Λ) (W: 𝐖), 
      (*  (8) *) ⪡ V ; tv ; t ⪢ ⭆ ⪡ V1 ; tv' ; t' ; W ⪢ /\

      (*  (8) *) (R ⊆ R')%rs    /\
      (* (10) *)(forall (r : resource), (r ∉ R)%rs /\ (r ∈ᵣᵦ V) -> 
                    ([⧐ᵣᵦ (V⁺ᵣᵦ) ≤ ((V1⁺ᵣᵦ) - (V⁺ᵣᵦ))] V) ⌊r⌋ᵣᵦ = V1 ⌊r⌋ᵣᵦ) /\
      (* (11) *) (forall (r : resource), (r ∈ (R' \ R))%rs -> (r ∈ (Stock.to_RS W))%rs /\ (r ∉ᵣᵦ V)) /\ 
      (* (12) *) (forall (r : resource), (r ∈ R)%rs -> RE.used r V1).
Proof.
  intros Hlt HltV Hwf Hunsd Hwt tv Hltv Hwtv.
  apply (progress_of_functional all_arrow_halting Re V tv t _ τ' R) in Hwtv as prog; auto.
  destruct prog as [V1 [tv' [t' [W [HfT [Hlt' [Hltv' HltV1]]]]]]].

  (* clean *)
  move tv before t; move tv' before tv; move t' before t; move V1 before V;
  move HltV1 before HltV; move Hlt' before Hlt; move Hltv' before Hltv; move Hwt before Hwtv;
  move Hunsd after HfT; move Hwf before Hunsd.
  (* clean *)

  apply (functional_preserves_typing_gen all_arrow_halting Re V V1 W _ tv' t t' _ τ' R) in Hwtv as preserve; auto.
  destruct preserve as [_ [HeqVV1 [_  [R' [_ [Hsub [_ [_ [HW [Husd _]]]]]]]]]].
  exists R'; exists V1; exists tv'; exists t'; exists W; repeat split; auto.
  - eapply HW; assumption.
  - eapply HW; assumption.
Qed.

End safety.