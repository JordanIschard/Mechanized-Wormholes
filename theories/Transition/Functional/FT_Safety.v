From Coq Require Import Program Lia Relations.Relation_Definitions Classes.RelationClasses PeanoNat
                        Classical_Prop Classical_Pred_Type Bool.Bool Lists.List Classes.Morphisms.
From Mecha Require Import Resource Resources Term Typ Var ReadStock Typing VContext RContext 
                          Cell REnvironment Stock ET_Definition ET_Props ET_Preservation 
                          FT_Definition FT_Props FT_Preservation FT_Progress.
Import ResourceNotations TermNotations TypNotations CellNotations
       VContextNotations RContextNotations REnvironmentNotations
       ReadStockNotations ResourcesNotations SetNotations StockNotations.
       
(** * Transition - Functional - Safety *)

Section safety.

Open Scope renvironment_scope.

Hypothesis all_arrow_halting : forall Re t α β,
  ∅%vc ⋅ Re ⊫ arr(t) ∈ (α ⟿ β ∣ ∅%s) -> forall v, ∅%vc ⋅ Re ⊫ v ∈ α -> halts (Re⁺)%rc <[t v]>.

(** * Proof of Resource safety *)

Theorem safety_resources_interaction (Re : ℜ) (V : 𝐕) (t : Λ) (τ τ' : Τ) (R : resources) :

    (* (1) *) halts (Re⁺)%rc t -> (* (2) *) RE.halts (Re⁺)%rc V ->

    (* (3) *) Wfᵣₜ(Re,V) -> (* (4) *) (forall (r : resource), (r ∈ R)%s -> RE.unused r V) ->

    (* (5) *) ∅%vc ⋅ Re ⊫ t ∈ (τ ⟿ τ' ∣ R) -> 

  (*-----------------------------------------------------------------------------------------------*)
    forall (tv : Λ), (* (6) *) halts (Re⁺)%rc tv -> (* (7) *) ∅%vc ⋅ Re ⊫ tv ∈ τ -> 

    exists (R' : resources) (V1 : 𝐕) (tv' t' : Λ) (W: 𝐖), 
      (*  (8) *) ⪡ V ; tv ; t ⪢ ⭆ ⪡ V1 ; tv' ; t' ; W ⪢ /\

      (*  (9) *) (R ⊆ R')%s    /\
      (* (10) *)(forall (r : resource), (r ∉ R)%s /\ (r ∈ V) -> 
                    ([⧐ (V⁺) – ((V1⁺) - (V⁺))] V) ⌊r⌋ = V1 ⌊r⌋) /\
      (* (11) *) (forall (r : resource), (r ∈ (R' \ R))%s -> (r ∈ W)%sk /\ (r ∉ V)) /\ 
      (* (12) *) (forall (r : resource), (r ∈ R)%s -> RE.used r V1).
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