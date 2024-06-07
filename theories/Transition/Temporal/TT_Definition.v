From Mecha Require Import Resource Term ReadStock WriteStock Stock REnvironment
                          FT_Definition Sample Samples RContext.
Import ResourceNotations TermNotations StockNotations REnvironmentNotations
       SamplesNotations RContextNotations.

(** * Transition - Temporal - Definition

Wormholes’s semantics is given by three sets of transition rules: the evaluation
transition, which extends standard β-reduction; the functional transition which
performs the logical instant, and the temporal transition which corresponds to
the reactivity of the program: it initializes the resources values, performs the
instant via functional transition and updates the system.

In this file, we focus on the temporal transition.
*)

(** ** Temporal Transition *)

Definition temporal (S S1 : 𝐒) (P P' : Λ) (W W1 : 𝐖) :=
  exists (Vin Vout : 𝓥) Wnew _tv,
    (Vin = Stock.init_virtual W (Samples.nexts S))%re /\
                    
    ⪡ Vin ; unit ; P ⪢ ⭆ ⪡ Vout ; _tv ; P' ; Wnew ⪢ /\
                    
    (S1 = Samples.puts Vout ([⧐ᵣₔ (Vin⁺ᵣᵦ) ≤ (Vout⁺ᵣᵦ - Vin⁺ᵣᵦ)] S))%rf /\ 
    (W1 = Stock.update Wnew Vout)%sk. 

Notation "'⟦' S ';' W ';' P '⟧' '⟾' '⟦' S1 ';' W1 ';' P1 '⟧'" 
  := (temporal S S1 P P1 W W1) (at level 30, S constr, S1 constr,
                                             P custom wh, P1 custom wh, 
                                             W constr, W1 constr, no associativity).


Definition wf_env_tT (Re : ℜ) (S : 𝐒) (W : 𝐖) := True.

Notation "'Wfₜₜ(' Re , Sa , W )" := (wf_env_tT Re Sa W) (at level 50).