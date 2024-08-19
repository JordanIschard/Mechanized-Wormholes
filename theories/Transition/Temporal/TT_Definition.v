From Mecha Require Import Resource Term ReadStock Stock REnvironment Typ
                          FT_Definition Sample Samples VContext RContext Cell Typing.
Import ResourceNotations TermNotations StockNotations REnvironmentNotations
       SamplesNotations RContextNotations VContextNotations CellNotations
       TypNotations.

(** * Transition - Temporal - Definition

Wormholes’s semantics is given by three sets of transition rules: the evaluation
transition, which extends standard β-reduction; the functional transition which
performs the logical instant, and the temporal transition which corresponds to
the reactivity of the program: it initializes the resources values, performs the
instant via functional transition and updates the system.

In this file, we focus on the temporal transition.
*)

Open Scope renvironment_scope.

(** ** Temporal Transition *)

Definition temporal (S S1 : 𝐒) (P P' : Λ) (W W1 : 𝐖) :=
  exists (Vin Vout : 𝐕) Wnew _tv,
    (Vin = Stock.env_from_stock W (Samples.nexts S))%re /\
                    
    ⪡ Vin ; unit ; P ⪢ ⭆ ⪡ Vout ; _tv ; P' ; Wnew ⪢ /\
                    
    (S1 = Samples.puts Vout ([⧐ (Vin⁺)%re – (Vout⁺ - Vin⁺)%re] S))%rf /\ 
    (W1 = Stock.update Wnew Vout)%sk. 

Notation "'⟦' S ';' W ';' P '⟧' '⟾' '⟦' S1 ';' W1 ';' P1 '⟧'" 
  := (temporal S S1 P P1 W W1) (at level 30, S constr, S1 constr,
                                             P custom wh, P1 custom wh, 
                                             W constr, W1 constr, no associativity).


Definition wf_env_tT (Re : ℜ) (S : 𝐒) (W : 𝐖) :=  
  (* key domain match *)
  (forall r, (r ∈ Re)%rc <-> (r ∈ S)%rf \/  (r ∈ W)%sk) /\ 
  (* validity properties *)
  (Re⁺ ⊩ Re)%rc /\ (S⁺ ⊩ S)%rf /\
  (* typing *)
  (forall r τ τ' v,  S⌊r⌋%rf = Some v -> Re⌊r⌋%rc = Some (τ,τ') -> 
                      Sample.well_typed (∅%vc) Re (Sample.shift (S⁺%rf) ((Re⁺)%rc - (S⁺)%rf) v) τ' τ)
                                            /\
  (forall (r : resource) (v : Λ) (τ τ' : Τ), 
        W⌊r⌋%sk = Some v -> Re⌊r⌋%rc = Some (τ',τ) -> ∅%vc ⋅ Re ⊫ v ∈ τ)
  .


Notation "'Wfₜₜ(' Re , Sa , W )" := (wf_env_tT Re Sa W) (at level 50).