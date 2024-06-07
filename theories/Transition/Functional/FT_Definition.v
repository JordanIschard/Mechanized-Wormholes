From Mecha Require Import Resource Term Typ Var ReadStock WriteStock Typing
                          ET_Definition Cell VContext REnvironment RContext Stock.
Import ResourceNotations TermNotations TypNotations CellNotations
       VContextNotations RContextNotations REnvironmentNotations
       ReadStockNotations WriteStockNotations StockNotations.

(** * Transition - Functional - Definition

Wormholes’s semantics is given by three sets of transition rules: the evaluation
transition, which extends standard β-reduction; the functional transition which
performs the logical instant, and the temporal transition which corresponds to
the reactivity of the program: it initializes the resources values, performs the
instant via functional transition and updates the system.

In this file, we focus on the functional transition.
*)

Reserved Notation "⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st1 ; t1 ; W ⪢" (at level 57, V constr, 
                                                                V1 constr, st custom wh,
                                                                st1 custom wh,
                                                                t custom wh, 
                                                                t1 custom wh, 
                                                                no associativity).

(** ** Functional Transition *)

Inductive functional : 𝓥 -> Λ -> Λ -> 𝓥 -> Λ -> Λ -> 𝐖 -> Prop :=

  | fT_eT_sf  :  forall (V V1 : 𝓥) (st st' t t' t'' : Λ) (W : 𝐖),

        V⁺ᵣᵦ ⊨ t ⟼ t' -> ⪡ V ; st ; t' ⪢ ⭆ ⪡ V1 ; st' ; t'' ; W ⪢ -> 
    (*-----------------------------------------------------------------------*)
              ⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st' ; t'' ; W ⪢

  | fT_eT_sv  :  forall (V V1 : 𝓥) (st st' st'' t t' : Λ) (W : 𝐖),

        V⁺ᵣᵦ ⊨ st ⟼ st' -> ⪡ V ; st' ; t ⪢ ⭆ ⪡ V1 ; st'' ; t' ; W ⪢ -> 
    (*-----------------------------------------------------------------------*)
              ⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st'' ; t' ; W ⪢

  | fT_arr   :  forall (st t : Λ) (V : 𝓥), 

    (*---------------------------------------------------------*)
        ⪡ V ; st ; arr(t) ⪢ ⭆ ⪡ V ; (t st) ; arr(t) ; ∅ₛₖ ⪢ 

  | fT_first :  forall (v1 v1' v2 t t' : Λ) (τ : Τ) (V V1 : 𝓥) (W : 𝐖),

        ⪡ V ; v1 ; t ⪢ ⭆ ⪡ V1 ; v1' ; t' ; W ⪢ ->
    (*----------------------------------------------------------------------------------------*)
        ⪡ V ; ⟨v1,v2⟩ ; first(τ:t) ⪢ 
          ⭆ ⪡ V1 ; ⟨v1',[⧐ₜₘ {V⁺ᵣᵦ} ≤ {V1⁺ᵣᵦ - V⁺ᵣᵦ}] v2⟩ ; first(τ:t') ; W ⪢

  | fT_comp  :  forall (st st' st'' t1 t1' t2 t2' : Λ) (V V1 V2 : 𝓥) (W W': 𝐖),

                                         ⪡ V ; st ; t1 ⪢ ⭆ ⪡ V1 ; st' ; t1' ; W ⪢ ->
        ⪡ V1 ; st' ; ([⧐ₜₘ {V⁺ᵣᵦ} ≤ {V1⁺ᵣᵦ - V⁺ᵣᵦ}] t2) ⪢ ⭆ ⪡ V2 ; st'' ; t2' ; W' ⪢ ->
    (*---------------------------------------------------------------------------------------*)
        ⪡ V ; st ; (t1 >>> t2) ⪢ 
          ⭆ ⪡ V2 ; st'' ; (([⧐ₜₘ {V1⁺ᵣᵦ} ≤ {V2⁺ᵣᵦ - V1⁺ᵣᵦ}] t1') >>> t2')
                          ; (([⧐ₛₖ V1⁺ᵣᵦ ≤ (V2⁺ᵣᵦ - V1⁺ᵣᵦ)] W) ∪ W')%sk ⪢

  | fT_rsf   :  forall (V : 𝓥) (st v : Λ) (r : resource),

                                V ⌈r ⩦ ⩽ v … ⩾⌉ᵣᵦ -> 
    (*-----------------------------------------------------------------------*)
        ⪡ V ; st ; rsf[r] ⪢ ⭆ ⪡ ⌈ r ⤆ ⩽ … st ⩾ ⌉ᵣᵦ V ; v ; rsf[r] ; ∅ₛₖ ⪢

  | fT_wh    :  forall (V V1 : 𝓥) (st st' i t t' : Λ) (W : 𝐖),
                
        ⪡ (⌈S (V⁺ᵣᵦ) ⤆ ⩽ <[unit]> … ⩾⌉ᵣᵦ (⌈V⁺ᵣᵦ ⤆ [⧐ᵣₓ V⁺ᵣᵦ ≤ 2] ⩽ i … ⩾⌉ᵣᵦ ([⧐ᵣᵦ V⁺ᵣᵦ ≤ 2] V))) ; 
            ([⧐ₜₘ {V⁺ᵣᵦ} ≤ 2] st) ; t ⪢ ⭆ ⪡ V1 ; st' ; t' ; W ⪢ ->
    (*-----------------------------------------------------------------------------------------*)
        ⪡ V ; st ; wormhole(i;t) ⪢ 
          ⭆ ⪡ V1 ; st' ; t' ; ⌈V⁺ᵣᵦ ~ S (V⁺ᵣᵦ) ⤆ <[[⧐ₜₘ {V⁺ᵣᵦ} ≤ {V1⁺ᵣᵦ - V⁺ᵣᵦ}] i]>⌉ₛₖ W ⪢

where "⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st1 ; t1 ; W ⪢" := (functional V st t V1 st1 t1 W)
.

(** ** Well formed property between the resource context and environment *)

Definition wf_env_fT (Re : ℜ) (V : 𝓥) :=
  (forall r, r ∈ᵣᵪ Re <-> r ∈ᵣᵦ V) /\ Re⁺ᵣᵪ ⊩ᵣᵪ Re /\ V⁺ᵣᵦ ⊩ᵣᵦ V /\
  (forall r τ τ' v,  Re ⌈ r ⩦ (τ,τ') ⌉ᵣᵪ ->  V ⌈ r ⩦ v ⌉ᵣᵦ -> 
                                            match v with
                                              | (⩽ v' … ⩾) => ∅ᵥᵪ ⋅ Re ⊫ v' ∈ τ'
                                              | (⩽ … v' ⩾) => ∅ᵥᵪ ⋅ Re ⊫ v' ∈ τ
                                            end).

Notation "'Wfᵣₜ(' Re , V )" := (wf_env_fT Re V) (at level 50).