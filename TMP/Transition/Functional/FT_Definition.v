From Mecha Require Import Resource Resources Term Typ Var ReadStock Typing
                          ET_Definition Cell VContext REnvironment RContext Stock.
Import ResourceNotations TermNotations TypNotations CellNotations
       VContextNotations RContextNotations REnvironmentNotations
       ReadStockNotations ResourcesNotations SetNotations StockNotations.

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

Open Scope renvironment_scope.

(** ** Functional Transition *)

Inductive functional : 𝐕 -> Λ -> Λ -> 𝐕 -> Λ -> Λ -> 𝐖 -> Prop :=

  | fT_eT_sf  :  forall (V V1 : 𝐕) (st st' t t' t'' : Λ) (W : 𝐖),

        V⁺ ⊨ t ⟼ t' -> ⪡ V ; st ; t' ⪢ ⭆ ⪡ V1 ; st' ; t'' ; W ⪢ -> 
    (*-----------------------------------------------------------------------*)
              ⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st' ; t'' ; W ⪢

  | fT_eT_sv  :  forall (V V1 : 𝐕) (st st' st'' t t' : Λ) (W : 𝐖),

        V⁺ ⊨ st ⟼ st' -> ⪡ V ; st' ; t ⪢ ⭆ ⪡ V1 ; st'' ; t' ; W ⪢ -> 
    (*-----------------------------------------------------------------------*)
              ⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st'' ; t' ; W ⪢

  | fT_arr   :  forall (st t : Λ) (V : 𝐕), 

    (*---------------------------------------------------------*)
        ⪡ V ; st ; arr(t) ⪢ ⭆ ⪡ V ; (t st) ; arr(t) ; (∅)%sk ⪢ 

  | fT_first :  forall (v1 v1' v2 t t' : Λ) (τ : Τ) (V V1 : 𝐕) (W : 𝐖),

        ⪡ V ; v1 ; t ⪢ ⭆ ⪡ V1 ; v1' ; t' ; W ⪢ ->
    (*----------------------------------------------------------------------------------------*)
        ⪡ V ; ⟨v1,v2⟩ ; first(τ:t) ⪢ 
          ⭆ ⪡ V1 ; ⟨v1',[⧐ {V⁺} – {V1⁺ - V⁺}] v2⟩ ; first(τ:t') ; W ⪢

  | fT_comp  :  forall (st st' st'' t1 t1' t2 t2' : Λ) (V V1 V2 : 𝐕) (W W': 𝐖),

                                         ⪡ V ; st ; t1 ⪢ ⭆ ⪡ V1 ; st' ; t1' ; W ⪢ ->
        ⪡ V1 ; st' ; ([⧐ {V⁺} – {V1⁺ - V⁺}] t2) ⪢ ⭆ ⪡ V2 ; st'' ; t2' ; W' ⪢ ->
    (*---------------------------------------------------------------------------------------*)
        ⪡ V ; st ; (t1 >>> t2) ⪢ 
          ⭆ ⪡ V2 ; st'' ; (([⧐ {V1⁺} – {V2⁺ - V1⁺}] t1') >>> t2')
                          ; (([⧐ V1⁺ – (V2⁺ - V1⁺)] W) ∪ W')%sk ⪢

  | fT_rsf   :  forall (V : 𝐕) (st v : Λ) (r : resource),

                                V⌊r⌋ = Some (⩽ v … ⩾) -> 
    (*-----------------------------------------------------------------------*)
        ⪡ V ; st ; rsf[r] ⪢ ⭆ ⪡ ⌈ r ⤆ ⩽ … st ⩾ ⌉ V ; v ; rsf[r] ; (∅)%sk ⪢

  | fT_wh    :  forall (V V1 : 𝐕) (st st' i t t' : Λ) (W : 𝐖),
                
        ⪡ (⌈S (V⁺) ⤆ ⩽ <[unit]> … ⩾⌉ (⌈V⁺ ⤆ ([⧐ V⁺ – 2] ⩽ i … ⩾)%cl⌉ ([⧐ V⁺ – 2] V))) ; 
            (<[[⧐ {V⁺} – 2] st]>) ; t ⪢ ⭆ ⪡ V1 ; st' ; t' ; W ⪢ ->
    (*-----------------------------------------------------------------------------------------*)
        ⪡ V ; st ; wormhole(i;t) ⪢ 
          ⭆ ⪡ V1 ; st' ; t' ; (⌈V⁺ ~ S (V⁺) ⤆ <[[⧐ {V⁺} – {V1⁺ - V⁺}] i]>⌉ W)%sk ⪢

where "⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st1 ; t1 ; W ⪢" := (functional V st t V1 st1 t1 W)
.

(** ** Well formed property between the resource context and environment *)

Definition wf_env_fT (Re : ℜ) (V : 𝐕) :=
  (forall r, (r ∈ Re)%rc <-> r ∈ V) /\ 
  (Re⁺ ⊩ Re)%rc /\ V⁺ ⊩ V /\
  (forall r τ τ' v,  Re⌊r⌋%rc = Some (τ,τ') ->  V⌊r⌋ = Some v -> 
                                            match v with
                                              | (⩽ v' … ⩾) => (∅)%vc ⋅ Re ⊫ v' ∈ τ'
                                              | (⩽ … v' ⩾) => (∅)%vc ⋅ Re ⊫ v' ∈ τ
                                            end).

Notation "'Wfᵣₜ(' Re , V )" := (wf_env_fT Re V) (at level 50).