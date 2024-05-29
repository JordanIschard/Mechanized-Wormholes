From Coq Require Import Program Lia Relations.Relation_Definitions Classes.RelationClasses PeanoNat
                        Classical_Prop Classical_Pred_Type Bool.Bool Classes.Morphisms.
From Mecha Require Import Resource Resources Term Typ Var ReadStock WriteStock
               Substitution Typing VContext RContext Evaluation
               Cell REnvironment Stock WfEnv.

(** * Transition - Functional

Wormholes's semantics are divided in three sub semantics:
- evaluation transition
- functional transition <--
- temporal transition

*)

Module RC := RContext.
Module RE := REnvironment.

(** *** Definition *)

Reserved Notation "⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st1 ; t1 ; W ⪢" (at level 57, V constr, 
                                                                V1 constr, st custom wormholes,
                                                                st1 custom wormholes,
                                                                t custom wormholes, 
                                                                t1 custom wormholes, 
                                                                no associativity).
Reserved Notation "'Wfᵣₜ(' Re , V )" (at level 50).

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

(** ** Lift of multiple evaluation transitions *)

Lemma fT_MeT_sf (V V1 : 𝓥) (W : 𝐖) (st st' t t' t'' : Λ) :

       V⁺ᵣᵦ ⊨ t ⟼⋆ t' -> ⪡ V ; st ; t' ⪢ ⭆ ⪡ V1 ; st' ; t'' ; W ⪢ -> 
    (*-------------------------------------------------------------------*)
                ⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st' ; t'' ; W ⪢.
Proof.
  intro HmeT. apply multi_indexed in HmeT as [k HieT].
  revert V V1 st st' t t' t'' HieT; induction k; intros; inversion HieT; subst; auto.
  apply fT_eT_sf with (t' := y); auto. apply IHk with (t' := t'); auto.
Qed.

Lemma fT_MeT_sv (V V1 : 𝓥) (W : 𝐖) (st st' st'' t t' : Λ) :

       V⁺ᵣᵦ ⊨ st ⟼⋆ st' -> ⪡ V ; st' ; t ⪢ ⭆ ⪡ V1 ; st'' ; t' ; W ⪢ -> 
    (*--------------------------------------------------------------------*)
                ⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st'' ; t' ; W ⪢.
Proof.
  intro HmeT. apply multi_indexed in HmeT as [k HieT].
  revert V V1 st st' st'' t t' HieT; induction k; intros; inversion HieT; subst; auto.
  apply fT_eT_sv with (st' := y); auto. apply IHk with (st' := st'); auto.
Qed.

Section safety.

Hypothesis all_arrow_halting : forall Re t α β,
  ∅ᵥᵪ ⋅ Re ⊫ arr(t) ∈ (α ⟿ β ∣ ∅ᵣₛ) -> forall v, ∅ᵥᵪ ⋅ Re ⊫ v ∈ α -> halts (Re⁺ᵣᵪ) <[t v]>.

Hint Resolve VContext.valid_empty_spec Stock.valid_empty_spec WriteStock.valid_empty_spec : core.


(** ** Preservation *)


(** *** Proof of preservation of validity through the functional transition 

  The concept of validity have to be consistent after a functional transition because
  typing, evaluation transition are based on.

  **** Hypothesis

  If there is a functional transition (1) with the environment (2), the stream term (3) and 
  the signal function (4) valid according to the new key of the environment;

  **** Result

  All output element of the functional transition (V1,st',...) are valid according to the new
  key of the output environment (5) and the new key of the output environment is greater or equal to the
  the new key of the input environment (6).
*)
Lemma functional_preserves_valid (V V1 : 𝓥) (W : 𝐖) (st st' sf sf' : Λ) :
  (* (1) *) ⪡ V ; st ; sf ⪢ ⭆ ⪡ V1 ; st' ; sf' ; W ⪢ ->
  (* (2) *) V⁺ᵣᵦ ⊩ᵣᵦ V -> 
  (* (3) *) V⁺ᵣᵦ ⊩ₜₘ st -> 
  (* (4) *) V⁺ᵣᵦ ⊩ₜₘ sf ->

  (* (5) *) V1⁺ᵣᵦ ⊩ᵣᵦ V1 /\ V1⁺ᵣᵦ ⊩ₜₘ st' /\ V1⁺ᵣᵦ ⊩ₜₘ sf' /\ V1⁺ᵣᵦ ⊩ₛₖ W /\ 
  (* (6) *) V⁺ᵣᵦ <= V1⁺ᵣᵦ.
Proof.
  clear all_arrow_halting.
  intro fT; dependent induction fT; intros HvV Hvst Hvt.
  (* fT_eT_sf *)
  - destruct IHfT as [HvV1 [Hvst' [Hvt'' [HvW Hlt]]]]; auto.
    apply evaluate_preserves_valid_term with (t := t); assumption.
  (* fT_eT_sv *)
  - destruct IHfT as [HvV1 [Hvst' [Hvt'' [HvW Hlt]]]]; auto.
    apply evaluate_preserves_valid_term with (t := st); assumption.
  (* fT_arr *)
  - repeat split; auto. constructor; inversion Hvt; subst; assumption.
  (* fT_first *)
  - inversion Hvst; inversion Hvt; subst; fold Term.valid in *; clear Hvst Hvt. 
    destruct IHfT as [HvV1 [Hvst' [Hvt'' [HvW Hlt]]]]; auto.
    repeat split; auto; try (now destruct HvW).
    -- constructor; auto. apply Term.shift_preserves_valid_3; auto.
    -- constructor; auto; eapply Typ.valid_weakening; eauto.
  (* fT_comp *)
  - inversion Hvt; subst; 
    destruct IHfT1 as [HvV1 [Hvst' [Hvt1' [HvW1 Hlt1]]]]; auto;
    destruct IHfT2 as [HvV2 [Hvst'' [Hvt2' [HvW2 Hlt2]]]]; auto; fold Term.valid in *.
    -- apply Term.shift_preserves_valid_3; auto.
    -- do 3 (split; auto).
       + constructor; auto. apply Term.shift_preserves_valid_3; auto.
       + split; try lia. apply Stock.valid_union_spec; split; try assumption.
         apply Stock.shift_preserves_valid_3; auto.
  (* fT_rsf *)
  - assert (r ∈ᵣᵦ V).
    { rewrite RE.in_find; rewrite H; intro c; now inversion c. }
    rewrite RE.Ext.new_key_add_spec_3; auto; try lia; repeat split; auto.
    -- now apply RE.valid_update_spec.
    -- now apply RE.valid_find_spec with (lb := V⁺ᵣᵦ) in H as [_ H].
  (* fT_wh *)
  - rewrite RE.new_key_wh_spec in *. inversion Hvt; subst; clear Hvt.
    destruct IHfT as [HvV1 [Hvst' [Hvt'' [HvW Hlt]]]]; auto; fold Term.valid in *. 
    + apply RE.valid_wh_spec_1; auto; try (constructor).
    + replace (S (S (V⁺ᵣᵦ))) with ((V⁺ᵣᵦ) + 2) by lia.
      now apply Term.shift_preserves_valid_1.
    + do 3 (split; auto); split; try lia.
      apply Stock.valid_add_spec; eauto.
      ++ unfold Resource.valid; lia.
      ++ apply Term.shift_preserves_valid_3; auto; lia.
Qed.


(** *** Proof of preservation of keys in the environment 

  Keeping consistent the typing through the functional transition is 
  needed for the resources environment. Thus, knowing that we cannot loose 
  keys is required.
*)
Lemma functional_preserves_keys (V V1 : 𝓥) (W : 𝐖) (sv sv' sf sf' : Λ) :
  ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ ->
  V⁺ᵣᵦ ⊩ᵣᵦ V -> 
  V⁺ᵣᵦ ⊩ₜₘ sv -> 
  V⁺ᵣᵦ ⊩ₜₘ sf ->

  (forall (r : resource), r ∈ᵣᵦ V -> r ∈ᵣᵦ V1).
Proof.
  intro fT; dependent induction fT; intros HvV Hvsv Hvsf r' HInV; auto.
  (* fT_eT_sf *)
  - apply IHfT in HInV; try assumption; apply evaluate_preserves_valid_term with t; auto.
  (* fT_eT_sf *)
  - apply IHfT in HInV; try assumption; apply evaluate_preserves_valid_term with st; auto.
  (* fT_first *) 
  - inversion Hvsf; inversion Hvsv; subst; apply IHfT in HInV; auto; fold Term.valid in *.
  (* fT_comp *)
  - inversion Hvsf; subst; fold Term.valid in *. apply IHfT1 in HInV; auto.
    apply functional_preserves_valid in fT1 as HD; auto; 
    destruct HD as [HvV1 [Hvst' [Hvt1' [HvW Hle]]]].
    apply IHfT2; auto. apply Term.shift_preserves_valid_3; auto.
  (* fT_rsf *)
  - destruct (Resource.eq_dec r r'); subst; apply RE.add_in_iff; auto.
  (* fT_wh *)
  - rewrite RE.new_key_wh_spec in *.
    inversion Hvsf; subst; destruct IHfT with (r := r'); auto.
    -- apply RE.valid_wh_spec_1; auto; constructor.
    -- replace (S (S (V⁺ᵣᵦ))) with ((V⁺ᵣᵦ) + 2) by lia.
       now apply Term.shift_preserves_valid_1.
    -- destruct (Resource.eq_dec r' (S (V⁺ᵣᵦ))); subst; apply RE.add_in_iff; auto.
       right; destruct (Resource.eq_dec r' (V⁺ᵣᵦ)); subst; apply RE.add_in_iff; auto.
       right; eapply RE.shift_in_spec in HInV as HInV1.
       eapply RE.valid_in_spec in HInV; eauto.
       rewrite Resource.shift_valid_refl in HInV1; eauto.
    -- now exists x.
Qed.

(** *** Proof of consistency between V and W 

  W stocks all virtual resources created during the functional transition. Those virtual
  resources are also added in the resource environment V1 and cannot be found in the environment V.
*)
Lemma consistency_V_W (V V1 : 𝓥) (W : 𝐖) (sv sv' sf sf' : Λ) :
  ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ ->
  V⁺ᵣᵦ ⊩ᵣᵦ V -> 
  V⁺ᵣᵦ ⊩ₜₘ sv -> 
  V⁺ᵣᵦ ⊩ₜₘ sf ->

  (forall (r : resource), r ∈ₛₖ W -> r ∉ᵣᵦ V /\ r ∈ᵣᵦ V1).
Proof.
  clear all_arrow_halting; intro fT; dependent induction fT; intros HvV Hvsv Hvsf; auto.
  (* fT_eT_sf *)
  - apply IHfT; auto; apply (evaluate_preserves_valid_term t _ _ Hvsf H).
  (* fT_eT_sv *)
  - apply IHfT; auto; apply (evaluate_preserves_valid_term st _ _ Hvsv H).
  (* fT_arr *)
  - intros r HIn; apply Stock.empty_in_spec in HIn; contradiction.
  (* fT_first *)
  - intros r HIn; inversion Hvsv; inversion Hvsf; subst; apply IHfT; auto.
  (* fT_comp *)
  - inversion Hvsf; subst; intros r HIn.
    apply functional_preserves_valid in fT1 as HD; auto; 
    destruct HD as [HvV1 [Hvst' [Hvt1' [HvW Hle]]]].
    apply Stock.union_spec in HIn as [HIn | HIn].
    -- apply Stock.shift_in_e_spec in HIn as Heq'; destruct Heq' as [r' Heq]; subst.
       apply Stock.shift_in_spec in HIn as HIn'.
       apply IHfT1 in HIn' as IH; auto.
       eapply Stock.valid_in_spec in HIn' as Hvr'; eauto.
       rewrite Resource.shift_valid_refl; auto.
       destruct IH; split; auto.
       eapply functional_preserves_keys in H0; eauto.
       apply Term.shift_preserves_valid_3; auto.
    -- apply IHfT2 in HIn; auto.
       + destruct HIn; split; auto. intro. eapply functional_preserves_keys in H2; eauto.
       + apply Term.shift_preserves_valid_3; auto.
  (* fT_rsf *)
  - intros r' HIn; apply Stock.empty_in_spec in HIn; contradiction.
  (* fT_wh *)
  - inversion Hvsf; subst; clear Hvsf; fold Term.valid in *.
    rewrite RE.new_key_wh_spec in *. intros rf HIn.
    apply Stock.add_spec in HIn as [Heq | [Heq | HIn]]; subst; split;
    try (apply RE.Ext.new_key_notin_spec; lia).
    -- eapply functional_preserves_keys; eauto; try rewrite RE.new_key_wh_spec; auto.
       + apply RE.valid_wh_spec_1; auto; constructor.
       + replace (S (S (V⁺ᵣᵦ))) with ((V⁺ᵣᵦ) + 2) by lia; 
         now apply Term.shift_preserves_valid_1.
       + repeat rewrite RE.add_in_iff; auto.
    -- eapply functional_preserves_keys; eauto; try rewrite RE.new_key_wh_spec; auto.
       + apply RE.valid_wh_spec_1; auto; constructor.
       + replace (S (S (V⁺ᵣᵦ))) with ((V⁺ᵣᵦ) + 2) by lia; 
         now apply Term.shift_preserves_valid_1.
       + repeat rewrite RE.add_in_iff; auto.
    -- eapply IHfT in HIn as [HnIn HIn]; eauto.
       + intro c; apply HnIn; repeat rewrite RE.add_in_iff; repeat right.
         apply RE.valid_in_spec_1; auto.
       + apply RE.valid_wh_spec_1; auto; constructor.
       + replace (S (S (V⁺ᵣᵦ))) with ((V⁺ᵣᵦ) + 2) by lia; 
         now apply Term.shift_preserves_valid_1.
    -- eapply IHfT in HIn as [HnIn HIn]; eauto. 
       + apply RE.valid_wh_spec_1; auto; constructor.
       + replace (S (S (V⁺ᵣᵦ))) with ((V⁺ᵣᵦ) + 2) by lia; 
         now apply Term.shift_preserves_valid_1.
Qed.

(** *** Proof of inner constraint of W 

  W stocks reading virtual resource names and writing virtual resource names. It is relevant
  to state that the intersection of set of reading and writing resource names is empty.
*)
Lemma W_well_formed (V V1 : 𝓥) (W : 𝐖) (sv sv' sf sf' : Λ) :
  ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ ->
  V⁺ᵣᵦ ⊩ᵣᵦ V -> 
  V⁺ᵣᵦ ⊩ₜₘ sv -> 
  V⁺ᵣᵦ ⊩ₜₘ sf ->

  (forall r, r ∈ₛₖ W -> (r ∈ᵣₖ (fst W) /\ r ∉ (snd W))%wk \/ (r ∉ᵣₖ (fst W) /\ r ∈ (snd W)))%wk.
Proof.
  clear all_arrow_halting. 
  intro fT; dependent induction fT; intros HvV Hvsv Hvsf; auto; intros r' HIn; 
  try (apply Stock.empty_in_spec in HIn; contradiction).
  (* fT_eT_sf *)
  - apply IHfT; auto; now apply evaluate_preserves_valid_term with t.
  (* fT_eT_sv *)
  - apply IHfT; auto; now apply evaluate_preserves_valid_term with st.
  (* fT_firts *)
  - inversion Hvsv; inversion Hvsf; subst; apply IHfT; auto.
  (* fT_comp *)
  - inversion Hvsf; subst; clear Hvsf; fold Term.valid in *.
    apply functional_preserves_valid in fT1 as Hv; auto; 
    destruct Hv as [HvV1 [Hvst' [Hvt1' [HvW Hle]]]].
    apply Stock.union_spec in HIn as [HInW | HInW'];
    destruct W as [Rw Ww]; destruct W' as [Rw' Ww']; 
    unfold Stock.In,Stock.shift,Stock.valid in *; simpl in *;
    destruct HvW as [HvRw HvWw].
    -- destruct HInW as [HInRw | HInWw].
       + left; split; try (rewrite ReadStock.map_union_spec; now left).
         rewrite WriteStock.union_notin_spec; rewrite WriteStock.valid_in_spec_1 in *; 
         auto; rewrite ReadStock.valid_in_spec_1 in *; auto; split.
         ++ apply IHfT1 with (r := r') in H2 as [[_ HnI] | [Hc _]]; auto.
         ++ apply consistency_V_W with (r := r') in fT1 as [_ HInV1]; auto;
            try (red; auto); intro HIn.
            apply IHfT2 with (r := r') in HvV1 as HI; auto.
            * destruct HI as [[_ HnI] | [Hc _]]; auto.
              apply consistency_V_W with (r := r') in fT2 as [HnInV1 _]; auto; try (red; auto).
              apply Term.shift_preserves_valid_3; auto.
            * apply Term.shift_preserves_valid_3; auto.
       + right; split; try (rewrite WriteStock.union_spec; now left).
         intro HIn; rewrite WriteStock.valid_in_spec_1 in *; auto;
         apply ReadStock.map_union_spec in HIn as [HInRw | HInRw'].
         ++ rewrite ReadStock.valid_in_spec_1 in *; auto.
            apply IHfT1 with (r := r') in H2 as [[_ HnI] | [Hc _]]; auto.
         ++ apply consistency_V_W with (r := r') in fT1 as [_ HInV1]; auto;
            try (red; auto).
            apply IHfT2 with (r := r') in HvV1 as HI; auto.
            * destruct HI as [[_ HnI] | [Hc _]]; auto.
              apply consistency_V_W with (r := r') in fT2 as [HnInV1 _]; auto; try (red; auto).
              apply Term.shift_preserves_valid_3; auto.
            * apply Term.shift_preserves_valid_3; auto.
    -- destruct HInW' as [HInRw' | HInWw']. 
       + left; split; try (rewrite ReadStock.map_union_spec; now right).
         rewrite WriteStock.union_notin_spec; rewrite WriteStock.valid_in_spec_1 in *; auto; split.
         ++ intro HInWw; apply IHfT1 with (r := r') in H2 as HI; auto.
            destruct HI as [[_ HnInWw] | [HnInRw _]]; auto.
            apply consistency_V_W with (r := r') in fT1 as [_ HInV1]; auto; try (red; auto).
            apply consistency_V_W with (r := r') in fT2 as [HnInV1 _]; auto; try (red; auto).
            apply Term.shift_preserves_valid_3; auto.
         ++ apply IHfT2 with (r := r') in HvV1 as [[_ HnI] | [Hc _]]; auto.
            apply Term.shift_preserves_valid_3; auto.
       + right; split; try (rewrite WriteStock.union_spec; now right).
         intro HIn; apply ReadStock.map_union_spec in HIn as [HInRw | HInRw'].
         ++ rewrite ReadStock.valid_in_spec_1 in *; auto.
            apply consistency_V_W with (r := r') in fT1 as [_ HInV1]; auto; try (red; auto).
            apply consistency_V_W with (r := r') in fT2 as [HnInV1 _]; auto; try (red; auto).
            apply Term.shift_preserves_valid_3; auto.
         ++ apply IHfT2 with (r := r') in HvV1 as [[_ HnI] | [Hc _]]; auto.
            apply Term.shift_preserves_valid_3; auto.
  (* fT_wh *)
  - inversion Hvsf; subst; fold Term.valid in *; unfold Stock.add, Stock.In in *; 
    clear Hvsf; destruct W as [Rw Ww]; simpl; destruct HIn as [HInRw | HInWw].
    -- simpl in HInRw; left; split; auto. 
       apply ReadStock.add_in_iff in HInRw as [Heq | HInRw]; subst.
       + rewrite WriteStock.add_notin_spec; split; try lia.
         intro HInWw. apply consistency_V_W with (r := V⁺ᵣᵦ) in fT as [HnIn _]; 
         try (rewrite RE.new_key_wh_spec); auto.
         ++ apply HnIn. repeat rewrite RE.add_in_iff; right; now left.
         ++ apply RE.valid_wh_spec_1; auto; constructor.
         ++ replace (S (S (V⁺ᵣᵦ))) with ((V⁺ᵣᵦ) + 2) by lia.
              now apply Term.shift_preserves_valid_1.
         ++ unfold Stock.In; simpl; auto.
       + rewrite WriteStock.add_notin_spec; split.
         ++ intro Heq; subst. apply consistency_V_W with (r := S (V⁺ᵣᵦ)) in fT as [HnIn _]; 
            try (rewrite RE.new_key_wh_spec); auto.
            * apply HnIn. repeat rewrite RE.add_in_iff; now left.
            * apply RE.valid_wh_spec_1; auto; constructor.
            * replace (S (S (V⁺ᵣᵦ))) with ((V⁺ᵣᵦ) + 2) by lia.
                  now apply Term.shift_preserves_valid_1.
            * unfold Stock.In; simpl; auto.
         ++ rewrite RE.new_key_wh_spec in *; 
            apply IHfT with (r := r') in H3 as [[_ HnInWw] | [HnInRw _]]; auto.
            * apply RE.valid_wh_spec_1; auto; constructor.
            * replace (S (S (V⁺ᵣᵦ))) with ((V⁺ᵣᵦ) + 2) by lia.
              now apply Term.shift_preserves_valid_1.
    -- simpl in HInWw; right; split; auto. 
       apply WriteStock.add_spec in HInWw as [Heq | HInWw]; subst.
       + intro HInRw; rewrite ReadStock.add_in_iff in HInRw; 
         destruct HInRw as [Hc | HInRw]; try lia.
         apply consistency_V_W with (r := S (V⁺ᵣᵦ)) in fT as [HnIn _]; 
         try (rewrite RE.new_key_wh_spec); auto.
         ++ apply HnIn. repeat rewrite RE.add_in_iff; now left.
         ++ apply RE.valid_wh_spec_1; auto; constructor.
         ++ replace (S (S (V⁺ᵣᵦ))) with ((V⁺ᵣᵦ) + 2) by lia.
              now apply Term.shift_preserves_valid_1.
         ++ unfold Stock.In; simpl; auto.
       + intro HInRw; rewrite ReadStock.add_in_iff in HInRw; 
         destruct HInRw as [Hc | HInRw]; subst.
         ++ apply consistency_V_W with (r := V⁺ᵣᵦ) in fT as [HnIn _]; 
            try (rewrite RE.new_key_wh_spec); auto.
            * apply HnIn. repeat rewrite RE.add_in_iff; right; now left.
            * apply RE.valid_wh_spec_1; auto; constructor.
            * replace (S (S (V⁺ᵣᵦ))) with ((V⁺ᵣᵦ) + 2) by lia.
              now apply Term.shift_preserves_valid_1.
            * unfold Stock.In; simpl; auto.
         ++ rewrite RE.new_key_wh_spec in *; 
            apply IHfT with (r := r') in H3 as [[_ HnInWw] | [HnInRw _]]; auto.
            * apply RE.valid_wh_spec_1; auto; constructor.
            * replace (S (S (V⁺ᵣᵦ))) with ((V⁺ᵣᵦ) + 2) by lia.
              now apply Term.shift_preserves_valid_1.
Qed.



(**
  *** General proof of preservation of typing through functional transition

  **** Hypothesis

  Suppose terms [sf],[sv] are well typed (4,5) and halts (1,2), a functional transition (6) using 
  [sf] and [sv] respectively as a signal function and a stream value, and [V] the input resource 
  environment such as each value in its halts (3) and it is well formed (7) regarding the resource
  context [Re] that is used for typing [sf] and [sv].

  **** Results

  We can state that:
  - each value mapped with a resource name present in [R] has to be unused in [V] (8);
  - each value mapped with a resource name not present in [R'] but present in [V] 
    has to be unchanged in [V1] (9);
  - we can found a context [Re1] and a resource set [R'] such as :
    - the old context is a subset of the new one (10);
    - the old resources set is a subset of the new one (11);
    - [V1] is well formed regarding [Re1] (12); 
    - all initial value stocked in [W] are well typed regards of the new context [Re1] (13);
    - all new resources founded in [R'] are stored in [W] and is not in [R] (14); 
    - each value mapped with a resource name present in [R'] has to be used in [V1] (15);
    - the output stream term [sv'] is well typed (16);
    - the term [sf'] is well typed (17);
    - terms [sf'] and [sv'] halts (18,19);
    - each value in [V1] halts (20).
*)
Theorem functional_preserves_typing_gen (Re : ℜ) (V V1 : 𝓥) (W : 𝐖) (sv sv' sf sf' : Λ) 
                                                                      (τ τ' : Τ) (R : resources) :

  (* (1) *) halts (Re⁺ᵣᵪ) sf -> (* (2) *) halts (Re⁺ᵣᵪ) sv -> (* (3) *) RE.halts (Re⁺ᵣᵪ) V -> 

  (* (4) *) ∅ᵥᵪ ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) ->
  (* (5) *) ∅ᵥᵪ ⋅ Re ⊫ sv ∈ τ -> 
  (* (6) *) ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ -> 
  (* (7) *) Wfᵣₜ(Re,V) ->


  (* (8) *)(forall (r : resource), (r ∈ R)%rs -> RE.unused r V) /\
  (* (9) *)(forall (r : resource), (r ∉ R)%rs /\ (r ∈ᵣᵦ V) -> 
              ([⧐ᵣᵦ (V⁺ᵣᵦ) ≤ ((V1⁺ᵣᵦ) - (V⁺ᵣᵦ))] V) ⌊r⌋ᵣᵦ = V1 ⌊r⌋ᵣᵦ) /\

  exists (Re1 : ℜ) (R' : resources), 
    (* (10) *) Re ⊆ᵣᵪ Re1     /\ 
    (* (11) *) (R ⊆ R')%rs    /\
    (* (12) *) Wfᵣₜ(Re1,V1) /\
    (* (13) *) (forall (r : resource) (v : Λ) (τ τ' : Τ), 
                  W ⌈ r ⩦ v ⌉ₛₖ -> Re1 ⌈r ⩦ (τ',τ)⌉ᵣᵪ -> ∅ᵥᵪ ⋅ Re1 ⊫ v ∈ τ) /\
    (* (14) *) (forall (r : resource), (r ∈ (R' \ R))%rs -> (r ∈ (Stock.to_RS W))%rs /\ (r ∉ᵣᵦ V)) /\
    (* (15) *) (forall (r : resource), (r ∈ R')%rs -> RE.used r V1) /\
    (* (16) *) ∅ᵥᵪ ⋅ Re1 ⊫ sv' ∈ τ' /\
    (* (17) *) ∅ᵥᵪ ⋅ Re1 ⊫ sf' ∈ (τ ⟿ τ' ∣ R') /\
    
    (* (18) *) halts (Re1⁺ᵣᵪ) sf' /\ (* (19) *) halts (Re1⁺ᵣᵪ) sv' /\ (* (20) *) RE.halts (Re1⁺ᵣᵪ) V1.
Proof.
  intros Hlsf Hlsv HltV Hwsf Hwsv fT. revert Re R τ τ' Hlsf Hlsv HltV Hwsf Hwsv.
  induction fT; intros Re R α β Hlsf Hlsv HlV Hwsf Hwsv Hwf;

  apply wf_env_fT_valid in Hwf as HvRe; destruct HvRe as [HvRe HvV];
  apply wf_env_fT_new in Hwf as Hnew;
  
  move HvRe before Hwf; move HvV before HvRe; move Hnew before Hwf.
  (* fT_eT_sf *)
  - 
    (* clean *)
    move Re before W; move R before Re; move α before R; move β before α; move fT after IHfT;
    rename fT into HfT; rename H into HeT; move HeT after HfT; clear all_arrow_halting.
    (* clean *)

    rewrite <- Hnew in HeT; apply evaluate_preserves_typing with (t' := t') in Hwsf as Hwsf'; 
    try assumption.
    
    (* clean *)
    clear Hwsf HvRe; move Hwsf' after Hwsv.
    (* clean *)

    apply IHfT; auto. rewrite <- evaluate_preserves_halting with (t := t); auto.
  (* fT_eT_sv *)
  - 
    (* clean *)
    move Re before W; move R before Re; move α before R; move β before α; move fT after IHfT;
    rename fT into HfT; rename H into HeT; move HeT after HfT.
    (* clean *)

    rewrite <- Hnew in HeT; apply evaluate_preserves_typing with (t' := st') in Hwsv as Hwsv'; 
    try assumption.
    
    (* clean *)
    clear HvRe; move Hwsv' after Hwsv.
    (* clean *)

    apply IHfT; auto. rewrite <- evaluate_preserves_halting with (t := st); auto.
  (* fT_arr *)
  - 
    (* clean *)
    inversion Hwsf; subst; rename H3 into Hwt; clear Hwsf; move Hwt after Hwsv.
    (* clean *)

    repeat split.
    -- intros r HIn; inversion HIn.
    -- intros r [HnIn HIn]; replace (V⁺ᵣᵦ - V⁺ᵣᵦ) with 0 by lia.
        now rewrite RE.shift_refl.
    -- exists Re; exists ∅ᵣₛ. repeat (split; try now auto).
        + apply wt_app with (τ2 := α); assumption.
        + now constructor. 
        + eapply all_arrow_halting with (β := β); eauto. 
          now constructor.
  (* fT_first *)
  -
    (* clean *)
    inversion Hwsf; subst; move Re before W; move R before Re; move τ1 before τ;
    move τ2 before τ1; clear Hwsf; rename H4 into Hwt; rename H7 into Hvτ;
    move Hwt after Hwsv; move Hvτ before Hwsv. rename fT into HfT;  move HfT after IHfT;
    inversion Hwsv; subst; rename H4 into Hwv1; rename H6 into Hwv2; move Hwv1 before Hwt;
    move Hwv2 before Hwv1; clear Hwsv; move HvRe after Hvτ; move HvV after HvRe.
    (* clean *)

    apply halts_first in Hlsf; apply halts_pair in Hlsv as [Hlv1 Hlv2].
    apply IHfT with (R := R) (τ' := τ2) in Hwv1 as IH; auto; clear IHfT.

    
    destruct IH as [Hunsd [Hlcl [Re' [R' [HSubRe [HSubR [Hwf' 
                          [HwtW [HInW [Husd [Hwv1' [Hwt' [Hlt' [Hlv1' HlV1]]]]]]]]]]]]]].

    (* clean *)
    move Re' before Re; move R' before R; move Hwv1' before Hwv1; clear Hwv1;
    move Hwt' before Hwt; clear Hwt; move Hwf' before Hwf; move Hunsd before Husd.
    move Hlt' before Hlsf; move Hlv1' before Hlv1; move HlV1 before HlV; move Hlcl after HSubR.
    (* clean *)

    apply wf_env_fT_new in Hwf' as Hnew'; move Hnew' before Hnew.

    repeat (split; try now auto).
    exists Re'; exists R'; repeat (split; try now auto).
    -- constructor; auto; rewrite <- Hnew; rewrite <- Hnew'.
       apply weakening_ℜ; auto.
    -- apply wt_first; try assumption.
       apply Typ.valid_weakening with (k := Re⁺ᵣᵪ); try assumption.
       apply RC.Ext.new_key_Submap_spec in HSubRe; assumption.
    -- now apply halts_first.
    -- apply halts_pair; split; auto. rewrite <- Hnew; rewrite <- Hnew'.
       apply halts_weakening; auto. apply RC.Ext.new_key_Submap_spec in HSubRe; assumption.

  (* fT_comp *)
  -
    (* clean *)
    inversion Hwsf; subst; apply Resources.eq_leibniz in H7; subst;
    clear Hwsf; move Re before W'; move R1 before Re; move R2 before R1; 
    move α before R2; move β before α; move τ before β; rename fT1 into HfT1;
    move HfT1 after IHfT2; rename fT2 into HfT2; move HfT2 after HfT1.
    rename H6 into Hwt1; rename H8 into Hwt2; rename H9 into HEmp.
    move Hwt1 after Hwsv; move Hwt2 before Hwt1.
    (* clean *)

    apply halts_comp in Hlsf as [Hlt1 Hlt2].
    apply IHfT1 with (R := R1) (τ' := τ) in Hwsv as IH1; auto;
    try (intros; apply Hunsd; rewrite Resources.union_spec; now left).
    clear IHfT1; 
    destruct IH1 as [Hunsd1 [Hlcl1 [Re' [R1' [HSubRe [HSubR1 [Hwf' 
                            [HwtW [HInW [Husd1 [Hwsv' [Hwt1' [Hlt1' [Hlst' HlV1]]]]]]]]]]]]]].

    (* clean *)
    move Re' before Re; move R1' before R1; move Hwsv' before Hwsv;
    move Hwt1' before Hwt1; move Hunsd1 after HInW; move Hwf' before Hwf;
    move Hlt1' before Hlt1; move Hlst' before Hlsv; move HlV1 before HlV.
    (* clean *)

    apply wf_env_fT_new in Hwf' as Hnew'; move Hnew' before Hnew.
    apply IHfT2 with (R := R2) (τ' := β) in Hwsv' as IH2; auto.

    -- destruct IH2 as [Hunsd2 [Hlcl2 [Re'' [R2' [HSubRe' [HSubR2 
                       [Hwf'' [HwtW' [HInW'  [Husd2 [Hwsv'' [Hwt2' [Hlt2' [Hlst'' HlV2]]]]]]]]]]]]]].

       (* clean *)
       move Re'' before Re'; move R2' before R2; move Hwsv'' before Hwsv';
       move Hwt2' before Hwt2; move Hunsd2 before Hunsd1; move Hwf'' before Hwf';
       clear IHfT2; move HSubRe' before HSubRe; move HSubR2 before HSubR1; move HInW' before HInW;
       move Husd2 before Husd1; move Hlcl2 before Hlcl1; move Hlt2' before Hlt2; 
       move Hlst'' before Hlst'; move HlV2 before HlV1.
       (* clean *)

       apply well_typed_implies_valid in Hwt1 as Hvt1; auto; destruct Hvt1 as [Hvt1 _].
       apply well_typed_implies_valid in Hwsv as Hvst; auto; destruct Hvst as [Hvst _].
       apply wf_env_fT_new in Hwf'' as Hnew''; move Hnew'' before Hnew'.
       apply functional_preserves_valid in HfT1 as HI; auto; (try now rewrite <- Hnew).
       destruct HI as [HvV1 [Hvst' [Hvt1' [HvW Hle]]]].

       (* clean *)
       move HvV1 before HvV; move Hvt1 before HvV1; move Hvt1' before Hvt1; 
       move Hvst before Hvt1'; move Hvst' before Hvst; move HvW before HvV1;
       move Hle before HvV1.
       (* clean *)

       assert (HEmp' : (∅ᵣₛ = R1' ∩ R2')%rs).
      {
        symmetry; apply Resources.empty_is_empty_1; unfold Resources.Empty.
        intros r' HIn; apply Resources.inter_spec in HIn as [HIn1 HIn2].
        destruct (Resources.In_dec r' R1) as [HInR1 | HnInR1]; 
        destruct (Resources.In_dec r' R2) as [HInR2 | HnInR2].
        - symmetry in HEmp; apply Resources.empty_is_empty_2 in HEmp.
          apply (HEmp r'). apply Resources.inter_spec; split; auto.
        - destruct (HInW' r') as [_ HnInV1]; try (rewrite Resources.diff_spec; split; auto).
          assert (HInV1 : r' ∈ᵣᵦ V).
          { apply Hunsd1 in HInR1 as [v HfV]. exists (⩽ v … ⩾); now apply RE.find_2. }
          rewrite Hnew in Hvt1,Hvst. 
          apply (functional_preserves_keys V V1 W st st' t1 t1') in HInV1; auto.
            
        - assert (HInV1 : r' ∈ᵣᵦ V).
          { 
            rewrite <- (wf_env_fT_in Re V Hwf r'). 
            destruct Hlt2 as [v2 [HmeT Hvv2]]. 
            apply multi_preserves_typing with (t' := v2) in Hwt2; auto.
            apply (typing_Re_R v2 (∅ᵥᵪ) _ τ β R2); auto.
          }

          revert HInV1; apply HInW; rewrite Resources.diff_spec; split; assumption.

        - destruct (HInW r') as [HInW1 HnInV]; try (rewrite Resources.diff_spec; now split).
          destruct (HInW' r') as [_ HnInV1]; try (rewrite Resources.diff_spec; now split).

          apply Stock.to_RS_in_spec in HInW1; 
          apply consistency_V_W with (r := r') in HfT1 as [_ Hc]; auto.

          -- rewrite <- Hnew. 
             apply (well_typed_implies_valid (∅ᵥᵪ) Re st α); auto. 
          -- rewrite <- Hnew. 
             apply (well_typed_implies_valid (∅ᵥᵪ) Re t1 <[α ⟿ τ ∣ R1]>); auto. 
        }

        move HEmp' before HEmp. repeat split.
        + intros r HIn; apply Resources.union_spec in HIn as [HInR1 | HInR2]; auto.
          destruct Hlt2 as [v2 [HmeT Hvv2]]; 
          apply multi_preserves_typing with (t' := v2) in Hwt2; auto.
          apply (typing_Re_R v2 (∅ᵥᵪ) Re τ β R2) in HInR2 as HInRe; auto.
          rewrite (wf_env_fT_in Re V Hwf r) in HInRe; destruct HInRe as [v HfV];
          apply RE.find_1 in HfV; destruct v.
          ++ now exists λ.
          ++ apply RE.shift_find_spec with (lb := V⁺ᵣᵦ) (k := V1⁺ᵣᵦ - V⁺ᵣᵦ) in HfV as HfV'.
             rewrite Resource.shift_valid_refl in HfV'.
             * rewrite Hlcl1 in HfV'.
               ** apply Hunsd2 in HInR2 as HunsdV1; destruct HunsdV1 as [λ1 HfV1].
                  rewrite HfV1 in *; simpl in *; inversion HfV'.
               ** split.
                  {
                    intro. symmetry in HEmp; apply Resources.empty_is_empty_2 in HEmp; 
                    apply (HEmp r); rewrite Resources.inter_spec; now split.
                  }
                  { exists (⩽ … λ ⩾); now apply RE.find_2.  }
             * apply RE.valid_in_spec with (m := V); auto. 
               exists (⩽ … λ ⩾); now apply RE.find_2.
        + intros r [HnInR HInV]. apply Resources.union_notin_spec in HnInR as [HnInR1 HnInR2].
          apply functional_preserves_keys with (r := r) in HfT1 as HInV1; auto;
          try (now rewrite <- Hnew). rewrite <- (RE.shift_unfold_1 _ (V1⁺ᵣᵦ)).
          ++ rewrite (RE.shift_find_spec_3 _ _ r ([⧐ᵣᵦ V⁺ᵣᵦ ≤ V1⁺ᵣᵦ - V⁺ᵣᵦ] V) V1); auto.
             * rewrite Hnew in *. now apply (RE.valid_in_spec _ _ V1).
             * apply RE.valid_in_spec with (lb := V⁺ᵣᵦ) in HInV as Hvr; auto.
               rewrite <- (Resource.shift_valid_refl (V⁺ᵣᵦ) (V1⁺ᵣᵦ - V⁺ᵣᵦ) r); auto.
               now apply RE.shift_in_spec.
          ++ rewrite <- Hnew; rewrite <- Hnew'; now apply RC.Ext.new_key_Submap_spec.
          ++ rewrite <- Hnew'; rewrite <- Hnew''; now apply RC.Ext.new_key_Submap_spec.
        + exists Re''; exists (R1' ∪ R2')%rs; repeat (split; try now auto; try (now transitivity Re')).
          ++ intros r HIn. rewrite Resources.union_spec in *; destruct HIn as [HIn | HIn]; auto.
          ++ intros r v τ1 τ' Hfi HfiRe.

            (* clean *)
            move r before τ; move τ1 before τ; move τ' before τ; move v before t2'.
            (* clean *)
            
            apply Stock.union_find_spec in Hfi; destruct Hfi.
            * apply ReadStock.shift_find_e_spec_1 in H as HI.
              destruct HI as [[r' Heq] [v' Heqv]]; subst. apply Term.eq_leibniz in Heqv; subst.

              rewrite <- Hnew''; rewrite <- Hnew'; apply weakening_ℜ; auto.
              ** apply (wf_env_fT_valid Re' V1 Hwf').
              ** apply ReadStock.shift_find_spec in H. apply (HwtW _ _ τ1 τ') in H; auto.
                 assert (r' ∈ₛₖ W). 
                 { unfold Stock.In; left. exists v'; now apply ReadStock.find_2. }

                 apply consistency_V_W with (r := r') in HfT1 as [_ HInV1]; auto;
                 try (now rewrite <- Hnew).
                 apply (wf_env_fT_in Re' V1 Hwf' r') in HInV1 as HInRe'. 
                 apply RE.valid_in_spec with (lb := V1⁺ᵣᵦ) in HInV1; auto.
                 rewrite Resource.shift_valid_refl in HfiRe; auto.
                 destruct HInRe' as [v HfRe']; apply RC.find_1 in HfRe'.
                 apply RC.Submap_find_spec with (m' := Re'') in HfRe' as HfRe''; auto.
                 rewrite HfRe'' in HfiRe; inversion HfiRe; now subst.
            * apply (HwtW' r _ _ τ'); auto.
          ++ apply Resources.diff_spec in H as [HIn HnIn]. 
             apply Resources.union_notin_spec in HnIn as [HnInR1 HnInR2].
             apply Resources.union_spec in HIn as [HInR1' | HInR2'].
             * destruct (HInW r) as [HInW1 HnInV]; try (apply Resources.diff_spec; split; auto).
               apply Stock.to_RS_union_spec; left; apply Stock.to_RS_in_spec in HInW1.
               apply Stock.to_RS_in_spec. 
               apply consistency_V_W with (r := r) in HfT1 as [_ HInV1]; auto;
               try (now rewrite <- Hnew).
               apply RE.valid_in_spec with (lb := V1⁺ᵣᵦ) in HInV1; auto.
               rewrite <- (Resource.shift_valid_refl (V1⁺ᵣᵦ) (V2⁺ᵣᵦ - V1⁺ᵣᵦ) r); auto.
               now apply Stock.shift_in_spec.
             * destruct (HInW' r) as [HInW1 HnInV]; try (apply Resources.diff_spec; split; auto).
               apply Stock.to_RS_union_spec; right; apply Stock.to_RS_in_spec in HInW1.
               now apply Stock.to_RS_in_spec. 
          ++ apply Resources.diff_spec in H as [HIn HnIn]. 
             apply Resources.union_notin_spec in HnIn as [HnInR1 HnInR2].
             apply Resources.union_spec in HIn as [HInR1' | HInR2'].
             * destruct (HInW r) as [HInW1 HnInV]; 
               try (apply Resources.diff_spec; split; auto); assumption.
             * intro HInV. apply functional_preserves_keys with (r := r) in HfT1; auto;
               try (now rewrite <- Hnew). revert HfT1.
               apply (HInW' r); apply Resources.diff_spec; split; assumption.
          ++ intros r HIn; apply Resources.union_spec in HIn as [HInR1' | HInR2']; auto.
             apply Husd1 in HInR1' as HI; destruct HI as [v HfV1].

             assert (HI : (r ∉ R2')%rs /\ r ∈ᵣᵦ V1). 
             { 
              split. 
              - intro. symmetry in HEmp'; apply Resources.empty_is_empty_2 in HEmp'; 
                apply (HEmp' r); rewrite Resources.inter_spec; split; auto.
              - apply RE.in_find. intro c; rewrite HfV1 in c; inversion c.
             }
             destruct HI as [HnInR2' HInV1].
             apply (RE.valid_in_spec _ r V1) in HvV1; auto.
             apply (RE.shift_find_spec (V1⁺ᵣᵦ) (V2⁺ᵣᵦ - V1⁺ᵣᵦ)) in HfV1 as HfshV1.
             simpl in *. rewrite Resource.shift_valid_refl in HfshV1; auto.
             rewrite Hlcl2 in HfshV1; auto. now exists <[[⧐ₜₘ{V1 ⁺ᵣᵦ} ≤ {V2 ⁺ᵣᵦ - V1 ⁺ᵣᵦ}] v]>.
          ++ rewrite <- Hnew'. rewrite <- Hnew''. 
             apply wt_comp with (R1 := R1') (R2 := R2') (τ := τ); auto; try reflexivity.
             apply weakening_ℜ; auto. apply (wf_env_fT_valid Re' V1 Hwf').
          ++ rewrite <- Hnew'. rewrite <- Hnew''. apply halts_comp; split; auto.
             apply halts_weakening; auto. now apply RC.Ext.new_key_Submap_spec.
    -- rewrite <- Hnew; rewrite <- Hnew'; apply halts_weakening; auto.
       apply RC.Ext.new_key_Submap_spec in HSubRe; assumption.
    -- rewrite <- Hnew; rewrite <- Hnew'; apply weakening_ℜ; auto.
  (* fT_rsf *)
  -
    (* clean *)
    inversion Hwsf; subst. clear Hwsf; move Re before V; rename H into HfV; rename H4 into HfRe;
    move HfV after HfRe. 
    (* clean *)

    repeat split.
    -- intros r' HIn; rewrite Resources.singleton_spec in HIn; subst; now exists v.
    -- intros r' [HnIn HIn]; apply Resources.singleton_notin_spec in HnIn.
        rewrite RE.add_neq_o; auto. rewrite RE.Ext.new_key_add_spec_3.
        + replace (V⁺ᵣᵦ - V⁺ᵣᵦ) with 0 by lia; now rewrite RE.shift_refl.
        + exists (⩽ v … ⩾); now apply RE.find_2.
    -- exists Re; exists \{{r}}; split; try reflexivity; auto; 
       repeat (split; try now auto).
       + intros. rewrite (wf_env_fT_in Re V) in H; auto.
         rewrite RE.OP.P.add_in_iff; now right.
       + intros HIn. apply RE.OP.P.add_in_iff in HIn as [Heq | HIn]; subst.
         ++ exists (α,β). now apply RC.OP.P.find_2.
         ++ now rewrite (wf_env_fT_in Re V).
       + apply RE.valid_find_spec with (lb := V⁺ᵣᵦ) in HfV as Hv; auto.
         destruct Hv as [Hvr Hvv].
         rewrite RE.Ext.new_key_add_spec_3.
         ++ apply RE.valid_add_spec; repeat split; auto.
            unfold Cell.valid; simpl. 
            rewrite <- (wf_env_fT_new Re V); auto.
            apply well_typed_implies_valid in Hwsv as [Hwst _]; auto.
         ++ exists (⩽ v … ⩾). now apply RE.OP.P.find_2.
       + intros r1 τ τ' v1 HfRe1 HfV1.
         destruct (Resource.eq_dec r r1); subst.
         ++ rewrite RE.OP.P.add_eq_o in *; auto. 
            inversion HfV1; subst; clear HfV1.
            rewrite HfRe in HfRe1; inversion HfRe1; now subst.
         ++ rewrite RE.OP.P.add_neq_o in HfV1; auto.
            now apply (wf_env_fT_well_typed Re V Hwf r1).
       + rename H into HIn; apply Resources.diff_spec in HIn as [HIn HnIn]; contradiction.
       + rename H into HIn; apply Resources.diff_spec in HIn as [HIn HnIn]; contradiction.
       + intros r' HIn; apply Resources.singleton_spec in HIn; subst; unfold RE.used.
         exists st; now apply RE.add_eq_o.
       + apply wf_env_fT_well_typed with (V := V) (v := ⩽ v … ⩾) in HfRe; try assumption.
       + apply wf_env_fT_valid in Hwf; destruct Hwf; auto; now constructor.
       + unfold RE.halts in *; apply HlV in HfV; now simpl in *.
       + apply RE.halts_add_spec; split; simpl; auto.
  (* fT_wh *)
  -
    (* clean *)
    inversion Hwsf; subst; unfold k in *; move Re before W; move R before Re; move R' before R;
    move τ before R'; move α before τ; move β before α; rename H6 into Hwi; rename H7 into Heq; 
    rename H8 into Hvα; rename H9 into Hvβ; rename H10 into Hwt;
    move Hwt after Hwsv; move Hwi after Hwt; clear k.
    (* clean *)

    apply halts_wh in Hlsf as [Hli Hlt].
    apply weakening_ℜ  with (Re1 := ⌈ S (Re⁺ᵣᵪ) ⤆ (τ, <[ 𝟙 ]>) ⌉ᵣᵪ 
                                      (⌈ Re⁺ᵣᵪ ⤆ (<[ 𝟙 ]>, τ) ⌉ᵣᵪ Re)) in Hwsv as Hwsv';
    try (now apply RC.Ext.new_key_Submap_spec_1); auto.
    rewrite RC.new_key_wh_spec in *. replace (S (S (Re⁺ᵣᵪ)) - Re⁺ᵣᵪ) with 2 in * by lia.

    apply IHfT with (Re :=  ⌈ S (Re⁺ᵣᵪ) ⤆ (τ, <[ 𝟙 ]>) ⌉ᵣᵪ 
                          (⌈ Re⁺ᵣᵪ ⤆ (<[ 𝟙 ]>, τ) ⌉ᵣᵪ Re)) (R := R') (τ' := β) in Hwt as IH;
    auto; try (now rewrite <- Hnew); clear IHfT.
    -- destruct IH as [Hunsd [Hlcl [Re1 [R1 [HSubRe1 [HSubR
                       [Hwf' [HwtW [HInW  [Husd [Hwst' [Hwt' [Hlt' [Hlst' HlV1]]]]]]]]]]]]]].
       repeat split.

       + intros r HIn; rewrite Heq in HIn. apply Resources.diff_spec in HIn as [HInR' HnIn].
         repeat rewrite Resources.add_notin_spec in HnIn; destruct HnIn as [Hneq [Hneq' _]].
         apply Hunsd in HInR' as HI; destruct HI as [v HfV]; rewrite Hnew in *.
         rewrite RE.add_neq_o in HfV; auto. rewrite RE.add_neq_o in HfV; auto.
         replace r with ([⧐ᵣ V⁺ᵣᵦ ≤ 2] r) in HfV.
         ++ apply RE.shift_find_e_spec in HfV as HE. destruct HE as [v' Heq''].
            destruct v'; simpl in Heq''; inversion Heq''; subst; clear Heq''.
            exists λ. eapply RE.shift_find_spec; eauto.
         ++ apply Resource.shift_valid_refl. eapply RE.valid_in_spec; eauto.
            rewrite <- (wf_env_fT_in Re V); auto.
            destruct Hlt as [t1 [HmeT Hvt1]]; destruct Hli as [i1 [HmeT' Hvi1]].
            rewrite <- Hnew in *. 
            apply multi_preserves_typing with (t' := <[wormhole(i1;t1)]>) in Hwsf; auto.
            * apply typing_Re_R with (r := r) in Hwsf; auto. rewrite Heq.
              rewrite WriteStock.diff_spec; split; auto.
              rewrite WriteStock.add_notin_spec; split; auto.
              rewrite WriteStock.add_notin_spec; split; auto; intro c; inversion c.
            * eapply multi_trans with (y := <[wormhole( i1; t)]>).
              ** now apply multi_wh1.
              ** now apply multi_wh2.
       + intros r [HInR HInV]. rewrite RE.new_key_wh_spec in *; rewrite <- Hlcl.
         ++ symmetry. repeat rewrite RE.shift_add_spec. simpl. repeat rewrite RE.add_neq_o.
            * replace (S (S (V⁺ᵣᵦ))) with ((V⁺ᵣᵦ) + 2) by lia. rewrite <- RE.shift_unfold.
              replace (2 + (V1⁺ᵣᵦ - (V⁺ᵣᵦ + 2))) with (V1⁺ᵣᵦ - V⁺ᵣᵦ); auto.
              apply functional_preserves_valid in fT; 
              try (rewrite RE.new_key_wh_spec in *); try lia.
              ** apply RE.valid_wh_spec_1; auto; try constructor.
                 red; simpl. apply well_typed_implies_valid in Hwi as [Hwi _]; auto.
                 now rewrite <- Hnew.
              ** replace (S (S (V ⁺ᵣᵦ))) with ((V⁺ᵣᵦ) + 2) by lia.
                 apply Term.shift_preserves_valid_1. rewrite <- Hnew.
                 apply well_typed_implies_valid in Hwsv as [Hvst _]; auto.
              ** apply well_typed_implies_valid in Hwt as [Hwt _]; auto; 
                 try (rewrite RC.new_key_wh_spec in *).
                 { now rewrite <- Hnew. }
                 { 
                  apply RC.valid_wh_spec; auto; split; simpl; try (constructor);
                  apply well_typed_implies_valid in Hwi as [Hwi Hvτ]; auto.
                 }
            * intro c; subst; revert HInV. apply RE.Ext.new_key_notin_spec.
              unfold Resource.shift.
              replace (Resource.leb (S (S (V⁺ᵣᵦ))) (V⁺ᵣᵦ)) with false; auto.
              symmetry; rewrite Resource.leb_nle; lia.
            * intro c; subst; revert HInV. apply RE.Ext.new_key_notin_spec.
              unfold Resource.shift.
              replace (Resource.leb (S (S (V⁺ᵣᵦ))) (S (V⁺ᵣᵦ))) with false; auto.
              symmetry; rewrite Resource.leb_nle; lia.
         ++ split.
            * rewrite Heq in HInR; 
              apply Resources.diff_notin_spec in HInR as [HnIn | HIn]; auto.
              apply Resources.add_spec in HIn as [Heq' | HIn]; subst.
              ** rewrite Hnew in HInV. apply RE.Ext.new_key_notin_spec in HInV; auto.
              ** apply Resources.add_spec in HIn as [Heq' | HIn]; subst.
                 { rewrite Hnew in HInV. apply RE.Ext.new_key_notin_spec in HInV; auto. }
                 { inversion HIn. }
            * repeat (rewrite RE.add_in_iff; right). 
              apply RE.valid_in_spec with (x := r) in HvV as Hvr; auto.
              rewrite <- (Resource.shift_valid_refl (V⁺ᵣᵦ) 2 r); auto.
              now apply RE.shift_in_spec.
       + exists Re1; exists R1; split.
         ++ apply RC.Ext.Submap_Add_spec with (m := (⌈ Re⁺ᵣᵪ ⤆ (<[ 𝟙 ]>, τ) ⌉ᵣᵪ Re))
                                              (x := S (Re⁺ᵣᵪ)) (v := (τ, <[ 𝟙 ]>)) in HSubRe1; auto.
            * apply RC.Submap_Add_spec with
                (m := Re) (x := Re⁺ᵣᵪ) (v := (<[ 𝟙 ]>, τ)) in HSubRe1; auto.
              ** apply RC.Ext.new_key_notin_spec; auto.
              ** unfold RC.Add;  reflexivity.
            * intro c. rewrite RC.add_in_iff in c; destruct c; try lia.
              revert H; apply RC.Ext.new_key_notin_spec; lia.
            * unfold RC.Add; reflexivity.
         ++ repeat (split; try now auto).
            * rewrite Heq; intro r. intros HIn.
              apply Resources.diff_spec in HIn as [HIn _]. now apply HSubR.   
            * intros r v τ1 τ' HfW HfRe1. unfold Stock.find,Stock.add in *; simpl in *.
              rewrite ReadStock.add_o in HfW; auto. destruct (Resource.eq_dec (V⁺ᵣᵦ) r); subst.
              ** inversion HfW; subst; clear HfW. rewrite <- Hnew.
                 apply wf_env_fT_new in Hwf' as Hnew'; rewrite <- Hnew'.
                 apply weakening_ℜ; auto.
                 { 
                  apply (RC.Submap_Add_spec Re1 Re (⌈Re⁺ᵣᵪ ⤆ (<[𝟙]>, τ) ⌉ᵣᵪ Re)
                                            (Re⁺ᵣᵪ) (<[𝟙]>, τ)); try (now unfold RC.Add). 
                  - apply (RC.Submap_Add_spec Re1 (⌈Re⁺ᵣᵪ ⤆ (<[𝟙]>, τ) ⌉ᵣᵪ Re)
                                              (⌈S(Re⁺ᵣᵪ) ⤆ (τ, <[𝟙]>)⌉ᵣᵪ (⌈Re⁺ᵣᵪ ⤆ (<[𝟙]>, τ) ⌉ᵣᵪ Re))
                                              (S (Re⁺ᵣᵪ)) (τ, <[𝟙]>)); try (now unfold RC.Add).
                    -- apply RC.Ext.new_key_notin_spec. rewrite RC.Ext.new_key_add_spec_1; auto.
                       apply RC.Ext.new_key_notin_spec; lia.
                  - apply RC.Ext.new_key_notin_spec; lia. 
                 }
                 {
                  apply (RC.Ext.Submap_find_spec _ _ (Re⁺ᵣᵪ) (<[𝟙]>,τ)) in HSubRe1 as HfRe.
                  - rewrite Hnew in HfRe; rewrite HfRe1 in HfRe; inversion HfRe; now subst.
                  - rewrite RC.add_neq_o; try lia; rewrite RC.add_eq_o; auto.
                 }
              ** apply (HwtW r _ τ1 τ'); auto.
            * apply Resources.diff_spec in H as [HInR1 HnInR]. rewrite Heq in HnInR.
              apply Resources.diff_notin_spec in HnInR as [HnInR' | HIn].
              ** apply Stock.to_RS_in_spec. destruct (HInW r); try (now apply Resources.diff_spec).
                 apply Stock.to_RS_in_spec in H. apply Stock.add_spec; right; right; assumption.
              ** apply Stock.to_RS_in_spec. rewrite <- Hnew.
                 repeat rewrite Resources.add_spec in HIn. 
                 destruct HIn as [Heq' | [Heq' | HIn]]; try (now inversion HIn); subst;
                 unfold Stock.In; simpl.
                 { left; apply ReadStock.add_in_iff; now left. }
                 { right; apply WriteStock.add_spec; now left. }
            * apply Resources.diff_spec in H as [HInR1 HnInR]. rewrite Heq in HnInR.
              apply Resources.diff_notin_spec in HnInR as [HnInR' | HIn].
              ** destruct (HInW r) as [_ HInsV]; try (apply Resources.diff_spec; now split).
                 intro HInV; apply HInsV. repeat (rewrite RE.add_in_iff; right).
                 apply RE.valid_in_spec with (lb := V⁺ᵣᵦ) in HInV as Hvr; auto.
                 rewrite (RE.shift_in_spec (V⁺ᵣᵦ) 2) in HInV. 
                 now rewrite Resource.shift_valid_refl in HInV.
              ** rewrite Hnew in HIn. repeat rewrite Resources.add_spec in HIn;
                 destruct HIn as [Heq' | [Heq' | HIn]]; try (inversion HIn); subst;
                 apply RE.Ext.new_key_notin_spec; auto.
    -- now rewrite RC.new_key_wh_spec.
    -- rewrite RC.new_key_wh_spec; replace (S (S (Re ⁺ᵣᵪ))) with ((Re ⁺ᵣᵪ) + 2) by lia.
       rewrite <- Hnew. apply halts_weakening_1; auto.
    -- rewrite RC.new_key_wh_spec. apply RE.halts_add_spec; split.
       + simpl; exists <[unit]>; split; auto.
       + apply RE.halts_add_spec; split.
         ++ replace (S (S (Re ⁺ᵣᵪ))) with ((Re ⁺ᵣᵪ) + 2) by lia.
            rewrite <- Hnew. apply halts_weakening_1; auto.
         ++ rewrite <- Hnew. replace (S (S (Re⁺ᵣᵪ))) with ((Re⁺ᵣᵪ) + 2) by lia.
            apply RE.halts_weakening_1; auto.
    -- repeat split.
       + intro HIn. repeat rewrite RC.OP.P.add_in_iff in HIn.
         repeat rewrite RE.OP.P.add_in_iff.
         destruct HIn as [Heq' | [Heq' | HIn]]; subst.
         ++ left; f_equal; symmetry.
            now apply (wf_env_fT_new Re V).
         ++ right; left. symmetry; now apply (wf_env_fT_new Re V).
         ++ repeat right. 
            rewrite (wf_env_fT_in Re V) in HIn; auto.
            apply RE.valid_in_spec with (lb := V⁺ᵣᵦ) in HIn as Hvr; auto.
            rewrite <- (Resource.shift_valid_refl (V⁺ᵣᵦ) 2 r); auto.
            now apply RE.shift_in_spec.
       + intro HIn. repeat rewrite RE.OP.P.add_in_iff in HIn.
         repeat rewrite RC.OP.P.add_in_iff.
         destruct HIn as [Heq' | [Heq' | HIn]]; subst.
         ++ left; f_equal; symmetry.
            now rewrite (wf_env_fT_new Re V).
         ++ right; left. symmetry; now rewrite (wf_env_fT_new Re V).
         ++ repeat right.
            apply RE.shift_in_e_spec in HIn as Hr'.
            destruct Hr' as [r' Heq']; subst.
            apply RE.shift_in_spec in HIn.
            apply RE.valid_in_spec with (lb := V⁺ᵣᵦ) in HIn as Hvr; auto.
            rewrite (Resource.shift_valid_refl (V⁺ᵣᵦ) 2 r'); auto.
            now apply (wf_env_fT_in Re V).
       + rewrite RC.new_key_wh_spec. 
         apply RC.valid_wh_spec; auto; split; simpl;
         try now constructor.
         ++ now apply well_typed_implies_valid in Hwi as [_ Hwτ].
         ++ now apply well_typed_implies_valid in Hwi as [_ Hwτ].
       + rewrite RE.new_key_wh_spec.
         apply RE.valid_wh_spec_1; auto; try now constructor.
         unfold Cell.valid; simpl.
         apply well_typed_implies_valid in Hwi as [Hwi _]; auto.
         now rewrite <- (wf_env_fT_new Re V).
       + intros r τ1 τ1' v HfRe HfV.
         destruct (Resource.eq_dec r (S (Re⁺ᵣᵪ))); subst.
         ++ rewrite RE.add_eq_o in HfV; auto.
            rewrite RC.add_eq_o in HfRe; auto.
            inversion HfRe; inversion HfV; subst; clear HfV HfRe.
            constructor.
         ++ destruct (Resource.eq_dec r (Re⁺ᵣᵪ)); subst.
            * rewrite RE.add_neq_o in HfV; try lia.
              rewrite RE.add_eq_o in HfV; auto.
              rewrite RC.add_neq_o in HfRe; try lia.
              rewrite RC.add_eq_o in HfRe; auto.
              inversion HfRe; inversion HfV; subst; clear HfV HfRe.
              apply (weakening_ℜ_bis _ Re); auto.
              { 
                apply RC.Ext.Submap_add_spec_1.
                - apply RC.Ext.new_key_notin_spec.
                  rewrite RC.Ext.new_key_add_spec_1; auto.
                  apply RC.Ext.new_key_notin_spec; lia.
                - apply RC.Ext.Submap_add_spec_1.
                  -- apply RC.Ext.new_key_notin_spec; lia.
                  -- reflexivity.
              }
              { rewrite RC.new_key_wh_spec; lia. }
           * rewrite RE.add_neq_o in HfV; try lia.
             rewrite RE.add_neq_o in HfV; try lia.
             rewrite RC.add_neq_o in HfRe; try lia.
             rewrite RC.add_neq_o in HfRe; try lia.
             apply RE.shift_find_e_spec_1 in HfV as Hr'.
             destruct Hr' as [[r' Heqr'] [v' Heqv']]; subst.
             rewrite Heqv' in *; clear Heqv'.
             apply RE.shift_find_spec in HfV.
             apply RE.valid_find_spec with (lb := V⁺ᵣᵦ) in HfV as Hvr'; auto.
             destruct Hvr' as [Hvr' _].
             rewrite Resource.shift_valid_refl in HfRe; auto.
             apply (wf_env_fT_well_typed Re V Hwf r' v') in HfRe as Hwv'; auto.
             destruct v'; auto; simpl.
             ** apply (weakening_ℜ_bis _ Re); auto.
                { 
                  apply RC.Ext.Submap_add_spec_1.
                  - apply RC.Ext.new_key_notin_spec.
                    rewrite RC.Ext.new_key_add_spec_1; auto.
                    apply RC.Ext.new_key_notin_spec; lia.
                  - apply RC.Ext.Submap_add_spec_1.
                    -- apply RC.Ext.new_key_notin_spec; lia.
                    -- reflexivity.
                }
                { rewrite RC.new_key_wh_spec; lia. }
             ** apply (weakening_ℜ_bis _ Re); auto.
                { 
                  apply RC.Ext.Submap_add_spec_1.
                  - apply RC.Ext.new_key_notin_spec.
                    rewrite RC.Ext.new_key_add_spec_1; auto.
                    apply RC.Ext.new_key_notin_spec; lia.
                  - apply RC.Ext.Submap_add_spec_1.
                    -- apply RC.Ext.new_key_notin_spec; lia.
                    -- reflexivity.
                }
                { rewrite RC.new_key_wh_spec; lia. }
Qed.

Theorem progress_of_functional_value (Re : ℜ) (V : 𝓥) (tv sf : Λ) (τ τ' : Τ) (R : resources) :
  (* (1) *) value(sf) -> (* (2) *) halts (Re⁺ᵣᵪ) tv -> (* (3) *) RE.halts (Re⁺ᵣᵪ) V -> 

  (* (4) *) ∅ᵥᵪ ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) ->
  (* (5) *) ∅ᵥᵪ ⋅ Re ⊫ tv ∈ τ ->

  (* (6) *) Wfᵣₜ(Re,V) ->
  (* (7) *)(forall (r : resource), (r ∈ R)%rs -> RE.unused r V) ->

  exists (V1 : 𝓥) (tv' sf' : Λ) (W : 𝐖),
    ⪡ V ; tv ; sf ⪢ ⭆ ⪡ V1 ; tv' ; sf' ; W ⪢.
Proof.
Admitted.

(** *** Some corollaries *)

Corollary functional_preserves_wf_env_fT (Re : ℜ) (V V1 : 𝓥) (W : 𝐖) (sv sv' sf sf' : Λ) 
                                                                      (τ τ' : Τ) (R : resources):

  (* (1) *) halts (Re⁺ᵣᵪ) sf -> (* (2) *) halts (Re⁺ᵣᵪ) sv -> (* (3) *) RE.halts (Re⁺ᵣᵪ) V -> 

  (* (4) *)  Wfᵣₜ(Re,V) ->
  (* (5) *)  ∅ᵥᵪ ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) -> 
  (* (6) *)  ∅ᵥᵪ ⋅ Re ⊫ sv ∈ τ -> 
  (* (7) *)  ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ -> 

  exists Re1, Wfᵣₜ(Re1,V1).
Proof.
  intros Hlsf Hlsv HlV Hwf Hwt Hwst HfT.
  eapply functional_preserves_typing_gen in HfT; eauto.
  destruct HfT as [_ [_ [Re1 [_ [_  [_ [Hwf1 _]]]]]]]; now exists Re1.
Qed.

Corollary functional_preserves_stream_typing (Re : ℜ) (V V1 : 𝓥) (W : 𝐖) 
                                                  (sv sv' sf sf' : Λ) (τ τ' : Τ) (R : resources): 

  (* (1) *) halts (Re⁺ᵣᵪ) sf -> (* (2) *) halts (Re⁺ᵣᵪ) sv -> (* (3) *) RE.halts (Re⁺ᵣᵪ) V -> 

  (* (2) *)  Wfᵣₜ(Re,V) ->
  (* (3) *)  ∅ᵥᵪ ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) -> 
  (* (4) *)  ∅ᵥᵪ ⋅ Re ⊫ sv ∈ τ -> 
  (* (5) *)  ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ -> 

  exists Re1, ∅ᵥᵪ ⋅ Re1 ⊫ sv' ∈ τ'.
Proof.
  intros Hlsf Hlsv HlV Hwf Hwt Hwst HfT.
  eapply functional_preserves_typing_gen in HfT; eauto.
  destruct HfT as [_ [_ [Re1 [_ [_ [_  [_ [Hwf' [_ [_ [Hwsv' _]]]]]]]]]]];
  now exists Re1.
Qed.

Corollary functional_preserves_halting (Re : ℜ) (V V1 : 𝓥) (W : 𝐖) 
                                                  (sv sv' sf sf' : Λ) (τ τ' : Τ) (R : resources): 

  (* (1) *) halts (Re⁺ᵣᵪ) sf -> (* (2) *) halts (Re⁺ᵣᵪ) sv -> (* (3) *) RE.halts (Re⁺ᵣᵪ) V -> 

  (* (2) *)  Wfᵣₜ(Re,V) ->
  (* (3) *)  ∅ᵥᵪ ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) -> 
  (* (4) *)  ∅ᵥᵪ ⋅ Re ⊫ sv ∈ τ -> 
  (* (5) *)  ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ -> 

  exists Re1, 
  (* (6) *) halts (Re1⁺ᵣᵪ) sf' /\ 
  (* (7) *) halts (Re1⁺ᵣᵪ) sv' /\ 
  (* (8) *) RE.halts (Re1⁺ᵣᵪ) V1.
Proof.
  intros Hlsf Hlsv HlV Hwf Hwt Hwst HfT.
  eapply functional_preserves_typing_gen in HfT; eauto.
  destruct HfT as [_ [_ [Re1 [_ [_ [_  [_ [_ [_ [_ [_ [_ [Hlsf' [Hlsv' HlV1]]]]]]]]]]]]]];
  now exists Re1.
Qed.

Corollary functional_preserves_typing (Re : ℜ) (V V1 : 𝓥) (W : 𝐖) (sv sv' sf sf' : Λ) 
                                                                   (τ τ' : Τ) (R : resources):

  (* (1) *) halts (Re⁺ᵣᵪ) sf -> (* (2) *) halts (Re⁺ᵣᵪ) sv -> (* (3) *) RE.halts (Re⁺ᵣᵪ) V -> 

  (* (4) *)  Wfᵣₜ(Re,V) ->
  (* (5) *)  ∅ᵥᵪ ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) ->
  (* (6) *)  ∅ᵥᵪ ⋅ Re ⊫ sv ∈ τ -> 
  (* (7) *)  ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ -> 

  exists (Re1 : ℜ) (R' : resources), 
    (*  (8) *) Re ⊆ᵣᵪ Re1 /\  
    (*  (9) *) (R ⊆ R')%rs /\ 
    (* (10) *) Wfᵣₜ(Re1,V1) /\ 
    (* (11) *) ∅ᵥᵪ ⋅ Re1 ⊫ sv' ∈ τ' /\
    (* (12) *) ∅ᵥᵪ ⋅ Re1 ⊫ sf' ∈ (τ ⟿ τ' ∣ R').
Proof.
  intros Hlsf Hlsv HlV Hwf Hwt Hwst HfT.
  eapply functional_preserves_typing_gen in HfT; eauto.
  destruct HfT as [_ [_ [Re1 [R' [HSubRe  [HSubR' [Hwf' [_ [_ [_ [Hwsv' [Hwsf' _]]]]]]]]]]]];
  exists Re1; now exists R'.
Qed.

End safety.