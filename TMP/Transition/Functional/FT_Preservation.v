From Coq Require Import Program Lia Relations.Relation_Definitions Classes.RelationClasses PeanoNat
                        Classical_Prop Classical_Pred_Type Bool.Bool Classes.Morphisms
                        Relations.Relation_Operators.
From Mecha Require Import Resource Resources Term Typ Var ReadStock Typing VContext RContext ET_Definition
                          Cell REnvironment Stock FT_Definition ET_Props ET_Preservation FT_Props.
Import ResourceNotations TermNotations TypNotations CellNotations
       VContextNotations RContextNotations REnvironmentNotations
       ReadStockNotations ResourcesNotations StockNotations SetNotations.

Module RC := RContext.
Module RE := REnvironment.

(** * Transition - Functional - Preservation *)

Section safety.

Open Scope renvironment_scope.

Hypothesis all_arrow_halting : forall Re t α β,
  ∅%vc ⋅ Re ⊫ arr(t) ∈ (α ⟿ β ∣ ∅%s) -> forall v, ∅%vc ⋅ Re ⊫ v ∈ α -> halts (Re⁺)%rc <[t v]>.

Hint Resolve VContext.valid_empty_spec Stock.valid_empty_spec Resources.valid_empty_spec : core.


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
Lemma functional_preserves_valid (V V1 : 𝐕) (W : 𝐖) (st st' sf sf' : Λ) :
  (* (1) *) ⪡ V ; st ; sf ⪢ ⭆ ⪡ V1 ; st' ; sf' ; W ⪢ ->
  (* (2) *) V⁺ ⊩ V -> 
  (* (3) *) (V⁺ ⊩ st)%tm -> 
  (* (4) *) (V⁺ ⊩ sf)%tm ->

  (* (5) *) V1⁺ ⊩ V1 /\ (V1⁺ ⊩ st')%tm /\ (V1⁺ ⊩ sf')%tm /\ (V1⁺ ⊩ W)%sk /\ 
  (* (6) *) V⁺ <= V1⁺.
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
    -- constructor; auto. apply Term.shift_preserves_valid_2; auto.
    -- constructor; auto; eapply Typ.valid_weakening; eauto.
  (* fT_comp *)
  - inversion Hvt; subst; 
    destruct IHfT1 as [HvV1 [Hvst' [Hvt1' [HvW1 Hlt1]]]]; auto;
    destruct IHfT2 as [HvV2 [Hvst'' [Hvt2' [HvW2 Hlt2]]]]; auto; fold Term.valid in *.
    -- apply Term.shift_preserves_valid_2; auto.
    -- do 3 (split; auto).
       + constructor; auto. apply Term.shift_preserves_valid_2; auto.
       + split; try lia. apply Stock.valid_union_spec; split; try assumption.
         apply Stock.shift_preserves_valid_2; auto.
  (* fT_rsf *)
  - assert (r ∈ V).
    { rewrite RE.in_find; rewrite H; intro c; now inversion c. }
    rewrite RE.Ext.new_key_add_in_spec; auto; try lia; repeat split; auto.
    -- now apply RE.valid_update_spec.
    -- now apply RE.valid_find_spec with (lb := V⁺) in H as [_ H].
  (* fT_wh *)
  - rewrite RE.new_key_wh_spec in *. inversion Hvt; subst; clear Hvt.
    destruct IHfT as [HvV1 [Hvst' [Hvt'' [HvW Hlt]]]]; auto; fold Term.valid in *. 
    + apply RE.valid_wh_spec_1; auto; try (constructor).
    + replace (S (S (V⁺))) with ((V⁺) + 2) by lia.
      now apply Term.shift_preserves_valid_1.
    + do 3 (split; auto); split; try lia.
      apply Stock.valid_add_spec; eauto.
      ++ unfold Resource.valid; lia.
      ++ apply Term.shift_preserves_valid_2; auto; lia.
Qed.


(** *** Proof of preservation of keys in the environment 

  Keeping consistent the typing through the functional transition is 
  needed for the resources environment. Thus, knowing that we cannot loose 
  keys is required.
*)
Lemma functional_preserves_keys (V V1 : 𝐕) (W : 𝐖) (sv sv' sf sf' : Λ) :
  ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ ->
  V⁺ ⊩ V -> 
  (V⁺ ⊩ sv)%tm -> 
  (V⁺ ⊩ sf)%tm ->

  (forall (r : resource), r ∈ V -> r ∈ V1).
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
    apply IHfT2; auto. apply Term.shift_preserves_valid_2; auto.
  (* fT_rsf *)
  - destruct (Resource.eq_dec r r'); subst; apply RE.add_in_iff; auto.
  (* fT_wh *)
  - rewrite RE.new_key_wh_spec in *.
    inversion Hvsf; subst; destruct IHfT with (r := r'); auto.
    -- apply RE.valid_wh_spec_1; auto; constructor.
    -- replace (S (S (V⁺))) with ((V⁺) + 2) by lia.
       now apply Term.shift_preserves_valid_1.
    -- destruct (Resource.eq_dec r' (S (V⁺))); subst; apply RE.add_in_iff; auto.
       right; destruct (Resource.eq_dec r' (V⁺)); subst; apply RE.add_in_iff; auto.
       right; eapply RE.shift_in_iff in HInV as HInV1.
       eapply RE.valid_in_spec in HInV; eauto.
       rewrite Resource.shift_valid_refl in HInV1; eauto.
    -- now exists x.
Qed.

(** *** Proof of consistency between V and W 

  W stocks all virtual resources created during the functional transition. Those virtual
  resources are also added in the resource environment V1 and cannot be found in the environment V.
*)
Lemma consistency_V_W (V V1 : 𝐕) (W : 𝐖) (sv sv' sf sf' : Λ) :
  ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ ->
  V⁺ ⊩ V -> 
  (V⁺ ⊩ sv)%tm -> 
  (V⁺ ⊩ sf)%tm ->

  (forall (r : resource), (r ∈ W)%sk -> r ∉ V /\ r ∈ V1).
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
       apply Stock.shift_in_iff in HIn as HIn'.
       apply IHfT1 in HIn' as IH; auto.
       eapply Stock.valid_in_spec in HIn' as Hvr'; eauto.
       rewrite Resource.shift_valid_refl; auto.
       destruct IH; split; auto.
       eapply functional_preserves_keys in H0; eauto.
       apply Term.shift_preserves_valid_2; auto.
    -- apply IHfT2 in HIn; auto.
       + destruct HIn; split; auto. intro. eapply functional_preserves_keys in H2; eauto.
       + apply Term.shift_preserves_valid_2; auto.
  (* fT_rsf *)
  - intros r' HIn; apply Stock.empty_in_spec in HIn; contradiction.
  (* fT_wh *)
  - inversion Hvsf; subst; clear Hvsf; fold Term.valid in *.
    rewrite RE.new_key_wh_spec in *. intros rf HIn.
    apply Stock.add_spec in HIn as [Heq | [Heq | HIn]]; subst; split;
    try (apply RE.Ext.new_key_notin_spec; lia).
    -- eapply functional_preserves_keys; eauto; try rewrite RE.new_key_wh_spec; auto.
       + apply RE.valid_wh_spec_1; auto; constructor.
       + replace (S (S (V⁺))) with ((V⁺) + 2) by lia; 
         now apply Term.shift_preserves_valid_1.
       + repeat rewrite RE.add_in_iff; auto.
    -- eapply functional_preserves_keys; eauto; try rewrite RE.new_key_wh_spec; auto.
       + apply RE.valid_wh_spec_1; auto; constructor.
       + replace (S (S (V⁺))) with ((V⁺) + 2) by lia; 
         now apply Term.shift_preserves_valid_1.
       + repeat rewrite RE.add_in_iff; auto.
    -- eapply IHfT in HIn as [HnIn HIn]; eauto.
       + intro c; apply HnIn; repeat rewrite RE.add_in_iff; repeat right.
         apply RE.valid_in_spec_1; auto.
       + apply RE.valid_wh_spec_1; auto; constructor.
       + replace (S (S (V⁺))) with ((V⁺) + 2) by lia; 
         now apply Term.shift_preserves_valid_1.
    -- eapply IHfT in HIn as [HnIn HIn]; eauto. 
       + apply RE.valid_wh_spec_1; auto; constructor.
       + replace (S (S (V⁺))) with ((V⁺) + 2) by lia; 
         now apply Term.shift_preserves_valid_1.
Qed.

(** *** Proof of inner constraint of W 

  W stocks reading virtual resource names and writing virtual resource names. It is relevant
  to state that the intersection of set of reading and writing resource names is empty.
*)
Lemma W_well_formed (V V1 : 𝐕) (W : 𝐖) (sv sv' sf sf' : Λ) :
  ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ ->
  V⁺ ⊩ V -> 
  (V⁺ ⊩ sv)%tm -> 
  (V⁺ ⊩ sf)%tm ->

  (forall r, (r ∈ W)%sk -> ((r ∈ (fst W))%rk /\ r ∉ (snd W))%s \/ ((r ∉ (fst W))%rk /\ r ∈ (snd W)))%s.
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
         rewrite Resources.St.union_notin_spec. rewrite Resources.valid_in_spec_1 in *; 
         auto; rewrite ReadStock.valid_in_spec_1 in *; auto; split.
         ++ apply IHfT1 with (r := r') in H2 as [[_ HnI] | [Hc _]]; auto.
         ++ apply consistency_V_W with (r := r') in fT1 as [_ HInV1]; auto;
            try (red; auto); intro HIn.
            apply IHfT2 with (r := r') in HvV1 as HI; auto.
            * destruct HI as [[_ HnI] | [Hc _]]; auto.
              apply consistency_V_W with (r := r') in fT2 as [HnInV1 _]; auto; try (red; auto).
              apply Term.shift_preserves_valid_2; auto.
            * apply Term.shift_preserves_valid_2; auto.
       + right; split; try (rewrite Resources.St.union_spec; now left).
         intro HIn; rewrite Resources.valid_in_spec_1 in *; auto;
         apply ReadStock.map_union_spec in HIn as [HInRw | HInRw'].
         ++ rewrite ReadStock.valid_in_spec_1 in *; auto.
            apply IHfT1 with (r := r') in H2 as [[_ HnI] | [Hc _]]; auto.
         ++ apply consistency_V_W with (r := r') in fT1 as [_ HInV1]; auto;
            try (red; auto).
            apply IHfT2 with (r := r') in HvV1 as HI; auto.
            * destruct HI as [[_ HnI] | [Hc _]]; auto.
              apply consistency_V_W with (r := r') in fT2 as [HnInV1 _]; auto; try (red; auto).
              apply Term.shift_preserves_valid_2; auto.
            * apply Term.shift_preserves_valid_2; auto.
    -- destruct HInW' as [HInRw' | HInWw']. 
       + left; split; try (rewrite ReadStock.map_union_spec; now right).
         rewrite Resources.St.union_notin_spec; rewrite Resources.valid_in_spec_1 in *; auto; split.
         ++ intro HInWw; apply IHfT1 with (r := r') in H2 as HI; auto.
            destruct HI as [[_ HnInWw] | [HnInRw _]]; auto.
            apply consistency_V_W with (r := r') in fT1 as [_ HInV1]; auto; try (red; auto).
            apply consistency_V_W with (r := r') in fT2 as [HnInV1 _]; auto; try (red; auto).
            apply Term.shift_preserves_valid_2; auto.
         ++ apply IHfT2 with (r := r') in HvV1 as [[_ HnI] | [Hc _]]; auto.
            apply Term.shift_preserves_valid_2; auto.
       + right; split; try (rewrite Resources.St.union_spec; now right).
         intro HIn; apply ReadStock.map_union_spec in HIn as [HInRw | HInRw'].
         ++ rewrite ReadStock.valid_in_spec_1 in *; auto.
            apply consistency_V_W with (r := r') in fT1 as [_ HInV1]; auto; try (red; auto).
            apply consistency_V_W with (r := r') in fT2 as [HnInV1 _]; auto; try (red; auto).
            apply Term.shift_preserves_valid_2; auto.
         ++ apply IHfT2 with (r := r') in HvV1 as [[_ HnI] | [Hc _]]; auto.
            apply Term.shift_preserves_valid_2; auto.
  (* fT_wh *)
  - inversion Hvsf; subst; fold Term.valid in *; unfold Stock.add, Stock.In in *; 
    clear Hvsf; destruct W as [Rw Ww]; simpl; destruct HIn as [HInRw | HInWw].
    -- simpl in HInRw; left; split; auto. 
       apply ReadStock.add_in_iff in HInRw as [Heq | HInRw]; subst.
       + rewrite Resources.St.add_notin_spec; split; try lia.
         intro HInWw. apply consistency_V_W with (r := V⁺) in fT as [HnIn _]; 
         try (rewrite RE.new_key_wh_spec); auto.
         ++ apply HnIn. repeat rewrite RE.add_in_iff; right; now left.
         ++ apply RE.valid_wh_spec_1; auto; constructor.
         ++ replace (S (S (V⁺))) with ((V⁺) + 2) by lia.
              now apply Term.shift_preserves_valid_1.
         ++ unfold Stock.In; simpl; auto.
       + rewrite Resources.St.add_notin_spec; split.
         ++ intro Heq; subst. apply consistency_V_W with (r := S (V⁺)) in fT as [HnIn _]; 
            try (rewrite RE.new_key_wh_spec); auto.
            * apply HnIn. repeat rewrite RE.add_in_iff; now left.
            * apply RE.valid_wh_spec_1; auto; constructor.
            * replace (S (S (V⁺))) with ((V⁺) + 2) by lia.
                  now apply Term.shift_preserves_valid_1.
            * unfold Stock.In; simpl; auto.
         ++ rewrite RE.new_key_wh_spec in *; 
            apply IHfT with (r := r') in H3 as [[_ HnInWw] | [HnInRw _]]; auto.
            * apply RE.valid_wh_spec_1; auto; constructor.
            * replace (S (S (V⁺))) with ((V⁺) + 2) by lia.
              now apply Term.shift_preserves_valid_1.
    -- simpl in HInWw; right; split; auto. 
       apply Resources.St.add_spec in HInWw as [Heq | HInWw]; subst.
       + intro HInRw; rewrite ReadStock.add_in_iff in HInRw; 
         destruct HInRw as [Hc | HInRw]; try lia.
         apply consistency_V_W with (r := S (V⁺)) in fT as [HnIn _]; 
         try (rewrite RE.new_key_wh_spec); auto.
         ++ apply HnIn. repeat rewrite RE.add_in_iff; now left.
         ++ apply RE.valid_wh_spec_1; auto; constructor.
         ++ replace (S (S (V⁺))) with ((V⁺) + 2) by lia.
              now apply Term.shift_preserves_valid_1.
         ++ unfold Stock.In; simpl; auto.
       + intro HInRw; rewrite ReadStock.add_in_iff in HInRw; 
         destruct HInRw as [Hc | HInRw]; subst.
         ++ apply consistency_V_W with (r := V⁺) in fT as [HnIn _]; 
            try (rewrite RE.new_key_wh_spec); auto.
            * apply HnIn. repeat rewrite RE.add_in_iff; right; now left.
            * apply RE.valid_wh_spec_1; auto; constructor.
            * replace (S (S (V⁺))) with ((V⁺) + 2) by lia.
              now apply Term.shift_preserves_valid_1.
            * unfold Stock.In; simpl; auto.
         ++ rewrite RE.new_key_wh_spec in *; 
            apply IHfT with (r := r') in H3 as [[_ HnInWw] | [HnInRw _]]; auto.
            * apply RE.valid_wh_spec_1; auto; constructor.
            * replace (S (S (V⁺))) with ((V⁺) + 2) by lia.
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
Theorem functional_preserves_typing_gen (Re : ℜ) (V V1 : 𝐕) (W : 𝐖) (sv sv' sf sf' : Λ) 
                                                                      (τ τ' : Τ) (R : resources) :

  (* (1) *) halts (Re⁺)%rc sf -> (* (2) *) halts (Re⁺)%rc sv -> (* (3) *) RE.halts (Re⁺)%rc V -> 

  (* (4) *) ∅%vc ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) ->
  (* (5) *) ∅%vc ⋅ Re ⊫ sv ∈ τ -> 
  (* (6) *) ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ -> 
  (* (7) *) Wfᵣₜ(Re,V) ->


  (* (8) *)(forall (r : resource), (r ∈ R)%s -> RE.unused r V) /\
  (* (9) *)(forall (r : resource), (r ∉ R)%s /\ (r ∈ V) -> 
              ([⧐ (V⁺) – ((V1⁺) - (V⁺))] V) ⌊r⌋ = V1 ⌊r⌋) /\

  exists (Re1 : ℜ) (R' : resources), 
    (* (10) *) (Re ⊆ Re1)%rc     /\ 
    (* (11) *) (R ⊆ R')%s    /\
    (* (12) *) Wfᵣₜ(Re1,V1) /\
    (* (13) *) (forall (r : resource) (v : Λ) (τ τ' : Τ), 
                  W⌊r⌋%sk = Some v -> Re1⌊r⌋%rc = Some (τ',τ) -> ∅%vc ⋅ Re1 ⊫ v ∈ τ) /\
    (* (14) *) (forall (r : resource), (r ∈ (R' \ R))%s -> (r ∈ W)%sk /\ (r ∉ V)) /\
    (* (15) *) (forall (r : resource), (r ∈ R')%s -> RE.used r V1) /\
    (* (16) *) ∅%vc ⋅ Re1 ⊫ sv' ∈ τ' /\
    (* (17) *) ∅%vc ⋅ Re1 ⊫ sf' ∈ (τ ⟿ τ' ∣ R') /\
    
    (* (18) *) halts (Re1⁺)%rc sf' /\ (* (19) *) halts (Re1⁺)%rc sv' /\ 
    (* (20) *) RE.halts (Re1⁺)%rc V1 /\ (* (21) *) Stock.halts (Re1⁺)%rc W.
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
    -- intros r [HnIn HIn]; replace (V⁺ - V⁺) with 0 by lia.
        now rewrite RE.shift_zero_refl.
    -- exists Re; exists ∅%s. repeat (split; try now auto).
        + apply wt_app with (α := α); assumption.
        + eapply all_arrow_halting with (β := β); eauto. 
  (* fT_first *)
  -
    (* clean *)
    inversion Hwsf; subst; move Re before W; move R before Re. move α0 before τ;
    move β0 before α0; clear Hwsf; rename H4 into Hwt; rename H7 into Hvτ;
    move Hwt after Hwsv; move Hvτ before Hwsv. rename fT into HfT;  move HfT after IHfT;
    inversion Hwsv; subst; rename H4 into Hwv1; rename H6 into Hwv2; move Hwv1 before Hwt;
    move Hwv2 before Hwv1; clear Hwsv; move HvRe after Hvτ; move HvV after HvRe.
    rename α0 into α; rename β0 into β.
    (* clean *)

    apply halts_first in Hlsf; apply halts_pair in Hlsv as [Hlv1 Hlv2].
    apply IHfT with (R := R) (τ' := β) in Hwv1 as IH; auto; clear IHfT.

    
    destruct IH as [Hunsd [Hlcl [Re' [R' [HSubRe [HSubR [Hwf' 
                          [HwtW [HInW [Husd [Hwv1' [Hwt' [Hlt' [Hlv1' [HlV1 HlW]]]]]]]]]]]]]]].

    (* clean *)
    move Re' before Re; move R' before R; move Hwv1' before Hwv1; clear Hwv1;
    move Hwt' before Hwt; clear Hwt; move Hwf' before Hwf; move Hunsd before Husd.
    move Hlt' before Hlsf; move Hlv1' before Hlv1; move HlV1 before HlV; 
    move Hlcl after HSubR; move HlW before HlV1.
    (* clean *)

    apply wf_env_fT_new in Hwf' as Hnew'; move Hnew' before Hnew.

    repeat (split; try now auto).
    exists Re'; exists R'; repeat (split; try now auto).
    -- constructor; auto; rewrite <- Hnew; rewrite <- Hnew'.
       apply weakening_ℜ; auto.
    -- apply wt_first; try assumption.
       apply Typ.valid_weakening with (k := (Re⁺)%rc); try assumption.
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
    try (intros; apply Hunsd; rewrite Resources.St.union_spec; now left).
    clear IHfT1; 
    destruct IH1 as [Hunsd1 [Hlcl1 [Re' [R1' [HSubRe [HSubR1 [Hwf' 
                    [HwtW [HInW [Husd1 [Hwsv' [Hwt1' [Hlt1' [Hlst' [HlV1 HlW1]]]]]]]]]]]]]]].

    (* clean *)
    move Re' before Re; move R1' before R1; move Hwsv' before Hwsv;
    move Hwt1' before Hwt1; move Hunsd1 after HInW; move Hwf' before Hwf;
    move Hlt1' before Hlt1; move Hlst' before Hlsv; move HlV1 before HlV.
    move HlW1 before HlV1.
    (* clean *)

    apply wf_env_fT_new in Hwf' as Hnew'; move Hnew' before Hnew.
    apply IHfT2 with (R := R2) (τ' := β) in Hwsv' as IH2; auto.

    -- destruct IH2 as [Hunsd2 [Hlcl2 [Re'' [R2' [HSubRe' [HSubR2 
                       [Hwf'' [HwtW' [HInW'  [Husd2 [Hwsv'' [Hwt2' [Hlt2' 
                       [Hlst'' [HlV2 HlW2]]]]]]]]]]]]]]].

       (* clean *)
       move Re'' before Re'; move R2' before R2; move Hwsv'' before Hwsv';
       move Hwt2' before Hwt2; move Hunsd2 before Hunsd1; move Hwf'' before Hwf';
       clear IHfT2; move HSubRe' before HSubRe; move HSubR2 before HSubR1; move HInW' before HInW;
       move Husd2 before Husd1; move Hlcl2 before Hlcl1; move Hlt2' before Hlt2; 
       move Hlst'' before Hlst'; move HlV2 before HlV1; move HlW2 before HlW1.
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

       assert (HEmp' : (∅ = R1' ∩ R2')%s).
      {
        symmetry; apply Resources.St.empty_is_empty_1; unfold Resources.St.Empty.
        intros r' HIn; apply Resources.St.inter_spec in HIn as [HIn1 HIn2].
        destruct (Resources.St.In_dec r' R1) as [HInR1 | HnInR1]; 
        destruct (Resources.St.In_dec r' R2) as [HInR2 | HnInR2].
        - symmetry in HEmp; apply Resources.St.empty_is_empty_2 in HEmp.
          apply (HEmp r'). apply Resources.St.inter_spec; split; auto.
        - destruct (HInW' r') as [_ HnInV1]; try (rewrite Resources.St.diff_spec; split; auto).
          assert (HInV1 : r' ∈ V).
          { apply Hunsd1 in HInR1 as [v HfV]. exists (⩽ v … ⩾); now apply RE.find_2. }
          rewrite Hnew in Hvt1,Hvst. 
          apply (functional_preserves_keys V V1 W st st' t1 t1') in HInV1; auto.
            
        - assert (HInV1 : r' ∈ V).
          { 
            rewrite <- (wf_env_fT_in Re V Hwf r'). 
            destruct Hlt2 as [v2 [HmeT Hvv2]]. 
            apply multi_preserves_typing with (t' := v2) in Hwt2; auto.
            apply (typing_Re_R v2 (∅%vc) _ τ β R2); auto.
          }

          revert HInV1; apply HInW; rewrite Resources.St.diff_spec; split; assumption.

        - destruct (HInW r') as [HInW1 HnInV]; try (rewrite Resources.St.diff_spec; now split).
          destruct (HInW' r') as [_ HnInV1]; try (rewrite Resources.St.diff_spec; now split).

          apply consistency_V_W with (r := r') in HfT1 as [_ Hc]; auto.

          -- rewrite <- Hnew. 
             apply (well_typed_implies_valid (∅%vc) Re st α); auto. 
          -- rewrite <- Hnew. 
             apply (well_typed_implies_valid (∅%vc) Re t1 <[α ⟿ τ ∣ R1]>); auto. 
        }

        move HEmp' before HEmp. repeat split.
        + intros r HIn; apply Resources.St.union_spec in HIn as [HInR1 | HInR2]; auto.
          destruct Hlt2 as [v2 [HmeT Hvv2]]; 
          apply multi_preserves_typing with (t' := v2) in Hwt2; auto.
          apply (typing_Re_R v2 (∅%vc) Re τ β R2) in HInR2 as HInRe; auto.
          rewrite (wf_env_fT_in Re V Hwf r) in HInRe; destruct HInRe as [v HfV];
          apply RE.find_1 in HfV; destruct v.
          ++ now exists λ.
          ++ apply RE.shift_find_iff with (lb := V⁺) (k := V1⁺ - V⁺) in HfV as HfV'.
             rewrite Resource.shift_valid_refl in HfV'.
             * rewrite Hlcl1 in HfV'.
               ** apply Hunsd2 in HInR2 as HunsdV1; destruct HunsdV1 as [λ1 HfV1].
                  rewrite HfV1 in *; simpl in *; inversion HfV'.
               ** split.
                  {
                    intro. symmetry in HEmp; apply Resources.St.empty_is_empty_2 in HEmp; 
                    apply (HEmp r); rewrite Resources.St.inter_spec; now split.
                  }
                  { exists (⩽ … λ ⩾); now apply RE.find_2.  }
             * apply RE.valid_in_spec with (m := V); auto. 
               exists (⩽ … λ ⩾); now apply RE.find_2.
        + intros r [HnInR HInV]. apply Resources.St.union_notin_spec in HnInR as [HnInR1 HnInR2].
          apply functional_preserves_keys with (r := r) in HfT1 as HInV1; auto;
          try (now rewrite <- Hnew). rewrite <- (RE.shift_unfold_1 _ (V1⁺)).
          ++ rewrite (RE.shift_find_spec_3 _ _ r ([⧐ V⁺ – V1⁺ - V⁺] V) V1); auto.
             * rewrite Hnew in *. now apply (RE.valid_in_spec _ _ V1).
             * apply RE.valid_in_spec with (lb := V⁺) in HInV as Hvr; auto.
               rewrite <- (Resource.shift_valid_refl (V⁺) (V1⁺ - V⁺) r); auto.
               now apply RE.shift_in_iff.
          ++ rewrite <- Hnew; rewrite <- Hnew'; now apply RC.Ext.new_key_Submap_spec.
          ++ rewrite <- Hnew'; rewrite <- Hnew''; now apply RC.Ext.new_key_Submap_spec.
        + exists Re''; exists (R1' ∪ R2')%rs; repeat (split; try now auto; try (now transitivity Re')).
          ++ intros r HIn. rewrite Resources.St.union_spec in *; destruct HIn as [HIn | HIn]; auto.
          ++ intros r v τ1 τ' Hfi HfiRe.

            (* clean *)
            move r before τ; move τ1 before τ; move τ' before τ; move v before t2'.
            (* clean *)
            
            apply Stock.union_find_spec in Hfi; destruct Hfi.
            * apply ReadStock.shift_find_e_spec_1 in H as HI.
              destruct HI as [[r' Heq] [v' Heqv]]; subst. apply Term.eq_leibniz in Heqv; subst.

              rewrite <- Hnew''; rewrite <- Hnew'; apply weakening_ℜ; auto.
              ** apply (wf_env_fT_valid Re' V1 Hwf').
              ** rewrite Heq in *. apply ReadStock.shift_find_iff in H. 
                 apply (HwtW _ _ τ1 τ') in H; auto.
                 assert (r' ∈ W)%sk. 
                 { unfold Stock.In; left. exists v'; now apply ReadStock.find_2. }

                 apply consistency_V_W with (r := r') in HfT1 as [_ HInV1]; auto;
                 try (now rewrite <- Hnew).
                 apply (wf_env_fT_in Re' V1 Hwf' r') in HInV1 as HInRe'. 
                 apply RE.valid_in_spec with (lb := V1⁺) in HInV1; auto.
                 rewrite Resource.shift_valid_refl in HfiRe; auto.
                 destruct HInRe' as [v HfRe']; apply RC.find_1 in HfRe'.
                 apply RC.Submap_find_spec with (m' := Re'') in HfRe' as HfRe''; auto.
                 rewrite HfRe'' in HfiRe; inversion HfiRe; now subst.
            * apply (HwtW' r _ _ τ'); auto.
          ++ apply Resources.St.diff_spec in H as [HIn HnIn]. 
             apply Resources.St.union_notin_spec in HnIn as [HnInR1 HnInR2].
             apply Resources.St.union_spec in HIn as [HInR1' | HInR2'].
             * destruct (HInW r) as [HInW1 HnInV]; try (apply Resources.St.diff_spec; split; auto).
               apply Stock.union_spec; left.
               apply consistency_V_W with (r := r) in HfT1 as [_ HInV1]; auto;
               try (now rewrite <- Hnew).
               apply RE.valid_in_spec with (lb := V1⁺) in HInV1; auto.
               rewrite <- (Resource.shift_valid_refl (V1⁺) (V2⁺ - V1⁺) r); auto.
               now apply Stock.shift_in_iff.
             * destruct (HInW' r) as [HInW1 HnInV]; try (apply Resources.St.diff_spec; split; auto).
               apply Stock.union_spec; now right.
          ++ apply Resources.St.diff_spec in H as [HIn HnIn]. 
             apply Resources.St.union_notin_spec in HnIn as [HnInR1 HnInR2].
             apply Resources.St.union_spec in HIn as [HInR1' | HInR2'].
             * destruct (HInW r) as [HInW1 HnInV]; 
               try (apply Resources.St.diff_spec; split; auto); assumption.
             * intro HInV. apply functional_preserves_keys with (r := r) in HfT1; auto;
               try (now rewrite <- Hnew). revert HfT1.
               apply (HInW' r); apply Resources.St.diff_spec; split; assumption.
          ++ intros r HIn; apply Resources.St.union_spec in HIn as [HInR1' | HInR2']; auto.
             apply Husd1 in HInR1' as HI; destruct HI as [v HfV1].

             assert (HI : (r ∉ R2')%s /\ r ∈ V1). 
             { 
              split. 
              - intro. symmetry in HEmp'; apply Resources.St.empty_is_empty_2 in HEmp'; 
                apply (HEmp' r); rewrite Resources.St.inter_spec; split; auto.
              - apply RE.in_find. intro c; rewrite HfV1 in c; inversion c.
             }
             destruct HI as [HnInR2' HInV1].
             apply (RE.valid_in_spec _ r V1) in HvV1; auto.
             apply (RE.shift_find_iff (V1⁺) (V2⁺ - V1⁺)) in HfV1 as HfshV1.
             simpl in *. rewrite Resource.shift_valid_refl in HfshV1; auto.
             rewrite Hlcl2 in HfshV1; auto. now exists <[[⧐ {V1 ⁺} – {V2 ⁺ - V1 ⁺}] v]>.
          ++ rewrite <- Hnew'. rewrite <- Hnew''. 
             apply wt_comp with (R1 := R1') (R2 := R2') (τ := τ); auto; try reflexivity.
             apply weakening_ℜ; auto. apply (wf_env_fT_valid Re' V1 Hwf').
          ++ rewrite <- Hnew'. rewrite <- Hnew''. apply halts_comp; split; auto.
             apply halts_weakening; auto. now apply RC.Ext.new_key_Submap_spec.
          ++ apply Stock.halts_union_spec; split; auto.
             rewrite <- (wf_env_fT_new Re'' V2); auto.
             rewrite <- (wf_env_fT_new Re' V1); auto.
             apply Stock.halts_weakening; auto.
             now apply RC.Ext.new_key_Submap_spec.
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
    -- intros r' HIn; rewrite Resources.St.singleton_spec in HIn; subst; now exists v.
    -- intros r' [HnIn HIn]; apply Resources.St.singleton_notin_spec in HnIn.
        rewrite RE.add_neq_o; auto. 
        rewrite RE.Ext.new_key_add_in_spec.
        + replace (V⁺ - V⁺) with 0 by lia; now rewrite RE.shift_zero_refl.
        + exists (⩽ v … ⩾); now apply RE.find_2.
    -- exists Re; exists \{{r}}; split; try reflexivity; auto; 
       repeat (split; try now auto).
       + intros. rewrite (wf_env_fT_in Re V) in H; auto.
         rewrite RE.OP.P.add_in_iff; now right.
       + intros HIn. apply RE.OP.P.add_in_iff in HIn as [Heq | HIn]; subst.
         ++ exists (α,β). now apply RC.OP.P.find_2.
         ++ now rewrite (wf_env_fT_in Re V).
       + apply RE.valid_find_spec with (lb := V⁺) in HfV as Hv; auto.
         destruct Hv as [Hvr Hvv].
         rewrite RE.Ext.new_key_add_in_spec.
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
       + rename H into HIn; apply Resources.St.diff_spec in HIn as [HIn HnIn]; contradiction.
       + rename H into HIn; apply Resources.St.diff_spec in HIn as [HIn HnIn]; contradiction.
       + intros r' HIn; apply Resources.St.singleton_spec in HIn; subst; unfold RE.used.
         exists st; now apply RE.add_eq_o.
       + apply wf_env_fT_well_typed with (V := V) (v := ⩽ v … ⩾) in HfRe; try assumption.
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
    apply weakening_ℜ  
    with (Re1 := (⌈ S (Re ⁺) ⤆ (τ, <[ 𝟙 ]>) ⌉ (⌈ Re ⁺ ⤆ (<[ 𝟙 ]>, τ) ⌉ Re))%rc) in Hwsv as Hwsv';
    try (now apply RC.Ext.new_key_Submap_add_spec); auto.
    rewrite RC.new_key_wh_spec in *. replace (S (S (Re⁺)) - Re⁺)%rc with 2 in * by lia.

    apply IHfT 
    with (Re := (⌈ S (Re⁺) ⤆ (τ, <[ 𝟙 ]>) ⌉ (⌈ Re⁺ ⤆ (<[ 𝟙 ]>, τ) ⌉ Re))%rc) 
         (R := R') (τ' := β) in Hwt as IH;
    auto; try (now rewrite <- Hnew); clear IHfT.
    -- destruct IH as [Hunsd [Hlcl [Re1 [R1 [HSubRe1 [HSubR [Hwf' 
                      [HwtW [HInW  [Husd [Hwst' [Hwt' [Hlt' [Hlst' [HlV1 HlW]]]]]]]]]]]]]]].
       repeat split.

       + intros r HIn; rewrite Heq in HIn. apply Resources.St.diff_spec in HIn as [HInR' HnIn].
         repeat rewrite Resources.St.add_notin_spec in HnIn; destruct HnIn as [Hneq [Hneq' _]].
         apply Hunsd in HInR' as HI; destruct HI as [v HfV]; rewrite Hnew in *.
         rewrite RE.add_neq_o in HfV; auto. rewrite RE.add_neq_o in HfV; auto.
         replace r with ([⧐ V⁺ – 2] r)%r in HfV.
         ++ apply RE.shift_find_e_spec in HfV as HE. destruct HE as [v' Heq''].
            destruct v'; simpl in Heq''; inversion Heq''; subst; clear Heq''.
            exists λ. eapply RE.shift_find_iff; eauto.
         ++ apply Resource.shift_valid_refl. eapply RE.valid_in_spec; eauto.
            rewrite <- (wf_env_fT_in Re V); auto.
            destruct Hlt as [t1 [HmeT Hvt1]]; destruct Hli as [i1 [HmeT' Hvi1]].
            rewrite <- Hnew in *. 
            apply multi_preserves_typing with (t' := <[wormhole(i1;t1)]>) in Hwsf; auto.
            * apply typing_Re_R with (r := r) in Hwsf; auto. rewrite Heq.
              rewrite Resources.St.diff_spec; split; auto.
              rewrite Resources.St.add_notin_spec; split; auto.
              rewrite Resources.St.add_notin_spec; split; auto; intro c; inversion c.
            * eapply multi_trans with (y := <[wormhole( i1; t)]>).
              ** now apply multi_wh1.
              ** now apply multi_wh2.
       + intros r [HInR HInV]. rewrite RE.new_key_wh_spec in *; rewrite <- Hlcl.
         ++ symmetry. repeat rewrite RE.shift_add_spec; simpl. 
            rewrite RE.add_neq_o.
            * rewrite RE.shift_add_spec; simpl.
              rewrite RE.add_neq_o.
              ** replace (S (S (V⁺))) with ((V⁺) + 2) by lia. rewrite <- RE.shift_unfold.
              replace (2 + (V1⁺ - (V⁺ + 2))) with (V1⁺ - V⁺); auto.
              apply functional_preserves_valid in fT; 
              try (rewrite RE.new_key_wh_spec in *); try lia.
              { 
                apply RE.valid_wh_spec_1; auto; try constructor.
                red; simpl. apply well_typed_implies_valid in Hwi as [Hwi _]; auto.
                now rewrite <- Hnew.
              }
              {
                replace (S (S (V ⁺))) with ((V⁺) + 2) by lia.
                apply Term.shift_preserves_valid_1. rewrite <- Hnew.
                apply well_typed_implies_valid in Hwsv as [Hvst _]; auto.
              }
              { 
                apply well_typed_implies_valid in Hwt as [Hwt _]; auto; 
                try (rewrite RC.new_key_wh_spec in *).
                - now rewrite <- Hnew. 
                - apply RC.valid_wh_spec; auto; split; simpl; try (constructor);
                  apply well_typed_implies_valid in Hwi as [Hwi Hvτ]; auto.
              }
              ** intro c; subst; revert HInV. apply RE.Ext.new_key_notin_spec.
                  unfold Resource.shift.
                  replace (Resource.leb (S (S (V⁺))) (V⁺)) with false; auto.
                  symmetry; rewrite Resource.leb_nle; lia.
            * intro c; subst; revert HInV. apply RE.Ext.new_key_notin_spec.
              unfold Resource.shift.
              replace (Resource.leb (S (S (V⁺))) (S (V⁺))) with false; auto.
              symmetry; rewrite Resource.leb_nle; lia.
         ++ split.
            * rewrite Heq in HInR; 
              apply Resources.St.diff_notin_spec in HInR as [HnIn | HIn]; auto.
              apply Resources.St.add_spec in HIn as [Heq' | HIn]; subst.
              ** rewrite Hnew in HInV. apply RE.Ext.new_key_notin_spec in HInV; auto.
              ** apply Resources.St.add_spec in HIn as [Heq' | HIn]; subst.
                 { rewrite Hnew in HInV. apply RE.Ext.new_key_notin_spec in HInV; auto. }
                 { inversion HIn. }
            * repeat (rewrite RE.add_in_iff; right). 
              apply RE.valid_in_spec with (x := r) in HvV as Hvr; auto.
              rewrite <- (Resource.shift_valid_refl (V⁺) 2 r); auto.
              now apply RE.shift_in_iff.
       + exists Re1; exists R1; split.
         ++ apply RC.Ext.Submap_Add_spec with (m := (⌈ Re⁺ ⤆ (<[ 𝟙 ]>, τ) ⌉ Re)%rc)
                                              (x := S (Re⁺)%rc) (v := (τ, <[ 𝟙 ]>)) in HSubRe1; auto.
            * apply RC.Submap_Add_spec with
                (m := Re) (x := (Re⁺)%rc) (e := (<[ 𝟙 ]>, τ)) in HSubRe1; auto.
              ** apply RC.Ext.new_key_notin_spec; auto.
              ** unfold RC.Add;  reflexivity.
            * intro c. rewrite RC.add_in_iff in c; destruct c; try lia.
              revert H; apply RC.Ext.new_key_notin_spec; lia.
            * unfold RC.Add; reflexivity.
         ++ repeat (split; try now auto).
            * rewrite Heq; intro r. intros HIn.
              apply Resources.St.diff_spec in HIn as [HIn _]. now apply HSubR.   
            * intros r v τ1 τ' HfW HfRe1. unfold Stock.find,Stock.add in *; simpl in *.
              rewrite ReadStock.add_o in HfW; auto. destruct (Resource.eq_dec (V⁺) r); subst.
              ** inversion HfW; subst; clear HfW. rewrite <- Hnew.
                 apply wf_env_fT_new in Hwf' as Hnew'; rewrite <- Hnew'.
                 apply weakening_ℜ; auto.
                 { 
                  apply (RC.Submap_Add_spec Re (⌈Re⁺ ⤆ (<[𝟙]>, τ) ⌉ Re)%rc Re1
                                            (Re⁺)%rc (<[𝟙]>, τ)); try (now unfold RC.Add). 
                  - apply (RC.Submap_Add_spec (⌈Re⁺ ⤆ (<[𝟙]>, τ) ⌉ Re)%rc
                                              (⌈S(Re⁺) ⤆ (τ, <[𝟙]>)⌉ (⌈Re⁺ ⤆ (<[𝟙]>, τ) ⌉ Re))%rc
                                              Re1
                                              (S (Re⁺)%rc) (τ, <[𝟙]>)); try (now unfold RC.Add).
                    -- apply RC.Ext.new_key_notin_spec. 
                       rewrite RC.Ext.new_key_add_ge_spec; auto.
                       apply RC.Ext.new_key_notin_spec. lia.
                  - apply RC.Ext.new_key_notin_spec; lia. 
                 }
                 {
                  apply (RC.Ext.Submap_find_spec _ _ (Re⁺)%rc (<[𝟙]>,τ)) in HSubRe1 as HfRe.
                  - rewrite Hnew in HfRe; rewrite HfRe1 in HfRe; inversion HfRe; now subst.
                  - rewrite RC.add_neq_o; try lia; rewrite RC.add_eq_o; auto.
                 }
              ** apply (HwtW r _ τ1 τ'); auto.
            * apply Resources.St.diff_spec in H as [HInR1 HnInR]. rewrite Heq in HnInR.
              apply Resources.St.diff_notin_spec in HnInR as [HnInR' | HIn].
              ** destruct (HInW r); try (now apply Resources.St.diff_spec).
                 apply Stock.add_spec; right; right; assumption.
              ** rewrite <- Hnew.
                 repeat rewrite Resources.St.add_spec in HIn. 
                 destruct HIn as [Heq' | [Heq' | HIn]]; try (now inversion HIn); subst;
                 unfold Stock.In; simpl.
                 { left; apply ReadStock.add_in_iff; now left. }
                 { right; apply Resources.St.add_spec; now left. }
            * apply Resources.St.diff_spec in H as [HInR1 HnInR]. rewrite Heq in HnInR.
              apply Resources.St.diff_notin_spec in HnInR as [HnInR' | HIn].
              ** destruct (HInW r) as [_ HInsV]; try (apply Resources.St.diff_spec; now split).
                 intro HInV; apply HInsV. repeat (rewrite RE.add_in_iff; right).
                 apply RE.valid_in_spec with (lb := V⁺) in HInV as Hvr; auto.
                 rewrite (RE.shift_in_iff (V⁺) 2) in HInV. 
                 now rewrite Resource.shift_valid_refl in HInV.
              ** rewrite Hnew in HIn. repeat rewrite Resources.St.add_spec in HIn;
                 destruct HIn as [Heq' | [Heq' | HIn]]; try (inversion HIn); subst;
                 apply RE.Ext.new_key_notin_spec; auto.
            * apply Stock.halts_add_spec; split; auto.
              rewrite <- (wf_env_fT_new Re V); auto.
              rewrite <- (wf_env_fT_new Re1 V1); auto.
              apply halts_weakening; auto.
              apply RC.Ext.new_key_Submap_spec.
              transitivity (⌈ S (Re⁺) ⤆ (τ, <[ 𝟙 ]>) ⌉ (⌈ Re⁺ ⤆ (<[ 𝟙 ]>, τ) ⌉ Re))%rc.
              ** apply RC.Ext.Submap_add_spec_1.
                 { 
                  apply RC.Ext.new_key_notin_spec.
                  rewrite RC.Ext.new_key_add_ge_spec; auto.
                  apply RC.Ext.new_key_notin_spec; lia.
                 }
                 {
                  apply RC.Ext.Submap_add_spec_1; try reflexivity.
                  apply RC.Ext.new_key_notin_spec; lia.
                 } 
              ** assumption.
    -- now rewrite RC.new_key_wh_spec.
    -- rewrite RC.new_key_wh_spec; replace (S (S (Re⁺)%rc)) with ((Re⁺)%rc + 2) by lia.
       rewrite <- Hnew. apply halts_weakening_1; auto.
    -- rewrite RC.new_key_wh_spec. apply RE.halts_add_spec; split.
       + simpl; exists <[unit]>; split; auto. apply rt1n_refl.
       + apply RE.halts_add_spec; split.
         ++ replace (S (S (Re⁺)%rc)) with ((Re⁺)%rc + 2) by lia.
            rewrite <- Hnew. apply halts_weakening_1; auto.
         ++ rewrite <- Hnew. replace (S (S (Re⁺)%rc)) with ((Re⁺)%rc + 2) by lia.
            apply RE.halts_weakening_1; auto.
    -- apply well_typed_implies_valid in Hwi as Hv; auto.
       destruct Hv as [Hvi Hvτ]; auto.
       apply wfFT_env_wh; auto.
Qed.

Corollary functional_preserves_wf_env_fT (Re : ℜ) (V V1 : 𝐕) (W : 𝐖) (sv sv' sf sf' : Λ) 
                                                                      (τ τ' : Τ) (R : resources):

  (* (1) *) halts (Re⁺)%rc sf -> (* (2) *) halts (Re⁺)%rc sv -> (* (3) *) RE.halts (Re⁺)%rc V -> 

  (* (4) *)  Wfᵣₜ(Re,V) ->
  (* (5) *)  ∅%vc ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) -> 
  (* (6) *)  ∅%vc ⋅ Re ⊫ sv ∈ τ -> 
  (* (7) *)  ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ -> 

  exists Re1, Wfᵣₜ(Re1,V1).
Proof.
  intros Hlsf Hlsv HlV Hwf Hwt Hwst HfT.
  eapply functional_preserves_typing_gen in HfT; eauto.
  destruct HfT as [_ [_ [Re1 [_ [_  [_ [Hwf1 _]]]]]]]; now exists Re1.
Qed.

Corollary functional_preserves_stream_typing (Re : ℜ) (V V1 : 𝐕) (W : 𝐖) 
                                                  (sv sv' sf sf' : Λ) (τ τ' : Τ) (R : resources): 

  (* (1) *) halts (Re⁺)%rc sf -> (* (2) *) halts (Re⁺)%rc sv -> (* (3) *) RE.halts (Re⁺)%rc V -> 

  (* (2) *)  Wfᵣₜ(Re,V) ->
  (* (3) *)  ∅%vc ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) -> 
  (* (4) *)  ∅%vc ⋅ Re ⊫ sv ∈ τ -> 
  (* (5) *)  ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ -> 

  exists Re1, ∅%vc ⋅ Re1 ⊫ sv' ∈ τ'.
Proof.
  intros Hlsf Hlsv HlV Hwf Hwt Hwst HfT.
  eapply functional_preserves_typing_gen in HfT; eauto.
  destruct HfT as [_ [_ [Re1 [_ [_ [_  [_ [Hwf' [_ [_ [Hwsv' _]]]]]]]]]]];
  now exists Re1.
Qed.

Corollary functional_preserves_halting (Re : ℜ) (V V1 : 𝐕) (W : 𝐖) 
                                                  (sv sv' sf sf' : Λ) (τ τ' : Τ) (R : resources): 

  (* (1) *) halts (Re⁺)%rc sf -> (* (2) *) halts (Re⁺)%rc sv -> (* (3) *) RE.halts (Re⁺)%rc V -> 

  (* (2) *)  Wfᵣₜ(Re,V) ->
  (* (3) *)  ∅%vc ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) -> 
  (* (4) *)  ∅%vc ⋅ Re ⊫ sv ∈ τ -> 
  (* (5) *)  ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ -> 

  exists Re1, 
  (* (6) *) halts (Re1⁺)%rc sf' /\ 
  (* (7) *) halts (Re1⁺)%rc sv' /\ 
  (* (8) *) RE.halts (Re1⁺)%rc V1 /\
  (* (9) *) Stock.halts (Re1⁺)%rc W.
Proof.
  intros Hlsf Hlsv HlV Hwf Hwt Hwst HfT.
  eapply functional_preserves_typing_gen in HfT; eauto.
  destruct HfT as [_ [_ [Re1 [_ [_ [_  [_ [_ [_ [_ [_ [_ 
                  [Hlsf' [Hlsv' [HlV1 HlW]]]]]]]]]]]]]]];
  now exists Re1.
Qed.

Corollary functional_preserves_typing (Re : ℜ) (V V1 : 𝐕) (W : 𝐖) (sv sv' sf sf' : Λ) 
                                                                   (τ τ' : Τ) (R : resources):

  (* (1) *) halts (Re⁺)%rc sf -> (* (2) *) halts (Re⁺)%rc sv -> (* (3) *) RE.halts (Re⁺)%rc V -> 

  (* (4) *)  Wfᵣₜ(Re,V) ->
  (* (5) *)  ∅%vc ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) ->
  (* (6) *)  ∅%vc ⋅ Re ⊫ sv ∈ τ -> 
  (* (7) *)  ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ -> 

  exists (Re1 : ℜ) (R' : resources), 
    (*  (8) *) (Re ⊆ Re1)%rc /\  
    (*  (9) *) (R ⊆ R')%s /\ 
    (* (10) *) Wfᵣₜ(Re1,V1) /\ 
    (* (11) *) ∅%vc ⋅ Re1 ⊫ sv' ∈ τ' /\
    (* (12) *) ∅%vc ⋅ Re1 ⊫ sf' ∈ (τ ⟿ τ' ∣ R').
Proof.
  intros Hlsf Hlsv HlV Hwf Hwt Hwst HfT.
  eapply functional_preserves_typing_gen in HfT; eauto.
  destruct HfT as [_ [_ [Re1 [R' [HSubRe  [HSubR' [Hwf' [_ [_ [_ [Hwsv' [Hwsf' _]]]]]]]]]]]];
  exists Re1; now exists R'.
Qed.

End safety.