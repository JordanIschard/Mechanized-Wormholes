From Coq Require Import Program Lia Relations.Relation_Definitions Classes.RelationClasses PeanoNat
                        Classical_Prop Classical_Pred_Type Bool.Bool Lists.List Classes.Morphisms.
From Mecha Require Import Resource Resources Term Typ Var ReadStock WriteStock Typing VContext RContext 
                          Cell REnvironment Stock ET_Definition ET_Props ET_Preservation 
                          FT_Definition FT_Props FT_Preservation.

Module RC := RContext.
Module RE := REnvironment.

Section progress.

Hypothesis all_arrow_halting : forall Re t α β,
  ∅ᵥᵪ ⋅ Re ⊫ arr(t) ∈ (α ⟿ β ∣ ∅ᵣₛ) -> forall v, ∅ᵥᵪ ⋅ Re ⊫ v ∈ α -> halts (Re⁺ᵣᵪ) <[t v]>.

Hint Resolve VContext.valid_empty_spec Stock.valid_empty_spec WriteStock.valid_empty_spec : core.

Fixpoint test (t : Λ) : nat :=
  match t with
    | Term.tm_app t1 t2 => (test t1) + (test t2) 
    | Term.tm_abs x τ t1 => (test t1)
    | Term.tm_pair t1 t2 => (test t1) + (test t2) 
    | Term.tm_fst t1 => (test t1)
    | Term.tm_snd t1 => (test t1)
    | Term.tm_first τ t1 => (test t1)
    | Term.tm_comp t1 t2 => (test t1) + (test t2) 
    | Term.tm_wh t1 t2 => (test t1) + S (S (test t2))
    | _ => 0
  end.


Theorem progress_of_functional_value (Re : ℜ) (V : 𝓥) (tv sf : Λ) (τ τ' : Τ) (R : resources) :
  (* (1) *) value(sf) -> (* (2) *) halts (Re⁺ᵣᵪ) tv -> (* (3) *) RE.halts (Re⁺ᵣᵪ) V -> 

  (* (4) *) ∅ᵥᵪ ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) ->
  (* (5) *) ∅ᵥᵪ ⋅ Re ⊫ tv ∈ τ ->

  (* (6) *) Wfᵣₜ(Re,V) ->
  (* (7) *)(forall (r : resource), (r ∈ R)%rs -> RE.unused r V) ->

(* k  k'  k <= V+ k ⊢ tv /\ sf    *)
  exists (V1 : 𝓥) (tv' sf' : Λ) (W : 𝐖),
    ⪡ V ; tv ; sf ⪢ ⭆ ⪡ V1 ; tv' ; sf' ; W ⪢.
Proof.
  (***
  définir un nombre de wh rencontré depuis le début.
  *)
 revert Re V tv τ τ' R; induction sf; 
 intros Re V tv τ1 τ1' R Hvsf Hltv HlV Hwsf Hwtv Hwf Hunsd; inversion Hvsf; inversion Hwsf; subst.
 
 - exists V; exists <[sf tv]>; exists <[arr(sf)]>; exists (∅ₛₖ). now constructor.
 
 - destruct Hltv as [tv' [HmeT Hvtv']].
   apply multi_preserves_typing with (t' := tv') in Hwtv as Hwtv'; auto.
   -- inversion Hvtv'; subst; inversion Hwtv'; subst.
      apply (IHsf Re V v1 _ τ3 R) in H8 as HfT; auto.
      + destruct HfT as [V1 [v1' [sf1 [W fT]]]].
        exists V1; exists <[⟨v1',[⧐ₜₘ {V⁺ᵣᵦ} ≤ {V1⁺ᵣᵦ - V⁺ᵣᵦ}] v2⟩]>; exists <[first(τ:sf1)]>; exists W.
        apply fT_MeT_sv with (st' := <[ ⟨ v1, v2 ⟩ ]>).
        ++ rewrite <- (wf_env_fT_new Re V); auto.
        ++ now constructor.
      + inversion Hvtv'; subst; exists v1; now split.
   -- eapply wf_env_fT_valid; eauto.
  
  - admit.
  - destruct (Hunsd r) as [tr HfV].
    -- now apply Resources.singleton_spec.
    -- exists (⌈ r ⤆ ⩽ … tv ⩾ ⌉ᵣᵦ V); exists tr; exists <[rsf[r]]>; exists (∅ₛₖ).
       now constructor.

  - clear IHsf1. 
    apply weakening_ℜ_bis 
    with (Re1 := (⌈ S k ⤆ (τ, <[ 𝟙 ]>) ⌉ᵣᵪ (⌈ k ⤆ (<[ 𝟙 ]>, τ) ⌉ᵣᵪ Re))) 
    (k := Re⁺ᵣᵪ) (k' := 2) in Hwtv as Hwtv'; auto.
    -- apply (IHsf2 _ (⌈S (V⁺ᵣᵦ) ⤆ ⩽ <[unit]> … ⩾⌉ᵣᵦ (⌈V⁺ᵣᵦ ⤆ [⧐ᵣₓ V⁺ᵣᵦ ≤ 2] ⩽ sf1 … ⩾⌉ᵣᵦ ([⧐ᵣᵦ V⁺ᵣᵦ ≤ 2] V)))
                    _ _ τ1' R') in Hwtv' as HfT; auto.
       + destruct HfT as [V1 [tv' [sf' [W HfT]]]].
         exists V1; exists tv'; exists sf'; exists (⌈V⁺ᵣᵦ ~ S (V⁺ᵣᵦ) ⤆ <[[⧐ₜₘ {V⁺ᵣᵦ} ≤ {V1⁺ᵣᵦ - V⁺ᵣᵦ}] sf1]>⌉ₛₖ W).
         constructor. rewrite (wf_env_fT_new Re V) in *; auto.
       + unfold k in *. rewrite RC.new_key_wh_spec.
         replace (S (S (Re ⁺ᵣᵪ))) with ((Re ⁺ᵣᵪ) + 2) by lia.
         now apply halts_weakening_1.
       + unfold k in *. rewrite RC.new_key_wh_spec.
         apply RE.halts_add_spec; split; simpl.
         ++ exists <[unit]>; now split.
         ++ apply RE.halts_add_spec; split; simpl.
            * rewrite <- (wf_env_fT_new Re V); auto.
              replace (S (S (Re ⁺ᵣᵪ))) with ((Re ⁺ᵣᵪ) + 2) by lia.
              apply halts_weakening_1. exists sf1; now split.
            * rewrite <- (wf_env_fT_new Re V); auto.
              replace (S (S (Re ⁺ᵣᵪ))) with ((Re ⁺ᵣᵪ) + 2) by lia.
              now apply RE.halts_weakening_1.
       + admit.
       + intros. unfold RE.unused. admit.
    -- eapply wf_env_fT_valid; eauto.
    -- unfold k in *. apply RC.Ext.Submap_add_spec_1.
       + apply RC.Ext.new_key_notin_spec.
         rewrite RC.Ext.new_key_add_spec_1; auto.
         apply RC.Ext.new_key_notin_spec; lia.
       + apply RC.Ext.Submap_add_spec_1; try reflexivity.
         apply RC.Ext.new_key_notin_spec; lia.
    -- unfold k in *. rewrite RC.new_key_wh_spec; lia.
Admitted.

Theorem progress_of_functional_value_gen (Re : ℜ) (m n : list nat) lb (V : 𝓥) (tv sf : Λ) (τ τ' : Τ) (R : resources) :
  (* (1) *) value(sf) -> (* (2) *) halts (Re⁺ᵣᵪ) tv -> (* (3) *) RE.halts (Re⁺ᵣᵪ) V -> 

  (* (4) *) ∅ᵥᵪ ⋅ Re ⊫ [⧐⧐ₜₘ m ≤ n] sf ∈ (τ ⟿ τ' ∣ R) ->
  (* (5) *) ∅ᵥᵪ ⋅ Re ⊫ tv ∈ τ ->
  (* (6) *) Wfᵣₜ(Re,V) ->
  (* (7) *)(forall (r : resource), (r ∈ R)%rs -> RE.unused r V) ->

  lb <= Re⁺ᵣᵪ ->
  lb ⊩ₜₘ sf ->
  exists (V1 : 𝓥) (tv' sf' : Λ) (W : 𝐖),
    ⪡ V ; tv ; [⧐⧐ₜₘ m ≤ n] sf ⪢ ⭆ ⪡ V1 ; tv' ; sf' ; W ⪢.
Proof.
  revert Re m n lb V tv τ τ' R; induction sf;
  intros Re m n lb V tv τ1 τ1' R Hvalsf Hltv HlV Hwsf Hwtv Hwf Hunsd Hle Hvsf;
  inversion Hvalsf; subst.
  
  - rewrite Term.multi_shift_abs in *. inversion Hwsf; subst.
  - rewrite Term.multi_shift_pair in *. inversion Hwsf; subst.
 
  - rewrite Term.multi_shift_arr in *. inversion Hwsf; subst.
    exists V; exists <[([⧐⧐ₜₘ m ≤ n] sf) tv]>; 
    exists <[arr([⧐⧐ₜₘ m ≤ n] sf)]>; exists (∅ₛₖ).
    simpl. now constructor.
 
  - rewrite Term.multi_shift_first in *. inversion Hwsf; subst.
    destruct Hltv as [tv' [HmeT Hvtv']].
    apply multi_preserves_typing with (t' := tv') in Hwtv as Hwtv'; auto.
    -- inversion Hvtv'; subst; inversion Hwtv'; subst.
      apply (IHsf Re m n lb V v1 _ τ2 R) in H9 as HfT; auto.
      + destruct HfT as [V1 [v1' [sf1 [W fT]]]].
        exists V1; exists <[⟨v1',[⧐ₜₘ {V⁺ᵣᵦ} ≤ {V1⁺ᵣᵦ - V⁺ᵣᵦ}] v2⟩]>; 
        exists <[first([⧐⧐ₜ m ≤ n] τ:sf1)]>; exists W.
        apply fT_MeT_sv with (st' := <[ ⟨ v1, v2 ⟩ ]>).
        ++ rewrite <- (wf_env_fT_new Re V); auto.
        ++ simpl. now constructor.
      + inversion Hvtv'; subst; exists v1; now split.
      + now inversion Hvsf.
    -- eapply wf_env_fT_valid; eauto.
  
  - rewrite Term.multi_shift_comp in *. inversion Hwsf; subst.
    apply (IHsf1 Re m n lb V tv τ1 τ R1) in Hwtv as HfT; auto.
    -- clear IHsf1; destruct HfT as [V1 [tv' [sf1' [W1 fT1]]]].
       apply functional_preserves_typing_gen
       with (Re := Re) (τ := τ1) (τ' := τ) (R := R1) in fT1 as Hfpt; auto.
       + destruct Hfpt as 
         [Hunsd1 [HeqVV1 [Re1 [R1' [Hsub1 [HsubR1 [Hwf1 [HW1 [HW1' [Husd1 [Hwtv' [Hwsf1' [Hlsf1' [Hltv' HlV1]]]]]]]]]]]]]].
         apply weakening_ℜ with (Re1 := Re1) in H10 as Hwsf2bis; 
         auto; try (eapply (wf_env_fT_valid Re V); now auto).
         rewrite <- Term.multi_shift_cons in Hwsf2bis.

         apply (IHsf2 Re1 (Re⁺ᵣᵪ :: m) ((Re1⁺ᵣᵪ - Re⁺ᵣᵪ) :: n) lb V1 tv' τ τ1' R2) in Hwtv' as HfT; auto.
         ++ destruct HfT as [V2 [tv'' [sf2' [W2 fT2]]]].
            exists V2; exists tv'';
            exists <[([⧐ₜₘ {V1⁺ᵣᵦ} ≤ {V2⁺ᵣᵦ - V1⁺ᵣᵦ}] sf1') >>> sf2']>;
            exists (([⧐ₛₖ V1⁺ᵣᵦ ≤ (V2⁺ᵣᵦ - V1⁺ᵣᵦ)] W1) ∪ W2)%sk.
            eapply fT_comp; eauto.
            rewrite <- (wf_env_fT_new Re1 V1); auto.
            rewrite <- (wf_env_fT_new Re V); auto.
         ++ intros.
            clear all_arrow_halting IHsf2 Hvsf.
            apply typing_Re_R with (r := r) in H10 as HInRe1; auto.
            * rewrite (wf_env_fT_in Re V) in HInRe1; auto.
              assert (r ∉ ∅ᵣₛ)%rs. { intro c. inversion c. }
              assert (r ∉ R1)%rs. 
              { intro HInR1. apply H0. rewrite H11. rewrite Resources.inter_spec; now split. }
              destruct (Hunsd r).
              ** rewrite H9. rewrite Resources.union_spec; now right.
              ** apply RE.valid_in_spec with (lb := V⁺ᵣᵦ) in HInRe1 as HvV.
                 { 
                  rewrite (RE.shift_find_spec (V⁺ᵣᵦ) (V1⁺ᵣᵦ - V⁺ᵣᵦ)) in H4. 
                  rewrite Resource.shift_valid_refl in H4; auto.
                  rewrite HeqVV1 in H4; try now split. 
                  simpl in *. now exists <[[⧐ₜₘ {V⁺ᵣᵦ} ≤ {V1⁺ᵣᵦ - V⁺ᵣᵦ}] x]>.
                 }
                 { eapply (wf_env_fT_valid Re V); auto. }
            * now apply Term.multi_shift_value_iff.
         ++ apply RC.Ext.new_key_Submap_spec in Hsub1. lia.
         ++ now inversion Hvsf.
       + exists <[[⧐⧐ₜₘ m ≤ n] sf1]>; split; auto.
         now apply Term.multi_shift_value_iff.
    -- intros. apply Hunsd. rewrite H9.
       rewrite Resources.union_spec; now left.
    -- now inversion Hvsf.

  - rewrite Term.multi_shift_rsf in *; inversion Hwsf; subst.
    destruct (Hunsd ([⧐⧐ᵣ m ≤ n] r)) as [tr HfV].
    -- now apply Resources.singleton_spec.
    -- exists (⌈ ([⧐⧐ᵣ m ≤ n] r) ⤆ ⩽ … tv ⩾ ⌉ᵣᵦ V); exists tr; exists <[rsf[[⧐⧐ᵣ m ≤ n] r]]>; exists (∅ₛₖ).
       now constructor.

  - clear IHsf1. rewrite Term.multi_shift_wh in *; inversion Hwsf; subst. 
    apply weakening_ℜ_bis 
      with (Re1 := (⌈ S k ⤆ (τ, <[ 𝟙 ]>) ⌉ᵣᵪ (⌈ k ⤆ (<[ 𝟙 ]>, τ) ⌉ᵣᵪ Re))) 
      (k := Re⁺ᵣᵪ) (k' := 2) in Hwtv as Hwtv'; auto.
    -- inversion Hvsf; subst.
       apply (IHsf2 _ 
                    m n (S (S lb)) 
                    (⌈S (V⁺ᵣᵦ) ⤆ ⩽ <[unit]> … ⩾⌉ᵣᵦ (⌈V⁺ᵣᵦ ⤆ [⧐ᵣₓ V⁺ᵣᵦ ≤ 2] ⩽ ([⧐⧐ₜₘ m ≤ n] sf1) … ⩾⌉ᵣᵦ ([⧐ᵣᵦ V⁺ᵣᵦ ≤ 2] V))))
       with (τ' := τ1') (R := R')
       in Hwtv' as HfT; auto.
       + destruct HfT as [V1 [tv' [sf' [W fT]]]].
         clear IHsf2.
         exists V1; exists tv'; exists sf'; 
         exists (⌈V⁺ᵣᵦ ~ S (V⁺ᵣᵦ) ⤆ <[[⧐ₜₘ {V⁺ᵣᵦ} ≤ {V1⁺ᵣᵦ - V⁺ᵣᵦ}] ([⧐⧐ₜₘ m ≤ n] sf1)]>⌉ₛₖ W).
         apply fT_wh. 
         rewrite (wf_env_fT_new Re V) in fT; auto.
       + unfold k in *; rewrite RC.new_key_wh_spec.
         replace (S (S (Re ⁺ᵣᵪ))) with ((Re ⁺ᵣᵪ) + 2) by lia.
         now apply halts_weakening_1.
       + unfold k; rewrite RC.new_key_wh_spec.
         apply RE.halts_add_spec; split; simpl.
         ++ exists <[unit]>; now split.
         ++ apply RE.halts_add_spec; split; simpl.
            * exists <[ [⧐ₜₘ {V ⁺ᵣᵦ} ≤ 2] [⧐⧐ₜₘ m ≤ n] sf1 ]>; split; auto.
              apply Term.shift_value_iff.
              now apply Term.multi_shift_value_iff.
            * replace (S (S (Re ⁺ᵣᵪ))) with ((Re ⁺ᵣᵪ) + 2) by lia.
              rewrite (wf_env_fT_new Re V) in *; auto.
              now apply RE.halts_weakening_1.
       + repeat split.
         ++ intro HIn. repeat rewrite RC.OP.P.add_in_iff in HIn.
            repeat rewrite RE.OP.P.add_in_iff.
            destruct HIn as [Heq' | [Heq' | HIn]]; subst.
            * left; f_equal; symmetry.
              now apply (wf_env_fT_new Re V).
            * right; left. symmetry; now apply (wf_env_fT_new Re V).
            * repeat right. 
              rewrite (wf_env_fT_in Re V) in HIn; auto.
              apply RE.valid_in_spec with (lb := V⁺ᵣᵦ) in HIn as Hvr; auto.
              ** rewrite <- (Resource.shift_valid_refl (V⁺ᵣᵦ) 2 r); auto.
                 now apply RE.shift_in_spec.
              ** eapply (wf_env_fT_valid Re V); auto.
         ++ intro HIn. repeat rewrite RE.OP.P.add_in_iff in HIn.
            repeat rewrite RC.OP.P.add_in_iff.
            destruct HIn as [Heq' | [Heq' | HIn]]; subst.
            * unfold k; left; f_equal; symmetry.
              now rewrite (wf_env_fT_new Re V).
            * unfold k in *; right; left. 
              symmetry; now rewrite (wf_env_fT_new Re V).
            * repeat right.
              apply RE.shift_in_e_spec in HIn as Hr'.
              destruct Hr' as [r' Heq']; subst.
              apply RE.shift_in_spec in HIn.
              apply RE.valid_in_spec with (lb := V⁺ᵣᵦ) in HIn as Hvr; auto.
              ** rewrite (Resource.shift_valid_refl (V⁺ᵣᵦ) 2 r'); auto.
                 now apply (wf_env_fT_in Re V).
              ** eapply (wf_env_fT_valid Re V); auto.
         ++ unfold k in *; rewrite RC.new_key_wh_spec. 
            apply RC.valid_wh_spec; auto.
            * eapply (wf_env_fT_valid Re V); auto.
            * split; simpl; try now constructor.
              apply well_typed_implies_valid in H8 as [_ Hwτ]; auto.
              eapply (wf_env_fT_valid Re V); auto.
            * split; simpl; try now constructor.
              apply well_typed_implies_valid in H8 as [_ Hwτ]; auto.
              eapply (wf_env_fT_valid Re V); auto.
        ++ rewrite RE.new_key_wh_spec.
            apply RE.valid_wh_spec_1; auto; try now constructor.
            unfold Cell.valid; simpl.
            apply well_typed_implies_valid in H8 as [H8 _]; auto.
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
                { rewrite RC.new_key_wh_spec; lia. }admit.
       + intros. 
         assert (r ∈ R \/ r = (S k) \/ r = k)%rs.
         {
          apply Classical_Prop.NNPP. intro c.
          apply Classical_Prop.not_or_and in c.
          destruct c.
          apply Classical_Prop.not_or_and in H3.
          destruct H3.
          apply H0. rewrite H9.
          apply Resources.diff_spec; split; auto.
          apply Resources.add_notin_spec; split; auto.
          apply Resources.add_notin_spec; split; auto.
          intro c; inversion c. 
         }
         destruct H0 as [HIn | [Heq | Heq]]; subst; unfold k in *.
         ++ apply typing_Re_R with (r := r) in Hwsf; auto.
            * admit.
            * constructor; now apply Term.multi_shift_value_iff.
         ++ exists <[unit]>. rewrite RE.OP.P.add_eq_o; auto.
            now rewrite (wf_env_fT_new Re V).
         ++ simpl. exists <[[⧐ₜₘ{V ⁺ᵣᵦ} ≤ 2] [⧐⧐ₜₘ m ≤ n] sf1]>.
            rewrite RE.OP.P.add_neq_o.
            * rewrite RE.OP.P.add_eq_o; auto.
              now rewrite (wf_env_fT_new Re V).
            *  now rewrite (wf_env_fT_new Re V).
       + unfold k in *; rewrite RC.new_key_wh_spec; lia.
    -- eapply wf_env_fT_valid; eauto.
    -- unfold k in *. apply RC.Ext.Submap_add_spec_1.
      + apply RC.Ext.new_key_notin_spec.
        rewrite RC.Ext.new_key_add_spec_1; auto.
        apply RC.Ext.new_key_notin_spec; lia.
      + apply RC.Ext.Submap_add_spec_1; try reflexivity.
        apply RC.Ext.new_key_notin_spec; lia.
    -- unfold k in *. rewrite RC.new_key_wh_spec; lia.
Admitted.

End progress.