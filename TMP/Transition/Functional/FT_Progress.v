From Coq Require Import Program Lia Relations.Relation_Definitions Classes.RelationClasses PeanoNat
                        Classical_Prop Classical_Pred_Type Bool.Bool Lists.List Classes.Morphisms
                        Relations.Relation_Operators.
From Mecha Require Import Resource Term Typ Var ReadStock Typing VContext RContext 
                          Cell REnvironment Stock ET_Definition ET_Props ET_Preservation 
                          FT_Definition FT_Props FT_Preservation Resources.
Import ResourceNotations TermNotations TypNotations CellNotations
       VContextNotations RContextNotations REnvironmentNotations
       ReadStockNotations ResourcesNotations SetNotations StockNotations.
       
Module RC := RContext.
Module RE := REnvironment.

(** * Transition - Functional - Progress *)

Section progress.

Open Scope renvironment_scope.

Hypothesis all_arrow_halting : forall Re t α β,
  ∅%vc ⋅ Re ⊫ arr(t) ∈ (α ⟿ β ∣ ∅%s) -> forall v, ∅%vc ⋅ Re ⊫ v ∈ α -> halts (Re⁺)%rc <[t v]>.

Hint Resolve VContext.valid_empty_spec Stock.valid_empty_spec Resources.valid_empty_spec : core.


Theorem progress_of_functional_value_gen (Re : ℜ) (m n : list nat) (V : 𝐕) (tv sf : Λ) (τ τ' : Τ) (R : resources) :
  (* (1) *) value(sf) -> (* (2) *) halts (Re⁺)%rc tv -> (* (3) *) RE.halts (Re⁺)%rc V -> 

  (* (4) *) ∅%vc ⋅ Re ⊫ [⧐⧐ m – n] sf ∈ (τ ⟿ τ' ∣ R) ->
  (* (5) *) ∅%vc ⋅ Re ⊫ tv ∈ τ ->
  (* (6) *) Wfᵣₜ(Re,V) ->
  (* (7) *)(forall (r : resource), (r ∈ R)%s -> RE.unused r V) ->

  exists (V1 : 𝐕) (tv' sf' : Λ) (W : 𝐖),
    ⪡ V ; tv ; [⧐⧐ m – n] sf ⪢ ⭆ ⪡ V1 ; tv' ; sf' ; W ⪢.
Proof.
  revert Re m n V tv τ τ' R; induction sf;
  intros Re m n V tv τ1 τ1' R Hvalsf Hltv HlV Hwsf Hwtv Hwf Hunsd;
  inversion Hvalsf; subst.
  
  - rewrite Term.multi_shift_abs in *. inversion Hwsf; subst.
  - rewrite Term.multi_shift_pair in *. inversion Hwsf; subst.
 
  - rewrite Term.multi_shift_arr in *. inversion Hwsf; subst.
    exists V; exists <[([⧐⧐ m – n] sf) tv]>; 
    exists <[arr([⧐⧐ m – n] sf)]>; exists (∅%sk).
    simpl. now constructor.
 
  - rewrite Term.multi_shift_first in *. inversion Hwsf; subst.
    destruct Hltv as [tv' [HmeT Hvtv']].
    apply multi_preserves_typing with (t' := tv') in Hwtv as Hwtv'; auto.
    -- inversion Hvtv'; subst; inversion Hwtv'; subst.
      apply (IHsf Re m n V v1 _ β R) in H9 as HfT; auto.
      + destruct HfT as [V1 [v1' [sf1 [W fT]]]].
        exists V1; exists <[⟨v1',[⧐ {V⁺} – {V1⁺ - V⁺}] v2⟩]>; 
        exists (Term.tm_first <[[⧐⧐ m – n] τ]>%ty sf1); exists W.
        apply fT_MeT_sv with (st' := <[ ⟨ v1, v2 ⟩ ]>).
        ++ rewrite <- (wf_env_fT_new Re V); auto.
        ++ simpl. now constructor.
      + inversion Hvtv'; subst; exists v1; split; auto; apply rt1n_refl.
    -- eapply wf_env_fT_valid; eauto.
  
  - rewrite Term.multi_shift_comp in *. inversion Hwsf; subst.
    apply (IHsf1 Re m n V tv τ1 τ R1) in Hwtv as HfT; auto.
    -- clear IHsf1; destruct HfT as [V1 [tv' [sf1' [W1 fT1]]]].
       apply functional_preserves_typing_gen
       with (Re := Re) (τ := τ1) (τ' := τ) (R := R1) in fT1 as Hfpt; auto.
       + destruct Hfpt as 
         [Hunsd1 [HeqVV1 [Re1 [R1' [Hsub1 [HsubR1 [Hwf1 
        [HW1 [HW1' [Husd1 [Hwtv' [Hwsf1' [Hlsf1' [Hltv' [HlV1 HlW]]]]]]]]]]]]]]].
         apply weakening_ℜ with (Re1 := Re1) in H10 as Hwsf2bis; 
         auto; try (eapply (wf_env_fT_valid Re V); now auto).
         rewrite <- Term.multi_shift_cons in Hwsf2bis.

         apply (IHsf2 Re1 (Re⁺ :: m)%rc ((Re1⁺ - Re⁺) :: n)%rc V1 tv' τ τ1' R2) in Hwtv' as HfT; auto.
         ++ destruct HfT as [V2 [tv'' [sf2' [W2 fT2]]]].
            exists V2; exists tv'';
            exists <[([⧐ {V1⁺} – {V2⁺ - V1⁺}] sf1') >>> sf2']>;
            exists (([⧐ V1⁺ – (V2⁺ - V1⁺)] W1) ∪ W2)%sk.
            eapply fT_comp; eauto.
            rewrite <- (wf_env_fT_new Re1 V1); auto.
            rewrite <- (wf_env_fT_new Re V); auto.
         ++ intros.
            clear all_arrow_halting IHsf2.
            apply typing_Re_R with (r := r) in H10 as HInRe1; auto.
            * rewrite (wf_env_fT_in Re V) in HInRe1; auto.
              assert (r ∉ ∅)%s. { intro c. inversion c. }
              assert (r ∉ R1)%s. 
              { intro HInR1. apply H0. rewrite H11. rewrite Resources.St.inter_spec; now split. }
              destruct (Hunsd r).
              ** rewrite H9. rewrite Resources.St.union_spec; now right.
              ** apply RE.valid_in_spec with (lb := V⁺) in HInRe1 as HvV.
                 { 
                  rewrite (RE.shift_find_iff (V⁺) (V1⁺ - V⁺)) in H4. 
                  rewrite Resource.shift_valid_refl in H4; auto.
                  rewrite HeqVV1 in H4; try now split. 
                  simpl in *. now exists <[[⧐ {V⁺} – {V1⁺ - V⁺}] x]>.
                 }
                 { eapply (wf_env_fT_valid Re V); auto. }
            * now apply Term.multi_shift_value_iff.
       + exists <[[⧐⧐ m – n] sf1]>; split; auto.
         ++ apply rt1n_refl. 
         ++ now apply Term.multi_shift_value_iff.
    -- intros. apply Hunsd. rewrite H9.
       rewrite Resources.St.union_spec; now left.

  - rewrite Term.multi_shift_rsf in *; inversion Hwsf; subst.
    destruct (Hunsd ([⧐⧐ m – n] r)%r) as [tr HfV].
    -- now apply Resources.St.singleton_spec.
    -- exists (⌈([⧐⧐ m – n] r)%r ⤆ ⩽ … tv ⩾ ⌉ V); exists tr; 
       exists <[rsf[([⧐⧐ m – n] r)%r]]>; exists ∅%sk.
       now constructor.

  - clear IHsf1. rewrite Term.multi_shift_wh in *; inversion Hwsf; subst. 
    apply weakening_ℜ_bis 
      with (Re1 := (⌈ S k ⤆ (τ, <[ 𝟙 ]>) ⌉ (⌈ k ⤆ (<[ 𝟙 ]>, τ) ⌉ Re))%rc) 
      (k := (Re⁺)%rc) (k' := 2) in Hwtv as Hwtv'; auto.
    -- apply (IHsf2 _ 
                    m n
                    (⌈S (V⁺) ⤆ ⩽ <[unit]> … ⩾⌉ (⌈V⁺ ⤆ ([⧐ V⁺ – 2] ⩽ ([⧐⧐ m – n] sf1) … ⩾)%cl⌉ ([⧐ V⁺ – 2] V))))
       with (τ' := τ1') (R := R')
       in Hwtv' as HfT; auto.
       + destruct HfT as [V1 [tv' [sf' [W fT]]]].
         clear IHsf2.
         exists V1; exists tv'; exists sf'; 
         exists (⌈V⁺ ~ S (V⁺) ⤆ <[[⧐ {V⁺} – {V1⁺ - V⁺}] ([⧐⧐ m – n] sf1)]>⌉ W)%sk.
         apply fT_wh. 
         rewrite (wf_env_fT_new Re V) in fT; auto.
       + unfold k in *; rewrite RC.new_key_wh_spec.
         replace (S (S (Re⁺)%rc)) with ((Re⁺)%rc + 2) by lia.
         now apply halts_weakening_1.
       + unfold k; rewrite RC.new_key_wh_spec.
         apply RE.halts_add_spec; split; simpl.
         ++ exists <[unit]>; split; auto; apply rt1n_refl.
         ++ apply RE.halts_add_spec; split; simpl.
            * exists <[ [⧐ {V⁺} – 2] [⧐⧐ m – n] sf1 ]>; split; auto.
              ** apply rt1n_refl.
              ** apply Term.shift_value_iff.
                 now apply Term.multi_shift_value_iff.
            * replace (S (S (Re⁺)%rc)) with ((Re⁺)%rc + 2) by lia.
              rewrite (wf_env_fT_new Re V) in *; auto.
              now apply RE.halts_weakening_1.
       + apply well_typed_implies_valid in H8 as Hv; auto.
         ++ destruct Hv as [Hvi Hvτ]; auto.
            apply wfFT_env_wh; auto.
         ++ eapply (wf_env_fT_valid Re V); auto.
       + intros. 
         assert (r ∈ R \/ r = (S k) \/ r = k)%s.
         {
          apply Classical_Prop.NNPP. intro c.
          apply Classical_Prop.not_or_and in c.
          destruct c.
          apply Classical_Prop.not_or_and in H3.
          destruct H3.
          apply H0. rewrite H9.
          apply Resources.St.diff_spec; split; auto.
          apply Resources.St.add_notin_spec; split; auto.
          apply Resources.St.add_notin_spec; split; auto.
          intro c; inversion c. 
         }
         destruct H0 as [HIn | [Heq | Heq]]; subst; unfold k in *.
         ++ apply typing_Re_R with (r := r) in Hwsf; auto.
            * apply Hunsd in HIn; destruct HIn.
              apply (RE.shift_find_iff (V⁺) 2) in H0.
              apply RC.valid_in_spec with (lb := (Re⁺)%rc) in Hwsf as Hvr.
              ** rewrite (wf_env_fT_new Re V) in Hvr; auto.
                 rewrite Resource.shift_valid_refl in H0; auto. simpl in *.
                 exists <[[⧐ {V ⁺} – 2] x]>.
                 rewrite RE.OP.P.add_neq_o.
                 { 
                  rewrite RE.OP.P.add_neq_o; auto.
                  unfold Resource.valid in *. lia.
                 }
                 { unfold Resource.valid in *. lia. }
              ** eapply (wf_env_fT_valid Re V); auto.
            * constructor; now apply Term.multi_shift_value_iff.
         ++ exists <[unit]>. rewrite RE.OP.P.add_eq_o; auto.
            now rewrite (wf_env_fT_new Re V).
         ++ simpl. exists <[[⧐ {V⁺} – 2] [⧐⧐ m – n] sf1]>.
            rewrite RE.OP.P.add_neq_o.
            * rewrite RE.OP.P.add_eq_o; auto.
              now rewrite (wf_env_fT_new Re V).
            *  now rewrite (wf_env_fT_new Re V).
    -- eapply wf_env_fT_valid; eauto.
    -- unfold k in *. rewrite RC.new_key_wh_spec; lia.
    -- unfold k in *. apply RC.Ext.Submap_add_spec_1.
      + apply RC.Ext.new_key_notin_spec.
        rewrite RC.Ext.new_key_add_ge_spec; auto.
        apply RC.Ext.new_key_notin_spec; lia.
      + apply RC.Ext.Submap_add_spec_1; try reflexivity.
        apply RC.Ext.new_key_notin_spec; lia.
  - rewrite Term.multi_shift_unit in *; inversion Hwsf.
  - rewrite Term.multi_shift_fix in *; inversion Hwsf.
Qed.

Theorem progress_of_functional_value (Re : ℜ) (V : 𝐕) (tv sf : Λ) (τ τ' : Τ) (R : resources) :
  (* (1) *) value(sf) -> (* (2) *) halts (Re⁺)%rc tv -> (* (3) *) RE.halts (Re⁺)%rc V -> 

  (* (4) *) ∅%vc ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) ->
  (* (5) *) ∅%vc ⋅ Re ⊫ tv ∈ τ ->
  (* (6) *) Wfᵣₜ(Re,V) ->
  (* (7) *)(forall (r : resource), (r ∈ R)%s -> RE.unused r V) ->

  exists (V1 : 𝐕) (tv' sf' : Λ) (W : 𝐖),
    ⪡ V ; tv ; sf ⪢ ⭆ ⪡ V1 ; tv' ; sf' ; W ⪢.
Proof.
  intros. rewrite <- (Term.multi_shift_nil sf) in H2.
  eapply progress_of_functional_value_gen in H3; eauto.
  destruct H3 as [V1 [tv' [sf' [W fT]]]].
  rewrite (Term.multi_shift_nil sf) in *.
  now exists V1; exists tv'; exists sf'; exists W.
Qed.

Theorem progress_of_functional(Re : ℜ) (V : 𝐕) (tv t : Λ) (τ τ' : Τ) (R : resources) :

  (* (1) *) halts (Re⁺)%rc  t -> (* (2) *) halts (Re⁺)%rc tv -> (* (3) *) RE.halts (Re⁺)%rc V ->

  (* (4) *) ∅%vc ⋅ Re ⊫ t ∈ (τ ⟿ τ' ∣ R) -> (* (5) *) ∅%vc ⋅ Re ⊫ tv ∈ τ ->

  (* (6) *) Wfᵣₜ(Re,V) -> (* (7) *) (forall (r : resource), (r ∈ R)%s -> RE.unused r V) ->

  (*-------------------------------------------------------------------------------------------------*)
    (exists (V1 : 𝐕) (tv' t' : Λ) (W : 𝐖), 
        (*  (8) *) ⪡ V ; tv ; t ⪢ ⭆ ⪡ V1 ; tv' ; t' ; W ⪢ /\
        (*  (9) *) halts (V1⁺) t' /\ (* (10) *) halts (V1⁺) tv'/\ (* (11) *) RE.halts (V1⁺) V1).
Proof. 
  intros Hlt; destruct Hlt as [t' [HmeT Hvt']]. apply multi_indexed in HmeT as [k HieT].
  revert Re V tv t τ τ' R t' HieT Hvt'. induction k; 
  intros Re V tv t τ τ' R t' HieT Hvt' Hltv HltV Hwt Hwtv Hwf Hunsd.
  (* sf is a value *)
  - inversion HieT; subst. 
    apply (progress_of_functional_value _ _ tv t' τ τ' R) in Hwf as HfT; try assumption.
    destruct HfT as [V1 [tv' [t'' [W fT]]]].
    eapply functional_preserves_typing_gen in fT as HfT; eauto.
    -- destruct HfT as [_ [_ [Re1 [R' [_ [_ [Hwf1 [_ [_ [_ [_ 
                       [_ [Ht'' [Hltv' [HlV' HlW]]]]]]]]]]]]]]].
       rewrite (wf_env_fT_new Re1 V1) in *; auto.  
       exists V1; exists tv'; exists t''; exists W; repeat split; auto.
    -- exists t'; split; auto; apply rt1n_refl.
  (* sf can be reduced at least one time *)
  - inversion HieT; subst.

    (* clean *)
    clear HieT; rename y into t1; rename H0 into HeT; rename H2 into HieT.
    move t1 before t; move t' before t.
    (* clean *)

    apply evaluate_preserves_typing with (t' := t1) in Hwt as Hwt1; auto.
    eapply IHk in HieT as IH; eauto; clear IHk.
    destruct IH as [V1 [tv' [t1' [W [HfT [Hlt1' [Hltv' HltV']]]]]]].
    -- exists V1; exists tv'; exists t1'; exists W; split; auto; eapply fT_eT_sf; eauto.
       now rewrite <- (wf_env_fT_new Re V).
    -- eapply (wf_env_fT_valid Re V); auto.
Qed.

End progress.