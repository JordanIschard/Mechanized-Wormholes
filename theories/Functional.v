From Coq Require Import Program Lia Relations.Relation_Definitions Classes.RelationClasses 
                        Classical_Prop Classical_Pred_Type Bool.Bool Classes.Morphisms.
Require Import Resource Resources Term Typ Var Substitution Typing VContext RContext Evaluation
               Cell REnvironment.

(** * Transition - Functional

rsf's semantics are divided in three sub semantics:
- evaluation transition
- functional transition <--
- temporal transition

*)

Module RC := RContext.
Module RE := REnvironment.

(** *** Definition *)

Reserved Notation "⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st1 ; t1 ⪢" (at level 57, V constr, 
                                                                V1 constr, st custom rsf,
                                                                st1 custom rsf,
                                                                t custom rsf, 
                                                                t1 custom rsf, 
                                                                no associativity).
Reserved Notation "'Instᵣₜ(' Re , V )" (at level 50).

Inductive functional : 𝓥 -> Λ -> Λ -> 𝓥 -> Λ -> Λ -> Prop :=

  | fT_eT    :  forall (V V' : 𝓥) (st st' t t' t'' : Λ),

        ⊨ t ⟼ t' -> ⪡ V ; st ; t' ⪢ ⭆ ⪡ V' ; st' ; t'' ⪢ -> 
    (*-------------------------------------------------------------*)
              ⪡ V ; st ; t ⪢ ⭆ ⪡ V' ; st' ; t'' ⪢

  | fT_arr   :  forall (st t : Λ) (V : 𝓥), 

                      value(<[arr(t)]>) ->
    (*------------------------------------------------------*)
        ⪡ V ; st ; arr(t) ⪢ ⭆ ⪡ V ; (t st) ; arr(t) ⪢ 

  | fT_first :  forall (st v1 v1' v2 t t' : Λ) (τ : Τ) (V V' : 𝓥),

                            value(<[first(τ:t)]>) ->
        ⊨ st ⟼⋆ ⟨v1,v2⟩ -> ⪡ V ; v1 ; t ⪢ ⭆ ⪡ V' ; v1' ; t' ⪢ ->
    (*----------------------------------------------------------------*)
        ⪡ V ; st ; first(τ:t) ⪢ ⭆ ⪡ V' ; ⟨v1',v2⟩ ; first(τ:t') ⪢

  | fT_comp  :  forall (st st' st'' t1 t1' t2 t2' : Λ) (V V' V'' : 𝓥),

        value(<[t1 >>> t2]>) -> ⪡ V ; st ; t1 ⪢ ⭆ ⪡ V' ; st' ; t1' ⪢ ->
                 ⪡ V' ; st' ; t2 ⪢ ⭆ ⪡ V'' ; st'' ; t2' ⪢ ->
    (*----------------------------------------------------------------------*)
          ⪡ V ; st ; (t1 >>> t2) ⪢ ⭆ ⪡ V'' ; st'' ; (t1' >>> t2') ⪢

  | fT_rsf   :  forall (V : 𝓥) (st v : Λ) (r : resource),

                              V ⌈r ⩦ ⩽ v … ⩾⌉ᵣᵦ -> 
    (*------------------------------------------------------------------*)
        ⪡ V ; st ; rsf[r] ⪢ ⭆ ⪡ ⌈ r ⤆ ⩽ … st ⩾ ⌉ᵣᵦ V ; v ; rsf[r] ⪢

where "⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st1 ; t1 ⪢" := (functional V st t V1 st1 t1).


Inductive instantiation_func : ℜ -> 𝓥 -> Prop := 
  | itfT_empty  : forall (Re : ℜ) (V : 𝓥), 
                    isEmptyᵣᵪ(Re) -> isEmptyᵣᵦ(V) -> Instᵣₜ(Re,V)

  | itfT_init   : 
    forall (Re Re' : ℜ) (V V' : 𝓥) (τ τ' : Τ) (v : Λ),
      Instᵣₜ(Re,V) -> newᵣᵪ(Re) ⊩ₜ τ ->
      Addᵣᵪ (newᵣᵪ(Re)) (τ,τ') Re Re' -> 
      Addᵣᵦ (newᵣᵦ(V)) ⩽ v … ⩾ V V' -> 
      ∅ᵥᵪ ⋅ Re ⊫ v ∈ τ' -> 
      Instᵣₜ(Re',V')
  
  | itfT_update : forall (Re : ℜ) (V V' : 𝓥) r (τ τ' : Τ) (v : Λ),
                    Instᵣₜ(Re,V) -> Re ⌈r ⩦ (τ,τ')⌉ᵣᵪ -> 
                    r ∈ᵣᵦ V -> Addᵣᵦ r ((⩽ … v ⩾)) V V' -> 
                    ∅ᵥᵪ ⋅ Re ⊫ v ∈ τ -> Instᵣₜ(Re,V')

where "'Instᵣₜ(' Re , V )" := (instantiation_func Re V).

(*

(** *** Instantiation *)

Lemma instantiation_is_empty_spec : forall (Re : ℜ) (V : 𝓥),
  Instᵣₜ(Re,V) -> RC.Raw.is_empty Re = RE.Raw.is_empty V.
Proof.
  intros Re V Hinst; induction Hinst.
  - rewrite RC.is_empty_1; auto; 
    now rewrite RE.is_empty_1.
  - apply RC.notEmpty_Add_spec in H0.
    apply RE.notEmpty_Add_spec in H1.
    destruct (RC.Raw.is_empty Re') eqn:HEmp.
    -- apply RC.is_empty_2 in HEmp; contradiction.
    -- destruct (RE.Raw.is_empty V') eqn:HEmp'; auto.
        apply RE.is_empty_2 in HEmp'; contradiction.
  - apply RE.notEmpty_Add_spec in H1.
    destruct (RC.Raw.is_empty Re) eqn:HEmp.
    -- apply RC.is_empty_2 in HEmp.
        apply RC.notEmpty_find_spec in H; auto; contradiction.
    -- destruct (RE.Raw.is_empty V') eqn:HEmp'; auto.
        apply RE.is_empty_2 in HEmp'; contradiction.
Qed.

Lemma instantiation_max : forall (Re : ℜ) (V : 𝓥),
  Instᵣₜ(Re,V) -> maxᵣᵪ(Re) = maxᵣᵦ(V).
Proof.
  intros Re V inst; induction inst.
  - rewrite RC.Ext.max_key_Empty_spec; auto.
    now rewrite RE.Ext.max_key_Empty_spec.
  - apply RC.Ext.max_key_Add_spec in H0 as [[H0 H0'] | [H0 H0']]; auto.
    -- rewrite H0. 
        apply RE.Ext.max_key_Add_spec in H1 as [[H1 H1'] | [H1 H1']].
        + rewrite H1; apply instantiation_is_empty_spec in inst as HEmp.
          unfold RC.Ext.new_key,RE.Ext.new_key; rewrite HEmp.
          destruct (RE.Raw.is_empty V); auto.
        + rewrite RE.shift_max_spec in H1'; auto.
          assert (newᵣᵦ(V) >= maxᵣᵦ(V)). { apply RE.Ext.new_key_geq_max_key. }
          lia.
        + apply RE.shift_new_notin_spec; auto.
    -- unfold RC.Ext.new_key in H0'. 
        destruct (RC.Raw.is_empty Re) eqn:HEmp; try lia.
        rewrite RC.Ext.max_key_Empty_spec in H0'; try lia.
        now apply RC.is_empty_2.
    -- apply RC.Ext.new_key_notin_spec; lia.
  - unfold RE.Add in H1; rewrite H1.
    rewrite RE.Ext.max_key_add_spec_3; auto.
Qed.

Lemma instantiation_new : forall (Re : ℜ) (V : 𝓥),
Instᵣₜ(Re,V) -> newᵣᵪ(Re) = newᵣᵦ(V).
Proof.
  intros Re V Hinst; unfold RC.Ext.new_key,RE.Ext.new_key.
  apply instantiation_is_empty_spec in Hinst as HisEmp.
  destruct (RC.Raw.is_empty Re) eqn:HEmp.
  - now rewrite <- HisEmp.
  - rewrite <- HisEmp; f_equal; now apply instantiation_max.
Qed.

Lemma instantiation_domains_match: forall (Re : ℜ) V (k : resource) (πτ : πΤ),
  Instᵣₜ(Re,V) -> Re ⌈k ⩦ πτ⌉ᵣᵪ -> exists (v : 𝑣), V ⌈k ⩦ v⌉ᵣᵦ.
Proof.
  intros Re V k πτ inst; revert k πτ; induction inst; intros k' πτ' Hfin.
  - apply RC.notEmpty_find_spec in Hfin; auto; contradiction.
  - rewrite H0 in *; destruct (Resource.eq_dec (newᵣᵪ(Re)) k'); subst.
    -- exists ([⧐ᵣₓ newᵣᵦ( V) ≤ 1] ⩽ v … ⩾); rewrite H1. 
        apply instantiation_new in inst as Hnew; rewrite Hnew.
        now apply RE.add_eq_o.
    -- rewrite RC.add_neq_o in Hfin; try assumption.
        apply IHinst in Hfin as [v' Hfin]; exists ([⧐ᵣₓ (newᵣᵦ(V)) ≤ 1] v'). rewrite H1.
        rewrite RE.add_neq_o.
        + rewrite <- Resource.shift_valid_refl with (lb := newᵣᵦ(V)) (t := k') (k := 1).
          ++ now apply RE.shift_find_spec.
          ++ unfold Resource.valid; apply RE.Ext.new_key_in_spec.
            exists v'; now apply RE.find_2.
        + apply instantiation_new in inst; now rewrite <- inst.
  - destruct (Resource.eq_dec r k'); subst.
    -- exists (⩽ … v ⩾); rewrite H1; now apply RE.add_eq_o.
    -- apply IHinst in Hfin; destruct Hfin.
        exists x. rewrite H1; now rewrite RE.add_neq_o.
Qed.

#[export] 
Instance itfT_eq : Proper (RC.eq ==> RE.eq ==> iff) (instantiation_func).
Proof.
  repeat red; split; intros.
  - revert y y0 H0 H; induction H1; subst; intros y y0 Heq Heq'.
    -- apply itfT_empty; try (now rewrite <- Heq); now rewrite <- Heq'.
    -- eapply itfT_init; eauto; try (now rewrite <- Heq); now rewrite <- Heq'.
    -- eapply itfT_update; eauto.
        + eapply IHinstantiation_func; auto. reflexivity.
        + rewrite <- Heq'; eauto.
        + rewrite <- Heq; eauto.
        + now rewrite <- Heq'. 
  - revert x x0 H0 H; induction H1; subst; intros x x0 Heq Heq'.
    -- apply itfT_empty; try (now rewrite Heq'); now rewrite Heq.
    -- eapply itfT_init; eauto; try (now rewrite Heq); now rewrite Heq'.
    -- eapply itfT_update; eauto.
        + eapply IHinstantiation_func; auto; reflexivity.
        + rewrite Heq'; eauto.
        + now rewrite Heq.
        + now rewrite Heq'.
Qed.

Lemma instantiation_valid : forall (Re : ℜ) V,
  Instᵣₜ(Re,V) -> newᵣᵪ(Re) ⊩ᵣᵪ Re /\ newᵣᵦ(V) ⊩ᵣᵦ V.
Proof.
  intros Re V inst; induction inst.
  - split; try now apply RC.valid_Empty_spec.
    now apply RE.valid_Empty_spec.
  - destruct IHinst as [IH1 IH2]; apply well_typed_implies_valid in H2 as [H2 H2']; 
    auto; try (now apply VContext.valid_empty_spec); split.
    -- rewrite <- RC.valid_Add_spec; eauto;
        try (now apply RC.Ext.new_key_notin_spec; lia).
        repeat split; simpl; unfold RC.Add in *;
         apply RC.Ext.new_key_eq in H0 as Hnew; rewrite Hnew;
        rewrite RC.Ext.new_key_add_new_key_spec; try lia.
        + unfold Resource.valid; lia.
        + apply Typ.valid_weakening with (k := newᵣᵪ( Re)); auto.
        + apply Typ.valid_weakening with (k := newᵣᵪ( Re)); auto.
        + apply RC.valid_weakening with (k := newᵣᵪ( Re)); auto.
    -- rewrite <- RE.valid_Add_spec; eauto;
        try (now apply RE.shift_new_notin_spec; eauto).
        repeat split;
        unfold RE.Add in *;
        apply RE.Ext.new_key_eq in H1 as Hnew; rewrite Hnew;
        replace (⌈ newᵣᵦ( V) ⤆ [⧐ᵣₓ newᵣᵦ( V) ≤ 1] ⩽ v … ⩾ ⌉ᵣᵦ ([⧐ᵣᵦ newᵣᵦ( V) ≤ 1] V)) 
        with (⌈ newᵣᵦ([⧐ᵣᵦ newᵣᵦ( V) ≤ 1] V) ⤆ [⧐ᵣₓ newᵣᵦ( V) ≤ 1] ⩽ v … ⩾ ⌉ᵣᵦ 
                    ([⧐ᵣᵦ newᵣᵦ( V) ≤ 1] V))
        by (f_equal; rewrite RE.shift_new_spec; lia);
        rewrite RE.Ext.new_key_add_new_key_spec; 
        rewrite RE.shift_new_spec; auto.
        + unfold Resource.valid; lia.
        + replace (S (newᵣᵦ( V))) with ((newᵣᵦ( V)) + 1) by lia.
          apply Cell.shift_preserves_valid_1.
          unfold Cell.valid; simpl. apply instantiation_new in inst.
          rewrite <- inst; auto.
        + replace (S (newᵣᵦ( V))) with ((newᵣᵦ( V)) + 1) by lia.
          now apply RE.shift_preserves_valid_1.
  - destruct IHinst; split; auto; apply RE.Ext.new_key_in_spec in H0 as Hlt.
    eapply RE.Ext.new_key_add_spec_3 in H0 as H0'.
    unfold RE.Add in H1.
    rewrite H1; rewrite H0'. apply RE.valid_update_spec; auto.
    unfold Cell.valid; simpl. apply well_typed_implies_valid in H2 as [H2 H2']; auto.
    -- apply instantiation_new in inst as Hnew; now rewrite Hnew in H2.
    -- apply VContext.valid_empty_spec.
Qed.

Lemma instantiation_well_typed : forall (Re : ℜ) V (r : resource) (v : 𝑣) (πτ : πΤ),
  Instᵣₜ(Re,V) -> newᵣᵪ( Re) ⊩ᵣᵪ Re -> Re ⌈ r ⩦ πτ ⌉ᵣᵪ -> V ⌈ r ⩦ v ⌉ᵣᵦ -> 
  match (πτ,v) with
    | ((_,τ),⩽ v' … ⩾) => ∅ᵥᵪ ⋅ Re ⊫ v' ∈ τ
    | ((τ,_),⩽ … v' ⩾) => ∅ᵥᵪ ⋅ Re ⊫ v' ∈ τ
  end.
Proof.
  intros Re V r v πτ inst; revert r v πτ; induction inst;
  intros r' v' πτ' HvRe HfRe HfV; destruct πτ'.
  - apply RC.notEmpty_find_spec in HfRe; auto; contradiction.
  - rewrite H0 in HfRe; rewrite H1 in HfV.
    apply instantiation_new in inst as Hnew. 
    destruct (Resource.eq_dec (newᵣᵪ(Re)) r'); subst.
    -- rewrite Hnew in HfV. rewrite RC.add_eq_o in HfRe; auto; 
        inversion HfRe; clear HfRe; subst.
        rewrite RE.add_eq_o in HfV; auto; inversion HfV; subst; clear HfV.
        rewrite <- Hnew. replace 1 with (newᵣᵪ(Re') - newᵣᵪ(Re)).
        + apply weakening_ℜ_1; auto.
          ++ apply VContext.valid_empty_spec.
          ++ apply instantiation_valid in inst as [HvRe' _]; auto.
          ++ unfold RC.Add in H0. 
            rewrite H0. apply RC.Submap_add_spec_1.
            * apply RC.Ext.new_key_notin_spec; lia.
            * apply RC.Submap_refl.
        + unfold RC.Add in H0. 
          rewrite H0; rewrite RC.Ext.new_key_add_new_key_spec; lia.
    -- rewrite <- Hnew in HfV. rewrite RC.add_neq_o in HfRe; auto.
        rewrite RE.add_neq_o in HfV; auto.
        apply instantiation_valid in inst as [HvRe' _].
        replace r' with ([⧐ᵣ newᵣᵪ(Re) ≤ 1] r') in HfV.
        + apply RE.shift_find_e_spec in HfV as HfV';
          destruct HfV' as [v'' Heq]; subst.
          apply RE.shift_find_spec in HfV.
          eapply IHinst in HfV; eauto. simpl in HfV.
          destruct v''; simpl; replace 1 with (newᵣᵪ(Re') - newᵣᵪ(Re));
          try (apply weakening_ℜ_1); auto; try (apply VContext.valid_empty_spec);
          unfold RC.Add in H0; rewrite H0; 
          try ( rewrite RC.Ext.new_key_add_spec_1; auto; try lia ); 
          try (apply RC.Submap_add_spec_1; try apply RC.Submap_refl);
          try (apply RC.Ext.new_key_notin_spec; lia). 
        + rewrite Resource.shift_valid_refl; auto. 
          eapply RC.valid_find_spec in HfRe; eauto; destruct HfRe; auto.
  - rewrite H1 in HfV; destruct (Resource.eq_dec r r'); subst.
    -- rewrite RE.add_eq_o in HfV; auto; inversion HfV; subst; clear HfV.
        rewrite H in HfRe; inversion HfRe; subst; auto.
    -- rewrite RE.add_neq_o in HfV; auto. eapply IHinst in HfV; eauto.
        now simpl in HfV.
Qed.

Lemma instantiation_in : forall (Re : ℜ) V (r : resource),
  Instᵣₜ(Re,V) -> r ∈ᵣᵪ Re <-> r ∈ᵣᵦ V.
Proof.
  split.
  - intros; destruct H0; apply RC.find_1 in H0. 
    eapply instantiation_domains_match in H0; eauto;
    destruct H0. exists x0; now apply RE.find_2.
  - revert r; induction H.
    -- intros. unfold RE.Empty in *; exfalso.
       destruct H1. now apply (H0 r x).
    -- intros. unfold RE.Add in *. rewrite H2 in *.
       unfold RC.Add in *. rewrite H1.
       apply RE.add_in_iff in H4; destruct H4; subst.
       + apply instantiation_new in H; rewrite H.
         rewrite RC.add_in_iff; now left.
       + rewrite RC.add_in_iff; right; apply IHinstantiation_func.
         rewrite <- RE.valid_in_spec_1; eauto. apply instantiation_valid in H.
         now destruct H.
    -- intros. unfold RE.Add in *. rewrite H2 in *. 
       apply IHinstantiation_func. rewrite RE.add_in_iff in H4.
       destruct H4; subst; auto.
Qed.

(** ** Preservation *)

Hint Resolve VContext.valid_empty_spec Stock.valid_empty_spec : core.

(** *** Proof of preservation of validity through the functional transition 

  The concept of validity have to be consistent after a functional transition because
  typing, evaluation transition are based on.

  **** Hypothesis

  If there is a functional transition (1) with the environment (2), the stream term (3) and 
  the signal function (4) valid according to the new key of the environment;

  **** Result

  All output element of the functional transition (V',st',...) are valid according to the new
  key of the output environment (5) and the new key of the output environment is greater or equal to the
  the new key of the input environment (6).
*)
Lemma functional_preserves_valid : forall (V V' : 𝓥) (W : 𝐖) (st st' sf sf' : Λ),
  (* (1) *) ⪡ V ; st ; sf ⪢ ⭆ ⪡ V' ; st' ; sf' ; W ⪢ ->
  (* (2) *) newᵣᵦ(V) ⊩ᵣᵦ V -> 
  (* (3) *) newᵣᵦ(V) ⊩ₜₘ st -> 
  (* (4) *) newᵣᵦ(V) ⊩ₜₘ sf ->

  (* (5) *) newᵣᵦ(V') ⊩ᵣᵦ V' /\ newᵣᵦ(V') ⊩ₜₘ st' /\ newᵣᵦ(V') ⊩ₜₘ sf' /\ newᵣᵦ(V') ⊩ₛₖ W /\ 
  (* (6) *) newᵣᵦ(V) <= newᵣᵦ(V').
Proof.
  intros V V' W st st' sf sf' fT; dependent induction fT; intros HvV Hvst Hvt.
  (* fT_eT *)
  - destruct IHfT as [HvV' [Hvst' [Hvt'' [HvW Hlt]]]]; auto.
    apply evaluate_preserves_valid_term with (t := t); assumption.
  (* fT_arr *)
  - split; try assumption; split.
    -- constructor; inversion Hvt; subst; assumption.
    -- split; auto; split; try lia. 
  (* fT_first *)
  - destruct IHfT as [HvV' [Hvst' [Hvt'' [HvW Hlt]]]]; try assumption.
    -- apply multi_preserves_valid_term with (t' := <[⟨ v1, v2 ⟩]>) in Hvst as Hvst';
        try assumption. inversion Hvst'; subst; assumption.
    -- inversion Hvt; subst; assumption.
    -- split; try assumption; split.
        + constructor; try assumption. 
          apply multi_preserves_valid_term with (t' := <[⟨ v1, v2 ⟩]>) in Hvst as Hvst2;
          try assumption. inversion Hvst2; subst.
          apply Term.shift_preserves_valid_1 
          with (lb := newᵣᵦ(V)) (k' := newᵣᵦ(V') - newᵣᵦ(V)) in H5.
          replace ((newᵣᵦ(V) + (newᵣᵦ(V') - newᵣᵦ(V)))) with (newᵣᵦ(V')) in H5; auto; lia.
        + split; constructor; try assumption. inversion Hvt; subst.
          eapply Typ.valid_weakening; eauto.
  (* fT_comp *)
  - inversion Hvt; subst; destruct IHfT1 as [HvV' [Hvst' [Hvt1' [HvW1 Hlt1]]]]; auto.
    destruct IHfT2 as [HvV'' [Hvst'' [Hvt2' [HvW2 Hlt2]]]]; try assumption.
    -- apply Term.shift_preserves_valid_1
        with (lb := newᵣᵦ(V)) (k' := newᵣᵦ(V') - newᵣᵦ(V)) in H4.
        replace ((newᵣᵦ(V) + (newᵣᵦ(V') - newᵣᵦ(V)))) with (newᵣᵦ(V')) in H4; try assumption; lia.
    -- split; try assumption; split; auto; split.
        + constructor; auto; apply Term.shift_preserves_valid_1
          with (lb := newᵣᵦ(V')) (k' := newᵣᵦ(V'') - newᵣᵦ(V')) in Hvt1'.
          replace ((newᵣᵦ(V') + (newᵣᵦ(V'') - newᵣᵦ(V')))) with (newᵣᵦ(V'')) in Hvt1';
          try assumption; lia.
        + split; try lia. apply Stock.valid_union_spec; split; try assumption.
          apply Stock.shift_preserves_valid_1 
          with (lb := newᵣᵦ(V')) (k' := newᵣᵦ(V'') - newᵣᵦ(V')) in HvW1.
          replace ((newᵣᵦ(V') + (newᵣᵦ(V'') - newᵣᵦ(V')))) with (newᵣᵦ(V'')) in HvW1;
          try assumption; lia.
  (* fT_rsf *)
  - assert (r ∈ᵣᵦ V).
    { rewrite RE.in_find; rewrite H; intro c; now inversion c. }
    rewrite RE.Ext.new_key_add_spec_3; try assumption; try lia.
    split.
    -- apply RE.valid_update_spec; try assumption.
    -- split.
        + apply RE.valid_find_spec with (lb := newᵣᵦ(V)) in H as [_ H]; assumption.
        + split; auto; split; try lia. 
  (* fT_wh *)
  - replace (newᵣᵦ( ⌈ S k ⤆ ⩽ unit … ⩾ ⌉ᵣᵦ (⌈ k ⤆ [⧐ᵣₓ k ≤ 2] ⩽ i … ⩾ ⌉ᵣᵦ ([⧐ᵣᵦ k ≤ 2] V))))
    with (S (S (newᵣᵦ(V)))) in *.
    -- inversion Hvt; subst; destruct IHfT as [HvV' [Hvst' [Hvt'' [HvW Hlt]]]]; try assumption. 
        + apply RE.valid_add_notin_spec.
          ++ unfold k. apply RE.Ext.new_key_notin_spec.
            rewrite RE.Ext.new_key_add_spec_1; auto.
            * apply RE.Ext.new_key_notin_spec; rewrite RE.shift_new_spec; auto.
            * rewrite RE.shift_new_spec; auto.
          ++ repeat split.
            * unfold Resource.valid; lia.
            * unfold Cell.valid; simpl; constructor.
            * apply RE.valid_add_notin_spec.
              ** apply RE.Ext.new_key_notin_spec; 
                  rewrite RE.shift_new_spec; auto.
              ** repeat split.
                  { unfold k,Resource.valid; lia. }
                  { 
                  unfold Cell.valid; simpl; replace (S (S (newᵣᵦ(V)))) 
                  with ((newᵣᵦ(V)) + 2) by lia. now apply Term.shift_preserves_valid_1.  
                  }
                  {
                  unfold Cell.valid; simpl; replace (S (S (newᵣᵦ(V)))) 
                  with ((newᵣᵦ(V)) + 2) by lia. now apply RE.shift_preserves_valid_1.  
                  }
        + replace (S (S (newᵣᵦ(V)))) with ((newᵣᵦ(V)) + 2) by lia.
          now apply Term.shift_preserves_valid_1.
        + split; try assumption; split; auto; split; auto; split.
          ++ apply Stock.valid_add_spec; eauto.
             * unfold Resource.valid; lia.
             * inversion Hvt; subst. 
                  apply Term.shift_preserves_valid_1
                  with (lb := newᵣᵦ(V)) (k' := newᵣᵦ(V') - newᵣᵦ(V)) in H5.
                  replace ((newᵣᵦ(V) + (newᵣᵦ(V') - newᵣᵦ(V)))) with (newᵣᵦ(V')) in H5; 
                  try assumption; lia.
          ++ lia.
    -- unfold k; rewrite RE.Ext.new_key_add_spec_1; auto.
        + apply RE.Ext.new_key_notin_spec; rewrite RE.Ext.new_key_add_spec_1; auto.
          ++ apply RE.Ext.new_key_notin_spec; rewrite RE.shift_new_spec; lia.
          ++ rewrite RE.shift_new_spec; lia.
        + rewrite RE.Ext.new_key_add_spec_1; auto.
          ++ apply RE.Ext.new_key_notin_spec; rewrite RE.shift_new_spec; lia.
          ++ rewrite RE.shift_new_spec; lia.
Qed.

(** *** Proof of preservation of keys in the environment 

  Keeping consistent the typing through the functional transition is 
  needed for the resources environment. Thus, knowing that we cannot loose 
  keys is required.
*)
Lemma functional_preserves_keys :  forall (V V' : 𝓥) (W : 𝐖) (sv sv' sf sf' : Λ),
  ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V' ; sv' ; sf' ; W ⪢ ->
  newᵣᵦ(V) ⊩ᵣᵦ V -> 
  newᵣᵦ(V) ⊩ₜₘ sv -> 
  newᵣᵦ(V) ⊩ₜₘ sf ->

  (forall (r : resource), r ∈ᵣᵦ V -> r ∈ᵣᵦ V').
Proof.
  intros V V' W sv sv' sf sf' fT; dependent induction fT; intros HvV Hvsv Hvsf r' HInV; auto.
  (* fT_eT *)
  - apply IHfT in HInV; try assumption; eapply evaluate_preserves_valid_term; eauto.
  (* fT_first *) 
  - inversion Hvsf; subst; apply IHfT in HInV; auto.
    eapply multi_preserves_valid_term in H0; try assumption; now inversion H0.
  (* fT_comp *)
  - inversion Hvsf; subst. apply IHfT1 in HInV; auto.
    apply functional_preserves_valid in fT1 as HD; auto; destruct HD as [HvV' [Hvst' [Hvt1' [HvW Hle]]]].
    apply IHfT2; auto.
    apply Term.shift_preserves_valid_1 with (lb := newᵣᵦ(V)) (k' := newᵣᵦ(V') - newᵣᵦ(V)) in H4.
    replace ((newᵣᵦ(V) + (newᵣᵦ(V') - newᵣᵦ(V)))) with (newᵣᵦ(V')) in H4; auto; lia.
  (* fT_rsf *)
  - destruct (Resource.eq_dec r r'); subst; apply RE.add_in_iff; auto.
  (* fT_wh *)
  - replace (newᵣᵦ( ⌈ S k ⤆ ⩽ unit … ⩾ ⌉ᵣᵦ (⌈ k ⤆ [⧐ᵣₓ k ≤ 2] ⩽ i … ⩾ ⌉ᵣᵦ ([⧐ᵣᵦ k ≤ 2] V))))
    with (S (S (newᵣᵦ(V)))) in *.
    -- inversion Hvsf; subst; destruct IHfT with (r := r'); auto.
        + apply RE.valid_add_notin_spec.
          ++ unfold k. apply RE.Ext.new_key_notin_spec. rewrite RE.Ext.new_key_add_spec_1; auto.
            * apply RE.Ext.new_key_notin_spec; rewrite RE.shift_new_spec; auto.
            * rewrite RE.shift_new_spec; auto.
          ++ repeat split.
            * unfold Resource.valid; lia.
            * unfold Cell.valid; simpl; constructor.
            * apply RE.valid_add_notin_spec.
              ** apply RE.Ext.new_key_notin_spec; rewrite RE.shift_new_spec; auto.
              ** repeat split.
                { unfold k,Resource.valid; lia. }
                { 
                  unfold Cell.valid; simpl; replace (S (S (newᵣᵦ(V)))) with ((newᵣᵦ(V)) + 2) by lia.
                  now apply Term.shift_preserves_valid_1.  
                }
                {
                  unfold Cell.valid; simpl; replace (S (S (newᵣᵦ(V)))) with ((newᵣᵦ(V)) + 2) by lia.
                  now apply RE.shift_preserves_valid_1.  
                }
      + replace (S (S (newᵣᵦ(V)))) with ((newᵣᵦ(V)) + 2) by lia.
        now apply Term.shift_preserves_valid_1.
      + destruct (Resource.eq_dec r' (S k)); subst; apply RE.add_in_iff; auto.
        right; destruct (Resource.eq_dec r' k); subst; apply RE.add_in_iff; auto.
        right; eapply RE.shift_in_spec in HInV as HInV'.
        eapply RE.valid_in_spec in HInV; eauto.
        rewrite Resource.shift_valid_refl in HInV'; eauto.
      + now exists x.
    -- unfold k; rewrite RE.Ext.new_key_add_spec_1; auto.
      + apply RE.Ext.new_key_notin_spec; rewrite RE.Ext.new_key_add_spec_1; auto.
        ++ apply RE.Ext.new_key_notin_spec; rewrite RE.shift_new_spec; lia.
        ++ rewrite RE.shift_new_spec; lia.
      + rewrite RE.Ext.new_key_add_spec_1; auto.
        ++ apply RE.Ext.new_key_notin_spec; rewrite RE.shift_new_spec; lia.
        ++ rewrite RE.shift_new_spec; lia.
Qed.

(** *** Proof of consistency between V and W 

  W stocks all virtual resources created during the functional transition. Those virtual
  resources are also added in the resource environment V' and cannot be found in the environment V.
*)
Lemma consistency_V_W : forall (V V' : 𝓥) (W : 𝐖) (sv sv' sf sf' : Λ),
  ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V' ; sv' ; sf' ; W ⪢ ->
  newᵣᵦ(V) ⊩ᵣᵦ V -> 
  newᵣᵦ(V) ⊩ₜₘ sv -> 
  newᵣᵦ(V) ⊩ₜₘ sf ->

  (forall (r : resource), r ∈ₛₖ W -> r ∉ᵣᵦ V /\ r ∈ᵣᵦ V').
Proof.
  intros V V' W sv sv' sf sf' fT; dependent induction fT; intros HvV Hvsv Hvsf; auto.
  (* fT_eT *)
  - apply IHfT; try assumption; eapply evaluate_preserves_valid_term; eauto. 
  (* fT_arr *)
  - intros. inversion H0; try now inversion H1.
  (* fT_first *)
  - intros r HIn; inversion Hvsf; subst; apply IHfT; auto;
    eapply multi_preserves_valid_term in H0; try assumption; now inversion H0.
  (* fT_comp *)
  - inversion Hvsf; subst; intros r HIn.
    apply functional_preserves_valid in fT1 as HD; auto; destruct HD as [HvV' [Hvst' [Hvt1' [HvW Hle]]]].
    apply Stock.union_spec in HIn as [HIn | HIn].
    -- apply Stock.shift_in_e_spec in HIn as Heq'; destruct Heq' as [r' Heq]; subst.
       apply Stock.shift_in_spec in HIn as HIn'.
       apply IHfT1 in HIn' as IH; auto.
       eapply Stock.valid_in_spec in HIn' as Hvr'; eauto.
       rewrite Resource.shift_valid_refl; auto.
       destruct IH; split; auto.
       eapply functional_preserves_keys in H1; eauto.
        apply Term.shift_preserves_valid_1 with (lb := newᵣᵦ(V)) (k' := newᵣᵦ(V') - newᵣᵦ(V)) in H4;
        replace ((newᵣᵦ(V) + (newᵣᵦ(V') - newᵣᵦ(V)))) with (newᵣᵦ(V')) in H4; try assumption; lia. 
    -- apply IHfT2 in HIn; auto.
       + destruct HIn; split; auto. intro. eapply functional_preserves_keys in H2; eauto.
       + apply Term.shift_preserves_valid_1 with (lb := newᵣᵦ(V)) (k' := newᵣᵦ(V') - newᵣᵦ(V)) in H4.
         replace ((newᵣᵦ(V) + (newᵣᵦ(V') - newᵣᵦ(V)))) with (newᵣᵦ(V')) in H4; try assumption; lia.
  (* fT_rsf *)
  - intros r' c; exfalso; eapply Stock.empty_in_spec; eauto.
  (* fT_wh *)
  - assert (newᵣᵦ( ⌈ S k ⤆ ⩽ unit … ⩾ ⌉ᵣᵦ (⌈ k ⤆ [⧐ᵣₓ k ≤ 2] ⩽ i … ⩾ ⌉ᵣᵦ ([⧐ᵣᵦ k ≤ 2] V)))= (S (S (newᵣᵦ(V))))).
    {
      unfold k; rewrite RE.Ext.new_key_add_spec_1; auto.
        + apply RE.Ext.new_key_notin_spec; rewrite RE.Ext.new_key_add_spec_1; auto.
          ++ apply RE.Ext.new_key_notin_spec; rewrite RE.shift_new_spec; lia.
          ++ rewrite RE.shift_new_spec; lia.
        + rewrite RE.Ext.new_key_add_spec_1; auto.
          ++ apply RE.Ext.new_key_notin_spec; rewrite RE.shift_new_spec; lia.
          ++ rewrite RE.shift_new_spec; lia.
    }
    inversion Hvsf; subst; intros rf HIn.
    assert (S (S (newᵣᵦ( V)))
                      ⊩ᵣᵦ ⌈ S (newᵣᵦ( V)) ⤆ ⩽ unit … ⩾⌉ᵣᵦ (⌈ newᵣᵦ( V) ⤆ [⧐ᵣₓ newᵣᵦ( V) ≤ 2] ⩽ i … ⩾ ⌉ᵣᵦ ([⧐ᵣᵦ newᵣᵦ( V) ≤ 2] V))).
    {
      apply RE.valid_add_notin_spec; simpl.
      + apply RE.Ext.new_key_notin_spec; rewrite RE.Ext.new_key_add_spec_1; auto.
          * apply RE.Ext.new_key_notin_spec; rewrite RE.shift_new_spec; auto.
          * rewrite RE.shift_new_spec; auto.
      + repeat split.
          * unfold Resource.valid; lia.
          * unfold Cell.valid; simpl; constructor.
          * apply RE.valid_add_notin_spec.
            ** apply RE.Ext.new_key_notin_spec; rewrite RE.shift_new_spec; auto.
            ** repeat split.
                { unfold k,Resource.valid; lia. }
                { 
                  unfold Cell.valid; simpl; replace (S (S (newᵣᵦ(V)))) with ((newᵣᵦ(V)) + 2) by lia.
                  now apply Term.shift_preserves_valid_1.
                }
                {
                  unfold Cell.valid; simpl; replace (S (S (newᵣᵦ(V)))) with ((newᵣᵦ(V)) + 2) by lia.
                  now apply RE.shift_preserves_valid_1.  
                }
    }
    rewrite Stock.add_spec in HIn; destruct HIn as [Heq | [Heq | HIn]]; subst; rewrite H0 in *.
    -- split.
       + unfold k. apply RE.Ext.new_key_notin_spec; lia.
       + simpl; unfold k; eapply functional_preserves_keys; unfold k in *; try rewrite H0; eauto;
        try ( replace (S (S (newᵣᵦ( V)))) with ((newᵣᵦ( V)) + 2) by lia; now apply Term.shift_preserves_valid_1).
        rewrite RE.add_in_iff; right; rewrite RE.add_in_iff; now left.
    -- split.
       + unfold k. apply RE.Ext.new_key_notin_spec; lia.
       +  simpl; unfold k; eapply functional_preserves_keys; subst; try rewrite H0; eauto;
          unfold k in *.
          ++ replace (S (S (newᵣᵦ( V)))) with ((newᵣᵦ( V)) + 2) by lia; now apply Term.shift_preserves_valid_1.
          ++ rewrite RE.add_in_iff; now left.
    -- eapply IHfT in HIn; eauto; unfold k; replace (S (S (newᵣᵦ( V)))) with ((newᵣᵦ( V)) + 2) by lia.
       + destruct HIn; split; auto. intro c; apply H2. repeat rewrite RE.add_in_iff; repeat right.
         unfold k. rewrite RE.valid_in_spec_1; auto.
       + now apply Term.shift_preserves_valid_1.
Qed.

(** *** Proof of inner constraint of W 

  W stocks reading virtual resource names and writing virtual resource names. It is relevant
  to state that the intersection of set of reading and writing resource names is empty.
*)
Lemma W_well_formed : forall (V V' : 𝓥) (W : 𝐖) (sv sv' sf sf' : Λ),
  ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V' ; sv' ; sf' ; W ⪢ ->
  newᵣᵦ(V) ⊩ᵣᵦ V -> 
  newᵣᵦ(V) ⊩ₜₘ sv -> 
  newᵣᵦ(V) ⊩ₜₘ sf ->

  (forall r, r ∈ₛₖ W -> (r ∈ᵣₖ (fst W) /\ r ∉ (snd W))%wk \/ (r ∉ᵣₖ (fst W) /\ r ∈ (snd W)))%wk.
Proof.
  intros V V' W sv sv' sf sf' fT; dependent induction fT; intros HvV Hvsv Hvsf; auto;
  try (intros r' c; inversion c; now inversion H0).
  (* fT_eT *)
  - intros r HIn. apply IHfT; auto.
    now apply evaluate_preserves_valid_term with t.
  (* fT_firts *)
  - intros; inversion Hvsf; subst; apply IHfT; auto.
    apply multi_preserves_valid_term in H0; auto; inversion H0; now subst.
  (* fT_comp *)
  - intros. rewrite Stock.union_spec in H0; destruct H0.
    -- inversion Hvsf; subst; eapply functional_preserves_valid in fT1 as Hv; auto.
       destruct Hv as [HvV' [Hvst' [Hvt1' [HvW Hle]]]].
       destruct W; unfold Stock.In,Stock.shift in *; simpl in *. inversion HvW.
       destruct H0. 
       + left; split; try (rewrite ReadStock.map_union_spec; now left).
         intro c; rewrite WriteStock.union_spec in *; destruct c.
         ++ rewrite ReadStock.valid_in_spec_1 in H0; auto.
            eapply ReadStock.valid_in_spec in H0 as H0'; eauto.
            replace r with ([⧐ᵣ newᵣᵦ( V') ≤ newᵣᵦ( V'') - newᵣᵦ( V')] r) in H3.
            * rewrite <- WriteStock.shift_in_spec in H3. 
              assert (r ∈ᵣₖ t \/ (r ∈ t0)%wk). { now right. }
              apply IHfT1 in H6; auto; destruct H6; destruct H6; auto.
            * now apply Resource.shift_valid_refl.
         ++ rewrite ReadStock.valid_in_spec_1 in H0; auto.
            assert (r ∈ᵣₖ t \/ (r ∈ t0)%wk). { now left. }
            eapply consistency_V_W in fT1 as HVW; eauto. destruct HVW as [HnV HV'].
            destruct W'; simpl in *. 
            assert (r ∈ᵣₖ t3 \/ (r ∈ t4)%wk). { now right. }
            eapply consistency_V_W in fT2 as HVW'; eauto.
            * destruct HVW' as [HnV' HV'']; contradiction.
            * replace (newᵣᵦ( V')) with (newᵣᵦ( V) + (newᵣᵦ( V') - newᵣᵦ( V))) by lia.
              apply Term.shift_preserves_valid_3; auto; lia.
       + simpl in *; right; split; try (rewrite WriteStock.union_spec; now left).
         rewrite WriteStock.valid_in_spec_1 in H0; auto. intro c.
         rewrite ReadStock.map_union_spec in *; destruct c.
         ++ rewrite ReadStock.valid_in_spec_1 in H3; auto.
            assert (r ∈ᵣₖ t \/ (r ∈ t0)%wk). { now left. }
            apply IHfT1 in H6; auto; destruct H6; destruct H6; auto.
         ++ assert (r ∈ᵣₖ t \/ (r ∈ t0)%wk). { now right. }
            destruct W'; simpl in *. inversion Hvsf; subst.
            eapply consistency_V_W in fT1 as HVW; eauto; destruct HVW as [HnV HV'].
            assert (r ∈ᵣₖ t3 \/ (r ∈ t4)%wk). { now left. }
            eapply consistency_V_W in fT2 as HVW'; eauto.
            * destruct HVW'; contradiction.
            * replace (newᵣᵦ( V')) with (newᵣᵦ( V) + (newᵣᵦ( V') - newᵣᵦ( V))) by lia.
              apply Term.shift_preserves_valid_3; auto; lia.
    -- inversion Hvsf; subst; eapply functional_preserves_valid in fT1 as Hv; auto.
       destruct Hv as [HvV' [Hvst' [Hvt1' [HvW Hle]]]].
       destruct W'; unfold Stock.In in *; simpl in *; destruct H0.
       + left; split; try (rewrite ReadStock.map_union_spec; now right).
         intro c. rewrite WriteStock.union_spec in c; destruct c.
         ++ destruct W; simpl in *; inversion HvW; simpl in *.
            rewrite WriteStock.valid_in_spec_1 in H1; auto.
            assert (r ∈ᵣₖ t3 \/ (r ∈ t4)%wk). { now right. }
            assert (r ∈ᵣₖ t \/ (r ∈ t0)%wk). { now left. }
            eapply consistency_V_W in fT1; eauto.
            eapply consistency_V_W in fT2; eauto.
            * destruct fT1,fT2; contradiction.
            * replace (newᵣᵦ( V')) with (newᵣᵦ( V) + (newᵣᵦ( V') - newᵣᵦ( V))) by lia.
              apply Term.shift_preserves_valid_3; auto; lia.
         ++ assert (r ∈ᵣₖ t \/ (r ∈ t0)%wk). { now right. }
            apply IHfT2 in H2; auto.
            * destruct H2; destruct H2; auto.
            * replace (newᵣᵦ( V')) with (newᵣᵦ( V) + (newᵣᵦ( V') - newᵣᵦ( V))) by lia.
              apply Term.shift_preserves_valid_3; auto; lia.
       + right; split; try (rewrite WriteStock.union_spec; now right).
         intro c. rewrite ReadStock.map_union_spec in c; destruct c.
         ++ destruct W; simpl in *; inversion HvW; simpl in *.
            rewrite ReadStock.valid_in_spec_1 in H1; auto.
            assert (r ∈ᵣₖ t3 \/ (r ∈ t4)%wk). { now left. }
            assert (r ∈ᵣₖ t \/ (r ∈ t0)%wk). { now right. }
            eapply consistency_V_W in fT1; eauto.
            eapply consistency_V_W in fT2; eauto.
            * destruct fT1,fT2; contradiction.
            * replace (newᵣᵦ( V')) with (newᵣᵦ( V) + (newᵣᵦ( V') - newᵣᵦ( V))) by lia.
              apply Term.shift_preserves_valid_3; auto; lia.
        ++ assert (r ∈ᵣₖ t \/ (r ∈ t0)%wk). { now right. }
            apply IHfT2 in H2; auto.
            * destruct H2; destruct H2; auto.
            * replace (newᵣᵦ( V')) with (newᵣᵦ( V) + (newᵣᵦ( V') - newᵣᵦ( V))) by lia.
              apply Term.shift_preserves_valid_3; auto; lia.
  (* fT_wh *)
  - assert (Heq : RE.Ext.new_key (@RE.Raw.add Cell.t k (Cell.inp (Term.shift k 2 i))
                            (RE.shift k 2 V)) = S (newᵣᵦ(V))).
    { 
      rewrite RE.Ext.new_key_add_spec_1; auto.
      - apply RE.shift_new_notin_spec; lia.
      - rewrite RE.shift_new_spec; lia.
    } 
    assert (Heq' : RE.Ext.new_key (@RE.Raw.add Cell.raw (S k) (Cell.inp Term.tm_unit)
                        (@RE.Raw.add Cell.t k (Cell.inp (Term.shift k 2 i))
                        (RE.shift k 2 V))) = S (S (newᵣᵦ(V)))).
    { 
      rewrite RE.Ext.new_key_add_spec_1; auto.
      - apply RE.Ext.new_key_notin_spec; rewrite Heq; auto.
      - rewrite RE.Ext.new_key_add_spec_1; auto.
        -- apply RE.shift_new_notin_spec; lia.
        -- rewrite RE.shift_new_spec; lia.  
    }
    assert (HvshV : S (S (newᵣᵦ(V))) ⊩ᵣᵦ
                      (@RE.Raw.add Cell.raw (S k) (Cell.inp Term.tm_unit)
                      (@RE.Raw.add Cell.t k (Cell.inp (Term.shift k 2 i))
                      (RE.shift k 2 V)))).
    {
      apply RE.valid_add_notin_spec.
      - apply RE.Ext.new_key_notin_spec; rewrite Heq; auto.
      - repeat split; try constructor. apply RE.valid_add_notin_spec.
        -- apply RE.shift_new_notin_spec; auto.
        -- split; try constructor; try lia.
           + inversion Hvsf; subst. unfold k.
             replace (S (S (newᵣᵦ( V)))) with ((newᵣᵦ( V)) + 2) by lia.
             unfold Cell.valid; simpl.
             now apply Term.shift_preserves_valid_1.
           + replace (S (S (newᵣᵦ( V)))) with ((newᵣᵦ( V)) + 2) by lia.
             now apply RE.shift_preserves_valid_1.
    }
    intros r HIn. unfold Stock.add, Stock.In in *; destruct W; simpl in *.
    destruct HIn.
    -- rewrite ReadStock.add_in_iff in H0; destruct H0; subst.
       + left; split; try (rewrite ReadStock.add_in_iff; now left).
         rewrite WriteStock.add_notin_spec; split; try lia.
         intro c. assert (k ∈ᵣₖ t0 \/ (k ∈ t1)%wk). { now right. }
         apply IHfT in H0 as H0'.
         ++ destruct H0'; destruct H1; auto. eapply consistency_V_W in fT; eauto.
            * apply fT. repeat rewrite RE.add_in_iff; right; now left.
            * rewrite Heq'; apply HvshV.
            * rewrite Heq'. replace (S (S (newᵣᵦ( V)))) with ((newᵣᵦ( V)) + 2) by lia.
              now apply Term.shift_preserves_valid_1.
            * inversion Hvsf; subst; now rewrite Heq'.
         ++ rewrite Heq'; apply HvshV.
         ++ rewrite Heq'. replace (S (S (newᵣᵦ( V)))) with ((newᵣᵦ( V)) + 2) by lia.
            now apply Term.shift_preserves_valid_1.
         ++ inversion Hvsf; subst; now rewrite Heq'.
       + left; split; try (rewrite ReadStock.add_in_iff; now right).
         rewrite WriteStock.add_notin_spec; split.
         ++ assert (r ∈ᵣₖ t0 \/ (r ∈ t1)%wk). { now left. }
            eapply consistency_V_W in fT; eauto.
            * intro c; subst; apply fT; rewrite RE.add_in_iff; now left.
            * rewrite Heq'; apply HvshV.
            * rewrite Heq'. replace (S (S (newᵣᵦ( V)))) with ((newᵣᵦ( V)) + 2) by lia.
                 now apply Term.shift_preserves_valid_1.
            * inversion Hvsf; subst; now rewrite Heq'.
         ++ assert (r ∈ᵣₖ t0 \/ (r ∈ t1)%wk). { now left. } eapply IHfT in H1 as H1'.
            * destruct H1'; destruct H2; auto.
            * rewrite Heq'; apply HvshV.
            * rewrite Heq'. replace (S (S (newᵣᵦ( V)))) with ((newᵣᵦ( V)) + 2) by lia.
              now apply Term.shift_preserves_valid_1.
            * inversion Hvsf; subst; now rewrite Heq'.
    -- rewrite WriteStock.add_spec in H0; destruct H0; subst.
       + right; split; try (rewrite WriteStock.add_spec; now left).
         rewrite ReadStock.add_in_iff; intro; destruct H0; try lia.
         assert ((S k) ∈ᵣₖ t0 \/ ((S k) ∈ t1)%wk). { now left. }
         eapply consistency_V_W in fT; eauto.
         ++ apply fT; rewrite RE.add_in_iff; now left.
         ++ rewrite Heq'; apply HvshV.
         ++ rewrite Heq'. replace (S (S (newᵣᵦ( V)))) with ((newᵣᵦ( V)) + 2) by lia.
            now apply Term.shift_preserves_valid_1.
         ++ inversion Hvsf; subst; now rewrite Heq'.
       + right; split; try (rewrite WriteStock.add_spec; now right).
         assert (r ∈ᵣₖ t0 \/ (r ∈ t1)%wk). { now right. }
         apply IHfT in H1.
         ++ destruct H1; destruct H1; auto.
            assert (r ∈ᵣₖ t0 \/ (r ∈ t1)%wk). { now right. }
            eapply consistency_V_W in fT; eauto.
            * intro c. apply fT. rewrite RE.add_in_iff;right. 
              rewrite ReadStock.add_in_iff in c; destruct c; subst;
              rewrite RE.add_in_iff; auto; contradiction.
            * rewrite Heq'; apply HvshV.
            * rewrite Heq'. replace (S (S (newᵣᵦ( V)))) with ((newᵣᵦ( V)) + 2) by lia.
              now apply Term.shift_preserves_valid_1.
            * inversion Hvsf; subst; now rewrite Heq'.
         ++ rewrite Heq'; apply HvshV.
         ++ rewrite Heq'. replace (S (S (newᵣᵦ( V)))) with ((newᵣᵦ( V)) + 2) by lia.
            now apply Term.shift_preserves_valid_1.
         ++ inversion Hvsf; subst; now rewrite Heq'.

Qed.


(**
  *** General proof of preservation of typing through functional transition

  **** Hypothesis

  Knowing the term sf is well typed (1), the stream term is also well typed (2),
  there is a transition using the two previous terms (3) and each term in the
  environment is well typed to a type findable in the context if they are
  the same resource name that mapped them (4);

  **** Results

  We can state that:
  - each value mapped with a resource name present in R has to be unused (5);
  - each value mapped with a resource name not present in R' but present in V has to be the same in V' (6);
  - we can found a context and a resource set such as :
    - the old context is a subset of the new one (7);
    - the old resources set is a subset of the new one (8);
    - there is the same property between Re' and V' that between Re and V (9); 
    - all initial value stocked in W are well typed regards of the new context Re' (10);
    - all new resources founded in R' are stored in W and is not in R (11); 
    - Each value mapped with a resource name present in R' has to be used in V' (12);
    - the output stream term is well typed (13);
    - the term sf' is well typed (14).

*)
Theorem functional_preserves_typing : 
  forall (Re : ℜ) (V V' : 𝓥) (W : 𝐖) (sv sv' sf sf' : Λ) (τ τ' : Τ) (R : resources),

    (* (1) *) ∅ᵥᵪ ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) ->
    (* (2) *) ∅ᵥᵪ ⋅ Re ⊫ sv ∈ τ -> 
    (* (3) *) ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V' ; sv' ; sf' ; W ⪢ -> 
    (* (4) *) Instᵣₜ(Re,V) ->


    (* (5) *)(forall (r : resource), (r ∈ R)%rs -> RE.unused r V) /\
    (* (6) *)(forall (r : resource), (r ∉ R)%rs /\ (r ∈ᵣᵦ V) -> 
                ([⧐ᵣᵦ (newᵣᵦ(V)) ≤ ((newᵣᵦ(V')) - (newᵣᵦ(V)))] V) ⌊r⌋ᵣᵦ = V' ⌊r⌋ᵣᵦ) /\

    exists (Re' : ℜ) (R' : resources), 
      (*  (7) *) Re ⊆ᵣᵪ Re'     /\ 
      (*  (8) *) (R ⊆ R')%rs    /\
      (*  (9) *) Instᵣₜ(Re',V') /\
      (* (10) *) (forall (r : resource) (v : Λ) (τ τ' : Τ), 
                    W ⌈ r ⩦ v ⌉ₛₖ -> Re' ⌈r ⩦ (τ',τ)⌉ᵣᵪ -> ∅ᵥᵪ ⋅ Re' ⊫ v ∈ τ) /\
      (* (11) *) (forall (r : resource), (r ∈ (R' \ R))%rs -> (r ∈ (Stock.to_RS W))%rs /\ (r ∉ᵣᵦ V)) /\
      (* (12) *) (forall (r : resource), (r ∈ R')%rs -> RE.used r V') /\
      (* (13) *) ∅ᵥᵪ ⋅ Re' ⊫ sv' ∈ τ' /\
      (* (14) *) ∅ᵥᵪ ⋅ Re' ⊫ sf' ∈ (τ ⟿ τ' ∣ R').
Proof.
  intros Re V V' W sv sv' sf sf' τ τ' R Hwsf Hwsv fT; revert Re R τ τ' Hwsf Hwsv;
  induction fT; intros Re R α β Hwsf Hwsv Hinst;

  apply instantiation_valid in Hinst as HvRe; destruct HvRe as [HvRe HvV];
  apply instantiation_new in Hinst as Hnew;
  
  move HvRe before Hinst; move HvV before HvRe; move Hnew before Hinst.
  (* fT_eT *)
  - 
    (* clean *)
    move Re before W; move R before Re; move α before R; move β before α; move fT after IHfT;
    rename fT into HfT; rename H into HeT; move HeT after HfT.
    (* clean *)

    rewrite <- Hnew in HeT; apply evaluate_preserves_typing with (t' := t') in Hwsf as Hwsf'; 
    try assumption.
    
    (* clean *)
    clear HeT Hwsf HvRe; move Hwsf' after Hwsv.
    (* clean *)

    apply IHfT; assumption.
  (* fT_arr *)
  - 
    (* clean *)
    inversion Hwsf; subst; rename H4 into Hwt; clear Hwsf H; move Hwt after Hwsv.
    (* clean *)

    repeat split.
    -- intros r HIn; inversion HIn.
    -- intros r [HnIn HIn]; replace (newᵣᵦ(V) - newᵣᵦ(V)) with 0 by lia.
        now rewrite RE.shift_refl.
    -- exists Re; exists ∅ᵣₛ; split; try reflexivity.
        repeat split; auto; try reflexivity; try constructor; auto.
        + intros; inversion H.
        + inversion H.
        + intros r HIn; inversion HIn.
        + apply wt_app with (τ2 := α); assumption.
  (* fT_first *)
  -
    (* clean *)
    clear H; inversion Hwsf; subst; move Re before W; move R before Re; move τ1 before τ;
    move τ2 before τ1; clear Hwsf; rename H5 into Hwt; rename H8 into Hvτ;
    move Hwt after Hwsv; move Hvτ before Hwsv; rename H0 into HmeT; rename fT into HfT;
    move HfT after IHfT; move HmeT after HfT.
    (* clean *)

    rewrite <- Hnew in HmeT; apply multi_preserves_typing with (t' := <[⟨v1,v2⟩]>) in Hwsv; 
    try assumption.

    (* clean *)
    inversion Hwsv; subst; rename H4 into Hwv1; rename H6 into Hwv2; move Hwv1 before Hwt;
    move Hwv2 before Hwv1; clear Hwsv; move HvRe after Hvτ.
    (* clean *)

    apply IHfT with (R := R) (τ' := τ2) in Hwv1 as IH; try assumption.

    clear IHfT; destruct IH as [Hunsd [Hlcl [Re' [R' [HSubRe [HSubR [Hinst' [HwtW [HInW [Husd [Hwv1' Hwt']]]]]]]]]]].

    (* clean *)
    move Re' before Re; move R' before R; move Hwv1' before Hwv1; clear Hwv1;
    move Hwt' before Hwt; clear Hwt; move Hinst' before Hinst; move Hunsd before Husd.
    (* clean *)

    apply instantiation_new in Hinst' as Hnew'; move Hnew' before Hnew.

    repeat split; auto.
    exists Re'; exists R'; repeat split; try assumption; try (destruct HSubRe; assumption);
    try (now apply HInW).
    -- constructor; try assumption; rewrite <- Hnew; rewrite <- Hnew'; 
        apply weakening_ℜ_1; auto.
    -- apply wt_first; try assumption.
        apply Typ.valid_weakening with (k := newᵣᵪ(Re)); try assumption.
        apply RC.Ext.new_key_Submap_spec in HSubRe; assumption.
  (* fT_comp *)
  -
    (* clean *)
    inversion H; subst; inversion Hwsf; subst; apply Resources.eq_leibniz in H10; subst;
    clear Hwsf; move Re before W'; move R1 before Re; move R2 before R1; 
    move α before R2; move β before α; move τ before β; rename fT1 into HfT1;
    move HfT1 after IHfT2; rename fT2 into HfT2; move HfT2 after HfT1.
    rename H9 into Hwt1; rename H11 into Hwt2; rename H12 into HEmp.
    rename H3 into Hvt2; clear H2; move Hwt1 after Hwsv; move Hwt2 before Hwt1; move Hvt2 after Hwt2.
    (* clean *)

    apply IHfT1 with (R := R1) (τ' := τ) in Hwsv as IH1; try assumption;
    try (intros; apply Hunsd; rewrite Resources.union_spec; now left).
    clear IHfT1; destruct IH1 as [Hunsd1 [Hlcl1 [Re' [R1' [HSubRe [HSubR1 [Hinst' [HwtW [HInW [Husd1 [Hwsv' Hwt1']]]]]]]]]]].

    (* clean *)
    move Re' before Re; move R1' before R1; move Hwsv' before Hwsv;
    move Hwt1' before Hwt1; move Hunsd1 after HInW; move Hinst' before Hinst.
    (* clean *)

    apply instantiation_new in Hinst' as Hnew'; move Hnew' before Hnew.
    apply weakening_ℜ_1 with (Re' := Re') in Hwt2 as Hwt2'; auto; 
    try now apply VContext.valid_empty_spec.
    apply IHfT2 with (R := R2) (τ' := β) in Hwsv' as IH2; try assumption;
    try (rewrite <- Hnew; now rewrite <- Hnew').

    destruct IH2 as [Hunsd2 [Hlcl2 [Re'' [R2' [HSubRe' [HSubR2 [Hinst'' [HwtW' [HInW'  [Husd2 [Hwsv'' Hwt2'']]]]]]]]]]].

    (* clean *)
    move Re'' before Re'; move R2' before R2; move Hwsv'' before Hwsv';
    move Hwt2' before Hwt2; move Hwt2'' before Hwt2'; move Hunsd2 before Hunsd1; move Hinst'' before Hinst';
    clear IHfT2; move HSubRe' before HSubRe; move HSubR2 before HSubR1; move HInW' before HInW;
    move Husd2 before Husd1; move Hlcl2 before Hlcl1.
    (* clean *)

    assert (HEmp' : (∅ᵣₛ = R1' ∩ R2')%rs).
    {
      symmetry; apply Resources.empty_is_empty_1; unfold Resources.Empty.
      intro r'; intro HIn; rewrite Resources.inter_spec in HIn; 
      destruct HIn as [HIn1 HIn2].
      destruct (Resources.In_dec r' R1); destruct (Resources.In_dec r' R2).
      -- symmetry in HEmp; apply Resources.empty_is_empty_2 in HEmp.
          unfold Resources.Empty in HEmp; apply (HEmp r').
          rewrite Resources.inter_spec; split; auto.
      -- assert (HnInV' : r' ∉ᵣᵦ V'). 
          { apply HInW'; rewrite Resources.diff_spec; split; assumption. }
          assert (HInV1 : r' ∈ᵣᵦ V).
          { 
          apply Hunsd1 in i; destruct i as [v HfV].  
          rewrite RE.in_find; intro c; rewrite HfV in *; inversion c.
          }

          apply well_typed_implies_valid in Hwt1 as Hv; eauto; 
          try (apply VContext.valid_empty_spec); destruct Hv as [Hvt1 _].
          apply well_typed_implies_valid in Hwsv as Hv; eauto; 
          try (apply VContext.valid_empty_spec); destruct Hv as [Hvsv _].
          rewrite Hnew in Hvt1,Hvsv.
          eapply functional_preserves_keys in HInV1; eauto.
          
      -- assert (HInV1 : r' ∈ᵣᵦ V).
          {
          eapply typing_Re_R in i as HInRe; eauto.
          eapply instantiation_in in HInRe; eauto. 
          }

          revert HInV1; apply HInW; rewrite Resources.diff_spec; split; assumption.

      -- assert ((r' ∈ Stock.to_RS W)%rs /\ r' ∉ᵣᵦ V).
          { apply HInW; rewrite Resources.diff_spec; split; assumption. }
          destruct H0 as [HInW1 HnInV].
          assert (r' ∉ᵣᵦ V').
          { apply HInW'; rewrite Resources.diff_spec; split; assumption. }
          
          apply well_typed_implies_valid in Hwt1 as Hv; eauto; 
          try (apply VContext.valid_empty_spec); destruct Hv as [Hvt1 _].
          apply well_typed_implies_valid in Hwsv as Hv; eauto; 
          try (apply VContext.valid_empty_spec); destruct Hv as [Hvsv _].
          rewrite Hnew in Hvt1,Hvsv.
          
          apply Stock.to_RS_in_spec in HInW1.
          eapply consistency_V_W in HfT1; eauto; simpl in *; destruct HfT1; auto.
      }

      move HEmp' before HEmp. repeat split.
      -- intros r HIn; rewrite Resources.union_spec in HIn; destruct HIn; auto.
          assert (HInV : r ∈ᵣᵦ V).
          { eapply typing_Re_R in H0 as HInRe; eauto. eapply instantiation_in in HInRe; eauto. }

          assert (HnInR1 : (r ∉ R1)%rs).
          { 
            intro; symmetry in HEmp; apply Resources.empty_is_empty_2 in HEmp; 
            apply (HEmp r); rewrite Resources.inter_spec; now split.
          }

          destruct HInV as [v HfV]; apply RE.find_1 in HfV; destruct v.
          + now exists λ.
          + assert (r ∈ᵣᵦ V). { exists (⩽ … λ ⩾); now apply RE.find_2. }
          
            apply RE.shift_find_spec with (lb := newᵣᵦ(V)) (k := newᵣᵦ(V') - newᵣᵦ(V)) in HfV.
            rewrite Resource.shift_valid_refl in HfV.
            ++ rewrite Hlcl1 in HfV; try split; auto. apply Hunsd2 in H0; destruct H0; rewrite H0 in *;
              inversion HfV.
            ++ eapply RE.valid_in_spec in H1; eauto.
      -- intros r [HnIn HIn]; rewrite Resources.union_notin_spec in HnIn; destruct HnIn as [HnIn1 HnIn2].

          assert (HIn' : r ∈ᵣᵦ V').
          { 
            apply well_typed_implies_valid in Hwt1 as Hv; eauto;
            try (apply VContext.valid_empty_spec); destruct Hv as [Hvt1 _].
            apply well_typed_implies_valid in Hwsv as Hv; eauto;
            try (apply VContext.valid_empty_spec); destruct Hv as [Hvsv _].
            rewrite Hnew in Hvt1,Hvsv.
            eapply functional_preserves_keys; eauto. 
          }

          assert ([⧐ᵣᵦ newᵣᵦ( V) ≤ newᵣᵦ( V'') - newᵣᵦ( V)] V = [⧐ᵣᵦ newᵣᵦ(V') ≤ newᵣᵦ( V'') - newᵣᵦ(V')]([⧐ᵣᵦ newᵣᵦ(V) ≤ newᵣᵦ(V') - newᵣᵦ(V)] V))%re.
          { 
            apply RC.Ext.new_key_Submap_spec in HSubRe,HSubRe'.
            apply instantiation_new in Hinst,Hinst',Hinst''.
            rewrite Hinst,Hinst' in HSubRe; rewrite Hinst',Hinst'' in HSubRe'.
            rewrite RE.shift_unfold_1; auto; reflexivity. 
          }

          rewrite H0; rewrite <- Hlcl2; try (split; auto).
          destruct HIn as [v HfV]; apply RE.find_1 in HfV.
          apply RE.shift_find_spec with (lb := newᵣᵦ(V)) (k := newᵣᵦ(V') - newᵣᵦ(V)) in HfV as HfV'.

          apply RE.valid_find_spec with (lb := newᵣᵦ(V)) in HfV as Hv; auto.
          destruct Hv as [Hvr _]. rewrite Resource.shift_valid_refl in HfV'; auto.
      
          apply RE.shift_find_spec with (lb := newᵣᵦ(V')) (k := newᵣᵦ(V'') - newᵣᵦ(V')) in HfV' as HfV''.

          apply instantiation_valid in Hinst' as Hv; destruct Hv as [_ HvV'].
          apply RE.valid_in_spec with (lb := newᵣᵦ(V')) in HIn' as Hv; auto.
          rewrite Resource.shift_valid_refl in HfV''; auto. rewrite HfV''. symmetry.

          rewrite <- Resource.shift_valid_refl with (lb := newᵣᵦ(V')) (t := r) (k := newᵣᵦ(V'') - newᵣᵦ(V')); auto.
          apply RE.shift_find_spec. rewrite <- Hlcl1.
          + rewrite <- Resource.shift_valid_refl with (lb := newᵣᵦ(V)) (t := r) (k := newᵣᵦ(V') - newᵣᵦ(V)); auto.
            now apply RE.shift_find_spec.
          + split; auto. apply RE.in_find; intro c; rewrite HfV in *; inversion c.         
      -- exists Re''; exists (R1' ∪ R2')%rs; split; try (now transitivity Re'); repeat split; auto.
          + unfold Resources.Subset; intros r HIn.
            rewrite Resources.union_spec in *; destruct HIn as [HIn | HIn]; auto.
          + intros r v τ0 τ' Hfi HfiRe. apply Stock.union_find_spec in Hfi; destruct Hfi.
            ++ assert (([⧐ₛₖ newᵣᵦ( V') ≤ newᵣᵦ( V'') - newᵣᵦ( V')] W) 
                            ⌈ ([⧐ᵣ newᵣᵦ( V') ≤ newᵣᵦ( V'') - newᵣᵦ( V')] r) ⩦ v ⌉ₛₖ). 
               {
                 assert (r ∈ᵣₖ ([⧐ᵣₖ newᵣᵦ( V') ≤ newᵣᵦ( V'') - newᵣᵦ( V')] (fst W))).
                 { unfold Stock.find,Stock.shift in *; simpl in *. exists v; now apply ReadStock.find_2. }
                 apply functional_preserves_valid in HfT1 as H3; auto.
                 - destruct H3 as [_ [_ [_ [H3 _]]]]. destruct H3.
                   rewrite ReadStock.valid_in_spec_1 in H1; auto.
                   eapply ReadStock.valid_in_spec with (lb := newᵣᵦ(V')) in H1; auto.
                   rewrite Resource.shift_valid_refl; auto.
                 - apply well_typed_implies_valid in Hwsv; auto.
                   destruct Hwsv; rewrite <- Hnew; assumption.
                 - apply well_typed_implies_valid in Hwt1; auto.
                   destruct Hwt1; rewrite <- Hnew; assumption.
               }
               unfold Stock.find,Stock.shift in H1; simpl in *. apply ReadStock.shift_find_e_spec in H1 as H1'.
               destruct H1'; subst. apply ReadStock.shift_find_spec in H1.
               eapply HwtW in H1.
               * rewrite <- Hnew'. 
                 apply instantiation_new in Hinst''. rewrite <- Hinst''.
                 apply weakening_ℜ_1; eauto.
                 apply instantiation_valid in Hinst'. destruct Hinst'; auto.
               * assert (r ∈ₛₖ W). { unfold Stock.In; left. exists x; now apply ReadStock.find_2. }
                 eapply consistency_V_W with (r := r) in HfT1 as H3; auto.
                 ** destruct H3. rewrite <- instantiation_in with (Re := Re') in H4; auto.
                    destruct H4. apply RC.find_1 in H4. 
                    apply RC.Submap_find_spec with (m' := Re'') in H4 as H4'; auto.
                    rewrite HfiRe in H4'; inversion H4'; subst; eauto.
                 ** apply well_typed_implies_valid in Hwsv; auto.
                    destruct Hwsv; rewrite <- Hnew; assumption.
                 ** apply well_typed_implies_valid in Hwt1; auto.
                    destruct Hwt1; rewrite <- Hnew; assumption. 
            ++ eapply HwtW'; eauto.
          + rename H0 into HIn. rewrite Resources.diff_spec in HIn; destruct HIn as [HIn HnIn];
            rewrite Resources.union_notin_spec in HnIn; destruct HnIn as [HnIn1 HnIn2];
            rewrite Resources.union_spec in HIn; destruct HIn as [HIn | HIn].
            ++ assert ((r ∈ Stock.to_RS W)%rs /\ r ∉ᵣᵦ V). { apply HInW; rewrite Resources.diff_spec; now split. }
              destruct H0.
               
              
              rewrite Stock.to_RS_union_spec; left.
              apply instantiation_valid in Hinst' as Hv; destruct Hv as [_ HvV'].

              assert (r ∈ᵣᵦ V'). 
              {
                apply well_typed_implies_valid in Hwt1 as Hv; eauto; destruct Hv as [Hvt1 _].
                apply well_typed_implies_valid in Hwsv as Hv; eauto; destruct Hv as [Hvsv _].
                rewrite Hnew in Hvt1,Hvsv.

                apply Stock.to_RS_in_spec in H0. eapply consistency_V_W in H0; eauto; destruct H0; auto.
              }

              eapply RE.valid_in_spec in H2; eauto.
              rewrite <- Resource.shift_valid_refl with (lb := newᵣᵦ(V')) (k := newᵣᵦ(V'') - newᵣᵦ(V')) (t := r); auto.
              rewrite <- Stock.to_RS_in_spec in *. now apply Stock.shift_in_spec.
            ++ apply Stock.to_RS_union_spec; right. 
               apply HInW'; rewrite Resources.diff_spec; split; assumption.
          + rename H0 into HIn. rewrite Resources.diff_spec in HIn; destruct HIn as [HIn HnIn];
            rewrite Resources.union_notin_spec in HnIn; destruct HnIn as [HnIn1 HnIn2];
            rewrite Resources.union_spec in HIn; destruct HIn as [HIn | HIn].
            ++ apply HInW; rewrite Resources.diff_spec; split; auto. 
            ++ intro HnInV. assert (HnInV' : r ∉ᵣᵦ V').
              { apply HInW'; rewrite Resources.diff_spec; split; assumption. }
              apply HnInV'. 
              apply well_typed_implies_valid in Hwt1 as Hv; eauto; destruct Hv as [Hvt1 _].
              apply well_typed_implies_valid in Hwsv as Hv; eauto; destruct Hv as [Hvsv _].
              rewrite Hnew in Hvt1,Hvsv.
              eapply functional_preserves_keys; eauto. 
          + intros r HIn; rewrite Resources.union_spec in HIn; destruct HIn as [HIn | HIn].

            ++ assert (HnIn' : (r ∉ R2')%rs). 
              { 
                intro. symmetry in HEmp'; apply Resources.empty_is_empty_2 in HEmp'; 
                apply (HEmp' r); rewrite Resources.inter_spec; split; auto. 
              }

              apply Husd1 in HIn as HuV'; destruct HuV' as [v HfV'].
              apply RE.shift_find_spec with (lb := newᵣᵦ(V')) (k := newᵣᵦ(V'') - newᵣᵦ(V')) in HfV' as HfV''.

              apply instantiation_valid in Hinst' as Hv; destruct Hv as [_ HvV'].
              rewrite Resource.shift_valid_refl in HfV''; simpl in *.
          
              * exists <[[⧐ₜₘ {newᵣᵦ( V')} ≤ {newᵣᵦ( V'') - newᵣᵦ( V')}] v]>. rewrite <- HfV'';
                symmetry; apply Hlcl2; split; auto; apply RE.in_find;
                intro c; rewrite HfV' in c; inversion c.
              * eapply RE.valid_find_spec in HfV'; eauto; now destruct HfV'.
            ++ apply Husd2 in HIn as HfV'; destruct HfV' as [v HfV']; now exists v.
          + apply wt_comp with (R1 := R1') (R2 := R2') (τ := τ); try reflexivity; auto.
            apply instantiation_new in Hinst'' as Hnew''; rewrite <- Hnew'; rewrite <- Hnew''.
            apply instantiation_valid in Hinst' as HvRe'; destruct HvRe' as [HvRe' _].
            apply weakening_ℜ_1; auto.
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
        + replace (newᵣᵦ(V) - newᵣᵦ(V)) with 0 by lia; now rewrite RE.shift_refl.
        + apply RE.in_find; intro c; rewrite HfV in c; inversion c.
    -- exists Re; exists \{{r}}; split; try reflexivity. repeat split; try reflexivity.
        + eapply itfT_update; eauto.
          ++ apply RE.in_find; intro c; rewrite HfV in c; inversion c.
          ++ unfold RE.Add; reflexivity.
        + intros; inversion H.
        + rename H into HIn; apply Resources.diff_spec in HIn as [HIn HnIn]; contradiction.
        + rename H into HIn; apply Resources.diff_spec in HIn as [HIn HnIn]; contradiction.
        + intros r' HIn; apply Resources.singleton_spec in HIn; subst; unfold RE.used.
          exists st; now apply RE.add_eq_o.
        + apply instantiation_well_typed with (V := V) (v := ⩽ v … ⩾) in HfRe; try assumption.
        + apply instantiation_valid in Hinst; destruct Hinst; auto; now constructor.
  (* fT_wh *)
  -
    (* clean *)
    rename H into Hvwh; inversion Hwsf; subst; move Re before W; move R before Re; move R' before R;
    move τ before R'; move α before τ; move β before α; unfold k0 in *; 
    unfold k in *; clear k k0; rename H6 into Hwi; rename H7 into Heq; 
    rename H8 into Hvα; rename H9 into Hvβ; rename H10 into Hwt;
    move Hwt after Hwsv; move Hwi after Hwt.
    (* clean *)

    apply weakening_ℜ_1  with (Re' := ⌈ S (newᵣᵪ( Re)) ⤆ (τ, <[ 𝟙 ]>) ⌉ᵣᵪ 
                                      (⌈ newᵣᵪ( Re) ⤆ (<[ 𝟙 ]>, τ) ⌉ᵣᵪ Re)) in Hwsv; 
    auto.
    -- rewrite RC.new_key_wh_spec in Hwsv.
        replace (S (S (newᵣᵪ( Re))) - newᵣᵪ( Re)) with 2 in Hwsv by lia. 
        apply IHfT with (Re :=  ⌈ S (newᵣᵪ( Re)) ⤆ (τ, <[ 𝟙 ]>) ⌉ᵣᵪ 
                              (⌈ newᵣᵪ( Re) ⤆ (<[ 𝟙 ]>, τ) ⌉ᵣᵪ Re)) (R := R') (τ' := β) in Hwt as IH;
        auto; try (now rewrite <- Hnew).
        + clear IHfT; destruct IH as [Hunsd [Hlcl [Re' [R1 [HSubRe [HSubR [Hinst' [HwtW [HInW [Husd [Hwv1' Hwt']]]]]]]]]]].

          repeat split.
          ++ intros r HIn. assert (HInV : r ∈ᵣᵦ V).
            { eapply typing_Re_R in Hwsf; eauto. eapply instantiation_in; eauto. }

            rewrite Heq in HIn; rewrite Resources.diff_spec in HIn; destruct HIn.
            apply Hunsd in H. repeat rewrite Resources.add_notin_spec in H0; destruct H0 as [Hneq [Hneq' _]].
            destruct H as [v HfV]; rewrite Hnew in Hneq,Hneq'; rewrite RE.add_neq_o in HfV; auto.
            rewrite RE.add_neq_o in HfV; auto; replace r with ([⧐ᵣ newᵣᵦ(V) ≤ 2] r) in HfV.
            * apply RE.shift_find_e_spec in HfV as HE. destruct HE as [v' Heq''].
              destruct v'; simpl in Heq''; inversion Heq''; subst; exists λ.
              eapply RE.shift_find_spec; eauto.
            * apply Resource.shift_valid_refl. eapply RE.valid_in_spec; eauto. 
          ++ intros r [HnIn HIn]; rewrite Heq in HnIn. rewrite Resources.diff_notin_spec in HnIn;
            destruct HnIn as [HnIn | HIn'].
            * simpl in Hlcl; symmetry. rewrite <- Hlcl.
              ** transitivity (([⧐ᵣᵦ (newᵣᵦ(V) + 2) ≤ newᵣᵦ( V') - (newᵣᵦ(V) + 2)] 
                            ⌈ S (newᵣᵦ( V)) ⤆ ⩽ unit … ⩾⌉ᵣᵦ (⌈ newᵣᵦ( V) ⤆ ⩽ [⧐ₜₘ{newᵣᵦ( V)} ≤ 2] i … ⩾ ⌉ᵣᵦ ([⧐ᵣᵦ newᵣᵦ( V) ≤ 2] V))) ⌊ r ⌋ᵣᵦ).
                  {
                  assert (newᵣᵦ( ⌈ S (newᵣᵦ(V)) ⤆ ⩽ unit … ⩾ ⌉ᵣᵦ 
                          (⌈ newᵣᵦ(V) ⤆ ⩽ [⧐ₜₘ {newᵣᵦ(V)} ≤ 2] i … ⩾ ⌉ᵣᵦ ([⧐ᵣᵦ newᵣᵦ(V) ≤ 2] V))) =  newᵣᵦ(V) + 2).
                  { 
                    rewrite RE.Ext.new_key_add_spec_1; try lia.
                    + apply RE.Ext.new_key_notin_spec; rewrite RE.Ext.new_key_add_spec_1; try lia.
                      ++ apply RE.shift_new_notin_spec; eauto.
                      ++ rewrite RE.shift_new_spec; lia.
                    + rewrite RE.Ext.new_key_add_spec_1; try lia.
                      ++ apply RE.shift_new_notin_spec; lia.
                      ++ rewrite RE.shift_new_spec; lia.
                  } 
                  f_equal; f_equal; f_equal; assumption.
                  }
                  {
                  rewrite RE.shift_add_notin_spec.
                  - rewrite RE.add_neq_o.
                    -- rewrite RE.shift_add_notin_spec.
                        + rewrite RE.add_neq_o.
                          ++ rewrite <- RE.shift_unfold. f_equal; f_equal.
                            apply RC.Ext.new_key_Submap_spec in HSubRe. rewrite RC.new_key_wh_spec in HSubRe.
                              rewrite Hnew in HSubRe. apply instantiation_new in Hinst'; rewrite Hinst' in HSubRe; lia.
                          ++ intro; subst. rewrite Resource.shift_valid_refl in HIn by (unfold Resource.valid; lia).
                            revert HIn; apply RE.Ext.new_key_notin_spec; lia.
                        + apply RE.shift_new_notin_spec; lia.
                    -- intro; subst. rewrite Resource.shift_valid_refl in HIn by (unfold Resource.valid; lia).
                        revert HIn; apply RE.Ext.new_key_notin_spec; lia.
                  - apply RE.Ext.new_key_notin_spec; rewrite RE.Ext.new_key_add_spec_1; auto.
                    -- apply RE.shift_new_notin_spec; lia.
                    -- rewrite RE.shift_new_spec; auto.
                  }
              ** split; auto. repeat rewrite RE.add_in_iff; repeat right.
                  eapply RE.shift_in_spec in HIn as HIn'; rewrite Resource.shift_valid_refl in HIn';
                  eauto; eapply RE.valid_in_spec in HIn; eauto. 
            * repeat rewrite Resources.add_spec in HIn'; destruct HIn' as [Heq' | [Heq' | HIn']];
              try (now inversion HIn); subst; rewrite Hnew in HIn; clear Hnew; exfalso;
              revert HIn; apply RE.Ext.new_key_notin_spec; lia.
          ++ exists Re'; exists R1.
            split.
            { 
              apply RC.Submap_Add_spec with (m := (⌈ newᵣᵪ( Re) ⤆ (<[ 𝟙 ]>, τ) ⌉ᵣᵪ Re))
                                              (x := S (newᵣᵪ( Re))) (v := (τ, <[ 𝟙 ]>)) in HSubRe; eauto.
              - apply RC.Submap_Add_spec with
                  (m := Re) (x := newᵣᵪ( Re)) (v := (<[ 𝟙 ]>, τ)) in HSubRe; eauto.
                -- apply RC.Ext.new_key_notin_spec; auto.
                -- unfold RC.Add;  reflexivity.
              - intro c. rewrite RC.add_in_iff in c; destruct c; try lia.
                revert H; apply RC.Ext.new_key_notin_spec; lia.
              - unfold RC.Add; reflexivity.
            }
            repeat split; auto.
            * unfold Resources.Subset; intros r' HIn. rewrite Heq in HIn. 
              rewrite Resources.diff_spec in HIn; destruct HIn. now apply HSubR.
            * intros r v τ0 τ' Hfi Hfi'. unfold Stock.find,Stock.add in Hfi; simpl in *.
              destruct (Resource.eq_dec r (newᵣᵦ(V))); subst.
              ** rewrite ReadStock.add_eq_o in Hfi; auto; inversion Hfi.
                 apply instantiation_new in Hinst'; rewrite <- Hinst'. rewrite <- Hnew.
                 apply weakening_ℜ_1; eauto.
                 { 
                  eapply RC.Submap_Add_spec with (x := (newᵣᵪ(Re))) 
                                                       (v := (<[ 𝟙 ]>, τ))
                                                       (m':= (⌈ newᵣᵪ( Re) ⤆ (<[ 𝟙 ]>, τ) ⌉ᵣᵪ Re)); eauto.
                  - eapply RC.Submap_Add_spec with (x := S (newᵣᵪ(Re))); eauto.
                    -- apply RC.Ext.new_key_notin_spec. rewrite RC.Ext.new_key_add_spec_1; eauto.
                       apply RC.Ext.new_key_notin_spec; lia.
                    -- unfold RC.Add; reflexivity.
                  - apply RC.Ext.new_key_notin_spec; lia.
                  - unfold RC.Add; reflexivity.
                 }
                 { 
                  eapply RC.Submap_find_spec with (x := (newᵣᵪ(Re))) (v := (<[ 𝟙 ]>, τ)) in HSubRe. 
                  - rewrite  <- Hnew in Hfi'. rewrite HSubRe in Hfi'; inversion Hfi'; now subst.
                  - rewrite RC.add_neq_o; try lia; rewrite RC.add_eq_o; auto.   
                 }
              ** rewrite ReadStock.add_neq_o in Hfi; auto. eapply HwtW; eauto.
            * rename H into HIn. rewrite Resources.diff_spec in HIn.
              destruct HIn as [HIn HnIn]. rewrite Heq in HnIn; rewrite Resources.diff_notin_spec in HnIn.
              destruct HnIn as [HnIn | HIn'].
              ** assert (r ∈ R1 \ R')%rs. { rewrite Resources.diff_spec; split; assumption. }
                  apply HInW in H as [HInW1 HnInV]. rewrite <- Stock.to_RS_in_spec in *.
                  rewrite Stock.add_spec; simpl; auto.
              ** apply Stock.to_RS_in_spec. apply Stock.add_spec; auto; repeat rewrite Resources.add_spec in HIn'; 
                  destruct HIn' as [Heq' | [Heq' | HIn']]; try (now inversion HIn'); subst; 
                  apply instantiation_new in Hinst; rewrite <- Hinst; simpl; auto.
            * rename H into HIn. rewrite Resources.diff_spec in HIn.
              destruct HIn as [HIn HnIn]. rewrite Heq in HnIn; rewrite Resources.diff_notin_spec in HnIn.
              destruct HnIn as [HnIn | HIn'].
              ** assert (r ∈ R1 \ R')%rs. { rewrite Resources.diff_spec; split; assumption. }
                  apply HInW in H as [HInW1 HnInV]; intro c; apply HnInV. 
                  repeat rewrite RE.add_in_iff; repeat right.
                  eapply RE.shift_in_spec in c as c'; rewrite Resource.shift_valid_refl in c'; eauto.
                  eapply RE.valid_in_spec in c; eauto.
              ** rewrite Hnew in HIn'. repeat rewrite Resources.add_spec in HIn'; 
                  destruct HIn' as [Heq' | [Heq' | HIn']]; try (inversion HIn'); subst; 
                  apply RE.Ext.new_key_notin_spec; lia.
        + replace 2 with (1 + 1) by lia. rewrite Cell.shift_unfold.
          replace ((newᵣᵦ(V)) + 1) with (S (newᵣᵦ(V))) by lia. 

          assert (RE.eq ([⧐ᵣᵦ (newᵣᵦ(V)) ≤ 1 + 1] V) ([⧐ᵣᵦ S (newᵣᵦ(V)) ≤ 1] [⧐ᵣᵦ (newᵣᵦ(V)) ≤ 1] V)).
          { rewrite RE.shift_unfold; replace ((newᵣᵦ(V)) + 1) with (S (newᵣᵦ(V))) by lia; reflexivity. }
          rewrite H.
      
          assert (RE.eq (⌈ (newᵣᵦ(V)) ⤆ [⧐ᵣₓ S (newᵣᵦ(V)) ≤ 1] [⧐ᵣₓ (newᵣᵦ(V)) ≤ 1] ⩽ i … ⩾ ⌉ᵣᵦ ([⧐ᵣᵦ S (newᵣᵦ(V)) ≤ 1] [⧐ᵣᵦ (newᵣᵦ(V)) ≤ 1] V))
                              ([⧐ᵣᵦ S (newᵣᵦ(V)) ≤ 1] (⌈ (newᵣᵦ(V)) ⤆ [⧐ᵣₓ (newᵣᵦ(V)) ≤ 1] ⩽ i … ⩾ ⌉ᵣᵦ ([⧐ᵣᵦ (newᵣᵦ(V)) ≤ 1] V)))).
          { 
            rewrite RE.shift_add_notin_spec.
            - replace ([⧐ᵣ S (newᵣᵦ(V)) ≤ 1] (newᵣᵦ(V))) with (newᵣᵦ(V)); try reflexivity.
              rewrite Resource.shift_valid_refl; auto; unfold Resource.valid; lia.
            - apply RE.shift_new_notin_spec; lia.
          }
          rewrite H0. clear H H0.
          eapply (itfT_init 
                    (⌈ newᵣᵪ( Re) ⤆ (<[ 𝟙 ]>, τ) ⌉ᵣᵪ Re)
                    (⌈ S (newᵣᵪ( Re)) ⤆ (τ, <[ 𝟙 ]>) ⌉ᵣᵪ (⌈ newᵣᵪ( Re) ⤆ (<[ 𝟙 ]>, τ) ⌉ᵣᵪ Re))
                    (⌈ newᵣᵦ( V) ⤆ [⧐ᵣₓ newᵣᵦ( V) ≤ 1] ⩽ i … ⩾ ⌉ᵣᵦ ([⧐ᵣᵦ newᵣᵦ( V) ≤ 1] V))
                    (⌈ S (newᵣᵦ( V)) ⤆ ⩽ unit … ⩾ ⌉ᵣᵦ ([⧐ᵣᵦ S (newᵣᵦ( V)) ≤ 1] ⌈ newᵣᵦ( V) ⤆ [⧐ᵣₓ newᵣᵦ( V) ≤ 1] ⩽ i … ⩾ ⌉ᵣᵦ ([⧐ᵣᵦ newᵣᵦ( V) ≤ 1] V)))
                    τ <[𝟙]> <[unit]>); eauto; try now constructor.
          ++ eapply (itfT_init Re (⌈ newᵣᵪ( Re) ⤆ (<[ 𝟙 ]>, τ) ⌉ᵣᵪ Re)
                                  V (⌈ newᵣᵦ( V) ⤆ [⧐ᵣₓ newᵣᵦ( V) ≤ 1] ⩽ i … ⩾ ⌉ᵣᵦ ([⧐ᵣᵦ newᵣᵦ( V) ≤ 1] V))
                                  <[𝟙]> τ); eauto; try constructor.
          ++ rewrite RC.Ext.new_key_add_spec_1; auto.
              * apply well_typed_implies_valid in Hwi; auto.
                destruct Hwi; apply Typ.valid_weakening with (k := newᵣᵪ( Re)); auto.
              * apply RC.Ext.new_key_notin_spec; auto.
          ++ unfold RC.Add;
            rewrite RC.Ext.new_key_add_spec_1; auto; try reflexivity.
            apply RC.Ext.new_key_notin_spec; auto.
          ++ unfold RE.Add;
            rewrite RE.Ext.new_key_add_spec_1; auto; try reflexivity.
            * apply RE.shift_new_notin_spec; lia.
            * rewrite RE.shift_new_spec; auto.
    -- apply RC.Submap_add_spec_1.
        + apply RC.Ext.new_key_notin_spec; rewrite RC.Ext.new_key_add_spec_1;
          auto. apply RC.Ext.new_key_notin_spec; lia.
        + apply RC.Submap_add_spec_1.
          ++ apply RC.Ext.new_key_notin_spec; lia.
          ++ apply RC.Submap_refl.
Qed.


(**
  *** General proof of preservation of typing value through functional transition

  This proof is almost the same as above with the difference that the signal function expression
  is a value. Knowing that we can state that if all expression on the environment and the stream 
  expression can be normalised then the output expressions in V' and the output stream expression
  can also be normalised.
  
  _This proof stands only if we can find a property that state that all arrow functions foundable in the signal function expression have all possible applications normalisable_. 

*)
Theorem functional_preserves_typing_value : 
  forall (Re : ℜ) (V V' : 𝓥) (W : 𝐖) (sv sv' sf sf' : Λ) (τ τ' : Τ) (R : resources),

    ∅ᵥᵪ ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) ->
    value(sf) ->
    ∅ᵥᵪ ⋅ Re ⊫ sv ∈ τ -> 
    ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V' ; sv' ; sf' ; W ⪢ -> 
    Instᵣₜ(Re,V) ->
    RE.halts (newᵣᵦ(V)) V ->
    halts (newᵣᵪ(Re)) sv ->


    (forall (r : resource), (r ∈ R)%rs -> RE.unused r V) /\
    (forall (r : resource), (r ∉ R)%rs /\ (r ∈ᵣᵦ V) -> 
                ([⧐ᵣᵦ (newᵣᵦ(V)) ≤ ((newᵣᵦ(V')) - (newᵣᵦ(V)))] V) ⌊r⌋ᵣᵦ = V' ⌊r⌋ᵣᵦ) /\

    exists (Re' : ℜ) (R' : resources), 
      Re ⊆ᵣᵪ Re'     /\ 
      (R ⊆ R')%rs    /\
      Instᵣₜ(Re',V') /\

      RE.halts (newᵣᵦ(V')) V' /\
      halts (newᵣᵪ(Re')) sv' /\

      (forall (r : resource) (v : Λ) (τ τ' : Τ), 
                    W ⌈ r ⩦ v ⌉ₛₖ -> Re' ⌈r ⩦ (τ',τ)⌉ᵣᵪ -> ∅ᵥᵪ ⋅ Re' ⊫ v ∈ τ) /\
      (forall (r : resource), (r ∈ (R' \ R))%rs -> (r ∈ (Stock.to_RS W))%rs /\ (r ∉ᵣᵦ V)) /\
      (forall (r : resource), (r ∈ R')%rs -> RE.used r V') /\
      ∅ᵥᵪ ⋅ Re' ⊫ sv' ∈ τ' /\
      ∅ᵥᵪ ⋅ Re' ⊫ sf' ∈ (τ ⟿ τ' ∣ R').
Proof.
  intros Re V V' W sv sv' sf sf' τ τ' R Hwsf Hvsf Hwsv fT; revert Re R τ τ' Hwsf Hvsf Hwsv;
  induction fT; intros Re R α β Hwsf Hvsf Hwsv Hinst HltV Hltst;

  apply instantiation_valid in Hinst as HvRe; destruct HvRe as [HvRe HvV];
  apply instantiation_new in Hinst as Hnew;

  move HvRe before Hinst; move HvV before HvRe; move Hnew before Hinst.
  (* fT_eT *)
  - apply evaluate_not_value in H; contradiction. 
  (* fT_arr *)
  - 
    (* clean *)
    inversion Hwsf; subst; rename H4 into Hwt; clear Hwsf H; move Hwt after Hwsv.
    (* clean *)

    repeat split.
    -- intros r HIn; inversion HIn.
    -- intros r [HnIn HIn]; replace (newᵣᵦ(V) - newᵣᵦ(V)) with 0 by lia.
        now rewrite RE.shift_refl.
    -- exists Re; exists ∅ᵣₛ; split; try reflexivity.
        repeat split; auto; try reflexivity; try constructor; auto.
        + admit. 
          (* 
            Add a new property that state that every arrow block has a function
            that finished for all normalisable well-typed expression 
          *)
        + intros; inversion H.
        + inversion H.
        + intros r HIn; inversion HIn.
        + apply wt_app with (τ2 := α); assumption.
  (* fT_first *)
  -
    (* clean *)
    clear H; inversion Hwsf; subst; move Re before W; move R before Re; move τ1 before τ;
    move τ2 before τ1; clear Hwsf; rename H5 into Hwt; rename H8 into Hvτ;
    move Hwt after Hwsv; move Hvτ before Hwsv; rename H0 into HmeT; rename fT into HfT;
    move HfT after IHfT; move HmeT after HfT.
    (* clean *)

    rewrite <- Hnew in HmeT; apply multi_preserves_typing with (t' := <[⟨v1,v2⟩]>) in Hwsv; 
    try assumption.

    (* clean *)
    inversion Hwsv; subst; rename H4 into Hwv1; rename H6 into Hwv2; move Hwv1 before Hwt;
    move Hwv2 before Hwv1; clear Hwsv; move HvRe after Hvτ; inversion Hvsf; subst;
    clear Hvsf; rename H0 into Hvsf.
    (* clean *)

    rewrite multi_preserves_halting in Hltst; eauto. rewrite halts_pair in Hltst.
    destruct Hltst as [Hltv1 Hltv2].
    apply IHfT with (R := R) (τ' := τ2) in Hwv1 as IH; try assumption.

    clear IHfT; 
    destruct IH as [Hunsd [Hlcl [Re' [R' [HSubRe [HSubR [Hinst' [HltV' [Hltv1' 
                            [HwtW [HInW [Husd [Hwv1' Hwt']]]]]]]]]]]]].

    (* clean *)
    move Re' before Re; move R' before R; move Hwv1' before Hwv1; clear Hwv1;
    move Hwt' before Hwt; clear Hwt; move Hinst' before Hinst; move Hunsd before Husd.
    (* clean *)

    apply instantiation_new in Hinst' as Hnew'; move Hnew' before Hnew.

    repeat split; auto.
    exists Re'; exists R'; repeat split; try assumption; try (destruct HSubRe; assumption);
    try (now apply HInW).
    -- rewrite halts_pair; split; auto. rewrite <- Hnew; rewrite <- Hnew'.
       apply halts_weakening; auto. now apply RC.Ext.new_key_Submap_spec.
    -- constructor; try assumption; rewrite <- Hnew; rewrite <- Hnew'; 
        apply weakening_ℜ_1; auto.
    -- apply wt_first; try assumption.
        apply Typ.valid_weakening with (k := newᵣᵪ(Re)); try assumption.
        apply RC.Ext.new_key_Submap_spec in HSubRe; assumption.
  (* fT_comp *)
  -
    (* clean *)
    inversion H; subst; inversion Hwsf; subst; apply Resources.eq_leibniz in H10; subst;
    clear Hwsf; move Re before W'; move R1 before Re; move R2 before R1; 
    move α before R2; move β before α; move τ before β; rename fT1 into HfT1;
    move HfT1 after IHfT2; rename fT2 into HfT2; move HfT2 after HfT1.
    rename H9 into Hwt1; rename H11 into Hwt2; rename H12 into HEmp.
    rename H3 into Hvt2; clear H2; move Hwt1 after Hwsv; move Hwt2 before Hwt1; move Hvt2 after Hwt2.
    inversion Hvsf; subst; clear Hvsf; rename H2 into Hvlt1; rename H3 into Hvlt2.
    (* clean *)

    apply IHfT1 with (R := R1) (τ' := τ) in Hwsv as IH1; try assumption;
    try (intros; apply Hunsd; rewrite Resources.union_spec; now left).
    clear IHfT1; destruct IH1 as [Hunsd1 [Hlcl1 [Re' [R1' [HSubRe [HSubR1 
                                    [Hinst' [HltV' [Hltst' [HwtW [HInW [Husd1 [Hwsv' Hwt1']]]]]]]]]]]]].

    (* clean *)
    move Re' before Re; move R1' before R1; move Hwsv' before Hwsv;
    move Hwt1' before Hwt1; move Hunsd1 after HInW; move Hinst' before Hinst.
    (* clean *)

    apply instantiation_new in Hinst' as Hnew'; move Hnew' before Hnew.
    apply weakening_ℜ_1 with (Re' := Re') in Hwt2 as Hwt2'; auto.
    apply IHfT2 with (R := R2) (τ' := β) in Hwsv' as IH2; try assumption;
    try (rewrite <- Hnew; now rewrite <- Hnew');
    try (now apply Term.shift_value_iff).

    destruct IH2 as [Hunsd2 [Hlcl2 [Re'' [R2' [HSubRe' [HSubR2 [Hinst'' 
                                              [HltV'' [Hltst'' [HwtW' [HInW'  [Husd2 [Hwsv'' Hwt2'']]]]]]]]]]]]].

    (* clean *)
    move Re'' before Re'; move R2' before R2; move Hwsv'' before Hwsv';
    move Hwt2' before Hwt2; move Hwt2'' before Hwt2'; move Hunsd2 before Hunsd1; move Hinst'' before Hinst';
    clear IHfT2; move HSubRe' before HSubRe; move HSubR2 before HSubR1; move HInW' before HInW;
    move Husd2 before Husd1; move Hlcl2 before Hlcl1.
    (* clean *)

    assert (HEmp' : (∅ᵣₛ = R1' ∩ R2')%rs).
    {
      symmetry; apply Resources.empty_is_empty_1; unfold Resources.Empty.
      intro r'; intro HIn; rewrite Resources.inter_spec in HIn; 
      destruct HIn as [HIn1 HIn2].
      destruct (Resources.In_dec r' R1); destruct (Resources.In_dec r' R2).
      -- symmetry in HEmp; apply Resources.empty_is_empty_2 in HEmp.
          unfold Resources.Empty in HEmp; apply (HEmp r').
          rewrite Resources.inter_spec; split; auto.
      -- assert (HnInV' : r' ∉ᵣᵦ V'). 
          { apply HInW'; rewrite Resources.diff_spec; split; assumption. }
          assert (HInV1 : r' ∈ᵣᵦ V).
          { 
          apply Hunsd1 in i; destruct i as [v HfV].  
          rewrite RE.in_find; intro c; rewrite HfV in *; inversion c.
          }

          apply well_typed_implies_valid in Hwt1 as Hv; eauto; destruct Hv as [Hvt1 _].
          apply well_typed_implies_valid in Hwsv as Hv; eauto; destruct Hv as [Hvsv _].
          rewrite Hnew in Hvt1,Hvsv.
          eapply functional_preserves_keys in HInV1; eauto.
          
      -- assert (HInV1 : r' ∈ᵣᵦ V).
          {
          eapply typing_Re_R in i as HInRe; eauto.
          eapply instantiation_in in HInRe; eauto. 
          }

          revert HInV1; apply HInW; rewrite Resources.diff_spec; split; assumption.

      -- assert ((r' ∈ Stock.to_RS W)%rs /\ r' ∉ᵣᵦ V).
          { apply HInW; rewrite Resources.diff_spec; split; assumption. }
          destruct H0 as [HInW1 HnInV].
          assert (r' ∉ᵣᵦ V').
          { apply HInW'; rewrite Resources.diff_spec; split; assumption. }
          
          apply well_typed_implies_valid in Hwt1 as Hv; eauto; destruct Hv as [Hvt1 _].
          apply well_typed_implies_valid in Hwsv as Hv; eauto; destruct Hv as [Hvsv _].
          rewrite Hnew in Hvt1,Hvsv.
          
          apply Stock.to_RS_in_spec in HInW1.
          eapply consistency_V_W in HfT1; eauto; simpl in *; destruct HfT1; auto.
      }

      move HEmp' before HEmp. repeat split.
      -- intros r HIn; rewrite Resources.union_spec in HIn; destruct HIn; auto.
          assert (HInV : r ∈ᵣᵦ V).
          { eapply typing_Re_R in H0 as HInRe; eauto. eapply instantiation_in in HInRe; eauto. }

          assert (HnInR1 : (r ∉ R1)%rs).
          { 
            intro; symmetry in HEmp; apply Resources.empty_is_empty_2 in HEmp; 
            apply (HEmp r); rewrite Resources.inter_spec; now split.
          }

          destruct HInV as [v HfV]; apply RE.find_1 in HfV; destruct v.
          + now exists λ.
          + assert (r ∈ᵣᵦ V). { exists (⩽ … λ ⩾); now apply RE.find_2. }
          
            apply RE.shift_find_spec with (lb := newᵣᵦ(V)) (k := newᵣᵦ(V') - newᵣᵦ(V)) in HfV.
            rewrite Resource.shift_valid_refl in HfV.
            ++ rewrite Hlcl1 in HfV; try split; auto. apply Hunsd2 in H0; destruct H0; rewrite H0 in *;
              inversion HfV.
            ++ eapply RE.valid_in_spec in H1; eauto.
      -- intros r [HnIn HIn]; rewrite Resources.union_notin_spec in HnIn; destruct HnIn as [HnIn1 HnIn2].

          assert (HIn' : r ∈ᵣᵦ V').
          { 
            apply well_typed_implies_valid in Hwt1 as Hv; eauto; destruct Hv as [Hvt1 _].
            apply well_typed_implies_valid in Hwsv as Hv; eauto; destruct Hv as [Hvsv _].
            rewrite Hnew in Hvt1,Hvsv.
            eapply functional_preserves_keys; eauto. 
          }

          assert ([⧐ᵣᵦ newᵣᵦ( V) ≤ newᵣᵦ( V'') - newᵣᵦ( V)] V = [⧐ᵣᵦ newᵣᵦ(V') ≤ newᵣᵦ( V'') - newᵣᵦ(V')]([⧐ᵣᵦ newᵣᵦ(V) ≤ newᵣᵦ(V') - newᵣᵦ(V)] V))%re.
          { 
            apply RC.Ext.new_key_Submap_spec in HSubRe,HSubRe'.
            apply instantiation_new in Hinst,Hinst',Hinst''.
            rewrite Hinst,Hinst' in HSubRe; rewrite Hinst',Hinst'' in HSubRe'.
            rewrite RE.shift_unfold_1; auto; reflexivity. 
          }

          rewrite H0; rewrite <- Hlcl2; try (split; auto).
          destruct HIn as [v HfV]; apply RE.find_1 in HfV.
          apply RE.shift_find_spec with (lb := newᵣᵦ(V)) (k := newᵣᵦ(V') - newᵣᵦ(V)) in HfV as HfV'.

          apply RE.valid_find_spec with (lb := newᵣᵦ(V)) in HfV as Hv; auto.
          destruct Hv as [Hvr _]. rewrite Resource.shift_valid_refl in HfV'; auto.
      
          apply RE.shift_find_spec with (lb := newᵣᵦ(V')) (k := newᵣᵦ(V'') - newᵣᵦ(V')) in HfV' as HfV''.

          apply instantiation_valid in Hinst' as Hv; destruct Hv as [_ HvV'].
          apply RE.valid_in_spec with (lb := newᵣᵦ(V')) in HIn' as Hv; auto.
          rewrite Resource.shift_valid_refl in HfV''; auto. rewrite HfV''. symmetry.

          rewrite <- Resource.shift_valid_refl with (lb := newᵣᵦ(V')) (t := r) (k := newᵣᵦ(V'') - newᵣᵦ(V')); auto.
          apply RE.shift_find_spec. rewrite <- Hlcl1.
          + rewrite <- Resource.shift_valid_refl with (lb := newᵣᵦ(V)) (t := r) (k := newᵣᵦ(V') - newᵣᵦ(V)); auto.
            now apply RE.shift_find_spec.
          + split; auto. apply RE.in_find; intro c; rewrite HfV in *; inversion c.         
      -- exists Re''; exists (R1' ∪ R2')%rs; split; try (now transitivity Re'); repeat split; auto.
          + unfold Resources.Subset; intros r HIn.
            rewrite Resources.union_spec in *; destruct HIn as [HIn | HIn]; auto.
          + intros r v τ0 τ' Hfi HfiRe. apply Stock.union_find_spec in Hfi; destruct Hfi.
            ++ assert (([⧐ₛₖ newᵣᵦ( V') ≤ newᵣᵦ( V'') - newᵣᵦ( V')] W) 
                            ⌈ ([⧐ᵣ newᵣᵦ( V') ≤ newᵣᵦ( V'') - newᵣᵦ( V')] r) ⩦ v ⌉ₛₖ). 
              {
                assert (r ∈ᵣₖ ([⧐ᵣₖ newᵣᵦ( V') ≤ newᵣᵦ( V'') - newᵣᵦ( V')] (fst W))).
                { unfold Stock.find,Stock.shift in *; simpl in *. exists v; now apply ReadStock.find_2. }
                apply functional_preserves_valid in HfT1 as H3; auto.
                - destruct H3 as [_ [_ [_ [H3 _]]]]. destruct H3.
                  rewrite ReadStock.valid_in_spec_1 in H1; auto.
                  eapply ReadStock.valid_in_spec with (lb := newᵣᵦ(V')) in H1; auto.
                  rewrite Resource.shift_valid_refl; auto.
                - apply well_typed_implies_valid in Hwsv; auto.
                  destruct Hwsv; rewrite <- Hnew; assumption.
                - apply well_typed_implies_valid in Hwt1; auto.
                  destruct Hwt1; rewrite <- Hnew; assumption.
              }
              unfold Stock.find,Stock.shift in H1; simpl in *. apply ReadStock.shift_find_e_spec in H1 as H1'.
              destruct H1'; subst. apply ReadStock.shift_find_spec in H1.
              eapply HwtW in H1.
              * rewrite <- Hnew'. 
                apply instantiation_new in Hinst''. rewrite <- Hinst''.
                apply weakening_ℜ_1; eauto.
                apply instantiation_valid in Hinst'. destruct Hinst'; auto.
              * assert (r ∈ₛₖ W). { unfold Stock.In; left. exists x; now apply ReadStock.find_2. }
                eapply consistency_V_W with (r := r) in HfT1 as H3; auto.
                ** destruct H3. rewrite <- instantiation_in with (Re := Re') in H4; auto.
                    destruct H4. apply RC.find_1 in H4. 
                    apply RC.Submap_find_spec with (m' := Re'') in H4 as H4'; auto.
                    rewrite HfiRe in H4'; inversion H4'; subst; eauto.
                ** apply well_typed_implies_valid in Hwsv; auto.
                    destruct Hwsv; rewrite <- Hnew; assumption.
                ** apply well_typed_implies_valid in Hwt1; auto.
                    destruct Hwt1; rewrite <- Hnew; assumption. 
            ++ eapply HwtW'; eauto.
          + rename H0 into HIn. rewrite Resources.diff_spec in HIn; destruct HIn as [HIn HnIn];
            rewrite Resources.union_notin_spec in HnIn; destruct HnIn as [HnIn1 HnIn2];
            rewrite Resources.union_spec in HIn; destruct HIn as [HIn | HIn].
            ++ assert ((r ∈ Stock.to_RS W)%rs /\ r ∉ᵣᵦ V). { apply HInW; rewrite Resources.diff_spec; now split. }
              destruct H0.
              
              
              rewrite Stock.to_RS_union_spec; left.
              apply instantiation_valid in Hinst' as Hv; destruct Hv as [_ HvV'].

              assert (r ∈ᵣᵦ V'). 
              {
                apply well_typed_implies_valid in Hwt1 as Hv; eauto; destruct Hv as [Hvt1 _].
                apply well_typed_implies_valid in Hwsv as Hv; eauto; destruct Hv as [Hvsv _].
                rewrite Hnew in Hvt1,Hvsv.

                apply Stock.to_RS_in_spec in H0. eapply consistency_V_W in H0; eauto; destruct H0; auto.
              }

              eapply RE.valid_in_spec in H2; eauto.
              rewrite <- Resource.shift_valid_refl with (lb := newᵣᵦ(V')) (k := newᵣᵦ(V'') - newᵣᵦ(V')) (t := r); auto.
              rewrite <- Stock.to_RS_in_spec in *. now apply Stock.shift_in_spec.
            ++ apply Stock.to_RS_union_spec; right. 
              apply HInW'; rewrite Resources.diff_spec; split; assumption.
          + rename H0 into HIn. rewrite Resources.diff_spec in HIn; destruct HIn as [HIn HnIn];
            rewrite Resources.union_notin_spec in HnIn; destruct HnIn as [HnIn1 HnIn2];
            rewrite Resources.union_spec in HIn; destruct HIn as [HIn | HIn].
            ++ apply HInW; rewrite Resources.diff_spec; split; auto. 
            ++ intro HnInV. assert (HnInV' : r ∉ᵣᵦ V').
              { apply HInW'; rewrite Resources.diff_spec; split; assumption. }
              apply HnInV'. 
              apply well_typed_implies_valid in Hwt1 as Hv; eauto; destruct Hv as [Hvt1 _].
              apply well_typed_implies_valid in Hwsv as Hv; eauto; destruct Hv as [Hvsv _].
              rewrite Hnew in Hvt1,Hvsv.
              eapply functional_preserves_keys; eauto. 
          + intros r HIn; rewrite Resources.union_spec in HIn; destruct HIn as [HIn | HIn].

            ++ assert (HnIn' : (r ∉ R2')%rs). 
              { 
                intro. symmetry in HEmp'; apply Resources.empty_is_empty_2 in HEmp'; 
                apply (HEmp' r); rewrite Resources.inter_spec; split; auto. 
              }

              apply Husd1 in HIn as HuV'; destruct HuV' as [v HfV'].
              apply RE.shift_find_spec with (lb := newᵣᵦ(V')) (k := newᵣᵦ(V'') - newᵣᵦ(V')) in HfV' as HfV''.

              apply instantiation_valid in Hinst' as Hv; destruct Hv as [_ HvV'].
              rewrite Resource.shift_valid_refl in HfV''; simpl in *.
          
              * exists <[[⧐ₜₘ {newᵣᵦ( V')} ≤ {newᵣᵦ( V'') - newᵣᵦ( V')}] v]>. rewrite <- HfV'';
                symmetry; apply Hlcl2; split; auto; apply RE.in_find;
                intro c; rewrite HfV' in c; inversion c.
              * eapply RE.valid_find_spec in HfV'; eauto; now destruct HfV'.
            ++ apply Husd2 in HIn as HfV'; destruct HfV' as [v HfV']; now exists v.
          + apply wt_comp with (R1 := R1') (R2 := R2') (τ := τ); try reflexivity; auto.
            apply instantiation_new in Hinst'' as Hnew''; rewrite <- Hnew'; rewrite <- Hnew''.
            apply instantiation_valid in Hinst' as HvRe'; destruct HvRe' as [HvRe' _].
            apply weakening_ℜ_1; auto.
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
        + replace (newᵣᵦ(V) - newᵣᵦ(V)) with 0 by lia; now rewrite RE.shift_refl.
        + apply RE.in_find; intro c; rewrite HfV in c; inversion c.
    -- exists Re; exists \{{r}}; split; try reflexivity. repeat split; try reflexivity.
        + eapply itfT_update; eauto.
          ++ apply RE.in_find; intro c; rewrite HfV in c; inversion c.
          ++ unfold RE.Add; reflexivity.
        + apply RE.halts_add_spec; split.
          ++ rewrite RE.Ext.new_key_add_spec_3; simpl.
             * now rewrite <- Hnew.
             * exists (⩽ v … ⩾); now apply RE.find_2.
          ++ rewrite RE.Ext.new_key_add_spec_3; auto. exists (⩽ v … ⩾); now apply RE.find_2.
        + rewrite Hnew; destruct (HltV r (⩽ v … ⩾)); auto.
          now exists x. 
        + intros; inversion H.
        + rename H into HIn; apply Resources.diff_spec in HIn as [HIn HnIn]; contradiction.
        + rename H into HIn; apply Resources.diff_spec in HIn as [HIn HnIn]; contradiction.
        + intros r' HIn; apply Resources.singleton_spec in HIn; subst; unfold RE.used.
          exists st; now apply RE.add_eq_o.
        + apply instantiation_well_typed with (V := V) (v := ⩽ v … ⩾) in HfRe; try assumption.
        + apply instantiation_valid in Hinst; destruct Hinst; auto; now constructor.
  (* fT_wh *)
  -
    (* clean *)
    rename H into Hvwh; inversion Hwsf; subst; move Re before W; move R before Re; move R' before R;
    move τ before R'; move α before τ; move β before α; unfold k0 in *; 
    unfold k in *; clear k k0; rename H6 into Hwi; rename H7 into Heq; 
    rename H8 into Hvα; rename H9 into Hvβ; rename H10 into Hwt;
    move Hwt after Hwsv; move Hwi after Hwt.
    inversion Hvsf; subst; clear Hvsf; rename H1 into Hvli; rename H2 into Hvl2.
    (* clean *)

    assert (Heqnk : (RE.Ext.new_key
      (@RE.Raw.add Cell.t (RE.Ext.new_key V) (Cell.shift (RE.Ext.new_key V) 2 (Cell.inp i))
      (RE.shift (RE.Ext.new_key V) 2 V))) = S (RE.Ext.new_key V)).
    { 
      rewrite RE.Ext.new_key_add_spec_1; auto.
      - apply RE.shift_new_notin_spec; auto.
      - rewrite RE.shift_new_spec; lia. 
    }

    assert (Heqnk' : (RE.Ext.new_key
    (@RE.Raw.add Cell.raw (S (RE.Ext.new_key V)) (Cell.inp Term.tm_unit)
       (@RE.Raw.add Cell.t (RE.Ext.new_key V) (Cell.shift (RE.Ext.new_key V) 2 (Cell.inp i))
          (RE.shift (RE.Ext.new_key V) 2 V)))) = S (S (RE.Ext.new_key V))).
    {
      rewrite RE.Ext.new_key_add_spec_1; auto.
      - apply RE.Ext.new_key_notin_spec; rewrite Heqnk; auto.
      - rewrite Heqnk; lia.
    }

    apply weakening_ℜ_1  with (Re' := ⌈ S (newᵣᵪ( Re)) ⤆ (τ, <[ 𝟙 ]>) ⌉ᵣᵪ 
                                      (⌈ newᵣᵪ( Re) ⤆ (<[ 𝟙 ]>, τ) ⌉ᵣᵪ Re)) in Hwsv; 
    auto.
    -- rewrite RC.new_key_wh_spec in Hwsv.
        replace (S (S (newᵣᵪ( Re))) - newᵣᵪ( Re)) with 2 in Hwsv by lia. 
        apply IHfT with (Re :=  ⌈ S (newᵣᵪ( Re)) ⤆ (τ, <[ 𝟙 ]>) ⌉ᵣᵪ 
                              (⌈ newᵣᵪ( Re) ⤆ (<[ 𝟙 ]>, τ) ⌉ᵣᵪ Re)) (R := R') (τ' := β) in Hwt as IH;
        auto; try (now rewrite <- Hnew).
        + clear IHfT; 
          destruct IH as [Hunsd [Hlcl [Re' [R1 [HSubRe [HSubR [Hinst' 
                                    [HltV' [Hltv1' [HwtW [HInW [Husd [Hwv1' Hwt']]]]]]]]]]]]].

          rewrite Heqnk' in *; repeat split.
          ++ intros r HIn. assert (HInV : r ∈ᵣᵦ V).
            { eapply typing_Re_R in Hwsf; eauto. eapply instantiation_in; eauto. }

            rewrite Heq in HIn; rewrite Resources.diff_spec in HIn; destruct HIn.
            apply Hunsd in H. repeat rewrite Resources.add_notin_spec in H0; destruct H0 as [Hneq [Hneq' _]].
            destruct H as [v HfV]; rewrite Hnew in Hneq,Hneq'; rewrite RE.add_neq_o in HfV; auto.
            rewrite RE.add_neq_o in HfV; auto; replace r with ([⧐ᵣ newᵣᵦ(V) ≤ 2] r) in HfV.
            * apply RE.shift_find_e_spec in HfV as HE. destruct HE as [v' Heq''].
              destruct v'; simpl in Heq''; inversion Heq''; subst; exists λ.
              eapply RE.shift_find_spec; eauto.
            * apply Resource.shift_valid_refl. eapply RE.valid_in_spec; eauto. 
          ++ intros r [HnIn HIn]; rewrite Heq in HnIn. rewrite Resources.diff_notin_spec in HnIn;
            destruct HnIn as [HnIn | HIn'].
            * symmetry. rewrite <- Hlcl.
              ** transitivity (([⧐ᵣᵦ (newᵣᵦ(V) + 2) ≤ newᵣᵦ( V') - (newᵣᵦ(V) + 2)] 
                            ⌈ S (newᵣᵦ( V)) ⤆ ⩽ unit … ⩾⌉ᵣᵦ (⌈ newᵣᵦ( V) ⤆ [⧐ᵣₓ (newᵣᵦ(V)) ≤ 2] ⩽ i … ⩾ ⌉ᵣᵦ ([⧐ᵣᵦ newᵣᵦ(V) ≤ 2] V))) ⌊ r ⌋ᵣᵦ).
                  { f_equal; f_equal; try lia. }
                  {
                  rewrite RE.shift_add_notin_spec.
                  - rewrite RE.add_neq_o.
                    -- rewrite RE.shift_add_notin_spec.
                        + rewrite RE.add_neq_o.
                          ++ rewrite <- RE.shift_unfold. f_equal; f_equal.
                            apply RC.Ext.new_key_Submap_spec in HSubRe. rewrite RC.new_key_wh_spec in HSubRe.
                              rewrite Hnew in HSubRe. apply instantiation_new in Hinst'; rewrite Hinst' in HSubRe; lia.
                          ++ intro; subst. rewrite Resource.shift_valid_refl in HIn by (unfold Resource.valid; lia).
                            revert HIn; apply RE.Ext.new_key_notin_spec; lia.
                        + apply RE.shift_new_notin_spec; lia.
                    -- intro; subst. rewrite Resource.shift_valid_refl in HIn by (unfold Resource.valid; lia).
                        revert HIn; apply RE.Ext.new_key_notin_spec; lia.
                  - apply RE.Ext.new_key_notin_spec. rewrite Heqnk; auto.
                  }
              ** split; auto. repeat rewrite RE.add_in_iff; repeat right.
                  eapply RE.shift_in_spec in HIn as HIn'; rewrite Resource.shift_valid_refl in HIn';
                  eauto; eapply RE.valid_in_spec in HIn; eauto. 
            * repeat rewrite Resources.add_spec in HIn'; destruct HIn' as [Heq' | [Heq' | HIn']];
              try (now inversion HIn); subst; rewrite Hnew in HIn; clear Hnew; exfalso;
              revert HIn; apply RE.Ext.new_key_notin_spec; lia.
          ++ exists Re'; exists R1.
            split.
            { 
              apply RC.Submap_Add_spec with (m := (⌈ newᵣᵪ( Re) ⤆ (<[ 𝟙 ]>, τ) ⌉ᵣᵪ Re))
                                              (x := S (newᵣᵪ( Re))) (v := (τ, <[ 𝟙 ]>)) in HSubRe; eauto.
              - apply RC.Submap_Add_spec with
                  (m := Re) (x := newᵣᵪ( Re)) (v := (<[ 𝟙 ]>, τ)) in HSubRe; eauto.
                -- apply RC.Ext.new_key_notin_spec; auto.
                -- unfold RC.Add; reflexivity.
              - intro c. rewrite RC.add_in_iff in c; destruct c; try lia.
                revert H; apply RC.Ext.new_key_notin_spec; lia.
              - unfold RC.Add; reflexivity.
            }
            repeat split; auto.
            * unfold Resources.Subset; intros r' HIn. rewrite Heq in HIn. 
              rewrite Resources.diff_spec in HIn; destruct HIn. now apply HSubR.
            * intros r v τ0 τ' Hfi Hfi'. unfold Stock.find,Stock.add in Hfi; simpl in *.
              destruct (Resource.eq_dec r (newᵣᵦ(V))); subst.
              ** rewrite ReadStock.add_eq_o in Hfi; auto; inversion Hfi.
                apply instantiation_new in Hinst'; rewrite <- Hinst'. rewrite <- Hnew.
                apply weakening_ℜ_1; eauto.
                { 
                  eapply RC.Submap_Add_spec with (x := (newᵣᵪ(Re))) 
                                                      (v := (<[ 𝟙 ]>, τ))
                                                      (m':= (⌈ newᵣᵪ( Re) ⤆ (<[ 𝟙 ]>, τ) ⌉ᵣᵪ Re)); eauto.
                  - eapply RC.Submap_Add_spec with (x := S (newᵣᵪ(Re))); eauto.
                    -- apply RC.Ext.new_key_notin_spec. rewrite RC.Ext.new_key_add_spec_1; eauto.
                      apply RC.Ext.new_key_notin_spec; lia.
                    -- unfold RC.Add; reflexivity.
                  - apply RC.Ext.new_key_notin_spec; lia.
                  - unfold RC.Add. reflexivity.
                }
                { 
                  eapply RC.Submap_find_spec with (x := (newᵣᵪ(Re))) (v := (<[ 𝟙 ]>, τ)) in HSubRe. 
                  - rewrite  <- Hnew in Hfi'. rewrite HSubRe in Hfi'; inversion Hfi'; now subst.
                  - rewrite RC.add_neq_o; try lia; rewrite RC.add_eq_o; auto.   
                }
              ** rewrite ReadStock.add_neq_o in Hfi; auto. eapply HwtW; eauto.
            * rename H into HIn. rewrite Resources.diff_spec in HIn.
              destruct HIn as [HIn HnIn]. rewrite Heq in HnIn; rewrite Resources.diff_notin_spec in HnIn.
              destruct HnIn as [HnIn | HIn'].
              ** assert (r ∈ R1 \ R')%rs. { rewrite Resources.diff_spec; split; assumption. }
                  apply HInW in H as [HInW1 HnInV]. rewrite <- Stock.to_RS_in_spec in *.
                  rewrite Stock.add_spec; simpl; auto.
              ** apply Stock.to_RS_in_spec. apply Stock.add_spec; auto; repeat rewrite Resources.add_spec in HIn'; 
                  destruct HIn' as [Heq' | [Heq' | HIn']]; try (now inversion HIn'); subst; 
                  apply instantiation_new in Hinst; rewrite <- Hinst; simpl; auto.
            * rename H into HIn. rewrite Resources.diff_spec in HIn.
              destruct HIn as [HIn HnIn]. rewrite Heq in HnIn; rewrite Resources.diff_notin_spec in HnIn.
              destruct HnIn as [HnIn | HIn'].
              ** assert (r ∈ R1 \ R')%rs. { rewrite Resources.diff_spec; split; assumption. }
                  apply HInW in H as [HInW1 HnInV]; intro c; apply HnInV. 
                  repeat rewrite RE.add_in_iff; repeat right.
                  eapply RE.shift_in_spec in c as c'; rewrite Resource.shift_valid_refl in c'; eauto.
                  eapply RE.valid_in_spec in c; eauto.
              ** rewrite Hnew in HIn'. repeat rewrite Resources.add_spec in HIn'; 
                  destruct HIn' as [Heq' | [Heq' | HIn']]; try (inversion HIn'); subst; 
                  apply RE.Ext.new_key_notin_spec; lia.
        + replace 2 with (1 + 1) by lia. rewrite Cell.shift_unfold.
          replace ((newᵣᵦ(V)) + 1) with (S (newᵣᵦ(V))) by lia. 

          assert (RE.eq ([⧐ᵣᵦ (newᵣᵦ(V)) ≤ 1 + 1] V) ([⧐ᵣᵦ S (newᵣᵦ(V)) ≤ 1] [⧐ᵣᵦ (newᵣᵦ(V)) ≤ 1] V)).
          { rewrite RE.shift_unfold; replace ((newᵣᵦ(V)) + 1) with (S (newᵣᵦ(V))) by lia; reflexivity. }
          rewrite H.
      
          assert (RE.eq (⌈ (newᵣᵦ(V)) ⤆ [⧐ᵣₓ S (newᵣᵦ(V)) ≤ 1] [⧐ᵣₓ (newᵣᵦ(V)) ≤ 1] ⩽ i … ⩾ ⌉ᵣᵦ ([⧐ᵣᵦ S (newᵣᵦ(V)) ≤ 1] [⧐ᵣᵦ (newᵣᵦ(V)) ≤ 1] V))
                              ([⧐ᵣᵦ S (newᵣᵦ(V)) ≤ 1] (⌈ (newᵣᵦ(V)) ⤆ [⧐ᵣₓ (newᵣᵦ(V)) ≤ 1] ⩽ i … ⩾ ⌉ᵣᵦ ([⧐ᵣᵦ (newᵣᵦ(V)) ≤ 1] V)))).
          { 
            rewrite RE.shift_add_notin_spec.
            - replace ([⧐ᵣ S (newᵣᵦ(V)) ≤ 1] (newᵣᵦ(V))) with (newᵣᵦ(V)); try reflexivity.
              rewrite Resource.shift_valid_refl; auto; unfold Resource.valid; lia.
            - apply RE.shift_new_notin_spec; lia.
          }

          rewrite H0; clear H H0.
          eapply (itfT_init 
                    (⌈ newᵣᵪ( Re) ⤆ (<[ 𝟙 ]>, τ) ⌉ᵣᵪ Re)
                    (⌈ S (newᵣᵪ( Re)) ⤆ (τ, <[ 𝟙 ]>) ⌉ᵣᵪ (⌈ newᵣᵪ( Re) ⤆ (<[ 𝟙 ]>, τ) ⌉ᵣᵪ Re))
                    (⌈ newᵣᵦ( V) ⤆ [⧐ᵣₓ newᵣᵦ( V) ≤ 1] ⩽ i … ⩾ ⌉ᵣᵦ ([⧐ᵣᵦ newᵣᵦ( V) ≤ 1] V))
                    (⌈ S (newᵣᵦ( V)) ⤆ ⩽ unit … ⩾ ⌉ᵣᵦ ([⧐ᵣᵦ S (newᵣᵦ( V)) ≤ 1] ⌈ newᵣᵦ( V) ⤆ [⧐ᵣₓ newᵣᵦ( V) ≤ 1] ⩽ i … ⩾ ⌉ᵣᵦ ([⧐ᵣᵦ newᵣᵦ( V) ≤ 1] V)))
                    τ <[𝟙]> <[unit]>); eauto; try now constructor.
          ++ eapply (itfT_init Re (⌈ newᵣᵪ( Re) ⤆ (<[ 𝟙 ]>, τ) ⌉ᵣᵪ Re)
                                  V (⌈ newᵣᵦ( V) ⤆ [⧐ᵣₓ newᵣᵦ( V) ≤ 1] ⩽ i … ⩾ ⌉ᵣᵦ ([⧐ᵣᵦ newᵣᵦ( V) ≤ 1] V))
                                  <[𝟙]> τ); eauto; try constructor.
          ++ rewrite RC.Ext.new_key_add_spec_1; auto.
              * apply well_typed_implies_valid in Hwi; auto.
                destruct Hwi; apply Typ.valid_weakening with (k := newᵣᵪ( Re)); auto.
              * apply RC.Ext.new_key_notin_spec; auto.
          ++ unfold RC.Add;
            rewrite RC.Ext.new_key_add_spec_1; auto; try reflexivity.
            apply RC.Ext.new_key_notin_spec; auto.
          ++ unfold RE.Add; 
            rewrite RE.Ext.new_key_add_spec_1; auto; try reflexivity.
            * apply RE.shift_new_notin_spec; lia.
            * rewrite RE.shift_new_spec; auto.
        + rewrite Heqnk'. apply RE.halts_add_spec; split.
          ++ simpl. exists <[unit]>. split; auto.
          ++ apply RE.halts_add_spec; split.
             * simpl; exists <[[⧐ₜₘ {newᵣᵦ( V)} ≤ 2] i]>; split; auto.
               now apply Term.shift_value_iff.
             * replace (S (S (newᵣᵦ(V)))) with (newᵣᵦ(V) + 2) by lia.
               unfold RE.halts; intros r' v' Hfi. 
               assert (r' ∈ᵣᵦ [⧐ᵣᵦ newᵣᵦ(V) ≤ 2] V). { exists v'; now apply RE.find_2. }
               apply RE.shift_in_e_spec in H as H'; destruct H'; subst.
               apply RE.shift_find_e_spec in Hfi as H'; destruct H'; subst.
               apply RE.shift_find_spec in Hfi; apply HltV in Hfi.
               destruct x0; simpl in *; destruct Hfi as [λ' [HmeT Hvλ]];
               exists <[ [⧐ₜₘ{newᵣᵦ( V)} ≤ 2] λ' ]>; split; try (now apply Term.shift_value_iff);
               apply multi_evaluate_valid_weakening with (k' := newᵣᵪ( Re) + 2) in HmeT; try lia; rewrite <- Hnew in *;
               replace (newᵣᵪ( Re) + 2 - newᵣᵪ( Re)) with 2 in HmeT; try lia; auto.
        + rewrite <- Hnew ; rewrite RC.new_key_wh_spec. 
          replace (S (S (newᵣᵪ(Re)))) with (newᵣᵪ(Re) + 2) by lia.
          destruct Hltst as [st'' [HmeT Hvlst'']]; exists <[[⧐ₜₘ {newᵣᵦ( V)} ≤ 2] st'']>; split.
          ++ rewrite <- Hnew. apply multi_evaluate_valid_weakening with (k' := newᵣᵪ( Re) + 2) in HmeT; try lia.
             replace (newᵣᵪ( Re) + 2 - newᵣᵪ( Re)) with 2 in HmeT; try lia; auto.
          ++ now apply Term.shift_value_iff.
    -- apply RC.Submap_add_spec_1.
        + apply RC.Ext.new_key_notin_spec; rewrite RC.Ext.new_key_add_spec_1;
          auto. apply RC.Ext.new_key_notin_spec; lia.
        + apply RC.Submap_add_spec_1.
          ++ apply RC.Ext.new_key_notin_spec; lia.
          ++ apply RC.Submap_refl.
Admitted.

(** *** Proof of Resource safety

  **** Hypothesis

  Knowing the term sf is well typed (1), the stream term is also well typed (2),
  there is a transition using the two previous terms (3) and each term in the
  environment is well typed to a type findable in the context if they are
  the same resource name that mapped them (4);

  **** Results

  We can state that:
  - each interaction with resources is done with values never used before (5);
  - we can found a context and a resource set such as :
    - all resources that are not in the set R have the same state before and after the functional transition (6);
    - after the interaction, the state of the cell where the value was stored changed.
      Consequently, the cell cannot be reused (7).

*)
Theorem safety_resources_interaction :
  forall (Re : ℜ) (V V' : 𝓥) (W : 𝐖) (sv sv' sf sf' : Λ) (τ τ' : Τ) (R : resources),

    (* (1) *) ∅ᵥᵪ ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) ->
    (* (2) *) ∅ᵥᵪ ⋅ Re ⊫ sv ∈ τ -> 
    (* (3) *) ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V' ; sv' ; sf' ; W ⪢ -> 
    (* (4) *) Instᵣₜ(Re,V) ->


    (* (5) *) (forall (r : resource), (r ∈ R)%rs -> RE.unused r V) /\

    exists (Re' : ℜ) (R' : resources),

      (* (6) *) (forall (r : resource), (r ∉ R')%rs /\ (r ∈ᵣᵦ V) -> 
                    ([⧐ᵣᵦ (newᵣᵦ(V)) ≤ ((newᵣᵦ(V')) - (newᵣᵦ(V)))] V) ⌊r⌋ᵣᵦ = V' ⌊r⌋ᵣᵦ) /\
      (* (7) *) (forall (r : resource), (r ∈ R')%rs -> RE.used r V')
.
Proof.
  intros Re V V' W sv sv' sf sf' τ2 τ2' R Hinst Hwt Hwst HfT.
  eapply functional_preserves_typing in HfT; eauto.
  destruct HfT as [Hunsd [Hlcl [Re' [R' [HSubRe  [HSubR' [Hinst' [_ [Hlcl1 [Husd [Hwsv' Hwsf']]]]]]]]]]].
  split; auto; exists Re'; exists R'; split; auto.
  intros r [HnIn HInV]; destruct (Resources.In_dec r R).
  - apply HSubR' in i; contradiction.
  - apply Hlcl; split; assumption.
Qed.

(* begin hide *)
(*
(** ** Progress *)
Section progress.


  Theorem experiment_1 : 
    forall (Re : ℜ) (V : 𝓥) (sv sf : Λ) (τ τ' : Τ) (R : resources),

      value(sf) -> 
      halts (newᵣᵪ(Re)) sv ->
      halts_V V ->
      (forall r, (r ∈ R)%rs -> RE.unused r V) ->
      
      Instᵣₜ(Re,V) ->
      
      ∅ᵥᵪ ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) -> 
      ∅ᵥᵪ ⋅ Re ⊫ sv ∈ τ ->

      exists (V' : 𝓥) (W : 𝐖) (sv' sf' : Λ), 
        ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V' ; sv' ; sf' ; W ⪢ /\
        (halts (newᵣᵦ(V')) sv') /\
        halts_V V'.
  Proof.
    intros. revert V sv H H0 H1 H2 H3 H5; dependent induction H4; intros;
    try now inversion H.

    - inversion H; clear H; subst. 
      exists V;
      exists ∅ₛₖ;
      exists <[t sv]>; 
      exists <[arr(t)]>; 
      repeat split; auto.
      -- now repeat constructor.
      -- (* Définir une props pour t sv *) admit.
    - inversion H0; subst; clear H0.
      destruct H1 as [sv' [HmeT Hvsv']].
      apply instantiation_valid in H5 as HvRe; destruct HvRe as [HvRe _].
      apply multi_preserves_typing with (t' := sv') in H6; auto.
      destruct sv'; inversion H6; inversion Hvsv'; subst.

      eapply IHwell_typed in H11; eauto.
      -- destruct H11 as [V' [W [sv' [sf' [HfT [Hltsv' HltV']]]]]].

          exists V';
          exists W;
          exists <[⟨sv',[⧐ₜₘ {newᵣᵦ(V)} ≤ {(newᵣᵦ(V')) - (newᵣᵦ(V))}] sv'2⟩]>;
          exists <[first(τ0 :sf')]>.
          repeat split; auto.
          + eapply fT_first; eauto.
            apply instantiation_new in H5; now rewrite <- H5.
          + destruct Hltsv' as [sv'' [HmeT' Hvsv'']].
            exists <[⟨sv'', [⧐ₜₘ{newᵣᵦ(V)} ≤ {newᵣᵦ(V') - newᵣᵦ(V)}] sv'2⟩]>; split.
            ++ now apply multi_pair1.
            ++ constructor; auto; now apply Term.shift_value_iff.
      -- exists sv'1; split; auto; apply multi_refl.
    (* wt_comp *)
    - admit.
    (* wt_rsf *)
    - clear H0.  

      assert (RE.unused r V). { apply H3; now apply Resources.singleton_spec. }
      destruct H0 as [sv' HfV].
      
      assert (Hvr : newᵣᵪ(Re) ⊩ᵣ r). 
      { 
        apply instantiation_valid in H4; destruct H4.
        eapply RC.valid_find_spec in H0 as [Hvr _]; eauto. 
      }
    
      exists (⌈ r ⤆ ⩽ … sv ⩾ ⌉ᵣᵦ V); 
      exists ∅ₛₖ; 
      exists sv';
      exists <[rsf[r]]>; repeat split.
      -- repeat rewrite Resource.shift_valid_refl; auto; now constructor.
      -- rewrite RE.Ext.new_key_add_spec_3.
         + now apply H2 in HfV.
         + apply RE.in_find; intro c; rewrite HfV in c; inversion c.
      -- unfold halts_V; intros r' v HfV'; rewrite RE.add_o in HfV';
         destruct (Resource.eq_dec r r'); subst; rewrite RE.Ext.new_key_add_spec_3;
         try (apply RE.in_find; intro c; rewrite HfV in c; inversion c).
         + inversion HfV'; subst; clear HfV'.
           apply instantiation_new in H4 as Hnew; now rewrite <- Hnew.
         + apply H2 in HfV'; auto.
    (* wt_wh *)
    - clear IHwell_typed1. fold VContext.empty in *. inversion H2; subst; clear H2.
      eapply weakening_ℜ_1 with (Re' := ⌈ S k ⤆ (τ0, <[ 𝟙 ]>) ⌉ᵣᵪ (⌈ k ⤆ (<[ 𝟙 ]>, τ0) ⌉ᵣᵪ Re)) in H7.
      -- replace (newᵣᵪ( ⌈ S k ⤆ (τ0, <[ 𝟙 ]>) ⌉ᵣᵪ (⌈ k ⤆ (<[ 𝟙 ]>, τ0) ⌉ᵣᵪ Re)) - newᵣᵪ(Re)) with 2 in H7.
         + eapply IHwell_typed2 with (V := (⌈(S k) ⤆ ⩽ <[unit]> … ⩾ ⌉ᵣᵦ 
         (⌈k ⤆ [⧐ᵣₓ k ≤ 2] ⩽ i … ⩾⌉ᵣᵦ  ([⧐ᵣᵦ k ≤ 2] V)))) in H7; eauto.
  Admitted.

  (*
  Theorem progress_of_functional_value : 
    forall (Re : ℜ) (V : 𝓥) (sv sf : Λ) (τ τ' : Τ) (R : resources),
      halts (newᵣᵪ(Re)) sv ->
      halts_V V ->
      (Forall_arr (fun t => forall s, halts (newᵣᵪ(Re)) <[t s]>) sf) ->

      value(sf) -> Instᵣₜ(Re,V) ->
      ∅ᵥᵪ ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) -> 
      ∅ᵥᵪ ⋅ Re ⊫ sv ∈ τ ->

      (exists (V' : 𝓥) (W : 𝐖) (sv' sf' : Λ), 
        ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V' ; sv' ; sf' ; W ⪢ /\
        (halts (newᵣᵦ(V')) sv') /\
        halts_V V').
  Proof.
    intros Re V sv sf τ τ' R Hltsv HltV HltFarr Hvsf Hinst Hwsf Hwsv.
    eapply progress_of_functional_value_gen with (Re' := Re) in Hwsv as IH; eauto.
    - destruct IH as [V' [W [sv' [sf' [HfT [Hltsv' HltV']]]]]].
      replace <[[⧐ₜₘ{newᵣᵪ( Re)} ≤ {newᵣᵪ( Re) - newᵣᵪ( Re)}] sf]> with sf in HfT.
      -- exists V'; exists W; exists sv'; exists sf'; auto.
      -- symmetry; apply Term.eq_leibniz; replace (newᵣᵪ(Re) - newᵣᵪ(Re)) with 0 by lia.
         now rewrite Term.shift_refl.
    - apply instantiation_valid in Hinst; destruct Hinst; assumption.
    - apply RC.Submap_refl.
  Qed.

  Theorem progress_of_functional : 
    forall (Re : ℜ) (V : 𝓥) (sv sf : Λ) (τ τ' : Τ) (R : resources),
      halts (newᵣᵪ(Re)) sf ->
      halts (newᵣᵪ(Re)) sv ->
      halts_V V ->
      (Forall_arr (fun t => forall s, halts (newᵣᵪ(Re)) <[t s]>) sf) ->

      Instᵣₜ(Re,V) ->
      ∅ᵥᵪ ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) -> 
      ∅ᵥᵪ ⋅ Re ⊫ sv ∈ τ ->

      (exists (V' : 𝓥) (W : 𝐖) (sv' sf' : Λ), 
            ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V' ; sv' ; sf' ; W ⪢ /\
            (halts (newᵣᵦ(V')) sv') /\
            halts_V V').
  Proof. 
    intros Re V sv sf τ τ' R Hltsf; revert V sv τ τ' R; destruct Hltsf as [sf' [HmeT Hvsf]].
    apply multi_indexed in HmeT as [k HieT]; revert Re sf sf' HieT Hvsf; induction k;
    intros Re sf sf' HieT Hvsf' V sv τ τ' R Hltsv HltV HltFarr Hinst Hwsf Hwsv.
    (* sf is a value *)
    - inversion HieT; subst; clear HieT;
      eapply progress_of_functional_value; eauto.
    (* sf can be reduced at least one time *)
    - inversion HieT; subst.

      (* clean *)
      clear HieT; rename y into sf1; rename H0 into HeT; rename H2 into HieT;
      move Re after IHk; move sf before Re; move sf' before sf; move sf1 before sf'.
      move sv before sf1; move V before Re; move τ before sv; move τ' before τ;
      move R before τ'.
      (* clean *)

      apply instantiation_valid in Hinst as Hv; destruct Hv as [HvRe _].
      apply evaluate_preserves_typing with (t' := sf1) in Hwsf as Hwsf1; auto.
      eapply IHk in HieT as IH; eauto.
      -- apply instantiation_new in Hinst as Hnew; rewrite Hnew in HeT; clear Hnew.
         destruct IH as [V' [W [sv' [sf1' [HfT [Hltsv' HltV']]]]]].
         exists V'; exists W; exists sv'; exists sf1'; split; auto.
         eapply fT_eT; eauto.
      -- (* ForAll_arr have to be preserved by evaluation transition *) admit.
  Admitted.
  *)

End progress.
*)
(* end hide *)

(** *** Some corollaries *)

Corollary functional_preserves_instantiation : 
  forall (Re : ℜ) (V V' : 𝓥) (W : 𝐖) (sv sv' sf sf' : Λ) (τ τ' : Τ) (R : resources),  
    Instᵣₜ(Re,V) ->
    ∅ᵥᵪ ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) -> 
    ∅ᵥᵪ ⋅ Re ⊫ sv ∈ τ -> 
    ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V' ; sv' ; sf' ; W ⪢ -> 

    exists Re', Instᵣₜ(Re',V').
Proof.
  intros Re V V' W sv sv' sf sf' τ2 τ2' R Hinst Hwt Hwst HfT.
  eapply functional_preserves_typing in HfT; eauto.
  destruct HfT as [_ [_ [Re' [_ [_  [_ [Hinst' [_ [_ [_ _]]]]]]]]]];
  now exists Re'.
Qed.


Corollary functional_preserves_stream_typing : 
  forall (Re : ℜ) (V V' : 𝓥) (W : 𝐖) (sv sv' sf sf' : Λ) (τ τ' : Τ) (R : resources),  
    Instᵣₜ(Re,V) ->
    ∅ᵥᵪ ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) -> 
    ∅ᵥᵪ ⋅ Re ⊫ sv ∈ τ -> 
    ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V' ; sv' ; sf' ; W ⪢ -> 

    exists Re', ∅ᵥᵪ ⋅ Re' ⊫ sv' ∈ τ'.
Proof.
  intros Re V V' W sv sv' sf sf' τ2 τ2' R Hinst Hwt Hwst HfT.
  eapply functional_preserves_typing in HfT; eauto.
  destruct HfT as [_ [_ [Re' [_ [_ [_  [_ [Hinst' [_ [_ [Hwsv' _]]]]]]]]]]];
  now exists Re'.
Qed.


Corollary functional_preserves_typing_1 : 
  forall (Re : ℜ) (V V' : 𝓥) (W : 𝐖) (sv sv' sf sf' : Λ) (τ τ' : Τ) (R : resources),

    Instᵣₜ(Re,V) ->
    ∅ᵥᵪ ⋅ Re ⊫ sf ∈ (τ ⟿ τ' ∣ R) ->
    ∅ᵥᵪ ⋅ Re ⊫ sv ∈ τ -> 
    ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V' ; sv' ; sf' ; W ⪢ -> 

    exists (Re' : ℜ) (R' : resources), 
      Re ⊆ᵣᵪ Re' /\  (R ⊆ R')%rs /\ Instᵣₜ(Re',V') /\ 
      ∅ᵥᵪ ⋅ Re' ⊫ sv' ∈ τ' /\
      ∅ᵥᵪ ⋅ Re' ⊫ sf' ∈ (τ ⟿ τ' ∣ R').
Proof.
  intros Re V V' W sv sv' sf sf' τ2 τ2' R Hinst Hwt Hwst HfT.
  eapply functional_preserves_typing in HfT; eauto.
  destruct HfT as [_ [_ [Re' [R' [HSubRe  [HSubR' [Hinst' [_ [_ [_ [Hwsv' Hwsf']]]]]]]]]]];
  exists Re'; now exists R'.
Qed.
*)