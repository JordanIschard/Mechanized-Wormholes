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
      Instᵣₜ(Re,V) ->
      Addᵣᵪ (newᵣᵪ(Re)) (τ,τ') Re Re' -> 
      Addᵣᵦ (newᵣᵦ(V)) (⩽ v … ⩾) V V' -> 
      ∅ᵥᵪ ⋅ Re ⊫ v ∈ τ' -> 
      Instᵣₜ(Re',V')
  
  | itfT_update : forall (Re : ℜ) (V V' : 𝓥) r (τ τ' : Τ) (v : Λ),
                    Instᵣₜ(Re,V) -> Re ⌈r ⩦ (τ,τ')⌉ᵣᵪ -> 
                    r ∈ᵣᵦ V -> Addᵣᵦ r ((⩽ … v ⩾)) V V' -> 
                    ∅ᵥᵪ ⋅ Re ⊫ v ∈ τ -> Instᵣₜ(Re,V')

where "'Instᵣₜ(' Re , V )" := (instantiation_func Re V).

Definition all_arrow_halting := forall Re t α β,
  ∅ᵥᵪ ⋅ Re ⊫ arr(t) ∈ (α ⟿ β ∣ ∅ᵣₛ) -> forall v, ∅ᵥᵪ ⋅ Re ⊫ v ∈ α -> halts <[t v]>.

(** *** Instantiation *)

Lemma instantiation_is_empty_spec : forall (Re : ℜ) (V : 𝓥),
  Instᵣₜ(Re,V) -> RC.Raw.is_empty Re = RE.Raw.is_empty V.
Proof.
  intros Re V Hinst; induction Hinst.
  - rewrite RC.OP.P.is_empty_1; auto; 
    now rewrite RE.OP.P.is_empty_1.
  - apply RC.notEmpty_Add_spec in H.
    apply RE.notEmpty_Add_spec in H0.
    destruct (RC.Raw.is_empty Re') eqn:HEmp.
    -- apply RC.OP.P.is_empty_2 in HEmp; contradiction.
    -- destruct (RE.Raw.is_empty V') eqn:HEmp'; auto.
        apply RE.OP.P.is_empty_2 in HEmp'; contradiction.
  - apply RE.notEmpty_Add_spec in H1.
    destruct (RC.Raw.is_empty Re) eqn:HEmp.
    -- apply RC.OP.P.is_empty_2 in HEmp.
        apply RC.notEmpty_find_spec in H; auto; contradiction.
    -- destruct (RE.Raw.is_empty V') eqn:HEmp'; auto.
        apply RE.OP.P.is_empty_2 in HEmp'; contradiction.
Qed.

Lemma instantiation_max : forall (Re : ℜ) (V : 𝓥),
  Instᵣₜ(Re,V) -> maxᵣᵪ(Re) = maxᵣᵦ(V).
Proof.
  intros Re V inst; induction inst.
  - rewrite RC.Ext.max_key_Empty_spec; auto.
    now rewrite RE.Ext.max_key_Empty_spec.
  - apply RC.Ext.max_key_Add_spec in H as [[H H'] | [H H']]; auto.
    -- rewrite H. 
        apply RE.Ext.max_key_Add_spec in H0 as [[H0 H0'] | [H0 H0']].
        + rewrite H0; apply instantiation_is_empty_spec in inst as HEmp.
          unfold RC.Ext.new_key,RE.Ext.new_key; rewrite HEmp.
          destruct (RE.Raw.is_empty V); auto.
        + assert (newᵣᵦ(V) >= maxᵣᵦ(V)). { apply RE.Ext.new_key_geq_max_key. }
          lia.
        + apply RE.new_key_notin_spec; auto.
    -- unfold RC.Ext.new_key in H'. 
        destruct (RC.Raw.is_empty Re) eqn:HEmp; try lia.
        rewrite RC.Ext.max_key_Empty_spec in H'; try lia.
        now apply RC.OP.P.is_empty_2.
    -- apply RC.Ext.new_key_notin_spec; lia.
  - unfold RE.OP.P.Add in H1; rewrite H1.
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
    -- exists (⩽ v … ⩾). 
        apply instantiation_new in inst as Hnew; rewrite Hnew.
        now apply RE.OP.P.add_eq_o.
    -- rewrite H in Hfin. rewrite RC.OP.P.add_neq_o in Hfin; try assumption.
        apply IHinst in Hfin as [v' Hfin]; exists v'. 
        rewrite RE.OP.P.add_neq_o; auto.
        apply instantiation_new in inst; now rewrite <- inst.
  - destruct (Resource.eq_dec r k'); subst.
    -- exists (⩽ … v ⩾); rewrite H1; now apply RE.OP.P.add_eq_o.
    -- apply IHinst in Hfin; destruct Hfin.
        exists x. rewrite H1; now rewrite RE.OP.P.add_neq_o.
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

Lemma instantiation_well_typed : forall (Re : ℜ) V (r : resource) (v : 𝑣) (πτ : πΤ),
  Instᵣₜ(Re,V) -> Re ⌈ r ⩦ πτ ⌉ᵣᵪ -> V ⌈ r ⩦ v ⌉ᵣᵦ -> 
  match (πτ,v) with
    | ((_,τ),⩽ v' … ⩾) => ∅ᵥᵪ ⋅ Re ⊫ v' ∈ τ
    | ((τ,_),⩽ … v' ⩾) => ∅ᵥᵪ ⋅ Re ⊫ v' ∈ τ
  end.
Proof.
  intros Re V r v πτ inst; revert r v πτ; induction inst;
  intros r' v' πτ' HfRe HfV; destruct πτ'.
  - apply RC.notEmpty_find_spec in HfRe; auto; contradiction.
  - rewrite H in HfRe; rewrite H0 in HfV.
    apply instantiation_new in inst as Hnew. 
    destruct (Resource.eq_dec (newᵣᵪ(Re)) r'); subst.
    -- rewrite Hnew in HfV. rewrite RC.OP.P.add_eq_o in HfRe; auto; 
        inversion HfRe; clear HfRe; subst.
        rewrite RE.OP.P.add_eq_o in HfV; auto; inversion HfV; subst; clear HfV.
        unfold RC.OP.P.Add in H; rewrite H. apply weakening_ℜ with Re; auto.
        apply RC.Submap_add_spec_1.
        + apply RC.Ext.new_key_notin_spec; lia.
        + apply RC.Submap_refl.
    -- rewrite <- Hnew in HfV. rewrite RC.OP.P.add_neq_o in HfRe; auto.
        rewrite RE.OP.P.add_neq_o in HfV; auto. eapply IHinst in HfV; eauto.
        simpl in *; destruct v'.
        + apply weakening_ℜ with Re; auto; unfold RC.OP.P.Add in H; rewrite H;
          apply RC.Submap_add_spec_1.
          ++ apply RC.new_key_notin_spec; lia.
          ++ apply RC.Submap_refl.
        + apply weakening_ℜ with Re; auto; unfold RC.OP.P.Add in H; rewrite H;
          apply RC.Submap_add_spec_1.
          ++ apply RC.new_key_notin_spec; lia.
          ++ apply RC.Submap_refl.
  - rewrite H1 in HfV; destruct (Resource.eq_dec r r'); subst.
    -- rewrite RE.OP.P.add_eq_o in HfV; auto; inversion HfV; subst; clear HfV.
        rewrite H in HfRe; inversion HfRe; subst; auto.
    -- rewrite RE.OP.P.add_neq_o in HfV; auto. eapply IHinst in HfV; eauto.
        now simpl in HfV.
Qed.

Lemma instantiation_in : forall (Re : ℜ) V (r : resource),
  Instᵣₜ(Re,V) -> r ∈ᵣᵪ Re <-> r ∈ᵣᵦ V.
Proof.
  split.
  - intros; destruct H0; apply RC.OP.P.find_1 in H0. 
    eapply instantiation_domains_match in H0; eauto;
    destruct H0. exists x0; now apply RE.OP.P.find_2.
  - revert r; induction H.
    -- intros. unfold RE.OP.P.Empty in *; exfalso.
       destruct H1. now apply (H0 r x).
    -- intros. unfold RE.OP.P.Add in *. rewrite H1 in *.
       unfold RC.OP.P.Add in *. rewrite H0.
       apply RE.OP.P.add_in_iff in H3; destruct H3; subst.
       + apply instantiation_new in H; rewrite H.
         rewrite RC.OP.P.add_in_iff; now left.
       + rewrite RC.OP.P.add_in_iff; right; now apply IHinstantiation_func.
    -- intros. unfold RE.OP.P.Add in *. rewrite H2 in *. 
       apply IHinstantiation_func. rewrite RE.OP.P.add_in_iff in H4.
       destruct H4; subst; auto.
Qed.

(** ** Preservation *)

(** *** Proof of preservation of keys in the environment 

  Keeping consistent the typing through the functional transition is 
  needed for the resources environment. Thus, knowing that we cannot loose 
  keys is required.
*)
Lemma functional_preserves_keys (V V' : 𝓥) (tv tv' sf sf' : Λ) :
  ⪡ V ; tv ; sf ⪢ ⭆ ⪡ V' ; tv' ; sf' ⪢ ->

  (forall (r : resource), r ∈ᵣᵦ V -> r ∈ᵣᵦ V').
Proof.
  intros fT; dependent induction fT; intros r' HInV; auto.
  (* fT_rsf *)
  - destruct (Resource.eq_dec r r'); subst; apply RE.OP.P.add_in_iff; auto.
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
  - there is the same property between Re and V' that between Re and V (7); 
  - Each value mapped with a resource name present in R has to be used in V' (8);
  - the output stream term is well typed (9);
  - the term sf' is well typed (10).

*)
Theorem functional_preserves_typing : 
  forall (Re : ℜ) (V V' : 𝓥) (tv tv' t t' : Λ) (τ τ' : Τ) (R : resources),

    (* (1) *) ∅ᵥᵪ ⋅ Re ⊫ t ∈ (τ ⟿ τ' ∣ R) ->
    (* (2) *) ∅ᵥᵪ ⋅ Re ⊫ tv ∈ τ -> 
    (* (3) *) ⪡ V ; tv ; t ⪢ ⭆ ⪡ V' ; tv' ; t' ⪢ -> 
    (* (4) *) Instᵣₜ(Re,V) ->


    (* (5) *)(forall (r : resource), (r ∈ R)%rs -> RE.unused r V) /\
    (* (6) *)(forall (r : resource), (r ∉ R)%rs /\ (r ∈ᵣᵦ V) -> V ⌊r⌋ᵣᵦ = V' ⌊r⌋ᵣᵦ) /\

    (*  (7) *) Instᵣₜ(Re,V') /\
    (*  (8) *) (forall (r : resource), (r ∈ R)%rs -> RE.used r V') /\
    (*  (9) *) ∅ᵥᵪ ⋅ Re ⊫ tv' ∈ τ' /\
    (* (10) *) ∅ᵥᵪ ⋅ Re ⊫ t' ∈ (τ ⟿ τ' ∣ R).
Proof.
  intros Re V V' tv tv' t t' τ τ' R Hwt Hwtv fT. revert Re R τ τ' Hwt Hwtv;
  induction fT; intros Re R α β Hwt Hwtv Hinst.
  (* fT_eT *)
  - 
    (* clean *)
    move R before Re; move α before R; move β before α; move fT after IHfT;
    rename fT into HfT; rename H into HeT; move HeT after HfT.
    (* clean *)

    apply evaluate_preserves_typing with (t' := t') in Hwt as Hwt'; auto.
  (* fT_arr *)
  - 
    (* clean *)
    inversion Hwt; subst; rename H4 into Hwt'; clear Hwt H; move Hwt' after Hwtv.
    (* clean *)

    repeat split; auto.
    -- intros r HIn; inversion HIn.
    -- intros r HIn; inversion HIn.
    -- apply wt_app with (τ2 := α); assumption.
    -- now constructor.
  (* fT_first *)
  -
    (* clean *)
    clear H; inversion Hwt; subst; move Re before V'; move R before Re; move τ1 before τ;
    move τ2 before τ1; clear Hwt; rename H3 into Hwt; move Hwt after Hwtv; rename H0 into HmeT; 
    rename fT into HfT; move HfT after IHfT; move HmeT after HfT.
    (* clean *)

    apply multi_preserves_typing with (t' := <[⟨v1,v2⟩]>) in Hwtv; auto.

    (* clean *)
    inversion Hwtv; subst; rename H4 into Hwv1; rename H6 into Hwv2; move Hwv1 before Hwt;
    move Hwv2 before Hwv1; clear Hwtv.
    (* clean *)

    apply IHfT with (R := R) (τ' := τ2) in Hwv1 as IH; try assumption.

    clear IHfT; destruct IH as [Hunsd [Hlcl [Hinst' [Husd [Hwt1' Hwt']]]]].

    (* clean *)
    move Hwt1' before Hwv1; clear Hwv1; 
    move Hwt' before Hwt; clear Hwt; move Hinst' before Hinst; move Hunsd before Husd.
    (* clean *)

    repeat split; auto; now constructor.
  (* fT_comp *)
  -
    (* clean *)
    inversion H; subst; inversion Hwt; subst; apply Resources.eq_leibniz in H10; subst;
    clear Hwt; move Re before V''; move R1 before Re; move R2 before R1; 
    move α before R2; move β before α; move τ before β; rename fT1 into HfT1;
    move HfT1 after IHfT2; rename fT2 into HfT2; move HfT2 after HfT1.
    rename H9 into Hwt1; rename H11 into Hwt2; rename H12 into HEmp.
    rename H3 into Hvt2; clear H2. move Hwt1 after Hwtv; move Hwt2 before Hwt1; move Hvt2 before Hwtv.
    (* clean *)

    apply IHfT1 with (R := R1) (τ' := τ) in Hwtv as IH1; auto.
    clear IHfT1; destruct IH1 as [Hunsd1 [Hlcl1 [Hinst' [Husd1 [Hwtv' Hwt1']]]]].

    (* clean *)
    move Hwtv' before Hwtv; move Hwt1' before Hwt1; move Hinst' before Hinst.
    (* clean *)

    apply IHfT2 with (R := R2) (τ' := β) in Hwtv' as IH2; auto.
    clear IHfT2; destruct IH2 as [Hunsd2 [Hlcl2 [Hinst'' [Husd2 [Hwtv'' Hwt2']]]]].

    (* clean *)
    move Hwtv'' before Hwtv'; move Hwt2' before Hwt2; move Hwt2' before Hwt2;
    move Hunsd2 before Hunsd1; move Hinst'' before Hinst';
    move Husd2 before Husd1; move Hlcl2 before Hlcl1.
    (* clean *)

    repeat split; auto.
    -- intros r HIn; rewrite Resources.union_spec in HIn; destruct HIn; auto.
       apply Hunsd2 in H0 as Hunsd. destruct Hunsd as [v HfV'].
       exists v; rewrite Hlcl1; auto; split.

       + intro; symmetry in HEmp. apply Resources.empty_is_empty_2 in HEmp.
         apply (HEmp r); rewrite Resources.inter_spec; now split.
       + eapply typing_Re_R in H0 as HInRe; eauto.
         eapply instantiation_in in HInRe; eauto. 

    -- intros r [HnIn HIn]; rewrite Resources.union_notin_spec in HnIn; 
       destruct HnIn as [HnIn1 HnIn2]. rewrite Hlcl1; auto.
       apply Hlcl2; split; auto. eapply functional_preserves_keys; eauto. 

    -- intros r HIn; rewrite Resources.union_spec in HIn; destruct HIn as [HIn | HIn]; auto.
       assert (HnIn' : (r ∉ R2)%rs). 
        { 
          intro. symmetry in HEmp; apply Resources.empty_is_empty_2 in HEmp; 
          apply (HEmp r); rewrite Resources.inter_spec; split; auto. 
        }

       apply Husd1 in HIn as HuV'; destruct HuV' as [v HfV'].
       exists v. rewrite <- Hlcl2; auto; split; auto.
       exists (⩽ … v ⩾); now apply RE.OP.P.find_2.

    -- econstructor; eauto. reflexivity.
  (* fT_rsf *)
  -
    (* clean *)
    inversion Hwt; subst. clear Hwt; move Re before V; rename H into HfV; rename H4 into HfRe;
    move HfV after HfRe. 
    (* clean *)

    repeat split.
    -- intros r' HIn; rewrite Resources.singleton_spec in HIn; subst; now exists v.
    -- intros r' [HnIn HIn]; apply Resources.singleton_notin_spec in HnIn.
       rewrite RE.OP.P.add_neq_o; auto.
    -- eapply itfT_update; eauto.
       + apply RE.OP.P.in_find; intro c; rewrite HfV in c; inversion c.
       + unfold RE.OP.P.Add; reflexivity.
    -- intros r' HIn; apply Resources.singleton_spec in HIn; subst; unfold RE.used.
       exists st; now apply RE.OP.P.add_eq_o.
    -- apply instantiation_well_typed with (V := V) (v := ⩽ v … ⩾) in HfRe; try assumption.
    -- now constructor.
Qed.


(** ** Progress *)


Theorem progress_of_functional_value (Re : ℜ) (V : 𝓥) (tv t : Λ) (τ τ' : Τ) (R : resources) :
    halts tv ->
    RE.halts V ->
    all_arrow_halting ->
    value(t) -> 
    
    ∅ᵥᵪ ⋅ Re ⊫ t ∈ (τ ⟿ τ' ∣ R) -> 
    ∅ᵥᵪ ⋅ Re ⊫ tv ∈ τ ->
    Instᵣₜ(Re,V) ->

    (exists (V' : 𝓥) (tv' : Λ), 
      ⪡ V ; tv ; t ⪢ ⭆ ⪡ V' ; tv' ; t ⪢ /\
      halts tv' /\
      RE.halts V').
Proof.
  intros Hltv HltV HlAll Hvt wt; revert V tv Hltv HltV HlAll Hvt.
  dependent induction wt; intros V tv Hltv HltV HlAll Hvt Hwtv Hinst; inversion Hvt; subst.
  (* wt-arr *)
  -
    (* clean *)
    clear Hvt; rename H0 into Hvt; move V before Re; move tv before t; clear IHwt.
    (* clean *)

    exists V; exists <[t tv]>; repeat split; auto.
    -- now repeat constructor.
    -- unfold all_arrow_halting in HlAll; apply (HlAll Re _ τ τ'); auto. 
       now constructor.
  (* wt-first *)
  -
    (* clean *)
    clear Hvt; rename H0 into Hvt; move V before Re; move tv before t.
    (* clean *)

    destruct Hltv as [tv' [HmeT Hvtv']].
    apply multi_preserves_typing with (t' := tv') in Hwtv as Hwtv'; auto.
    destruct tv'; subst; inversion Hwtv'; subst; inversion Hvtv'; subst.

    (* clean *)
    clear Hwtv Hwtv' Hvtv'; rename H4 into Hwtv'1; rename H6 into Hwtv'2.
    rename H1 into Hvtv'1; rename H2 into Hvtv'2. move wt before Hwtv'1. move Hvt before Hvtv'1.
    move tv'1 before tv; move tv'2 before tv'1.
    (* clean *)

    eapply IHwt in Hwtv'1 as IH; eauto; clear IHwt.
    -- destruct IH as [V' [tv''1 [HfT [Hltv''1 HltV']]]].
       exists V'; exists <[⟨tv''1,tv'2⟩]>; repeat split; auto.
       + eapply fT_first; eauto.
       + apply halts_pair; split; auto. exists tv'2; auto.
    -- exists tv'1; split; auto.
  (* wt-comp *)
  - admit.
  (* wt-rsf *)
  - (* Il faut des garanti sur l'état des valeurs associé à tout r dans R dans V. *)
 Admitted.

Theorem progress_of_functional(Re : ℜ) (V : 𝓥) (tv t : Λ) (τ τ' : Τ) (R : resources) : 
  halts t -> halts tv -> RE.halts V ->
  all_arrow_halting ->

  ∅ᵥᵪ ⋅ Re ⊫ t ∈ (τ ⟿ τ' ∣ R) -> 
  ∅ᵥᵪ ⋅ Re ⊫ tv ∈ τ ->
  Instᵣₜ(Re,V) ->

  (exists (V' : 𝓥) (tv' t' : Λ), 
    ⪡ V ; tv ; t ⪢ ⭆ ⪡ V' ; tv' ; t' ⪢ /\
    halts t' /\ halts tv'/\ RE.halts V'
  ).
Proof. 
  intros Hlt; destruct Hlt as [t' [HmeT Hvt']]. apply multi_indexed in HmeT as [k HieT].
  revert Re V tv t τ τ' R t' HieT Hvt'. induction k; 
  intros Re V tv t τ τ' R t' HieT Hvt' Hltv HltV HltAll Hwt Hwtv Hinst.
  (* sf is a value *)
  - inversion HieT; subst. 
    apply (progress_of_functional_value _ _ tv t' τ τ' R) in Hinst; try assumption.
    destruct Hinst as [V' [tv' [HfT [Hltv' HltV']]]].
    exists V'; exists tv'; exists t'; repeat split; auto.
    exists t'; split; auto.
  (* sf can be reduced at least one time *)
  - inversion HieT; subst.

    (* clean *)
    clear HieT; rename y into t1; rename H0 into HeT; rename H1 into HieT.
    move t1 before t; move t' before t.
    (* clean *)

    apply evaluate_preserves_typing with (t' := t1) in Hwt as Hwt1; auto.
    eapply IHk in HieT as IH; eauto; clear IHk.
    destruct IH as [V' [tv' [t1' [HfT [Hlt1' [Hltv' HltV']]]]]].
    exists V'; exists tv'; exists t1'; split; auto; eapply fT_eT; eauto.
Qed.

(** *** Proof of Resource safety

  **** Hypothesis

  Knowing the term sf is well typed (1), the stream term is also well typed (2),
   using the two previous terms (3) and each term in the
  environment is well typed to a type findable in the context if they are
  the same resource name that mapped them (3);

  **** Results

  There is a transition such that :
  - each interaction with resources is done with values never used before (5);
  - we can found a context and a resource set such as :
    - all resources that are not in the set R have the same state before and after the functional transition (6);
    - after the interaction, the state of the cell where the value was stored changed.
      Consequently, the cell cannot be reused (7).

*)
Theorem safety_resources_interaction :
  forall (Re : ℜ) (V V' : 𝓥) (tv tv' t t' : Λ) (τ τ' : Τ) (R : resources),

    (* (1) *) ∅ᵥᵪ ⋅ Re ⊫ t ∈ (τ ⟿ τ' ∣ R) ->
    (* (2) *) ∅ᵥᵪ ⋅ Re ⊫ tv ∈ τ -> 
    (* (3) *) Instᵣₜ(Re,V) ->


    (* (5) *) (forall (r : resource), (r ∈ R)%rs -> RE.unused r V) ->

    exists (Re' : ℜ) (R' : resources),

      (* (6) *) (forall (r : resource), (r ∉ R')%rs /\ (r ∈ᵣᵦ V) -> 
                    V ⌊r⌋ᵣᵦ = V' ⌊r⌋ᵣᵦ) /\
      (* (7) *) (forall (r : resource), (r ∈ R')%rs -> RE.used r V')
.
Proof.
  intros. 

 Admitted.