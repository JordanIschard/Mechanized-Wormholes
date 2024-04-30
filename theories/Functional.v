From Coq Require Import Program Lia Relations.Relation_Definitions Classes.RelationClasses 
                        Classical_Prop Classical_Pred_Type Bool.Bool Classes.Morphisms.
From Mecha Require Import Resource Resources Term Typ Var Substitution Typing VContext RContext Evaluation
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
Reserved Notation "'Wfᵣₜ(' Re , V )" (at level 50).

Inductive functional : 𝓥 -> Λ -> Λ -> 𝓥 -> Λ -> Λ -> Prop :=

  | fT_eT_sf  :  forall (V V' : 𝓥) (st st' t t' t'' : Λ),

        ⊨ t ⟼ t' -> ⪡ V ; st ; t' ⪢ ⭆ ⪡ V' ; st' ; t'' ⪢ -> 
    (*-------------------------------------------------------------*)
              ⪡ V ; st ; t ⪢ ⭆ ⪡ V' ; st' ; t'' ⪢

  | fT_eT_sv :  forall (V V' : 𝓥) (st st' st'' t t' : Λ),

        ⊨ st ⟼ st' -> ⪡ V ; st' ; t ⪢ ⭆ ⪡ V' ; st'' ; t' ⪢ -> 
    (*-------------------------------------------------------------*)
              ⪡ V ; st ; t ⪢ ⭆ ⪡ V' ; st'' ; t' ⪢

  | fT_arr   :  forall (st t : Λ) (V : 𝓥), 

    (*------------------------------------------------------*)
        ⪡ V ; st ; arr(t) ⪢ ⭆ ⪡ V ; (t st) ; arr(t) ⪢ 

  | fT_first :  forall (v1 v1' v2 t t' : Λ) (τ : Τ) (V V' : 𝓥),

                     ⪡ V ; v1 ; t ⪢ ⭆ ⪡ V' ; v1' ; t' ⪢ ->
    (*--------------------------------------(((--------------------------*)
       ⪡ V ; ⟨v1,v2⟩ ; first(τ:t) ⪢ ⭆ ⪡ V' ; ⟨v1',v2⟩ ; first(τ:t') ⪢

  | fT_comp  :  forall (st st' st'' t1 t1' t2 t2' : Λ) (V V' V'' : 𝓥),

        ⪡ V ; st ; t1 ⪢ ⭆ ⪡ V' ; st' ; t1' ⪢ ->
                      ⪡ V' ; st' ; t2 ⪢ ⭆ ⪡ V'' ; st'' ; t2' ⪢ ->
    (*----------------------------------------------------------------------*)
          ⪡ V ; st ; (t1 >>> t2) ⪢ ⭆ ⪡ V'' ; st'' ; (t1' >>> t2') ⪢

  | fT_rsf   :  forall (V : 𝓥) (st v : Λ) (r : resource),

                              V ⌈r ⩦ ⩽ v … ⩾⌉ᵣᵦ -> 
    (*------------------------------------------------------------------*)
        ⪡ V ; st ; rsf[r] ⪢ ⭆ ⪡ ⌈ r ⤆ ⩽ … st ⩾ ⌉ᵣᵦ V ; v ; rsf[r] ⪢

where "⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st1 ; t1 ⪢" := (functional V st t V1 st1 t1).


Inductive wf_env_fT : ℜ -> 𝓥 -> Prop := 
  | wfFT_empty  : forall (Re : ℜ) (V : 𝓥), 
                    isEmptyᵣᵪ(Re) -> isEmptyᵣᵦ(V) -> Wfᵣₜ(Re,V)

  | wfFT_add   : 
    forall (Re Re' : ℜ) (V V' : 𝓥) (τ τ' : Τ) (v : Λ),
      Wfᵣₜ(Re,V) ->
      Addᵣᵪ (newᵣᵪ(Re)) (τ,τ') Re Re' -> 
      Addᵣᵦ (newᵣᵦ(V)) (⩽ v … ⩾) V V' -> 
      ∅ᵥᵪ ⋅ Re ⊫ v ∈ τ' -> 
      Wfᵣₜ(Re',V')
  
  | wfFT_update : forall (Re : ℜ) (V V' : 𝓥) r (τ τ' : Τ) (v : Λ),
                    Wfᵣₜ(Re,V) -> Re ⌈r ⩦ (τ,τ')⌉ᵣᵪ -> 
                    r ∈ᵣᵦ V -> Addᵣᵦ r ((⩽ … v ⩾)) V V' -> 
                    ∅ᵥᵪ ⋅ Re ⊫ v ∈ τ -> Wfᵣₜ(Re,V')

where "'Wfᵣₜ(' Re , V )" := (wf_env_fT Re V).

(** *** wf_env_fT *)

Lemma wf_env_fT_is_empty_spec : forall (Re : ℜ) (V : 𝓥),
  Wfᵣₜ(Re,V) -> RC.Raw.is_empty Re = RE.Raw.is_empty V.
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

Lemma wf_env_fT_max : forall (Re : ℜ) (V : 𝓥),
  Wfᵣₜ(Re,V) -> maxᵣᵪ(Re) = maxᵣᵦ(V).
Proof.
  intros Re V inst; induction inst.
  - rewrite RC.Ext.max_key_Empty_spec; auto.
    now rewrite RE.Ext.max_key_Empty_spec.
  - apply RC.Ext.max_key_Add_spec in H as [[H H'] | [H H']]; auto.
    -- rewrite H. 
        apply RE.Ext.max_key_Add_spec in H0 as [[H0 H0'] | [H0 H0']].
        + rewrite H0; apply wf_env_fT_is_empty_spec in inst as HEmp.
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

Lemma wf_env_fT_new : forall (Re : ℜ) (V : 𝓥),
  Wfᵣₜ(Re,V) -> newᵣᵪ(Re) = newᵣᵦ(V).
Proof.
  intros Re V Hinst; unfold RC.Ext.new_key,RE.Ext.new_key.
  apply wf_env_fT_is_empty_spec in Hinst as HisEmp.
  destruct (RC.Raw.is_empty Re) eqn:HEmp.
  - now rewrite <- HisEmp.
  - rewrite <- HisEmp; f_equal; now apply wf_env_fT_max.
Qed.

Lemma wf_env_fT_domains_match: forall (Re : ℜ) V (k : resource) (πτ : πΤ),
  Wfᵣₜ(Re,V) -> Re ⌈k ⩦ πτ⌉ᵣᵪ -> exists (v : 𝑣), V ⌈k ⩦ v⌉ᵣᵦ.
Proof.
  intros Re V k πτ inst; revert k πτ; induction inst; intros k' πτ' Hfin.
  - apply RC.notEmpty_find_spec in Hfin; auto; contradiction.
  - rewrite H0 in *; destruct (Resource.eq_dec (newᵣᵪ(Re)) k'); subst.
    -- exists (⩽ v … ⩾). 
        apply wf_env_fT_new in inst as Hnew; rewrite Hnew.
        now apply RE.OP.P.add_eq_o.
    -- rewrite H in Hfin. rewrite RC.OP.P.add_neq_o in Hfin; try assumption.
        apply IHinst in Hfin as [v' Hfin]; exists v'. 
        rewrite RE.OP.P.add_neq_o; auto.
        apply wf_env_fT_new in inst; now rewrite <- inst.
  - destruct (Resource.eq_dec r k'); subst.
    -- exists (⩽ … v ⩾); rewrite H1; now apply RE.OP.P.add_eq_o.
    -- apply IHinst in Hfin; destruct Hfin.
        exists x. rewrite H1; now rewrite RE.OP.P.add_neq_o.
Qed.

#[export] 
Instance wfFT_eq : Proper (RC.eq ==> RE.eq ==> iff) (wf_env_fT).
Proof.
  repeat red; split; intros.
  - revert y y0 H0 H; induction H1; subst; intros y y0 Heq Heq'.
    -- apply wfFT_empty; try (now rewrite <- Heq); now rewrite <- Heq'.
    -- eapply wfFT_add; eauto; try (now rewrite <- Heq); now rewrite <- Heq'.
    -- apply (wfFT_update y V y0 r τ τ' v); auto.
        + eapply IHwf_env_fT; auto. reflexivity.
        + rewrite <- Heq'; auto.
        + rewrite <- Heq; auto.
        + now rewrite <- Heq'. 
  - revert x x0 H0 H; induction H1; subst; intros x x0 Heq Heq'.
    -- apply wfFT_empty; try (now rewrite Heq'); now rewrite Heq.
    -- eapply wfFT_add; eauto; try (now rewrite Heq); now rewrite Heq'.
    -- apply (wfFT_update x V x0 r τ τ' v); auto.
        + apply IHwf_env_fT; auto; reflexivity.
        + rewrite Heq'; auto.
        + now rewrite Heq.
        + now rewrite Heq'.
Qed.

Lemma wf_env_fT_well_typed : forall (Re : ℜ) V (r : resource) (v : 𝑣) (πτ : πΤ),
  Wfᵣₜ(Re,V) -> Re ⌈ r ⩦ πτ ⌉ᵣᵪ -> V ⌈ r ⩦ v ⌉ᵣᵦ -> 
  match (πτ,v) with
    | ((_,τ),⩽ v' … ⩾) => ∅ᵥᵪ ⋅ Re ⊫ v' ∈ τ
    | ((τ,_),⩽ … v' ⩾) => ∅ᵥᵪ ⋅ Re ⊫ v' ∈ τ
  end.
Proof.
  intros Re V r v πτ inst; revert r v πτ; induction inst;
  intros r' v' πτ' HfRe HfV; destruct πτ'.
  - apply RC.notEmpty_find_spec in HfRe; auto; contradiction.
  - rewrite H in HfRe; rewrite H0 in HfV.
    apply wf_env_fT_new in inst as Hnew. 
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

Lemma wf_env_fT_in : forall (Re : ℜ) V (r : resource),
  Wfᵣₜ(Re,V) -> r ∈ᵣᵪ Re <-> r ∈ᵣᵦ V.
Proof.
  split.
  - intros; destruct H0; apply RC.OP.P.find_1 in H0. 
    eapply wf_env_fT_domains_match in H0; eauto;
    destruct H0. exists x0; now apply RE.OP.P.find_2.
  - revert r; induction H.
    -- intros. unfold RE.OP.P.Empty in *; exfalso.
       destruct H1. now apply (H0 r x).
    -- intros. unfold RE.OP.P.Add in *. rewrite H1 in *.
       unfold RC.OP.P.Add in *. rewrite H0.
       apply RE.OP.P.add_in_iff in H3; destruct H3; subst.
       + apply wf_env_fT_new in H; rewrite H.
         rewrite RC.OP.P.add_in_iff; now left.
       + rewrite RC.OP.P.add_in_iff; right; now apply IHwf_env_fT.
    -- intros. unfold RE.OP.P.Add in *. rewrite H2 in *. 
       apply IHwf_env_fT. rewrite RE.OP.P.add_in_iff in H4.
       destruct H4; subst; auto.
Qed.

(** ** Lift of multiple evaluation transitions *)

Lemma fT_MeT_sv :  forall (V V' : 𝓥) (st st' st'' t t' : Λ),

        ⊨ st ⟼⋆ st' -> ⪡ V ; st' ; t ⪢ ⭆ ⪡ V' ; st'' ; t' ⪢ -> 
    (*-------------------------------------------------------------*)
              ⪡ V ; st ; t ⪢ ⭆ ⪡ V' ; st'' ; t' ⪢.
Proof.
  intros V V' st st' st'' t t' HmeT. apply multi_indexed in HmeT as [k HieT].
  revert V V' st st' st'' t t' HieT; induction k; intros; inversion HieT; subst; auto.
  apply fT_eT_sv with (st' := y); auto. apply IHk with (st' := st'); auto.
Qed.


Lemma fT_MeT_sf :  forall (V V' : 𝓥) (st st' t t' t'' : Λ),

        ⊨ t ⟼⋆ t' -> ⪡ V ; st ; t' ⪢ ⭆ ⪡ V' ; st' ; t'' ⪢ -> 
    (*-------------------------------------------------------------*)
              ⪡ V ; st ; t ⪢ ⭆ ⪡ V' ; st' ; t'' ⪢.
Proof.
  intros V V' st st' t t' t'' HmeT. apply multi_indexed in HmeT as [k HieT].
  revert V V' st st' t t' t'' HieT; induction k; intros; inversion HieT; subst; auto.
  apply fT_eT_sf with (t' := y); auto. apply IHk with (t' := t'); auto.
Qed.


(** ** Preservation *)

(** *** Proof of preservation of keys in the environment 

  Keeping consistent the typing through the functional transition is 
  required for the resources environment. Thus, knowing that we cannot loose 
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

Section safety.

Hypothesis all_arrow_halting : forall Re t α β,
  ∅ᵥᵪ ⋅ Re ⊫ arr(t) ∈ (α ⟿ β ∣ ∅ᵣₛ) -> forall v, ∅ᵥᵪ ⋅ Re ⊫ v ∈ α -> halts <[t v]>.

(** ** Preservation *)

Theorem functional_preserves_typing (Re : ℜ) (V V' : 𝓥) (tv tv' t t' : Λ) (τ τ' : Τ) (R : resources) :

  (* (1) *) halts t -> (* (2) *) halts tv -> (* (3) *) RE.halts V ->

  (* (4) *) ∅ᵥᵪ ⋅ Re ⊫ t ∈ (τ ⟿ τ' ∣ R) -> (* (5) *) ∅ᵥᵪ ⋅ Re ⊫ tv ∈ τ -> 
  (* (6) *) ⪡ V ; tv ; t ⪢ ⭆ ⪡ V' ; tv' ; t' ⪢ -> 

  (* (7) *) Wfᵣₜ(Re,V) ->

(*---------------------------------------------------------------------------------------------*)
  (*  (8) *)(forall (r : resource), (r ∈ R)%rs -> RE.unused r V) /\
  (*  (9) *)(forall (r : resource), (r ∉ R)%rs /\ (r ∈ᵣᵦ V) -> V ⌊r⌋ᵣᵦ = V' ⌊r⌋ᵣᵦ) /\
  (* (10) *) Wfᵣₜ(Re,V') /\ (* (11) *) (forall (r : resource), (r ∈ R)%rs -> RE.used r V') /\

  (* (12) *) ∅ᵥᵪ ⋅ Re ⊫ tv' ∈ τ' /\ (* (13) *) ∅ᵥᵪ ⋅ Re ⊫ t' ∈ (τ ⟿ τ' ∣ R) /\

  (* (14) *) halts t' /\ (* (15) *) halts tv'/\ (* (16) *) RE.halts V'.
Proof.
  intros Hlt Hltv HltV Hwt Hwtv fT; revert Re R τ τ' Hlt Hltv HltV Hwt Hwtv.
  induction fT; intros Re R α β Hlt Hltv HltV Hwt Hwtv Hinst.
  (* fT_eT_sf *)
  - 
    (* clean *)
    move R before Re; move α before R; move β before α; move fT after IHfT;
    rename fT into HfT; rename H into HeT; move HeT after HfT.
    (* clean *)

    apply evaluate_preserves_typing with (t' := t') in Hwt as Hwt'; auto.
    rewrite evaluate_preserves_halting in Hlt; eauto.
  (* fT_eT_sv *)
  -
    (* clean *)
    move R before Re; move α before R; move β before α; move fT after IHfT;
    rename fT into HfT; rename H into HeT; move HeT after HfT.
    (* clean *)

    apply evaluate_preserves_typing with (t' := st') in Hwtv as Hwtv'; auto.
    rewrite evaluate_preserves_halting in Hltv; eauto.
  (* fT_arr *)
  - 
    (* clean *)
    inversion Hwt; subst; rename H3 into Hwt'; clear Hwt; move Hwt' after Hwtv.
    (* clean *)

    repeat split; auto.
    -- intros r HIn; inversion HIn.
    -- intros r HIn; inversion HIn.
    -- apply wt_app with (τ2 := α); assumption.
    -- eapply all_arrow_halting; eauto; econstructor; eauto.
  (* fT_first *)
  -
    (* clean *)
    inversion Hwt; subst; move Re before V'; move R before Re; move τ1 before τ;
    move τ2 before τ1; clear Hwt; rename H2 into Hwt; move Hwt after Hwtv;
    inversion Hwtv; subst; rename fT into HfT; move HfT after IHfT;
    rename H4 into Hwv1; rename H6 into Hwv2; move Hwv1 before Hwt;
    move Hwv2 before Hwv1; clear Hwtv.
    (* clean *)

    apply IHfT with (R := R) (τ' := τ2) in Hwv1 as IH; auto.
    --  clear IHfT; destruct IH as [Hunsd [Hlcl [Hinst' [Husd [Hwt1' [Hwt' [Hlt' [Hlv1' HltV']]]]]]]].

        (* clean *)
        move Hwt1' before Hwv1; clear Hwv1; move Hlt' before Hlt; move Hlv1' before Hltv; 
        move HltV' before HltV.
        move Hwt' before Hwt; clear Hwt; move Hinst' before Hinst; move Hunsd before Husd.
        (* clean *)

        repeat split; auto.
        + now apply halts_first.
        + rewrite halts_pair in *; destruct Hltv as [_ Hltv2]; split; assumption.

    -- now apply halts_first in Hlt.
    -- rewrite halts_pair in *; destruct Hltv as [Hltv1 _]; assumption.
  (* fT_comp *)
  -
    (* clean *)
    inversion Hwt; subst; apply Resources.eq_leibniz in H7; subst;
    clear Hwt; move Re before V''; move R1 before Re; move R2 before R1; 
    move α before R2; move β before α; move τ before β; rename fT1 into HfT1;
    move HfT1 after IHfT2; rename fT2 into HfT2; move HfT2 after HfT1;
    rename H6 into Hwt1; rename H8 into Hwt2; rename H9 into HEmp;
    move Hwt1 after Hwtv; move Hwt2 before Hwt1.
    (* clean *)

    apply IHfT1 with (R := R1) (τ' := τ) in Hwtv as IH1; auto.
    --  clear IHfT1; destruct IH1 as [Hunsd1 [Hlcl1 [Hinst' 
                                 [Husd1 [Hwtv' [Hwt1' [Hlt1' [Hltv' HltV']]]]]]]].

        (* clean *)
        move Hwtv' before Hwtv; move Hwt1' before Hwt1; move Hinst' before Hinst;
        move Hlt1' before Hlt; move Hltv' before Hltv; move HltV' before HltV.
        (* clean *)

        apply IHfT2 with (R := R2) (τ' := β) in Hwtv' as IH2; auto.
        + clear IHfT2; destruct IH2 as [Hunsd2 [Hlcl2 [Hinst'' 
                                  [Husd2 [Hwtv'' [Hwt2' [Hlt2' [Hltv'' HltV'']]]]]]]].

          (* clean *)
          move Hwtv'' before Hwtv'; move Hwt2' before Hwt2; move Hwt2' before Hwt2;
          move Hunsd2 before Hunsd1; move Hinst'' before Hinst';
          move Husd2 before Husd1; move Hlcl2 before Hlcl1;
          move Hlt2' before Hlt1'; move Hltv'' before Hltv'; move HltV'' before HltV'.
          (* clean *)

          repeat split; auto.
          ++ intros r HIn; rewrite Resources.union_spec in HIn; destruct HIn as [HIn1 | HIn2]; auto.
             apply Hunsd2 in HIn2 as Hunsd. destruct Hunsd as [v HfV'].
             exists v; rewrite Hlcl1; auto; split.

             * intro; symmetry in HEmp. apply Resources.empty_is_empty_2 in HEmp.
               apply (HEmp r); rewrite Resources.inter_spec; now split.
             * destruct Hlt2' as [t2'' [HmeT Hvt2'']].
               eapply multi_preserves_typing in Hwt2' as Hwt2''; eauto.
               eapply typing_Re_R with (Re := Re) in Hwt2'' as HInRe; eauto.
               eapply wf_env_fT_in in HInRe; eauto.

          ++ intros r [HnIn HIn]; rewrite Resources.union_notin_spec in HnIn; 
             destruct HnIn as [HnIn1 HnIn2]. rewrite Hlcl1; auto.
             apply Hlcl2; split; auto. eapply functional_preserves_keys; eauto. 

          ++  intros r HIn; rewrite Resources.union_spec in HIn; destruct HIn as [HIn | HIn]; auto.
              assert (HnIn' : (r ∉ R2)%rs). 
                { 
                  intro. symmetry in HEmp; apply Resources.empty_is_empty_2 in HEmp; 
                  apply (HEmp r); rewrite Resources.inter_spec; split; auto. 
                }

              apply Husd1 in HIn as HuV'; destruct HuV' as [v HfV'].
              exists v. rewrite <- Hlcl2; auto; split; auto.
              exists (⩽ … v ⩾); now apply RE.OP.P.find_2.

          ++ econstructor; eauto. reflexivity.

          ++ rewrite halts_comp in *; split; assumption.
        + now apply halts_comp in Hlt as [].
    -- now apply halts_comp in Hlt as [].
  (* fT_rsf *)
  -
    (* clean *)
    inversion Hwt; subst; clear Hwt; move Re before V; rename H into HfV; rename H4 into HfRe;
    move HfV after HfRe. 
    (* clean *)

    repeat split.
    -- intros r' HIn; rewrite Resources.singleton_spec in HIn; subst; now exists v.
    -- intros r' [HnIn HIn]; apply Resources.singleton_notin_spec in HnIn.
       rewrite RE.OP.P.add_neq_o; auto.
    -- eapply wfFT_update; eauto.
       + apply RE.OP.P.in_find; intro c; rewrite HfV in c; inversion c.
       + unfold RE.OP.P.Add; reflexivity.
    -- intros r' HIn; apply Resources.singleton_spec in HIn; subst; unfold RE.used.
       exists st; now apply RE.OP.P.add_eq_o.
    -- apply wf_env_fT_well_typed with (V := V) (v := ⩽ v … ⩾) in HfRe; try assumption.
    -- now constructor.
    -- exists <[rsf[r]]>; split; auto.
    -- unfold RE.halts in HltV; apply HltV in HfV; now simpl in *.
    -- unfold RE.halts in *; intros. rewrite RE.OP.P.add_o in H.
       destruct (Resource.eq_dec r r0); subst.
       + now inversion H; subst; simpl.
       + apply (HltV r0 _ H).
Qed.



(** ** Progress *)

Theorem progress_of_functional_value (Re : ℜ) (V : 𝓥) (tv t : Λ) (τ τ' : Τ) (R : resources) :

    (* (1) *) halts tv -> (* (2) *) RE.halts V ->
    
    (* (3) *) value(t) -> 

    (* (4) *) ∅ᵥᵪ ⋅ Re ⊫ t ∈ (τ ⟿ τ' ∣ R) -> 
    (* (5) *) ∅ᵥᵪ ⋅ Re ⊫ tv ∈ τ ->

    (* (6) *) Wfᵣₜ(Re,V) -> (* (7) *) (forall (r : resource), (r ∈ R)%rs -> RE.unused r V) ->

  (*-------------------------------------------------------------------------------------------------*)
    (exists (V' : 𝓥) (tv' : Λ), (* (8) *) ⪡ V ; tv ; t ⪢ ⭆ ⪡ V' ; tv' ; t ⪢ /\ 
                                (* (9) *) halts tv' /\ (* (10) *) RE.halts V').
Proof.
  intros Hltv HltV Hvt wt; revert V tv Hltv HltV Hvt.
  dependent induction wt; intros V tv Hltv HltV Hvt Hwtv Hinst Hunsd; inversion Hvt; subst.
  (* wt-arr *)
  -
    (* clean *)
    clear Hvt; rename H0 into Hvt; move V before Re; move tv before t; clear IHwt; move wt before Hwtv.
    (* clean *)

    exists V; exists <[t tv]>; repeat split; auto.
    -- now repeat constructor.
    -- apply (all_arrow_halting Re _ τ τ'); auto. 
  (* wt-first *)
  -
    (* clean *)
    clear Hvt; rename H0 into Hvt; move V before Re; move tv before t; move wt before Hwtv.
    (* clean *)

    destruct Hltv as [tv' [HmeT Hvtv']].
    apply multi_preserves_typing with (t' := tv') in Hwtv as Hwtv'; auto.
    destruct tv'; subst; inversion Hwtv'; subst; inversion Hvtv'; subst.

    (* clean *)
    clear Hwtv Hwtv' Hvtv'; rename H4 into Hwtv'1; rename H6 into Hwtv'2.
    rename H1 into Hvtv'1; rename H2 into Hvtv'2. move wt before Hwtv'1.
    move tv'1 before tv; move tv'2 before tv'1; move Hvt before Hvtv'1.
    (* clean *)

    eapply IHwt in Hwtv'1 as IH; eauto; clear IHwt.
    -- destruct IH as [V' [tv''1 [HfT [Hltv''1 HltV']]]].
       exists V'; exists <[⟨tv''1,tv'2⟩]>; repeat split; auto.
       + apply fT_MeT_sv with (st' := <[⟨tv'1,tv'2⟩]>); auto.
         now constructor.
       + apply halts_pair; split; auto. exists tv'2; auto.
    -- exists tv'1; split; auto.
  (* wt-comp *)
  -
    (* clean *)
    clear Hvt; rename H3 into Hvt1; rename H4 into Hvt2; move V before Re; move tv before t2.
    move wt1 before Hwtv; move wt2 before Hwtv. rename H into Hunion; rename H0 into Hempty.
    (* clean *)

    eapply IHwt1 in Hwtv as IH; eauto.
    -- clear IHwt1; destruct IH as [V' [tv' [HfT [Hltv' HltV']]]].

      (* clean *)
      move HfT before Hwtv; move V' before V; move tv' before tv;
      move Hltv' before Hltv; move HltV' before HltV.
      (* clean *)
    
      eapply functional_preserves_typing in HfT as H; eauto.
      destruct H as [_ [HwfV [Hinst' [Husd [Hwtv' _]]]]].

      (* clean *)
      move Husd before Hunsd; move HwfV before Husd; move Hinst' before Hinst; 
      move Hwtv' before Hwtv.
      (* clean *)

      eapply IHwt2 in Hwtv' as IH; eauto.

      + clear IHwt2; destruct IH as [V'' [tv'' [HfT' [Hltv'' HltV'']]]]. 

        (* clean *)
        move HfT' before HfT; move V'' before V'; move tv'' before tv';
        move Hltv'' before Hltv'; move HltV'' before HltV'.
        (* clean *)

        exists V''; exists tv''; repeat split; auto.
        eapply fT_comp; eauto.

      + intros r HIn. destruct (Hunsd r).
        ++ rewrite Hunion; rewrite Resources.union_spec; now right.
        ++ exists x; rewrite <- HwfV; auto; split.
           * intro HIn'; assert (r ∈ R1 ∩ R2)%rs.
             { rewrite Resources.inter_spec; split; auto. }
             rewrite <- Hempty in H0; inversion H0.
           * exists (⩽ x … ⩾); now apply RE.OP.P.find_2.
        
      + exists t1; split; auto.

    -- intros r HI. apply Hunsd; rewrite Hunion. rewrite Resources.union_spec; now left.
  (* wt-rsf *)
  - 
    (* clean *)
    clear all_arrow_halting Hvt. rename H into HfRe; move HfRe before Hwtv.
    (* clean *)

    destruct (Hunsd r); try (now apply Resources.singleton_spec). 
    
    (* clean *)
    move x before tv; rename H into HfV; move HfV before HfRe.
    (* clean *)

    exists (⌈r ⤆ ⩽ … tv ⩾⌉ᵣᵦ V); exists x. repeat split.
    -- now apply fT_rsf.
    -- unfold RE.halts in *. apply HltV in HfV; now simpl in *.
    -- unfold RE.halts in *; intros. rewrite RE.OP.P.add_o in H.
       destruct (Resource.eq_dec r r0); subst.
       + now inversion H; subst; simpl.
       + apply (HltV r0 _ H).
Qed.

Theorem progress_of_functional(Re : ℜ) (V : 𝓥) (tv t : Λ) (τ τ' : Τ) (R : resources) :

  (* (1) *) halts t -> (* (2) *) halts tv -> (* (3) *) RE.halts V ->

  (* (4) *) ∅ᵥᵪ ⋅ Re ⊫ t ∈ (τ ⟿ τ' ∣ R) -> (* (5) *) ∅ᵥᵪ ⋅ Re ⊫ tv ∈ τ ->

  (* (6) *) Wfᵣₜ(Re,V) -> (* (7) *) (forall (r : resource), (r ∈ R)%rs -> RE.unused r V) ->

  (*-------------------------------------------------------------------------------------------------*)
    (exists (V' : 𝓥) (tv' t' : Λ), (*  (8) *) ⪡ V ; tv ; t ⪢ ⭆ ⪡ V' ; tv' ; t' ⪢ /\
                                   (*  (9) *) halts t' /\ (* (10) *) halts tv'/\ 
                                   (* (11) *) RE.halts V').
Proof. 
  intros Hlt; destruct Hlt as [t' [HmeT Hvt']]. apply multi_indexed in HmeT as [k HieT].
  revert Re V tv t τ τ' R t' HieT Hvt'. induction k; 
  intros Re V tv t τ τ' R t' HieT Hvt' Hltv HltV Hwt Hwtv Hinst Hunsd.
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
    exists V'; exists tv'; exists t1'; split; auto; eapply fT_eT_sf; eauto.
Qed.

(** *** Proof of Resource safety *)
Theorem safety_resources_interaction (Re : ℜ) (V : 𝓥) (t : Λ) (τ τ' : Τ) (R : resources) :

    (* (1) *) halts t -> (* (2) *) RE.halts V ->

    (* (3) *) Wfᵣₜ(Re,V) -> (* (4) *) (forall (r : resource), (r ∈ R)%rs -> RE.unused r V) ->

    (* (5) *) ∅ᵥᵪ ⋅ Re ⊫ t ∈ (τ ⟿ τ' ∣ R) -> 

  (*-----------------------------------------------------------------------------------------------*)
    forall (tv : Λ), (* (6) *) halts tv -> (* (7) *) ∅ᵥᵪ ⋅ Re ⊫ tv ∈ τ -> 

    exists (V' : 𝓥) (tv' t' : Λ), 
      (*  (8) *) ⪡ V ; tv ; t ⪢ ⭆ ⪡ V' ; tv' ; t' ⪢ /\

      (*  (9) *) (forall (r : resource), (r ∉ R)%rs /\ (r ∈ᵣᵦ V) -> V ⌊r⌋ᵣᵦ = V' ⌊r⌋ᵣᵦ) /\
      (* (10) *) (forall (r : resource), (r ∈ R)%rs -> RE.used r V').
Proof.
  intros Hlt HltV Hinst Hunsd Hwt tv Hltv Hwtv.
  apply (progress_of_functional _ V _ t _ τ' R) in Hwtv as prog; auto.
  destruct prog as [V' [tv' [t' [HfT [Hlt' [Hltv' HltV']]]]]].

  (* clean *)
  move tv before t; move tv' before tv; move t' before t; move V' before V;
  move HltV' before HltV; move Hlt' before Hlt; move Hltv' before Hltv; move Hwt before Hwtv;
  move Hunsd after HfT; move Hinst before Hunsd.
  (* clean *)

  apply (functional_preserves_typing _ V V' _ tv' t t' _ τ' R) in Hwtv as preserve; auto.
  destruct preserve as [_ [Htr [Hinst' [Husd [Hwtv' Hwt']]]]].

  (* clean *)
  move Hinst' before Hinst; move Hwtv' before Hwtv; move Hwt' before Hwt.
  (* clean *)

  exists V'; exists tv'; exists t'; repeat split; assumption.
Qed.

End safety.