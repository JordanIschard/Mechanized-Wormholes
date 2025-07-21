From Coq Require Import Lia Morphisms Lists.List Arith Lists.Streams.
From Mecha Require Import Resource Resources Term Typ Cell VContext RContext  
                          Type_System Evaluation_Transition Functional_Transition 
                          REnvironment Stock SREnvironment.
Import ResourceNotations TermNotations TypNotations CellNotations ListNotations
       VContextNotations RContextNotations REnvironmentNotations ResourcesNotations 
       SetNotations StockNotations SREnvironmentNotations.

(** * Semantics - Temporal

  Wormholes’s dynamic semantics is split in three sets of transition rules: the evaluation transition, defined in [Evaluation_Transition.v], which extends standard β-reduction; the functional transition which performs the logical instant, defined in [Functional_Transition.v], and the temporal transition which corresponds to the reactivity of the program: it initializes the resources values, performs the instant via the functional transition and updates the system. In this file, we focus on the temporal transition.
*)


(** ** Definition - Temporal *)

Module RE := REnvironment.
Module SRE := SREnvironment.
Module ST := Stock.
Module RC := RContext.



(** *** Well-formed environments-context *)


Definition well_formed_tt (Rc : ℜ) (R : 𝐄) (W : 𝐖) :=
  (* all ressources in the context are in the stock or the input environment or both *)
  (forall (r : resource), (r ∈ Rc)%rc <->  (In r (ST.keys W)) \/ (r ∈ R)%sr) /\ 
  (* the stock and the input environment are disjoint *)
  (forall (r : resource), (In r (ST.keys W)) -> (r ∉ R)%sr) /\
  (* the context, the stock and the input environment are well-formed under themselves *)
  (Rc⁺ ⊩ Rc)%rc /\ (R⁺ ⊩ R)%sr /\ (ST.Wf (W⁺)%sk W) /\
  (* all terms in the stock are well-typed and have the type form (𝟙,α), it is a "get" interaction *)
  (forall (r : resource) (α : πΤ) (v : Λ), 
      Rc⌊r⌋%rc = Some α -> 
      R⌊r⌋%sr = Some v ->
      (∅)%vc ⋅ Rc ⊢ {Term.shift (R⁺)%sr ((max (R⁺)%sr (W⁺)%sk) - (R⁺)%sr) v} ∈ {snd α}) /\
  (forall (r r' : resource) (α β : Τ) (v : Λ),
      Rc⌊r⌋%rc = Some (α,β) -> In (r,r',v) W ->  ∅%vc ⋅ Rc ⊢ v ∈ β /\ α = <[𝟙]>)
      /\
  (forall (r r' : resource) (α β : Τ) (v : Λ),
      Rc⌊r'⌋%rc = Some (α,β) -> In (r,r',v) W -> ∅%vc ⋅ Rc ⊢ v ∈ α /\ β = <[𝟙]>)
      /\
  NoDup (ST.keys W) /\
   (* If the stock is empty then the new key of the stock is equal to the new key of the context *)
  (~ W = [] -> (W⁺)%sk = (Rc⁺)%rc /\ (W⁺)%sk > (R⁺)%sr).


Notation "'WFₜₜ(' Rc , R , W )" := (well_formed_tt Rc R W) (at level 50).


(** *** [puts] function *)

Definition put_aux (r: resource) (V: 𝐕) :=
  match (V⌊r⌋) with
    | Some (Cell.out v) => Some v
    | _ => None 
  end.

Definition puts (put : resource * (option Λ) -> Λ) (R : 𝐄) (V: 𝐕) :=
  SRE.foldkeys (fun k acc => ⌈k ⤆ put (k,(put_aux k V))⌉ acc)%sr R ∅%sr.

(** *** Initialize the input resource environment 

  The input resource environment consists of locals resources (from W) and global resources (from R). Global resources, at the first instant, are well formed under R. After that, they must be shift in order to be well formed under the maximum between W⁺ and R⁺ because W may contains local resources which are, by construction, greater than global resources. 
*)

Definition init_input_env (R : 𝐄) (W : 𝐖) : 𝐕 :=
  ST.init_locals W 
  (SRE.init_globals (SRE.shift (R⁺)%sr ((max (R⁺)%sr (W⁺)%sk) - (R⁺)%sr) R)).

(** *** Temporal transition *)

Definition temporal (put : resource * (option Λ) -> Λ) (R R': 𝐄) (P P' : Λ) (W W' : 𝐖) :=

  (** (1) Initialize the local memory [Vin] with global and local resources. *)
  let Vin := init_input_env R W in

  exists (Vout : 𝐕) Wnew _tv,
  (** (2) Perform the instant with the functional transition. *)                  
  ⪡ Vin ; unit ; P ⪢ ⭆ ⪡ Vout ; _tv ; P' ; Wnew ⪢ /\

  (** (3) Update the global and local resources. *)               
  (R' = puts put R Vout)%sr  /\
  (W' = (ST.update_locals (([⧐ (W⁺)%sk – (Vout⁺ - (W⁺)%sk)%re] W) ++ Wnew) Vout))%sk.

Notation "# n '⟦' R ';' W ';' P '⟧' '⟾' '⟦' S1 ';' W1 ';' P1 '⟧'" := (temporal n R S1 P P1 W W1) 
(at level 30, R constr, S1 constr, P custom wh, P1 custom wh, W constr, W1 constr, no associativity).

(** ---- *)

(** *** [puts] properties *)

Section put_props.

Variable put : resource * (option Λ) -> Λ. 

#[export] Instance aux_eq (V: 𝐕) : Proper (eq ==> SRE.eq ==> SRE.eq) 
  (fun (k: resource) (acc : SRE.t) => (⌈k ⤆ put (k, put_aux k V) ⌉ acc)%sr).
Proof.
  intros r' r Heqr R R' HeqR; subst.
  now rewrite HeqR.
Qed.

Lemma aux_diamond  (V: 𝐕) : SRE.Diamond SRE.eq 
  (fun (k: resource) (_: Λ) (acc : SRE.t) => (⌈ k ⤆ put (k, put_aux k V) ⌉ acc)%sr).
Proof.
  intros r r' _ _ R1 R R' Hneq Heq Heq'.
  rewrite <- Heq, <- Heq'.
  rewrite SRE.add_add_2; now auto.
Qed.

Hint Resolve srenvironment_equiv_eq aux_eq aux_diamond : core.

Lemma puts_Empty (R: 𝐄)  (V: 𝐕) :
  (isEmpty(R))%sr -> (isEmpty(puts put R V))%sr.
Proof.
  intro HEmp; unfold puts.
  rewrite SRE.foldkeys_Empty; auto.
  apply SRE.empty_1.
Qed.

Lemma puts_Empty_iff (R: 𝐄)  (V : 𝐕) :
  (isEmpty(R))%sr -> ((puts put R V) = ∅)%sr.
Proof.
  intro HEmp; unfold puts.
  rewrite SRE.foldkeys_Empty; now auto.
Qed.

Lemma puts_Add (r: resource) (e: Λ) (R R': 𝐄) (V: 𝐕) :
  (r ∉ R)%sr -> SRE.Add r e R R' ->
  (puts put R' V = (⌈r ⤆ put (r,(put_aux r V))⌉ (puts put R V))%sr)%sr.
Proof.
  intros HnIn HAdd.
  unfold puts at 1.
  rewrite SRE.foldkeys_Add; now auto.
Qed.

#[export] Instance puts_eq : Proper (SRE.eq ==> RE.eq ==> SRE.eq) (puts put).
Proof.
  intros R R' HeqR V V' HeqV.
  revert R' HeqR.
  induction R using SRE.map_induction; intros R' Heq.
  - do 2 (rewrite puts_Empty_iff; auto).
    -- reflexivity.
    -- now rewrite <- Heq.
  - rewrite puts_Add; eauto.
    rewrite (puts_Add x e R1 R'); auto.
    -- unfold put_aux.
       destruct (V⌊x⌋)%re eqn:Hfi.
       + rewrite HeqV in Hfi.
         rewrite Hfi.
         now rewrite (IHR1 R1).
       + rewrite HeqV in Hfi.
         rewrite Hfi.
         now rewrite (IHR1 R1).
    -- unfold SRE.Add in *.
       now rewrite <- Heq.
Qed.  

Lemma puts_add (r: resource) (e: Λ) (R: 𝐄) (V: 𝐕) :
  (r ∉ R)%sr ->
  (puts put (⌈r ⤆ e⌉ R) V = ⌈r ⤆ put (r,(put_aux r V))⌉ (puts put R V))%sr.
Proof.
  intro HnIn.
  rewrite (puts_Add r e R); auto.
  - reflexivity.
  - apply SRE.Add_add. 
Qed.

Lemma puts_in_iff (R: 𝐄) (V: 𝐕) (r: resource) :
  (r ∈ R)%sr <-> (r ∈ (puts put R V))%sr.
Proof.
  revert r.
  induction R using SRE.map_induction; intro r.
  - split; intros [v HM]; exfalso.
    -- apply (H r v HM).
    -- apply (puts_Empty _ V) in H.
       apply (H r v HM).
  - unfold SRE.Add in H0; rewrite H0; clear H0.
    rewrite puts_add; auto.
    do 2 rewrite SRE.add_in_iff.
    now rewrite IHR1.
Qed.

Lemma puts_new_key (R: 𝐄)  (V: 𝐕) :
  (R⁺)%sr = ((puts put R V)⁺)%sr.
Proof.
  induction R using SRE.map_induction.
  - do 2 (rewrite SRE.Ext.new_key_Empty; auto).
    now apply puts_Empty.
  - unfold SRE.Add in *; rewrite H0; clear H0.
    rewrite puts_add; auto.
    do 2 rewrite SRE.Ext.new_key_add_max; lia.
Qed.

Lemma puts_Wf (k : lvl) (R : 𝐄)  (V: 𝐕) :
  (forall r v, (r ∈ R)%sr -> k ⊩ put (r,v))%tm ->
  (k ⊩ R)%sr -> (k ⊩ (puts put R V))%sr.
Proof.
  revert V.
  induction R using SRE.map_induction; intros V Hwfput HwfR.
  - rewrite puts_Empty_iff; auto.
    apply SRE.Wf_empty.
  - unfold SRE.Add in H0; rewrite H0 in *.
    rewrite puts_add; auto.
    apply SRE.Wf_add_notin in HwfR as [Hwfx [_ Hwfe1]]; auto.
    apply SRE.Wf_add_notin.
    -- now rewrite <- puts_in_iff.
    -- repeat (split; auto).
       + apply Hwfput.
         rewrite H0.
         rewrite SRE.add_in_iff; now left.
       + apply IHR1; auto.
         intros.
         apply Hwfput.
         rewrite H0.
         rewrite SRE.add_in_iff; now right.
Qed.

Lemma puts_Wf_V (R : 𝐄)  (V: 𝐕) :
  (forall r v, (V⁺) ⊩ put (r,v))%tm ->
  (R⁺)%sr <= V⁺ -> ((V⁺) ⊩ V) -> ((V⁺)%re ⊩ (puts put R V))%sr.
Proof.
  revert V.
  induction R using SRE.map_induction; intros V Hwfput Hleq HwfV.
  - rewrite puts_Empty_iff; auto.
    apply SRE.Wf_empty.
  - unfold SRE.Add in H0; rewrite H0 in *; clear H0.
    rewrite puts_add; auto.
    apply SRE.Wf_add_notin.
    -- now rewrite <- puts_in_iff.
    -- rewrite SRE.Ext.new_key_add_max in Hleq.
       repeat (split; auto).
       + unfold Resource.Wf; lia.
       + apply IHR1; auto; lia. 
Qed.

Lemma puts_halts (k: lvl) (R : 𝐄)  (V: 𝐕) :
  (forall r v, halts k (put (r,v)))%tm ->
  SRE.halts k (puts put R V).
Proof.
  intro Hyput.
  induction R using SRE.map_induction.
  - apply SRE.halts_Empty.
    now apply puts_Empty.
  - unfold SRE.Add in H0; rewrite H0 in *; clear H0.
    rewrite puts_add; auto.
    apply SRE.halts_add; split; auto.
Qed.

Lemma puts_halts_1 (R : 𝐄)  (V: 𝐕) :
  (forall r v, halts (R⁺)%sr (put (r,v)))%tm ->
  SRE.halts ((puts put R V)⁺)%sr (puts put R V).
Proof.
  intro Hyput.
  apply puts_halts.
  intros r v.
  rewrite <- puts_new_key.
  now apply Hyput.
Qed.

Lemma puts_find (R : 𝐄) (V: 𝐕) (r: resource) (v: Λ) :
  (puts put R V ⌊r⌋)%sr = Some v -> exists v', (v = put (r, v'))%type.
Proof.
  revert r v; induction R using SRE.map_induction; intros r v Hfi. 
  - exfalso.
    apply (puts_Empty _ V) in H.
    apply (H r v).
    now apply SRE.find_2.
  - unfold SRE.Add in H0; rewrite H0 in *; clear H0.
    rewrite puts_add in Hfi; auto.
    destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- rewrite SRE.add_eq_o in Hfi; auto.
       inversion Hfi; subst; clear Hfi.
       now exists (put_aux r V).
    -- rewrite SRE.add_neq_o in Hfi; auto.
Qed.

End put_props.

(** *** [init_input_env] property *)

Lemma init_input_env_in_iff (R: 𝐄) (W: 𝐖) (r: resource) : 
  (In r (ST.keys W)) \/ (r ∈ R)%sr <-> r ∈ init_input_env R W.
Proof.
  unfold init_input_env.
  rewrite ST.init_locals_in_iff.
  rewrite SRE.init_globals_in_iff.
  now rewrite SRE.shift_in_new_key.
Qed.

Lemma init_input_env_new_key (R: 𝐄) (W: 𝐖) :
  (init_input_env R W)⁺ = max (R⁺)%sr (W⁺)%sk.
Proof.
  unfold init_input_env.
  rewrite ST.init_locals_new_key.
  replace (Nat.max (R⁺)%sr (W⁺)%sk) with (Nat.max (W ⁺)%sk (R⁺)%sr) by lia.
  f_equal.
  rewrite SRE.init_globals_new_key.
  rewrite SRE.shift_new_refl; auto.
Qed.

Lemma init_input_env_Wf (R: 𝐄) (W: 𝐖) :
  (~ W = [] -> (W⁺)%sk > (R⁺)%sr) ->
  (R⁺ ⊩ R)%sr -> (W⁺ ⊩ W)%sk ->
  (init_input_env R W)⁺ ⊩ init_input_env R W.
Proof.
  intros HnEmp HwfS HwfW.
  rewrite init_input_env_new_key.
  unfold init_input_env.
  apply ST.init_locals_Wf.
  destruct W.
  - simpl; rewrite max_l by lia.
    split.
    -- intros r Hc; inversion Hc.
    -- replace (R⁺ - R⁺)%sr with 0 by lia.
       apply SRE.init_globals_Wf.
       now rewrite SRE.shift_zero_refl.
  - assert (p :: W <> []) by (intro Hc; inversion Hc).
    apply HnEmp in H. 
    remember (p :: W) as W'.
    rewrite max_r by lia; split; auto.
    apply SRE.init_globals_Wf.
    apply SRE.shift_preserves_wf_2; auto; lia.
Qed.

Lemma init_input_env_find_e r c (R: 𝐄) (W: 𝐖) :
  init_input_env R W ⌊ r ⌋ = Some c -> exists v, Logic.eq c (Cell.inp v).
Proof.
  clear.
  intros Hfi.
  unfold init_input_env in Hfi.
  apply ST.init_locals_find_e in Hfi; auto.
  clear Hfi; intro Hfi.
  now apply SRE.init_globals_find_e in Hfi.
Qed.

Lemma init_input_env_W r v R W :
  (r ∉ R)%sr ->
  init_input_env R W ⌊r⌋ = Some (Cell.inp v) ->
  exists r', 
  (In (r,r',v) W \/ (exists v', In (r',r,v') W /\ v = Term.tm_unit)).
Proof.
  intros HnIn Hfi.
  unfold init_input_env in *.
  apply ST.init_locals_find_W in Hfi; auto.
  rewrite SRE.init_globals_in_iff.
  intro HIn.
  rewrite SRE.shift_in_new_key in HIn; contradiction.
Qed.

Lemma init_input_env_R r v R W :
  (r ∉ ST.keys W)%sk ->
  init_input_env R W ⌊r⌋ = Some (Cell.inp v) ->
  exists v', 
  (R ⌊r⌋)%sr = Some v' /\ (Term.shift (R⁺)%sr ((max (R⁺)%sr (W⁺)%sk) - (R⁺)%sr) v') = v.
Proof.
  intros.
  unfold init_input_env in *.
  apply ST.init_locals_find_V in H0; auto.
  apply SRE.init_globals_find_iff in H0.
  apply SRE.shift_find_e_1 in H0 as HI.
  destruct HI as [[r' Heq] [v' Heq']]; subst.
  exists v'; split; auto.
  rewrite <- SRE.shift_find_iff in H0.
  assert (HIn : (r' ∈ R)%sr).
  { exists v'; now apply SRE.find_2. }
  apply SRE.Ext.new_key_in in HIn.
  rewrite Resource.shift_wf_refl; auto.
Qed. 

  

(** *** [eqDom] properties *)


Lemma TT_EqDom_Empty (Rc : ℜ) (R : 𝐄) (W : 𝐖) :
  (forall r : resource, (r ∈ Rc)%rc <-> (In r (ST.keys W)) \/ (r ∈ R)%sr) -> 
  RC.Empty Rc <-> (SRE.Empty R) /\ W = [].
Proof.
  intro HIn; split.
  - intros HEmp; split.
    -- intros k v HM.
       assert ((In k (ST.keys W)) \/ (k ∈ R)%sr).
       + right; now exists v.
       + rewrite <- HIn in H.
         destruct H as [v' HM'].
         apply (HEmp k v' HM').
    -- destruct W; auto.
       destruct p as [[rg rs] v].
       assert ((rg ∈ Rc)%rc).
       { rewrite HIn; simpl; auto. }
       exfalso.
       destruct H as [v' HM'].
       apply (HEmp rg v' HM').
  - intros [HEmpS HEmpW] k v HM; subst; simpl in *.
    assert (k ∈ Rc)%rc by now exists v.
    rewrite HIn in H.
    destruct H as [HIn' | [v' HM']]; try contradiction.
    apply (HEmpS k v' HM').
Qed. 

Lemma TT_EqDom_new (Rc : ℜ) (R : 𝐄) (W : 𝐖) :
  NoDup (ST.keys W) -> 
  (forall (r : resource), (In r (ST.keys W)) -> (r ∉ R)%sr) ->
  (forall r : resource, (r ∈ Rc)%rc <-> (In r (ST.keys W)) \/ (r ∈ R)%sr) ->  
  (Rc⁺)%rc = max (R⁺)%sr (W⁺)%sk.
Proof.
  clear.
  revert Rc R; induction W; intros Rc R HNoD HDisj HeqDom.
  - simpl.
    rewrite max_l by lia.
    assert (HDom : forall r : resource, (r ∈ Rc)%rc <-> (r ∈ R)%sr).
    { 
      intro r; split; intro HIn.
      - rewrite HeqDom in HIn; destruct HIn; auto.
        simpl in *; inversion H.
      - rewrite HeqDom; auto.
    }
    clear HeqDom HNoD.
    revert R HDom HDisj; induction Rc using RC.map_induction; intros R HDom HDisj.
    -- clear HDisj.
       revert HDom; induction R using SRE.map_induction; intros HDom.
       + rewrite RC.Ext.new_key_Empty; auto. 
         rewrite SRE.Ext.new_key_Empty; auto.
       + exfalso.
         assert (x ∈ Rc)%rc.
         { 
          rewrite HDom; unfold SRE.Add in H1; rewrite H1. 
          rewrite SRE.add_in_iff; auto.
         }
         destruct H2.
         now apply (H x x0).
    -- unfold RC.Add in H0; rewrite H0 in *.
       assert (x ∈ R)%sr.
       { rewrite <- HDom, H0, RC.add_in_iff; auto. }
       destruct H1 as [v Hfi].
       apply SRE.find_1 in Hfi.
       rewrite <- SRE.add_id in Hfi.
       rewrite <- Hfi.
       rewrite <- SRE.add_remove_1 in *.
       rewrite SRE.Ext.new_key_add_max.
       rewrite RC.Ext.new_key_add_max.
       f_equal.
       apply IHRc1; auto.
       intro r; split; intro HIn.
       + assert (r ∈ Rc2)%rc.
         { rewrite H0, RC.add_in_iff; auto. }
         rewrite HDom in H1.
         rewrite SRE.remove_in_iff; split; auto.
         destruct (Resource.eq_dec x r); subst; auto.
       + apply SRE.remove_in_iff in HIn as [Hneq HIn].
         rewrite <- HDom in HIn.
         rewrite H0 in HIn.
         apply RC.add_in_iff in HIn as [Heq | HIn]; auto.
         contradiction.
  - destruct a as [[rg rs] v]. 
    rewrite ST.new_key_cons.
    assert (HDisj' : forall r : resource, (r ∈ ST.keys W)%sk -> (r ∉ R)%sr).
    { intros; apply HDisj; simpl; auto. }
    simpl in HNoD.
    inversion HNoD; subst.
    simpl in H1.
    apply Classical_Prop.not_or_and in H1 as [Hneq HnIn].
    inversion H2; subst.
    rename H1 into HnIn'; clear H2 HNoD; rename H3 into HNoD.
    assert (HeqDom' : forall r : resource, 
                        (r ∈ (RC.Raw.remove rg (RC.Raw.remove rs Rc)))%rc <-> 
                        (r ∈ ST.keys W)%sk \/ (r ∈ R)%sr).
    {
      intro r.
      do 2 (rewrite RC.remove_in_iff); split.
      - intros [Hneq' [Hneq'' HIn]]; simpl in *.
        apply HeqDom in HIn as [[|[|HIn]]|]; subst; auto; try contradiction.
      - intros [|].
        -- do 2 (split; try (intro Heq; subst; contradiction)).
           rewrite HeqDom; simpl; auto.
        -- split.
           + intro; subst.
             revert H; apply HDisj; simpl; auto.
           + split.
             ++ intro; subst.
                revert H; apply HDisj; simpl; auto.
             ++ rewrite HeqDom; simpl; auto.  
    }
    assert (HIn : (rs ∈ Rc)%rc).
    { apply HeqDom; simpl; auto. }
    assert (HIn' : (rg ∈ RC.Raw.remove rs Rc)%rc).
    { 
      apply RC.remove_in_iff; split; auto.  
      apply HeqDom; simpl; auto.
    }
    apply RC.new_key_in_remove_1 in HIn.
    apply RC.new_key_in_remove_1 in HIn'.
    rewrite HIn, HIn'; clear HIn HIn'.
    rewrite IHW with (R := R); auto; lia.
Qed.

#[export] Instance WF_in_eq : Proper (RContext.eq ==> SRE.eq ==> Logic.eq ==> iff) well_formed_tt.
Proof.
  intros Rc Rc1 HeqRe R R' HeqS W W' HeqW; subst; split.
  - intros [HeqDom [HDisj [HvRc [HvS [HvW [Hwt [Hwt' [Hwt'' [HND HnEmp]]]]]]]]].
    split.
    { intro r; rewrite <- HeqS, <- HeqRe; auto. }
    split.
    { intro r; rewrite <- HeqS; auto. }
    split; try (now rewrite <- HeqRe).
    split; try (now rewrite <- HeqS).
    split; auto.
    split.
    {
      intros r πα v.
      rewrite <- HeqS, <- HeqRe.
      apply Hwt.
    }
    split.
    { 
      intros r r' ty ty' v Hfi HIn.
      rewrite <- HeqRe in *.
      eapply Hwt'; eauto.
    }
    split.
    {
      intros r r' ty ty' v Hfi HIn.
      rewrite <- HeqRe in *.
      eapply Hwt''; eauto.
    }
    { 
      rewrite <- HeqRe, <- HeqS; auto. 
    }
  - intros [HeqDom [HDisj [HvRc [HvS [HvW [Hwt [Hwt' [Hwt'' [HND HnEmp]]]]]]]]].
    split.
    { intro r; rewrite HeqS, HeqRe; auto. }
    split.
    { intro r; rewrite HeqS; auto. }
    split; try (now rewrite HeqRe).
    split; try (now rewrite HeqS).
    split; auto.
    split.
    {
      intros r πα v.
      rewrite HeqS, HeqRe.
      apply Hwt.
    }
    split.
    { 
      intros r r' ty ty' v Hfi HIn.
      rewrite HeqRe in *.
      eapply Hwt'; eauto.
    }
    split.
    {
      intros r r' ty ty' v Hfi HIn.
      rewrite HeqRe in *.
      eapply Hwt''; eauto.
    }
    { 
      rewrite HeqRe, HeqS; auto. 
    }
Qed.

Lemma WF_tt_new (Rc : ℜ) (R : 𝐄) (W : 𝐖) :
  WFₜₜ(Rc, R, W) -> (Rc⁺)%rc = max (R⁺)%sr (W⁺)%sk.
Proof.
  intros [HeqDom [HDisj [_ [_ [_ [_ [_ [_ [HNoD _]]]]]]]]].
  apply TT_EqDom_new; auto.
Qed.

Lemma WF_tt_Wf (Rc : ℜ) (R : 𝐄) (W : 𝐖) :
  WFₜₜ(Rc, R, W) -> (Rc⁺ ⊩ Rc)%rc /\ (R⁺ ⊩ R)%sr /\ (W⁺ ⊩ W)%sk.
Proof.
  intros [_ [_ [HwfRc [HwfS [HwfW _]]]]]; auto.
Qed.

Lemma WF_tt_to_WF_ec (Rc : ℜ) (R : 𝐄) (W : 𝐖) :
  WFₜₜ(Rc, R, W) -> WF(Rc,init_input_env R W).
Proof.
  intros [HeqDom [HDisj [HwfRc [HwfR [HwfW [Hwt [Hwt' [Hwt'' [HNoD HnEmp]]]]]]]]].
  split.
  {
    intro r.
    rewrite HeqDom.
    now rewrite init_input_env_in_iff.
  }
  do 2 (split; auto).
  { 
    apply init_input_env_Wf; auto. 
    intro HW.
    now apply HnEmp in HW as [].  
  }
  {
   intros r ty ty' c HfiRc HfiV.
   apply init_input_env_find_e in HfiV as Heq.
   destruct Heq as [v Heq]; subst.
   destruct W eqn:HeqW.
   - unfold init_input_env in HfiV. 
     simpl in *. 
     replace (Init.Nat.max (R⁺) 0 - R ⁺)%sr with 0 in * by lia.
     apply SRE.init_globals_find_iff in HfiV.
     rewrite SREnvironment.shift_zero_refl in HfiV.
     apply Hwt with (α := (ty,ty'))in HfiV; auto.
     now rewrite Term.shift_zero_refl in HfiV; simpl in *.
   - rewrite <- HeqW in *.
     destruct HnEmp.
     -- rewrite HeqW; intro Hc; inversion Hc.
     -- destruct (SRE.In_dec R r) as [HIn | HnIn].
        + assert (HnIn : (r ∉ (ST.keys W))%sk).
          { intro; apply HDisj in H1; contradiction. }
          apply init_input_env_R in HfiV; auto.
          destruct HfiV as [v' [Hfi Heq]]; subst v.
          apply Hwt with (v := v') in HfiRc; auto.
        + apply init_input_env_W in HfiV; auto.
          destruct HfiV as [r' [HIn | [v' [HIn Heq]]]].
          ++ apply Hwt' with (α := ty) (β := ty') in HIn as [Hwt1 Heq]; auto.  
          ++ subst v.
             apply Hwt'' with (α := ty) (β := ty') in HIn as [Hwt1 Heq]; auto.
             subst ty'.
             constructor.  
  }
Qed.


(* ---- *)

Lemma temporal_preserves_global_keys (put : resource * (option Λ) -> Λ) (R R': 𝐄) (P P': Λ) (W W' : 𝐖) :
  # put ⟦R ; W ; P⟧ ⟾ ⟦R' ; W' ; P'⟧ -> (forall (k : resource), (k ∈ R)%sr <-> (k ∈ R')%sr). 
Proof.
  intros [Vin [Wnew [_tv [_ [Heq _]]]]] k.
  now rewrite Heq; rewrite <- puts_in_iff.
Qed.

Lemma temporal_preserves_Wf (put : resource * (option Λ) -> Λ) (R R': 𝐄) (P P' : Λ) (W W' : 𝐖) :
  (forall r v, (R⁺)%sr ⊩ put (r,v))%tm ->
  NoDup (ST.keys W) ->
  (~ W = [] -> (W⁺)%sk > (R⁺)%sr) ->
  (R⁺ ⊩ R)%sr -> (W⁺ ⊩ W)%sk -> (max (R⁺)%sr (W⁺)%sk ⊩ P)%tm ->
  # put ⟦R ; W ; P⟧ ⟾ ⟦R' ; W' ; P'⟧ -> 
  (R'⁺ ⊩ R')%sr /\ (W'⁺ ⊩ W')%sk /\ (max (R'⁺)%sr (W'⁺)%sk ⊩ P')%tm.
Proof.
  intros Hwfput HNoD HnEmp HwfS HwfW HwfP [Vout [Wnew [_tv [fT [HeqS HeqW]]]]].
  rewrite HeqS, HeqW.
  rewrite <- (puts_new_key _ _ Vout).
  rewrite ST.update_locals_new_key.
  rewrite ST.new_key_app.
  rewrite ST.new_key_shift_refl; auto.
  apply functional_W_props in fT as HI.
  destruct HI as [HNoD' [HeqDom HnEmp']].
  apply functional_preserves_keys in fT as HI.
  destruct HI as [Hincl Hle].
  apply functional_preserves_Wf in fT as HI.
  - destruct HI as [HwfV [_ [HwfP' [HwfW' Hleq]]]].
    split.
    { apply puts_Wf; auto. }
    split.
    {  
     destruct W eqn:Hemp'.
     - simpl; 
       destruct Wnew eqn:Hemp; try (now simpl; auto).
       destruct HnEmp' as [Hnew Hlt].
       -- intro c; inversion c.
       -- rewrite Hnew in HwfW'. 
          apply ST.update_locals_Wf; split; auto.
          now rewrite <- Hnew.
     - assert (W <> []) by (subst; intro Hc; inversion Hc).
       rewrite <- Hemp' in *. 
       apply HnEmp in H.
       destruct Wnew eqn:Hemp.
       -- simpl.
          rewrite max_l by lia.
          rewrite app_nil_r.
          assert (Heq: Vout⁺ = (init_input_env R W)⁺).
          {
            rewrite (RE.new_key_diff (init_input_env R W) Vout); auto.
            simpl in HeqDom.
            rewrite (ST.eqDom'_new_key _ Wnew); subst; auto.
          }
          rewrite init_input_env_new_key in Heq.
          rewrite max_r in Heq by lia.
          rewrite Heq in *.
          replace (W⁺ - W⁺)%sk with 0 by lia.
          rewrite ST.shift_zero_refl.
          apply ST.update_locals_Wf; split; auto.
       -- rewrite <- Hemp in *.
          assert (Wnew <> []) by (subst; intro Hc; inversion Hc).
          apply HnEmp' in H0 as [Heq Hlt].
          rewrite init_input_env_new_key in Hlt.
          rewrite max_r by lia.
          rewrite Heq in *.
          apply ST.update_locals_Wf; split; auto.
          apply ST.Wf_app; split; auto.
          apply ST.shift_preserves_wf_2; auto; lia.
    }
    {
      destruct Wnew eqn:Hemp.
      - simpl.
        rewrite (max_l _ 0) by lia.
        assert (Heq: Vout⁺ = (init_input_env R W)⁺).
        {
          rewrite (RE.new_key_diff (init_input_env R W) Vout); auto.
          simpl in HeqDom.
          rewrite (ST.eqDom'_new_key _ Wnew); subst; auto.
        }
        rewrite init_input_env_new_key in Heq.
        rewrite <- Heq; auto.
      - rewrite <- Hemp in *.
        assert (Wnew <> []) by (subst; intro Hc; inversion Hc).
        apply HnEmp' in H as [Heq Hlt].
        rewrite init_input_env_new_key in Hlt.
        do 2 rewrite max_r by lia.
        now rewrite Heq in *.
    }
  - now apply init_input_env_Wf.
  - constructor.
  - now rewrite init_input_env_new_key.
Qed.

(** ** Preservation - Temporal *)

Definition tT_IO_halts n R W P :=
  halts n P /\ SRE.halts (R⁺)%sr R /\ ST.halts (W⁺)%sk W.

Lemma tT_inp_to_fT_inp Rc R W P :
  (Rc ⁺)%rc = Init.Nat.max (R ⁺)%sr (W ⁺)%sk ->
  (W <> [] -> (W⁺)%sk > (R⁺)%sr) ->
  tT_IO_halts (Rc⁺)%rc R W P ->
  fT_inputs_halts (Rc⁺)%rc (init_input_env R W) <[ unit ]> P.
Proof.
  intros Heq HnEmp [HltP [HltR HltW]]; split.
  - unfold init_input_env.
    rewrite Heq.
    apply ST.halts_init_locals.
    -- destruct W eqn:HeqW'.
       + constructor.
       + rewrite <- HeqW'.
         assert (p :: t <> []) by (intro Hc; inversion Hc).
         apply HnEmp in H.
         rewrite <- HeqW' in *.
         now rewrite max_r by lia. 
    -- apply SRE.halts_init_globals.
       apply SRE.halts_weakening; auto; lia.
  - split; auto.
    exists <[unit]>; split; auto.
    reflexivity.
Qed.

Definition tT_outputs_halts n W P :=
  halts n P /\ ST.halts (W⁺)%sk W.


Definition put_good_behavior (put : resource * (option Λ) -> Λ) Rc R := 
  forall r v, (r ∈ R)%sr -> 
    (forall α β, Rc⌊r⌋%rc = Some (α,β) -> 
      (
        match v with
          | None => True
          | Some v' => ∅%vc ⋅ Rc ⊢ {Term.shift (R⁺)%sr ((Rc⁺)%rc - (R⁺)%sr) v'} ∈ α 
        end ->
        ∅%vc ⋅ Rc ⊢ {Term.shift (R⁺)%sr ((Rc⁺)%rc - (R⁺)%sr) (put (r,v))} ∈ β
      )
    ) /\
    ((R⁺)%sr ⊩ put (r,v))%tm /\
    halts (R⁺)%sr (put (r,v))
.



Theorem temporal_preserves_typing (put : resource * (option Λ) -> Λ)
                                  (Rc : ℜ) (R R': 𝐄) 
                                  (W W' : 𝐖) (P P' : Λ) (Rs : resources) :

       tT_IO_halts (Rc⁺)%rc R W P -> halts_arr Rc P ->
                        WFₜₜ(Rc,R,W) -> 
                    put_good_behavior put Rc R ->
          
                    ∅%vc ⋅ Rc ⊢ P ∈ (𝟙 ⟿ 𝟙 ∣ Rs) -> 
                      
                  # put ⟦ R ; W ; P ⟧ ⟾ ⟦ R' ; W' ; P' ⟧ ->
  (* ------------------------------------------------------------------------ *)
      exists (Rc1 : ℜ) (Rs' : resources),
            (Rs ⊆ Rs')%s /\ (Rc ⊆ Rc1)%rc /\ WFₜₜ(Rc1,R',W') /\
          
                     ∅%vc ⋅ Rc1 ⊢ P' ∈ (𝟙 ⟿ 𝟙 ∣ Rs') /\ 
     
      tT_outputs_halts (Rc1⁺)%rc W' P' /\ halts_arr Rc1 P'.
Proof.
  intros Hinplt Harrlt HWF Hpwb HwtP HTT.
  apply WF_tt_to_WF_ec in HWF as HWF'.
  apply WF_tt_new in HWF as Hnew.
  assert (HnEmp: W <> [] -> (W ⁺)%sk > (R ⁺)%sr).
  {
    destruct HWF as [_ [_ [_ [_ [_ [_ [_ [_ [_ ]]]]]]]]].
    intro HI; apply H in HI as []; assumption.
  }
  apply tT_inp_to_fT_inp in Hinplt as Hinplt'; auto.
  assert (HTT': # put ⟦ R; W; P ⟧ ⟾ ⟦ R'; W'; P' ⟧) by assumption.
  destruct HTT as [Vout [Wnew [_tv [HfT [HeqR HeqW]]]]].
  apply functional_W_props in HfT as HI.
  destruct HI as [HND [HeqDom HnEmp']].

  apply functional_preserves_keys in HfT as HI.
  destruct HI as [HIn Hle].

  apply functional_preserves_Wf in HfT as HI; auto.
  - destruct HI as [HwfVout [_ [HwfP' [HwfWnew HleVout]]]].

    apply Functional_Transition.functional_preserves_typing 
    with (Rc := Rc) (α := <[𝟙]>) (β := <[𝟙]>) (R := Rs)
    in HfT; auto.
    destruct HfT as [Hunsd [Hunsd' [Rc1 [Rs' [HsubRc [HsubRs 
                      [Hout [Harrlt' [Hwt [Hwt' [HWF'' [HwW [Hdisj Husd]]]]]]]]]]]]]. 
    exists Rc1, Rs'.
    do 3 (split; auto).
    { 
      split. 
      {
        intro r. 
        rewrite HeqR, HeqW.
        rewrite ST.update_locals_keys_In.
        rewrite <- puts_in_iff.
        rewrite ST.keys_in_app.
        rewrite ST.keys_in_shift_new_key.
        clear HTT' HwW Hunsd Hunsd' Hpwb.
        rewrite (WF_ec_In Rc1 Vout); auto.
        split.
        - intro HInVout.
          specialize (HeqDom r).
          rewrite RE.diff_in_iff in HeqDom.
          rewrite <- init_input_env_in_iff in HeqDom.
          destruct (List.In_dec Resource.eq_dec r (ST.keys W)) as [|HnInW]; auto.
          destruct (SRE.In_dec R r) as [|HnInR]; auto.
          left; right.
          rewrite <- HeqDom; split; auto.
          now intros [|].
        - intros [[HInW|HInWnew]|HInR].
          -- apply HIn.
             rewrite <- init_input_env_in_iff; auto.
          -- rewrite <- HeqDom in HInWnew.
             rewrite RE.diff_in_iff in HInWnew.
             now destruct HInWnew.
          -- apply HIn.
             rewrite <- init_input_env_in_iff; auto.
      } 
      split. 
      {
        intros r.
        rewrite HeqW, HeqR.
        rewrite ST.update_locals_keys_In.
        rewrite <- puts_in_iff.
        rewrite ST.keys_in_app.
        rewrite ST.keys_in_shift_new_key.
        clear HTT' HwW Hunsd Hunsd' Hpwb.
        intros [HInW | HInWnew].
        - destruct HWF as [_ []]; auto.
        - rewrite <- HeqDom in HInWnew.
          rewrite RE.diff_in_iff in HInWnew.
          destruct HInWnew as [_ HIninp].
          rewrite <- init_input_env_in_iff in HIninp.
          intro c; apply HIninp; auto.
      } 
      split. 
      { now apply WF_ec_Wf in HWF'' as []. } 
      split. 
      {
        rewrite HeqR.
        rewrite <- puts_new_key.
        apply puts_Wf.
        - intros. destruct (Hpwb r v); auto.
          now destruct H1.
        - now destruct HWF as [_ [_ [_ []]]]. 
      } 
      split. 
      {
        clear Hpwb Hwt Hwt' Harrlt' HTT' HeqR Hunsd Hunsd' HwW Husd.
        destruct W, Wnew.
        - simpl in *.
          rewrite HeqW.
          apply ST.Wf_nil.
        - remember (p :: Wnew) as Wnew'; clear HnEmp.
          simpl in *.
          rewrite HeqW.
          destruct HnEmp'.
          -- subst; intro c; inversion c.
          -- rewrite ST.update_locals_new_key.
             apply ST.update_locals_Wf; split; rewrite <- H; auto.
        - remember (p :: W) as W1; clear HnEmp'.
          simpl in *.
          rewrite HeqW.
          rewrite app_nil_r in *.
          assert (W1 <> []) by (subst; intro c; inversion c).
          apply HnEmp in H.
          assert (Vout⁺ <= (init_input_env R W1)⁺).
          { 
            apply RE.new_key_incl.
            now apply RE.diff_in_false.
          }
          rewrite init_input_env_new_key in *.
          rewrite max_r in * by lia.
          assert (Vout⁺ = W1⁺%sk) by lia.
          rewrite H1.
          rewrite ST.update_locals_new_key.
          replace (W1 ⁺ - W1 ⁺)%sk with 0 by lia.
          rewrite ST.shift_zero_refl.
          destruct HWF as [_ [_ [_ [_ []]]]].
          apply ST.update_locals_Wf; split; auto; rewrite <- H1; auto.
        - remember (p :: W) as W1.
          remember (p0 :: Wnew) as Wnew1.
          destruct HnEmp'.
          { subst; intro c; inversion c. }
          assert (W1 <> []) by (subst; intro c; inversion c).
          apply HnEmp in H1; clear HnEmp.
          rewrite init_input_env_new_key in *.
          rewrite max_r in * by lia.
          rewrite HeqW.
          rewrite ST.update_locals_new_key.
          rewrite ST.new_key_app.
          rewrite ST.new_key_shift_refl; auto.
          rewrite max_r by lia.
          rewrite <- H.
          apply ST.update_locals_Wf; split; auto.
          apply ST.Wf_app; split; auto.
          apply ST.shift_preserves_wf_2; auto.
          destruct HWF as [_ [_ [_ [_ [ ]]]]]; assumption.
      } 
      split. 
      { 
        intros r [ty ty'] v HfiRc1.
        rewrite HeqR, HeqW.
        rewrite <- puts_new_key.
        rewrite ST.update_locals_new_key.
        rewrite ST.new_key_app.
        rewrite ST.new_key_shift_refl; auto.
        unfold put_good_behavior in Hpwb.
        simpl in *.
        intro HfiR.
        assert (HInR : (r ∈ R)%sr).
        { 
          rewrite puts_in_iff.
          exists v.
          apply SRE.find_2 in HfiR; eauto. 
        }
        specialize (Hpwb r (Some v) HInR).
        destruct Hpwb as [Hwtput _].
        apply puts_find in HfiR as HI.
        destruct HI as [v' Heq]; subst.
        admit. 
      } 
      split. 
      {
        intros r r' ty ty' v Hfi HInW'.
        rewrite HeqW in HInW'.
        apply ST.update_locals_In in HInW' as [[HInW' Hnfi]|[v'[HInW' HfiVout]]].
        - apply List.in_app_or in HInW' as [HInW|HInWnew].
          -- admit.
          -- apply HwW in HInWnew as [τ [Hwtv [HfiRc1 HfiRc1']]].
             rewrite Hfi in HfiRc1.
             inversion HfiRc1; subst; split; auto.
        - apply List.in_app_or in HInW' as [HInW|HInWnew].
          -- admit.
          -- apply HwW in HInWnew as [τ [Hwtv [HfiRc1 HfiRc1']]].
             rewrite Hfi in HfiRc1.
             inversion HfiRc1; subst; split; auto.
             destruct HWF'' as [_ [_ [_ H]]].
             apply H with (v := (Cell.out v)) in HfiRc1'; auto.
      } 
      split. 
      { 
        intros r r' ty ty' v Hfi HInW'.
        rewrite HeqW in HInW'.
        apply ST.update_locals_In in HInW' as [[HInW' Hnfi]|[v'[HInW' HfiVout]]].
        - apply List.in_app_or in HInW' as [HInW|HInWnew].
          -- admit.
          -- apply HwW in HInWnew as [τ [Hwtv [HfiRc1 HfiRc1']]].
             rewrite Hfi in HfiRc1'.
             inversion HfiRc1'; subst; split; auto.
        - apply List.in_app_or in HInW' as [HInW|HInWnew].
          -- admit.
          -- apply HwW in HInWnew as [τ [Hwtv [HfiRc1 HfiRc1']]].
             rewrite Hfi in HfiRc1'.
             inversion HfiRc1'; subst; split; auto.
             destruct HWF'' as [_ [_ [_ H]]].
             apply H with (v := (Cell.out v)) in Hfi; auto.
      }
      split.
      { 
        rewrite HeqW.
        apply ST.update_locals_NoDup_keys.
        apply ST.NoDup_keys_app; auto.
        - apply ST.NoDup_keys_shift.
          now destruct HWF as [_ [_ [_ [_ [_ [_ [_ [_ [ ]]]]]]]]].
        - intro r.
          rewrite <- HeqDom.
          rewrite RE.diff_in_iff; intros [HInVout HIninp].
          rewrite <- init_input_env_in_iff in HIninp.
          rewrite ST.keys_in_shift_new_key.
          intro c; apply HIninp; auto.
      }
      { 
        rewrite HeqW, HeqR.
        rewrite <- puts_new_key.
        rewrite ST.update_locals_new_key.
        rewrite ST.new_key_app.
        rewrite ST.new_key_shift_refl; auto.
        intro Hnnil.
        rewrite ST.update_locals_not_nil in Hnnil.
        apply ST.app_not_nil in Hnnil.
        rewrite ST.shift_not_nil in Hnnil.
        destruct Hnnil as [Hnnil|Hnnil].
        - apply HnEmp in Hnnil.
          split; try lia. 
          destruct Wnew.
          -- simpl in *.
             rewrite max_l by lia.
             assert (Vout⁺ <= (init_input_env R W)⁺).
             { 
              apply RE.new_key_incl.
              now apply RE.diff_in_false. 
             }
             assert (Vout⁺ = (init_input_env R W)⁺) by lia.
             rewrite (WF_ec_new Rc1 Vout); auto.
             rewrite H0.
             rewrite init_input_env_new_key; lia.
          -- remember (p :: Wnew) as Wnew'.
             destruct HnEmp'.
             + subst; intro c; inversion c.
             + rewrite init_input_env_new_key in H0.
               rewrite max_r by lia.
               rewrite (WF_ec_new Rc1 Vout); auto.
        - apply HnEmp' in Hnnil as [Heq Hle']; rewrite <- Heq in *.
          rewrite init_input_env_new_key in Hle'.
          rewrite (WF_ec_new Rc1 Vout); auto.
          split; lia.
      } 
    }
    do 2 (split; auto).
    { 
      clear Hpwb Hwt Hwt' Harrlt' HTT' HeqR Hunsd Hunsd' HwW Husd.
      split; auto.
      - destruct Hout as [_ [_ []]]; auto.
      - destruct W, Wnew.
        -- simpl in *; rewrite HeqW.
          apply ST.halts_nil.
        -- remember (p :: Wnew) as Wnew'.
          rewrite HeqW in *; simpl in *.
          destruct HnEmp'.
          + rewrite HeqWnew'; intro Hc; inversion Hc.
          + rewrite ST.update_locals_new_key.
            rewrite <- H.
            rewrite <- (WF_ec_new Rc1 Vout); auto.
            destruct Hout as [HoutV [HoutW ]].
            now apply ST.halts_update_locals.
        -- remember (p :: W) as W1.
          clear HnEmp'.
          rewrite HeqW in *; simpl in *.
          rewrite app_nil_r in *.
          assert (Vout⁺ <= (init_input_env R W1)⁺).
          { 
            apply RE.new_key_incl.
            now apply RE.diff_in_false.
          }
          assert (W1 <> []) by (subst; intro c; inversion c).
          apply HnEmp in H0.
          rewrite init_input_env_new_key in *.
          rewrite max_r in * by lia.
          replace ((Vout⁺)%re - W1⁺)%sk with 0 by lia.
          rewrite ST.update_locals_new_key.
          rewrite ST.shift_zero_refl.
          destruct Hout as [HoutV _].
          destruct Hinplt as [_ [HltR HltW1]].
          apply ST.halts_update_locals; auto.
          assert ((W1⁺)%sk = Vout⁺) by lia.
          rewrite H1.
          rewrite <- (WF_ec_new Rc1 Vout); auto.
        -- remember (p0 :: Wnew) as Wnew'.
          remember (p :: W) as W1.
          assert (W1 <> []).
          { subst; intro c; inversion c. }
          apply HnEmp in H; clear HnEmp.
          rewrite init_input_env_new_key in *.
          rewrite max_r in * by lia.
          assert (Wnew' <> []).
          { subst; intro c; inversion c. }
          apply HnEmp' in H0; clear HnEmp'.
          destruct H0 as [Heq Hlt].
          rewrite HeqW.
          rewrite ST.update_locals_new_key.
          rewrite ST.new_key_app.
          rewrite ST.new_key_shift_refl; auto.
          rewrite max_r by lia.
          destruct Hout as [HoutV [HoutW]].
          destruct Hinplt as [_ [HltR HltW1]].
          apply ST.halts_update_locals; auto.
          + rewrite <- Heq.
            rewrite <- (WF_ec_new Rc1 Vout); auto.
          + apply ST.halts_app; split.
            ++ rewrite Heq.
                apply ST.halts_weakening; auto; lia.
            ++ rewrite <- Heq.
                rewrite <- (WF_ec_new Rc1 Vout); auto.
    }
  - destruct HWF as [_ [_ [HwfRc [HwfR []]]]]. 
    apply init_input_env_Wf; auto.
  - constructor.
  - rewrite <- (WF_ec_new Rc); auto.
    apply well_typed_implies_Wf in HwtP as []; auto.
    now destruct HWF as [_ [_ []]].
Admitted.

(** ---- *)


(** ** Progress - Temporal *)

(* Theorem temporal_reactivity (n : nat) (Rc : ℜ) (R : resources) (W: 𝐖) (P : Λ) (Rs : resources) :

          halts (Rc⁺)%rc P -> ST.halts (W⁺)%sk W ->
 
          (* inputs_restriction n R Rc W ->  WFₜₜ(R,Rc,W) ->  *)

               ∅%vc ⋅ Rc ⊢ P ∈ (𝟙 ⟿ 𝟙 ∣ Rs) ->
  (* ------------------------------------------------------------------------ *)
       exists (P': Λ) (W': 𝐖), #n ⟦ R ; W ; P ⟧ ⟾ ⟦ R' ; W' ; P' ⟧.
Proof. admit.

Admitted. *)