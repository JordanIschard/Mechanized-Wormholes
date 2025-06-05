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

Section temporal.

Hypothesis put : nat -> resource * (option Λ) -> Λ.


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
  (forall (r r' : resource) (v : Λ),
      (In (r,r',v) W) ->  exists (α : Τ), 
                            ∅%vc ⋅ Rc ⊢ v ∈ α /\
                            Rc⌊r⌋%rc = Some (<[𝟙]>,α) /\ 
                            Rc⌊r'⌋%rc = Some (α,<[𝟙]>)) /\
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

Definition puts (n : nat) (R : 𝐄) (V: 𝐕) :=
  SRE.foldkeys (fun k acc => ⌈k ⤆ put n (k,(put_aux k V))⌉ acc)%sr R ∅%sr.

(** *** Initialize the input resource environment 

  The input resource environment consists of locals resources (from W) and global resources (from R). Global resources, at the first instant, are well formed under R. After that, they must be shift in order to be well formed under the maximum between W⁺ and R⁺ because W may contains local resources which are, by construction, greater than global resources. 
*)

Definition init_input_env (R : 𝐄) (W : 𝐖) : 𝐕 :=
  ST.init_locals W 
  (SRE.init_globals (SRE.shift (R⁺)%sr ((max (R⁺)%sr (W⁺)%sk) - (R⁺)%sr) R)).

(** *** Temporal transition *)

Definition temporal (n : nat) (R R': 𝐄) (P P' : Λ) (W W' : 𝐖) :=

  (** (1) Initialize the local memory [Vin] with global and local resources. *)
  let Vin := init_input_env R W in

  exists (Vout : 𝐕) Wnew _tv,
  (** (2) Perform the instant with the functional transition. *)                  
  ⪡ Vin ; unit ; P ⪢ ⭆ ⪡ Vout ; _tv ; P' ; Wnew ⪢ /\

  (** (3) Update the global and local resources. *)               
  (R' = puts n R Vout)%sr  /\
  (W' = (ST.update_locals (([⧐ (W⁺)%sk – (Vout⁺ - (W⁺)%sk)%re] W) ++ Wnew) Vout))%sk.

Notation "# n '⟦' R ';' W ';' P '⟧' '⟾' '⟦' S1 ';' W1 ';' P1 '⟧'" := (temporal n R S1 P P1 W W1) 
(at level 30, R constr, S1 constr, P custom wh, P1 custom wh, W constr, W1 constr, no associativity).

(** ---- *)

(** *** [puts] properties *)

#[export] Instance aux_eq (n : nat) (V: 𝐕) : Proper (eq ==> SRE.eq ==> SRE.eq) 
  (fun (k: resource) (acc : SRE.t) => (⌈k ⤆ put n (k, put_aux k V) ⌉ acc)%sr).
Proof.
  intros r' r Heqr R R' HeqR; subst.
  now rewrite HeqR.
Qed.

Lemma aux_diamond (n : nat) (V: 𝐕) : SRE.Diamond SRE.eq 
  (fun (k: resource) (_: Λ) (acc : SRE.t) => (⌈ k ⤆ put n (k, put_aux k V) ⌉ acc)%sr).
Proof.
  intros r r' _ _ R1 R R' Hneq Heq Heq'.
  rewrite <- Heq, <- Heq'.
  rewrite SRE.add_add_2; now auto.
Qed.

Hint Resolve srenvironment_equiv_eq aux_eq aux_diamond : core.

Lemma puts_Empty (n : nat) (R: 𝐄) (V: 𝐕) :
  (isEmpty(R))%sr -> (isEmpty(puts n R V))%sr.
Proof.
  intro HEmp; unfold puts.
  rewrite SRE.foldkeys_Empty; auto.
  apply SRE.empty_1.
Qed.

Lemma puts_Empty_iff (n : nat) (R: 𝐄) (V: 𝐕) :
  (isEmpty(R))%sr -> ((puts n R V) = ∅)%sr.
Proof.
  intro HEmp; unfold puts.
  rewrite SRE.foldkeys_Empty; now auto.
Qed.

Lemma puts_Add (n : nat) (r: resource) (e: Λ) (R R': 𝐄) (V: 𝐕) :
  (r ∉ R)%sr -> SRE.Add r e R R' ->
  (puts n R' V = (⌈r ⤆ put n (r,(put_aux r V))⌉ (puts n R V))%sr)%sr.
Proof.
  intros HnIn HAdd.
  unfold puts at 1.
  rewrite SRE.foldkeys_Add; now auto.
Qed.

#[export] Instance puts_eq (n : nat) : Proper (SRE.eq ==> RE.eq ==> SRE.eq) (puts n).
Proof.
  intros R R' HeqR V V' HeqV.
  revert R' HeqR.
  induction R using SRE.map_induction; intros R' Heq.
  - do 2 (rewrite puts_Empty_iff; auto).
    -- reflexivity.
    -- now rewrite <- Heq.
  - rewrite puts_Add; eauto.
    rewrite (puts_Add _ x e R1 R'); auto.
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

Lemma puts_add (n : nat) (r: resource) (e: Λ) (R: 𝐄) (V: 𝐕) :
  (r ∉ R)%sr ->
  (puts n (⌈r ⤆ e⌉ R) V = ⌈r ⤆ put n (r,(put_aux r V))⌉ (puts n R V))%sr.
Proof.
  intro HnIn.
  rewrite (puts_Add _ r e R); auto.
  - reflexivity.
  - apply SRE.Add_add. 
Qed.

Lemma puts_in_iff (n : nat) (R: 𝐄) (V: 𝐕) (r: resource) :
  (r ∈ R)%sr <-> (r ∈ (puts n R V))%sr.
Proof.
  revert r.
  induction R using SRE.map_induction; intro r.
  - split; intros [v HM]; exfalso.
    -- apply (H r v HM).
    -- apply (puts_Empty n _ V) in H.
       apply (H r v HM).
  - unfold SRE.Add in H0; rewrite H0; clear H0.
    rewrite puts_add; auto.
    do 2 rewrite SRE.add_in_iff.
    now rewrite IHR1.
Qed.

Lemma puts_new_key (n : nat) (R: 𝐄) (V: 𝐕) :
  (R⁺)%sr = ((puts n R V)⁺)%sr.
Proof.
  induction R using SRE.map_induction.
  - do 2 (rewrite SRE.Ext.new_key_Empty; auto).
    now apply puts_Empty.
  - unfold SRE.Add in *; rewrite H0; clear H0.
    rewrite puts_add; auto.
    do 2 rewrite SRE.Ext.new_key_add_max; lia.
Qed.

Lemma puts_Wf (n : nat) (k : lvl) (R : 𝐄) (V : 𝐕) :
  (forall r v, k ⊩ put n (r,v))%tm ->
  (k ⊩ R)%sr -> (k ⊩ (puts n R V))%sr.
Proof.
  revert V.
  induction R using SRE.map_induction; intros V Hwfput HwfR.
  - rewrite puts_Empty_iff; auto.
    apply SRE.Wf_empty.
  - unfold SRE.Add in H0; rewrite H0 in *; clear H0.
    rewrite puts_add; auto.
    apply SRE.Wf_add_notin in HwfR as [Hwfx [_ Hwfe1]]; auto.
    apply SRE.Wf_add_notin.
    -- now rewrite <- puts_in_iff.
    -- repeat (split; auto).
Qed.

Lemma puts_Wf_V (n : nat) (R : 𝐄) (V : 𝐕) :
  (forall r v, (V⁺) ⊩ put n (r,v))%tm ->
  (R⁺)%sr <= V⁺ -> ((V⁺) ⊩ V) -> ((V⁺)%re ⊩ (puts n R V))%sr.
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

Lemma puts_halts (n : nat) (k: lvl) (R : 𝐄) (V : 𝐕) :
  (forall r v, halts k (put n (r,v)))%tm ->
  SRE.halts k (puts n R V).
Proof.
  intro Hyput.
  induction R using SRE.map_induction.
  - apply SRE.halts_Empty.
    now apply puts_Empty.
  - unfold SRE.Add in H0; rewrite H0 in *; clear H0.
    rewrite puts_add; auto.
    apply SRE.halts_add; split; auto.
Qed.

Lemma puts_halts_1 (n : nat) (R : 𝐄) (V : 𝐕) :
  (forall r v, halts (R⁺)%sr (put n (r,v)))%tm ->
  SRE.halts ((puts n R V)⁺)%sr (puts n R V).
Proof.
  intro Hyput.
  apply puts_halts.
  intros r v.
  rewrite <- puts_new_key.
  now apply Hyput.
Qed.

Lemma puts_find (n : nat) (R : 𝐄) (V : 𝐕) (r: resource) (v: Λ) :
  (puts n R V ⌊r⌋)%sr = Some v -> exists v', (v = put n (r, v'))%type.
Proof.
  revert r v; induction R using SRE.map_induction; intros r v Hfi. 
  - exfalso.
    apply (puts_Empty n _ V) in H.
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

(* 
Lemma new_key_in_remove_1 (x: lvl) (t: t) :
  In x t -> new_key t = max (S x) (new_key (remove x t)). *)
#[export] Instance WF_in_eq : Proper (RContext.eq ==> SRE.eq ==> Logic.eq ==> iff) well_formed_tt.
Proof.
  intros Rc Rc1 HeqRe R R' HeqS W W' HeqW; subst; split.
  - intros [HeqDom [HDisj [HvRc [HvS [HvW [Hwt [Hwt' HnEmp ]]]]]]].  
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
      intros r r' v HIn.
      apply (Hwt' r r' v) in HIn as [α HIn].
      exists α.
      now rewrite <- HeqRe.
    }
    { 
      rewrite <- HeqRe, <- HeqS; auto. 
    }
  - intros [HeqDom [HDisj [HvRc [HvS [HvW [Hwt [Hwt' HnEmp ]]]]]]].  
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
      intros r r' v HIn.
      apply (Hwt' r r' v) in HIn as [α HIn].
      exists α.
      now rewrite HeqRe.
    }
    { 
      rewrite HeqRe, HeqS; auto. 
    }
Qed.

Lemma WF_tt_new (Rc : ℜ) (R : 𝐄) (W : 𝐖) :
  WFₜₜ(Rc, R, W) -> (Rc⁺)%rc = max (R⁺)%sr (W⁺)%sk.
Proof.
  intros [HeqDom [HDisj [_ [_ [_ [_ [_ [HNoD _]]]]]]]].
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
  intros [HeqDom [HDisj [HwfRc [HwfR [HwfW [Hwt [Hwt' [HNoD HnEmp]]]]]]]].
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
     -- admit.
  }
Admitted.


(* ---- *)

Lemma temporal_preserves_global_keys (n : nat) (R R': 𝐄) (P P': Λ) (W W' : 𝐖) :
  # n ⟦R ; W ; P⟧ ⟾ ⟦R' ; W' ; P'⟧ -> (forall (k : resource), (k ∈ R)%sr <-> (k ∈ R')%sr). 
Proof.
  intros [Vin [Wnew [_tv [_ [Heq _]]]]] k.
  now rewrite Heq; rewrite <- puts_in_iff.
Qed.

Lemma temporal_preserves_Wf (n : nat) (R R': 𝐄) (P P' : Λ) (W W' : 𝐖) :
  (forall r v, (R⁺)%sr ⊩ put n (r,v))%tm ->
  NoDup (ST.keys W) ->
  (~ W = [] -> (W⁺)%sk > (R⁺)%sr) ->
  (R⁺ ⊩ R)%sr -> (W⁺ ⊩ W)%sk -> (max (R⁺)%sr (W⁺)%sk ⊩ P)%tm ->
  #n ⟦R ; W ; P⟧ ⟾ ⟦R' ; W' ; P'⟧ -> 
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

Hypothesis all_arrow_halting : forall Rc t α β,
  ∅%vc ⋅ Rc ⊢ arr(t) ∈ (α ⟿ β ∣ ∅%s) -> forall v, ∅%vc ⋅ Rc ⊢ v ∈ α -> halts (Rc⁺)%rc <[t v]>.

Hypothesis put_well_behaves : 
  forall n Rc R, 
  (forall r, (r ∈ R)%sr -> 
    (forall α β, Rc⌊r⌋%rc = Some (α,β) -> 
      (forall v,
        match v with
          | None => True
          | Some v' => ∅%vc ⋅ Rc ⊢ {Term.shift (R⁺)%sr ((Rc⁺)%rc - (R⁺)%sr) v'} ∈ α 
        end ->
        ((R⁺)%sr ⊩ put n (r,v))%tm /\
        halts (R⁺)%sr (put n (r,v)) /\
       ∅%vc ⋅ Rc ⊢ {Term.shift (R⁺)%sr ((Rc⁺)%rc - (R⁺)%sr) (put n (r,v))} ∈ β
      )
    )
  )
.

Theorem temporal_preserves_typing (n : nat) (Rc : ℜ) (R R': 𝐄) 
                                  (W W' : 𝐖) (P P' : Λ) (Rs : resources) :

       halts (Rc⁺)%rc P -> SRE.halts (R⁺)%sr R -> ST.halts (W⁺)%sk W ->
                             WFₜₜ(Rc,R,W) -> 
          
                    ∅%vc ⋅ Rc ⊢ P ∈ (𝟙 ⟿ 𝟙 ∣ Rs) -> 
                      
                  # n ⟦ R ; W ; P ⟧ ⟾ ⟦ R' ; W' ; P' ⟧ ->
  (* ------------------------------------------------------------------------ *)
      exists (Rc1 : ℜ) (Rs' : resources),
            (Rs ⊆ Rs')%s /\ (Rc ⊆ Rc1)%rc /\ WFₜₜ(Rc1,R',W') /\
          
                     ∅%vc ⋅ Rc1 ⊢ P' ∈ (𝟙 ⟿ 𝟙 ∣ Rs') /\ 
     
      halts (Rc1⁺)%rc P' /\ ST.halts (W'⁺)%sk W'.
Proof.
  intros HltP HltW HR HWF HwtP HTT.
  assert (HTT': # n ⟦ R; W; P ⟧ ⟾ ⟦ R'; W'; P' ⟧) by assumption.
  destruct HTT as [Vout [Wnew [_tv [HfT [HeqR HeqW]]]]].

  apply Functional_Transition.functional_preserves_typing_gen 
  with (Rc := Rc) (α := <[𝟙]>) (β := <[𝟙]>) (R := Rs)
  in HfT; auto.
  - destruct HfT as [Hunsd [Hunsd' [Rc1 [Rs' [HsubRc [HsubRs 
                    [Hout [Hwt [Hwt' [HWF' [HwW [Hdisj Husd]]]]]]]]]]]]. 
    exists Rc1, Rs'.
    do 3 (split; auto).
    {
      destruct HWF 
      as [HeqDom [Hdisj' [HwfRc [HwfR [HwfW [HwtR [HwtW [HnDup HnewW]]]]]]]].
      destruct HWF' as [HeqDom' [HwfRc1 [HwfVout HwtV]]].
      split.
      { 
        intro r.
        rewrite <- temporal_preserves_global_keys; eauto.
        rewrite HeqW.
        admit.
      }
      split.
      { admit. }
      split; auto.  
    admit. }
    do 2 (split; auto).
    { now destruct Hout as [_ [_ [_ ]]]. }
    { 
      rewrite HeqW.
      rewrite ST.update_locals_new_key.
      rewrite ST.new_key_app.
      rewrite ST.new_key_shift_refl; auto.
      apply ST.halts_update_locals;
      admit. 
    }
  - repeat split; auto.
    -- unfold init_input_env.
       apply WF_tt_new in HWF as Hnew.
       rewrite Hnew.
       apply ST.halts_init_locals; auto.
       + destruct W eqn:HeqW'.
         ++ constructor.
         ++ rewrite <- HeqW'.
            destruct HWF as [_ [_ [_ [_ [_ [_ [_ [_ ]]]]]]]].
            destruct H.
            * intro Hc; inversion Hc.
            * rewrite <- HeqW' in *.
              now rewrite max_r by lia.
       + apply SRE.halts_init_globals.
         apply SRE.halts_weakening; auto; lia.
    -- exists <[unit]>; split; auto; reflexivity.
  - now apply WF_tt_to_WF_ec.
Admitted.

  (* assert (HnEmp: ~ ST.Empty W -> (W ⁺)%sk > (R ⁺)%sr).
  {
   destruct HWF as [_ [_ [_ [_ [_ [_ [_ [HnEmp _]]]]]]]].
   intros Hn.
   now apply HnEmp in Hn as []. 
  }
  apply temporal_W_props in HTT as HI; auto.
  destruct HI as [HinclW HnEmp'].

  apply WF_tt_Wf in HWF as HI.
  destruct HI as [HwfRc [HwfS HwfW]].
  apply well_typed_implies_Wf in HwtP as HI; auto.
  destruct HI as [HwfP _].
  rewrite (WF_tt_new _ _ _ HWF) in HwfP.

  apply temporal_preserves_Wf in HTT as HI; auto.
  rewrite <- (WF_tt_new _ _ _ HWF) in HwfP.
  destruct HI as [HwfS' [HwfW' HwfP']].
  destruct HTT as [Vout [Wnew [_tv [fT [HeqS' HeqW']]]]].

  (* clean *)
  move Vout before R; move R' before R; move Wnew before W'; 
  move _tv before P'; move fT before HwtP;
  move HwfRc before Rs; move HwfS before HwfRc;
  move HwfW before HwfS; move HwfP before HwfW;
  move HeqS' before Rs; move HeqW' before HeqS';
  move HnEmp before HnEmp'; move HwfS' before HwfS;
  move HwfW' before HwfW; move HwfP' before HwfP; 
  move Hyput before Rs; move Hyput' before Hyput.
  (* clean *)

  apply WF_tt_to_WF_ec in HWF as HWF'; move HWF' before HWF.
  apply functional_W_props in fT as H.
  destruct H as [_ [_ [HeqD [HnEmpnew _]]]].

  assert (Hinp: fT_inputs_halts (Rc ⁺)%rc (init_input_env R W) <[ unit ]> P).
  {
    repeat split; auto.
    - unfold init_input_env.
      apply ST.halts_init_locals; auto.
      -- rewrite (TT_EqDom_new _ R W); auto;
         destruct HWF as [HIn [Hdisj [_ [_ [HvW [_ [HEmp _]]]]]]]; auto.
         destruct (ST.is_empty W) eqn:Heq.
         + apply ST.Empty_is_empty in Heq.
           now apply ST.halts_Empty.
         + apply ST.not_Empty_is_empty in Heq.
           apply HnEmp in Heq.
           now replace (Init.Nat.max (R⁺)%sr (W⁺)%sk) with (W⁺)%sk by lia.
      -- apply SRE.halts_init_globals.
         rewrite (TT_EqDom_new Rc R W) in * by (destruct HWF as [HIn [Hdisj _]]; auto).
         apply SRE.halts_weakening; auto; lia.
    - exists <[unit]>; split; auto; reflexivity.
  }

  apply (functional_preserves_typing_gen 
              all_arrow_halting Rc _ _ _ _ _ _ _ <[𝟙]> <[𝟙]> Rs) in fT as IH; auto.
  destruct IH as [Hunsd [Hlcl [Rc' [Rs' [HsubRc [HsubR [[HltVout [HltWnew [_ HltP']]] 
                        [Hwtv' [HwtP' [HWF'' [HwtW1 [HInR Husd1]]]]]]]]]]]].    
  apply WF_ec_Wf in HWF'' as HI.
  destruct HI as [HwfRc' HwfVout].

  (* clean *)
  move Rc' before Rc; move Rs' before Rs; move HltVout before HltP;
  move HltWnew before HltW; move HltP' before HltP; move Hwtv' before HwtP;
  move HwtP' before HwtP; move Hinp before HltWnew; move HWF'' before HWF';
  move HsubRc before HeqW'; move HsubR before HsubRc; move HeqD before HinclW;
  move HwfRc' before HwfRc; move HwfVout before HwfW'; move Hyput'' before Hyput'.
  (* clean *)

  exists Rc', Rs'.
  do 3 (split; auto).
  { 
    split.
    {
      intro r. 
      destruct HWF as [HeqDom _].
      rewrite HeqW', HeqS', ST.update_locals_in_iff, 
              <- puts_in_iff, ST.union_in_iff,
              ST.shift_new_key_in_iff, <- (HeqD r).
      rewrite or_assoc, <- or_comm, or_assoc,
             (or_comm (r ∈ R)%sr), <- HeqDom.
      rewrite RE.diff_in_iff, <- (WF_ec_In Rc' Vout HWF''),
              <- (WF_ec_In Rc _ HWF'), <- RC.diff_in_iff.
      now rewrite <- RC.diff_Submap_in; auto.
    }
    split.
    {
      intro r.
      destruct HWF as [HeqDom [Hdisj _]].
      rewrite HeqW', HeqS', ST.update_locals_in_iff, 
              <- puts_in_iff, ST.union_in_iff,
              ST.shift_new_key_in_iff, <- (HeqD r).
      rewrite RE.diff_in_iff, <- (WF_ec_In Rc' Vout HWF''),
              <- (WF_ec_In Rc _ HWF').
      specialize (Hdisj r).
      destruct Hdisj as [Hdisj1 Hdisj2].
      split.
      - intros [HIn | [HIn HnIn]]; auto.
        rewrite HeqDom in HnIn.
        intro Hc; apply HnIn; now right.
      - intros HIn [HInW | [HInRc' HnIn]].
        -- revert HInW; now apply Hdisj2.
        -- apply HnIn.
           rewrite HeqDom; auto. 
    }
    do 4 (split; auto).
    {
      destruct HWF as [HeqDom _].
      apply TT_EqDom_new in HeqDom as Hnew.
      intros r [α β] v HfiRc.
      rewrite HeqS', <- puts_new_key, HeqW', 
              ST.update_locals_new_key, ST.new_key_union.
      rewrite ST.shift_new_refl; auto; simpl.
      replace (max (R ⁺)%sr (max (W ⁺)%sk (Wnew ⁺)%sk))
      with    (max (max (R ⁺)%sr (W ⁺)%sk) (Wnew ⁺)%sk) by lia.
      rewrite <- Hnew.
      intro HfiR'.
      apply TT_EqDom_new' in HeqD as Hnew'.
      rewrite <- Hnew', (WF_ec_new _ _ HWF').
      replace (max (init_input_env R W ⁺) (RE.diff Vout (init_input_env R W) ⁺))
      with (max (RE.diff Vout (init_input_env R W) ⁺) (init_input_env R W ⁺)) by lia.
      rewrite <- RE.new_key_diff.
      - rewrite <- (WF_ec_new _ _ HWF'').
        apply puts_find in HfiR' as Heq.
        destruct Heq as [v' Heq]; subst.
        assert (HIn: (r ∈ Rc)%rc).
        {
          rewrite (WF_ec_In _ _ HWF'), <- init_input_env_in_iff.
          right.
          rewrite (puts_in_iff _ Vout).
          exists (put (r,v')).
          now apply SRE.find_2.
        }
        assert (HfiRc': (Rc⌊r⌋)%rc = Some (α, β)).
        {
          destruct HIn as [v Hfi].
          apply RC.find_1 in Hfi.
          apply (RC.Ext.Submap_find _ _ _ Rc') in Hfi as Hfi'; auto.
          rewrite Hfi' in HfiRc; inversion HfiRc; now subst.
        }
        apply (Hyput'' r v' _) in HfiRc'.
        apply (weakening_ℜ _ _ Rc') in HfiRc'; auto.
        rewrite (Term.shift_unfold_1) in HfiRc'; auto.
        -- rewrite (WF_ec_new _ _ HWF').
           rewrite init_input_env_new_key; lia.
        -- now apply RC.Ext.new_key_Submap.
      - apply functional_preserves_keys in fT as []; auto.
    }
    split.
    {
      intros r [α β] v HfiRc' HfiW'.
      rewrite HeqW' in HfiW'.
      admit. 
    }
    split.
    { 
      intro HnEmp1; split; auto; revert HnEmp1.
      rewrite HeqW', ST.update_locals_Empty, ST.Empty_union,
              <- ST.shift_Empty_iff, ST.update_locals_new_key,
              ST.new_key_union, ST.shift_new_refl; auto. 
      intro HEmp.
      apply Classical_Prop.not_and_or in HEmp as [HnEmp1 | HnEmp1].
      - apply HnEmp in HnEmp1 as Hgt.
        destruct (ST.is_empty Wnew) eqn:Hemp.
        -- apply ST.Empty_is_empty in Hemp. 
           rewrite (ST.new_key_Empty Wnew); auto.
           rewrite max_l by lia.
           assert (forall r, r ∈ Rc <-> r ∈ Rc')%rc.
            {
              intro r; split; intro HIn.
              - apply (RC.Submap_in _ Rc); auto.
              -  destruct (RC.In_dec Rc r) as [| HnIn]; auto.
                exfalso.
                apply Stock.Empty_unfold in Hemp.
                apply Hemp.
                exists r.
                rewrite <- HeqD.
                rewrite RE.diff_in_iff.
                rewrite <- (WF_ec_In Rc _ HWF'). 
                rewrite <- (WF_ec_In Rc' _ HWF'').
                split; auto. 
            }
           assert (Vout⁺ = (init_input_env R W)⁺).
            {  
              apply RE.new_key_in_eqDom.
              intro r.
              rewrite <- (WF_ec_In Rc' Vout); auto.
              rewrite <- (WF_ec_In Rc); auto.
              symmetry; auto.
            }
           rewrite (WF_ec_new _ _ HWF''), H0, init_input_env_new_key; lia.
        -- apply ST.not_Empty_is_empty in Hemp. 
           apply HnEmpnew in Hemp as [Heq Hgt'].
           rewrite init_input_env_new_key in Hgt'.
           rewrite max_r by lia.
           rewrite <- Heq.
           symmetry.
           now apply WF_ec_new.
      - apply HnEmpnew in HnEmp1 as [Heq Hgt].
        rewrite init_input_env_new_key in Hgt.
        rewrite max_r by lia.
        rewrite <- Heq.
        symmetry.
        now apply WF_ec_new.
    }
    split.
    {
      intros r [α β] HIn Hfi'.
      rewrite HeqW' in HIn.
      simpl in *.
      apply RM.extend_in_iff in HIn as [HIn | HIn].
      - admit. 
      - admit.
    }
    split.
    { admit. }
    {
      intros r r' v [Hfi Hfi'].
      rewrite HeqW' in Hfi, Hfi'.
      simpl in *.
      apply RM.find_2 in Hfi, Hfi'.
      apply RM.extend_mapsto_iff in Hfi, Hfi'.
      destruct Hfi as [Hfi | [Hfi HnIn]].
      - destruct Hfi' as [Hfi' | [Hfi' HnIn']].
        -- apply RM.find_1 in Hfi, Hfi'.
           apply functional_W_props in fT as 
           [_ [_ [_ [_ [_ [_ ]]]]]].
           apply (H r r' v); split; auto.
        -- assert (HIn: (r' ∈ W)%sk).
           { 
              unfold ST.In; right. 
              admit.
           }
           (* apply HinclW in HIn.
           rewrite HeqW' in HIn.
           rewrite ST.update_locals_in_iff in HIn.
           rewrite ST.union_in_iff in HIn.
           rewrite ST.shift_new_key_in_iff in HIn.
           destruct HIn as [HIn | HIn].
           + apply functional_W_props in fT as 
           [_ [_ [_ [_ [_ [_ ]]]]]]. *)
            admit.
      - destruct Hfi' as [Hfi' | [Hfi' HnIn']].
        -- admit.
        -- admit.
    }
  }
  do 3 (split; auto).
  {
    rewrite HeqS'.
    now apply puts_halts_1.
  }
  {
    rewrite HeqW', ST.update_locals_new_key, 
            ST.new_key_union, ST.shift_new_refl; auto.
    destruct (Stock.is_empty W) eqn:Hemp'.
    - apply ST.Empty_is_empty in Hemp'.
      rewrite ST.new_key_Empty at 1; simpl; auto. 
      destruct (Stock.is_empty Wnew) eqn:Hemp.
      -- apply ST.Empty_is_empty in Hemp.
         apply ST.halts_Empty.
         apply ST.update_locals_Empty.
         apply ST.Empty_union; split; auto.
         apply ST.shift_Empty_iff; auto.
      -- apply ST.not_Empty_is_empty in Hemp.
         apply HnEmpnew in Hemp as [Heq Hgt].
         rewrite <- Heq.
         rewrite <- (WF_ec_new Rc' Vout); auto.
         apply ST.halts_update_locals; auto.
         apply ST.halts_union; split; auto.
         apply ST.halts_weakening; auto.

         apply RC.Ext.new_key_Submap in HsubRc.
         rewrite (WF_ec_new Rc _ HWF') in HsubRc; auto.
         rewrite init_input_env_new_key in HsubRc; lia.
    - apply ST.not_Empty_is_empty in Hemp'.
      destruct (Stock.is_empty Wnew) eqn:Hemp.
      -- apply ST.Empty_is_empty in Hemp.
         rewrite (Stock.new_key_Empty Wnew); auto.
         rewrite Resource.max_l; try lia.

         assert (forall r, r ∈ Rc <-> r ∈ Rc')%rc.
         {
           intro r; split; intro HIn.
           - apply (RC.Submap_in _ Rc); auto.
           -  destruct (RC.In_dec Rc r) as [| HnIn]; auto.
             exfalso.
             apply Stock.Empty_unfold in Hemp.
             apply Hemp.
             exists r.
             rewrite <- HeqD.
             rewrite RE.diff_in_iff.
             rewrite <- (WF_ec_In Rc _ HWF'). 
             rewrite <- (WF_ec_In Rc' _ HWF'').
             split; auto. 
         }
         assert (Vout⁺ = (init_input_env R W)⁺).
         {  
           apply RE.new_key_in_eqDom.
           intro r.
           rewrite <- (WF_ec_In Rc' Vout); auto.
           rewrite <- (WF_ec_In Rc); auto.
           symmetry; auto.
         }
         rewrite H0.
         rewrite init_input_env_new_key. 

         destruct HWF as [_ [_ [_ [_ [_ [_ [_ [Hgt _]]]]]]]].
         apply Hgt in Hemp'.
         rewrite Resource.max_r by lia.
         replace (W⁺ - W⁺)%sk with 0 by lia.
         apply ST.halts_update_locals.
         + rewrite init_input_env_new_key in H0.
           rewrite Resource.max_r in H0 by lia.
           rewrite <- H0; auto.
           rewrite <- (WF_ec_new Rc'); auto.
         + apply ST.halts_union; split. 
           ++ rewrite ST.shift_zero_refl; auto.
           ++ now apply ST.halts_Empty.
      -- apply ST.not_Empty_is_empty in Hemp.
         apply HnEmpnew in Hemp as [Heq Hgt].
         rewrite <- Heq.
         assert ((W ⁺)%sk <= (Rc' ⁺)%rc).
         + apply RC.Ext.new_key_Submap in HsubRc.
           rewrite (WF_ec_new Rc _ HWF') in HsubRc; auto.
           rewrite init_input_env_new_key in HsubRc; lia.
         + rewrite <- (WF_ec_new Rc' Vout); auto.
           rewrite Resource.max_r by lia.
           apply ST.halts_update_locals; auto.
           apply ST.halts_union; split; auto.
           apply ST.halts_weakening; auto.
  }
Abort. *)

(* Lemma init_input_env_unused f R R' W :
 forall r, (r ∈ R)%s -> RE.unused r (init_input_env f R' W).
Proof.
  clear; intros r HIn.
  unfold init_input_env.
  induction W.
  - unfold init_input_env; simpl.
    revert r HIn.
    induction R using Resources.St.set_induction; intros r HIn.
    -- exfalso.
       now apply (H r).
    -- admit.
  - destruct a as [[rg rs] v].
    simpl.
    apply RE.unused_add_1; split; try now simpl.
    apply RE.unused_add_1; split; try now simpl.
Admitted. *)

(** ---- *)


(** ** Progress - Temporal *)

Theorem temporal_progress (n : nat) (Rc : ℜ) (R : resources) (W: 𝐖) (P : Λ) (Rs : resources) :

          halts (Rc⁺)%rc P -> ST.halts (W⁺)%sk W ->
 
          (* inputs_restriction n R Rc W ->  WFₜₜ(R,Rc,W) ->  *)

               ∅%vc ⋅ Rc ⊢ P ∈ (𝟙 ⟿ 𝟙 ∣ Rs) ->
  (* ------------------------------------------------------------------------ *)
       exists (P': Λ) (W': 𝐖), #n ⟦ R ; W ; P ⟧ ⟾ ⟦ R' ; W' ; P' ⟧.
Proof. admit.

  (* intros HltP HltS Hinp HWF Hwt.
  eapply progress_of_functional 
  with (V := init_input_env (next n) R W) (tv := <[unit]>) in Hwt as HI; auto.
  - destruct HI as [V1 [_tv [P' [Wnew [fT Hltout]]]]].
    exists P'.
    exists (ST.update_locals ((ST.shift (W⁺)%sk ((V1⁺)%re - (W⁺)%sk) W) ++ Wnew) V1).
    unfold temporal.
    exists V1, Wnew, _tv; split; auto.
    split; auto.
    admit.
  - repeat split; auto.
    -- unfold init_input_env.
       apply ST.halts_init_locals; auto.
       + destruct W.
         ++ constructor.
         ++ remember (p :: W) as W1.
            destruct HWF as [_ [_ [_ [_ [_ HnEmp]]]]].
            destruct HnEmp.
            * rewrite HeqW1; symmetry; apply nil_cons.
            * now rewrite <- H.
       + *)
        (* apply RE.halts_weakening. apply halts_init_globals.
         intros r HIn.
         apply Hinp in HIn as [Hlt _]. *)
         (* rewrite (TT_EqDom_new Rc R W) in * by (destruct HWF as [HIn [Hdisj _]]; auto). *)
         (* apply SRE.halts_weakening; auto; lia. *)
         (* admit.
    -- exists <[unit]>; split; auto; reflexivity.
  - 
   (* now apply WF_tt_to_WF_ec. *)
   admit.
  - intros r HIn.
    admit. *)
Admitted.


End temporal.
(* 
From Coq Require Import Lia Morphisms Lists.List Arith Lists.Streams.
From Mecha Require Import Resource Resources Term Typ Cell VContext RContext  
                          Type_System Evaluation_Transition Functional_Transition 
                          REnvironment SREnvironment ResourcesMap Stock.
Import ResourceNotations TermNotations TypNotations CellNotations ListNotations
       VContextNotations RContextNotations REnvironmentNotations
       SREnvironmentNotations ResourcesNotations SetNotations StockNotations ResourcesMapNotations.

(** * Semantics - Temporal

  Wormholes’s dynamic semantics is split in three sets of transition rules: the evaluation transition, defined in [Evaluation_Transition.v], which extends standard β-reduction; the functional transition which performs the logical instant, defined in [Functional_Transition.v], and the temporal transition which corresponds to the reactivity of the program: it initializes the resources values, performs the instant via the functional transition and updates the system. In this file, we focus on the temporal transition.
*)


(** ** Definition - Temporal *)

Module RE := REnvironment.
Module SRE := SREnvironment.
Module RM := ResourcesMap.
Module ST := Stock.
Module RC := RContext.

Section temporal.

Hypothesis put : resource * (option Λ) -> Λ.


(** *** Well-formed environments-context *)

Definition well_formed_tt (Rc : ℜ) (R : 𝐄) (W : 𝐖) :=
  (* all ressources in the context are in the stock or the input environment or both *)
  (forall (r : resource), (r ∈ Rc)%rc <->  (r ∈ W)%sk \/ (r ∈ R)%sr) /\ 
  (* the stock and the input environment are disjoint *)
  (forall (r : resource), ((r ∈ W)%sk -> (r ∉ R)%sr) /\ ((r ∈ R)%sr -> (r ∉ W)%sk)) /\
  (* the context, the stock and the input environment are well-formed under themselves *)
  (Rc⁺ ⊩ Rc)%rc /\ (R⁺ ⊩ R)%sr /\ (W⁺ ⊩ W)%sk /\
  (* all terms in the input environment are well-typed module shift application *)
  (forall (r : resource) (α : πΤ) (v : Λ), Rc⌊r⌋%rc = Some α -> R⌊r⌋%sr = Some v ->
          (∅)%vc ⋅ Rc ⊢ {Term.shift (R⁺)%sr ((max (R⁺)%sr (W⁺)%sk) - (R⁺)%sr) v} ∈ {snd α}) /\
  (* all terms in the stock are well-typed and have the type form (𝟙,α), it is a "get" interaction *)
  (forall (r : resource) (α : πΤ) (v : Λ), Rc⌊r⌋%rc = Some α -> W⌊r⌋%sk = Some v ->
          (∅)%vc ⋅ Rc ⊢ v ∈ {snd α} /\ fst α = <[𝟙]>) /\
  (* If the stock is empty then the new key of the stock is equal to the new key of the context *)
  (~ ST.Empty W -> (W⁺)%sk = (Rc⁺)%rc /\ (W⁺)%sk > (R⁺)%sr) /\
  (* all writers are typed as (α,𝟙) *)
  (forall (r : resource) (α : πΤ), 
                    (r ∈ (ST.writers W))%rm -> Rc⌊r⌋%rc = Some α -> (snd α) = <[𝟙]>) /\ 
  (* all readers in the stock are associated to a writer *)
  (forall r : resource, (r ∈ ST.readers W)%sr -> exists r' : resource, ((ST.writers W ⌊ r' ⌋)%rm = Some r))%type /\ 
  (* the find function for writers is injective *)
  (forall (r r' v: resource), 
            ((snd W)⌊r⌋)%rm = Some v /\ ((snd W)⌊r'⌋)%rm = Some v -> r = r').


Notation "'WFₜₜ(' Rc , R , W )" := (well_formed_tt Rc R W) (at level 50).

(** *** [puts] function *)

Definition put_aux (r: resource) (V: 𝐕) :=
  match (V⌊r⌋) with
    | Some (Cell.out v) => Some v
    | _ => None 
  end.

Definition puts (R : 𝐄) (V: 𝐕) :=
  SRE.foldkeys (fun k acc => ⌈k ⤆ put (k,(put_aux k V))⌉ acc)%sr R ∅%sr.

(** *** Initialize the input resource environment 

  The input resource environment consists of locals resources (from W) and global resources (from R). Global resources, at the first instant, are well formed under R. After that, they must be shift in order to be well formed under the maximum between W⁺ and R⁺ because W may contains local resources which are, by construction, greater than global resources. 
*)
Definition init_input_env (R : 𝐄) (W : 𝐖) : 𝐕 :=
  ST.init_locals W (SRE.init_globals (SRE.shift (R⁺)%sr ((max (R⁺)%sr (W⁺)%sk) - (R⁺)%sr) R)).

(** *** Temporal transition *)

Definition temporal (R R': 𝐄) (P P' : Λ) (W W' : 𝐖) :=

  (** (1) Initialize the local memory [Vin] with global and local resources. *)
  let Vin := init_input_env R W in

  exists (Vout : 𝐕) Wnew _tv,
  (** (2) Perform the instant with the functional transition. *)                  
  ⪡ Vin ; unit ; P ⪢ ⭆ ⪡ Vout ; _tv ; P' ; Wnew ⪢ /\

  (** (3) Update the global and local resources. *)               
  (R' = puts R Vout)%sr  /\
  (* ORE.update_globals ([⧐ (R⁺)%sr – (Vout⁺ - (R⁺)%sr)%re] R)%sr Vout)%or /\ *)
  (W' = (ST.update_locals (([⧐ (W⁺)%sk – (Vout⁺ - (W⁺)%sk)%re] W) ∪ Wnew) Vout))%sk.

Notation "'⟦' R ';' W ';' P '⟧' '⟾' '⟦' S1 ';' W1 ';' P1 '⟧'" := (temporal R S1 P P1 W W1) 
(at level 30, R constr, S1 constr, P custom wh, P1 custom wh, W constr, W1 constr, no associativity).

(** ---- *)

(** ** Property - Temporal *)

(** *** [puts] properties *)

#[export] Instance aux_eq (V: 𝐕) : Proper (eq ==> SRE.eq ==> SRE.eq) 
  (fun (k: resource) (acc : SRE.t) => (⌈k ⤆ put (k, put_aux k V) ⌉ acc)%sr).
Proof.
  intros r' r Heqr R R' HeqR; subst.
  now rewrite HeqR.
Qed.

Lemma aux_diamond (V: 𝐕) : SRE.Diamond SRE.eq 
  (fun (k: resource) (_: Λ) (acc : SRE.t) => (⌈ k ⤆ put (k, put_aux k V) ⌉ acc)%sr).
Proof.
  intros r r' _ _ R1 R R' Hneq Heq Heq'.
  rewrite <- Heq, <- Heq'.
  rewrite SRE.add_add_2; now auto.
Qed.

Hint Resolve srenvironment_equiv_eq aux_eq aux_diamond : core.

Lemma puts_Empty (R: 𝐄) (V: 𝐕) :
  (isEmpty(R))%sr -> (isEmpty(puts R V))%sr.
Proof.
  intro HEmp; unfold puts.
  rewrite SRE.foldkeys_Empty; auto.
  apply SRE.empty_1.
Qed.

Lemma puts_Empty_iff (R: 𝐄) (V: 𝐕) :
  (isEmpty(R))%sr -> ((puts R V) = ∅)%sr.
Proof.
  intro HEmp; unfold puts.
  rewrite SRE.foldkeys_Empty; now auto.
Qed.

Lemma puts_Add (r: resource) (e: Λ) (R R': 𝐄) (V: 𝐕) :
  (r ∉ R)%sr -> SRE.Add r e R R' ->
  (puts R' V = (⌈r ⤆ put (r,(put_aux r V))⌉ (puts R V))%sr)%sr.
Proof.
  intros HnIn HAdd.
  unfold puts at 1.
  rewrite SRE.foldkeys_Add; now auto.
Qed.

#[export] Instance puts_eq : Proper (SRE.eq ==> RE.eq ==> SRE.eq) puts.
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
  (puts (⌈r ⤆ e⌉ R) V = ⌈r ⤆ put (r,(put_aux r V))⌉ (puts R V))%sr.
Proof.
  intro HnIn.
  rewrite (puts_Add r e R); auto.
  - reflexivity.
  - apply SRE.Add_add. 
Qed.

Lemma puts_in_iff (R: 𝐄) (V: 𝐕) (r: resource) :
  (r ∈ R)%sr <-> (r ∈ (puts R V))%sr.
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

Lemma puts_new_key (R: 𝐄) (V: 𝐕) :
  (R⁺)%sr = ((puts R V)⁺)%sr.
Proof.
  induction R using SRE.map_induction.
  - do 2 (rewrite SRE.Ext.new_key_Empty; auto).
    now apply puts_Empty.
  - unfold SRE.Add in *; rewrite H0; clear H0.
    rewrite puts_add; auto.
    do 2 rewrite SRE.Ext.new_key_add_max; lia.
Qed.

Lemma puts_Wf (k : lvl) (R : 𝐄) (V : 𝐕) :
  (forall r v, k ⊩ put (r,v))%tm ->
  (k ⊩ R)%sr -> (k ⊩ (puts R V))%sr.
Proof.
  revert V.
  induction R using SRE.map_induction; intros V Hwfput HwfR.
  - rewrite puts_Empty_iff; auto.
    apply SRE.Wf_empty.
  - unfold SRE.Add in H0; rewrite H0 in *; clear H0.
    rewrite puts_add; auto.
    apply SRE.Wf_add_notin in HwfR as [Hwfx [_ Hwfe1]]; auto.
    apply SRE.Wf_add_notin.
    -- now rewrite <- puts_in_iff.
    -- repeat (split; auto).
Qed.

Lemma puts_Wf_V (R : 𝐄) (V : 𝐕) :
  (forall r v, (V⁺) ⊩ put (r,v))%tm ->
  (R⁺)%sr <= V⁺ -> ((V⁺) ⊩ V) -> ((V⁺)%re ⊩ (puts R V))%sr.
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

Lemma puts_halts (k: lvl) (R : 𝐄) (V : 𝐕) :
  (forall r v, halts k (put (r,v)))%tm ->
  SRE.halts k (puts R V).
Proof.
  intro Hyput.
  induction R using SRE.map_induction.
  - apply SRE.halts_Empty.
    now apply puts_Empty.
  - unfold SRE.Add in H0; rewrite H0 in *; clear H0.
    rewrite puts_add; auto.
    apply SRE.halts_add; split; auto.
Qed.

Lemma puts_halts_1 (R : 𝐄) (V : 𝐕) :
  (forall r v, halts (R⁺)%sr (put (r,v)))%tm ->
  SRE.halts ((puts R V)⁺)%sr (puts R V).
Proof.
  intro Hyput.
  apply puts_halts.
  intros r v.
  rewrite <- puts_new_key.
  now apply Hyput.
Qed.

Lemma puts_find (R : 𝐄) (V : 𝐕) (r: resource) (v: Λ) :
  (puts R V ⌊r⌋)%sr = Some v -> exists v', (v = put(r, v'))%type.
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

(** *** [init_input_env] property *)

Lemma init_input_env_in_iff (R: 𝐄) (W: 𝐖) (r: resource) : 
  (r ∈ W)%sk \/ (r ∈ R)%sr <-> r ∈ init_input_env R W.
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
  (~ ST.Empty W -> (W⁺)%sk > (R⁺)%sr) ->
  (R⁺ ⊩ R)%sr -> (W⁺ ⊩ W)%sk ->
  (init_input_env R W)⁺ ⊩ init_input_env R W.
Proof.
  intros HnEmp HwfS HwfW.
  rewrite init_input_env_new_key.
  unfold init_input_env.
  apply ST.init_locals_Wf.
  split.
  - destruct (ST.is_empty W) eqn:Hemp.
    -- apply ST.Empty_is_empty in Hemp.
       now apply ST.Wf_Empty.
    -- apply ST.not_Empty_is_empty in Hemp.
       apply HnEmp in Hemp.
       now rewrite max_r by lia.
  - apply SRE.init_globals_Wf.
    destruct (ST.is_empty W) eqn:Hemp.
    -- apply ST.Empty_is_empty in Hemp.
       rewrite ST.new_key_Empty; auto.
       rewrite max_l by lia.
       replace (R⁺ - R⁺)%sr with 0 by lia.
       now rewrite SRE.shift_zero_refl.
    -- apply ST.not_Empty_is_empty in Hemp.
       apply HnEmp in Hemp.
       rewrite max_r by lia.
       apply SRE.shift_preserves_wf_2; auto; lia.
Qed.   

Lemma temporal_preserves_global_keys (R R': 𝐄) (P P': Λ) (W W' : 𝐖) :
  ⟦R ; W ; P⟧ ⟾ ⟦R' ; W' ; P'⟧ -> (forall (k : resource), (k ∈ R)%sr <-> (k ∈ R')%sr). 
Proof.
  intros [Vin [Wnew [_tv [_ [Heq _]]]]] k.
  now rewrite Heq; rewrite <- puts_in_iff.
Qed.

Lemma temporal_preserves_Wf (R R': 𝐄) (P P' : Λ) (W W' : 𝐖) :
  (forall r v, (R⁺)%sr ⊩ put (r,v))%tm ->
  (~ ST.Empty W -> (W⁺)%sk > (R⁺)%sr) ->
  (R⁺ ⊩ R)%sr -> (W⁺ ⊩ W)%sk -> (max (R⁺)%sr (W⁺)%sk ⊩ P)%tm ->
  ⟦R ; W ; P⟧ ⟾ ⟦R' ; W' ; P'⟧ -> 
  (R'⁺ ⊩ R')%sr /\ (W'⁺ ⊩ W')%sk /\ (max (R'⁺)%sr (W'⁺)%sk ⊩ P')%tm.
Proof.
  intros Hwfput HnEmp HwfS HwfW HwfP [Vout [Wnew [_tv [fT [HeqS HeqW]]]]].
  rewrite HeqS, HeqW.
  rewrite <- (puts_new_key _ Vout).
  rewrite ST.update_locals_new_key.
  rewrite ST.new_key_union.
  (* rewrite SRE.shift_new_refl; auto. *)
  rewrite ST.shift_new_refl; auto.
  apply functional_W_props in fT as HI.
  destruct HI as [_ [_ [HeqDom [HnEmp' _]]]].
  apply functional_preserves_keys in fT as HI.
  destruct HI as [Hincl Hle].
  apply functional_preserves_Wf in fT as HI.
  - destruct HI as [HwfV [_ [HwfP' [HwfW' Hleq]]]].
    split.
    { apply puts_Wf; auto. }
     (* destruct (ST.is_empty Wnew) eqn:Hemp.
     - apply ST.Empty_is_empty in Hemp.
       rewrite (ST.new_key_Empty Wnew); auto.
       replace (max (W⁺)%sk 0) with (W⁺)%sk by lia.
       assert (Heq: Vout⁺ = (init_input_env R W)⁺).
       {
        rewrite (RE.new_key_diff (init_input_env R W) Vout); auto.
        rewrite (ST.eqDom'_new_key _ Wnew); auto.
        rewrite (ST.new_key_Empty Wnew); auto; simpl.
       }
       rewrite init_input_env_new_key in Heq.
       rewrite <- Heq in *.
       apply puts_Wf_V; auto.
       -- intros.
          rewrite Heq.
          specialize (Hwfput r v).
          rewrite HeqW, HeqS in Hwfput.
          rewrite <- (puts_new_key _ Vout) in Hwfput.
          rewrite ST.update_locals_new_key in Hwfput.
          rewrite ST.new_key_union in Hwfput.
          rewrite ST.shift_new_refl in Hwfput; auto.
          rewrite (ST.new_key_Empty Wnew) in Hwfput; auto.
          now replace (max (W⁺)%sk 0) with (W⁺)%sk in Hwfput by lia.
       -- lia.
     - apply ST.not_Empty_is_empty in Hemp.
       apply HnEmp' in Hemp as [Heq Hgt].
       rewrite init_input_env_new_key in Hgt.
       do 2 (rewrite max_r by lia).
       rewrite <- Heq.
       apply puts_Wf_V; auto.
       -- intros.
          rewrite Heq.
          specialize (Hwfput r v).
          rewrite HeqW, HeqS in Hwfput.
          rewrite <- (puts_new_key _ Vout) in Hwfput.
          rewrite ST.update_locals_new_key in Hwfput.
          rewrite ST.new_key_union in Hwfput.
          rewrite ST.shift_new_refl in Hwfput; auto.
          now do 2 (rewrite max_r in Hwfput by lia).
       -- lia.
    } *)
    split.
    {  
     destruct (Stock.is_empty W) eqn:Hemp'.
     - destruct (Stock.is_empty Wnew) eqn:Hemp.
       -- apply Stock.Empty_is_empty in Hemp, Hemp'.
          apply ST.Wf_Empty.
          apply ST.update_locals_Empty.
          apply ST.Empty_union; split; auto.
          apply ST.shift_Empty_iff; auto.

       -- apply ST.Empty_is_empty in Hemp'.
          apply ST.not_Empty_is_empty in Hemp.
          apply HnEmp' in Hemp as [Heq _].
          rewrite ST.new_key_Empty; auto; simpl.
          rewrite <- Heq.
          apply ST.update_locals_Wf; split; auto.
          apply ST.Wf_union; split; auto.
          apply ST.Wf_Empty.
          now apply ST.shift_Empty_iff.
     - apply ST.not_Empty_is_empty in Hemp'.
       apply HnEmp in Hemp' as Hgt.
       destruct (Stock.is_empty Wnew) eqn:Hemp.
       -- apply Stock.Empty_is_empty in Hemp.
          rewrite (Stock.new_key_Empty Wnew); auto.
          rewrite Resource.max_l; try lia.
          assert (Heq: Vout⁺ = (init_input_env R W)⁺).
          {
            rewrite (RE.new_key_diff (init_input_env R W) Vout); auto.
            rewrite (ST.eqDom'_new_key _ Wnew); auto.
            rewrite (ST.new_key_Empty Wnew); auto; simpl.
          }
          rewrite init_input_env_new_key in Heq.
          rewrite max_r in Heq by lia.
          apply ST.update_locals_Wf; split.
          + apply ST.Wf_union; split.
            ++ rewrite Heq.
               replace (W⁺ - W⁺)%sk with 0 by lia.
               now rewrite ST.shift_zero_refl.
            ++ now apply ST.Wf_Empty.
          + now rewrite <- Heq.
       -- apply ST.not_Empty_is_empty in Hemp.
          apply HnEmp' in Hemp as [Heq _].
          rewrite <- Heq.
          rewrite init_input_env_new_key in Hle.
          rewrite max_r by lia.
          apply ST.update_locals_Wf; split; auto.
          apply ST.Wf_union; split; auto.
          apply ST.shift_preserves_wf_2; auto; lia.
    }
    {
     destruct (Stock.is_empty W) eqn:Hemp'.
     - apply Stock.Empty_is_empty in Hemp'.
       destruct (Stock.is_empty Wnew) eqn:Hemp.
       -- apply Stock.Empty_is_empty in Hemp.
          do 2 (rewrite ST.new_key_Empty; auto); simpl.
          assert (Heq: Vout⁺ = (init_input_env R W)⁺).
          {
            rewrite (RE.new_key_diff (init_input_env R W) Vout); auto.
            rewrite (ST.eqDom'_new_key _ Wnew); auto.
            rewrite (ST.new_key_Empty Wnew); auto; simpl.
          }
          rewrite init_input_env_new_key in Heq.
          rewrite ST.new_key_Empty in Heq; auto.
          rewrite max_l in * by lia.
          now rewrite <- Heq.
       -- apply Stock.not_Empty_is_empty in Hemp; auto.
          apply HnEmp' in Hemp as [Heq Hgt].
          rewrite init_input_env_new_key in Hgt.
          do 2 rewrite max_r by lia.
          now rewrite <- Heq. 
     - apply ST.not_Empty_is_empty in Hemp'.
       apply HnEmp in Hemp'.
       rewrite max_r by lia.
       destruct (Stock.is_empty Wnew) eqn:Hemp.
       -- apply Stock.Empty_is_empty in Hemp.
          rewrite (ST.new_key_Empty Wnew); auto; simpl.
          rewrite max_l by lia.
          assert (Heq: Vout⁺ = (init_input_env R W)⁺).
          {
            rewrite (RE.new_key_diff (init_input_env R W) Vout); auto.
            rewrite (ST.eqDom'_new_key _ Wnew); auto.
            rewrite (ST.new_key_Empty Wnew); auto; simpl.
          }
          rewrite init_input_env_new_key in Heq.
          rewrite max_r in * by lia.
          now rewrite <- Heq.
       -- apply Stock.not_Empty_is_empty in Hemp; auto.
          apply HnEmp' in Hemp as [Heq Hgt].
          rewrite init_input_env_new_key in Hgt.
          rewrite max_r by lia.
          now rewrite <- Heq.
    }
  - now apply init_input_env_Wf.
  - constructor.
  - now rewrite init_input_env_new_key.
Qed.


Lemma temporal_W_props (R R' : 𝐄) (P P' : Λ) (W W' : 𝐖) :
  (~ ST.Empty W -> (W⁺)%sk > (R⁺)%sr) ->
  ⟦R ; W ; P⟧ ⟾ ⟦R' ; W' ; P'⟧ -> 
  (forall (k : resource), (k ∈ W)%sk -> (k ∈ W')%sk) /\ 
  (~ ST.Empty W' -> (W'⁺)%sk > (R'⁺)%sr).
Proof. 
  intros HnEmp [Vout [Wnew [_tv [HfT [HeqR' Heq]]]]]; split.
  - intros k HIn.
    rewrite Heq; clear Heq.
    rewrite ST.update_locals_in_iff.
    rewrite ST.union_in_iff; left.
    rewrite ST.shift_new_key_in_iff; auto.
  - rewrite Heq; intros HnEmp'.
    rewrite ST.update_locals_Empty in HnEmp'.
    rewrite ST.Empty_union in HnEmp'.
    apply Classical_Prop.not_and_or in HnEmp' as [HnEmp' | HnEmp'].
    -- rewrite ST.update_locals_new_key.
       rewrite ST.new_key_union.
       rewrite ST.shift_new_refl; auto.
       rewrite <- ST.shift_Empty_iff in HnEmp'.
       rewrite HeqR'.
       rewrite <- puts_new_key. 
       apply HnEmp in HnEmp'; lia.
    -- rewrite ST.update_locals_new_key.
       rewrite ST.new_key_union.
       rewrite ST.shift_new_refl; auto.
       apply functional_W_props in HfT as HI.
       destruct HI as [_ [_ [_ [HnEmp'' _]]]].
       apply HnEmp'' in HnEmp' as [Heq' Hgt].
       rewrite HeqR'.
       rewrite <- puts_new_key. 
       rewrite init_input_env_new_key in Hgt; lia.
Qed.


(** *** [eqDom] properties *)


Lemma TT_EqDom_Empty (Rc : ℜ) (R : 𝐄) (W : 𝐖) :
  (forall r : resource, (r ∈ Rc)%rc <-> (r ∈ W)%sk \/ (r ∈ R)%sr) -> 
  RC.Empty Rc <-> (SRE.Empty R) /\ (ST.Empty W).
Proof.
  intro HIn; split.
  - intros HEmp; split.
    -- intros k v HM.
       assert ((k ∈ W)%sk \/ (k ∈ R)%sr).
       + right; now exists v.
       + rewrite <- HIn in H.
         destruct H as [v' HM'].
         apply (HEmp k v' HM').
    -- apply ST.Empty_notin; intros r HIn'.
       assert ((r ∈ W)%sk \/ (r ∈ R)%sr) by now left.
       rewrite <- HIn in H.
       destruct H as [v' HM'].
       apply (HEmp r v' HM').
  - intros [HEmpS HEmpW] k v HM.
    assert (k ∈ Rc)%rc by now exists v.
    rewrite HIn in H.
    destruct H as [HIn' | [v' HM']].
    -- revert HIn'.
       now apply ST.Empty_notin_1.
    -- apply (HEmpS k v' HM').
Qed. 

Lemma TT_EqDom_new (Rc : ℜ) (R : 𝐄) (W : 𝐖) :
  (forall r : resource, (r ∈ Rc)%rc <-> (r ∈ W)%sk \/ (r ∈ R)%sr) ->  
  (Rc⁺)%rc = max (R⁺)%sr (W⁺)%sk.
Proof.
  revert R W.
  induction Rc using RC.map_induction; intros R W HeqDom.
  - rewrite RC.Ext.new_key_Empty; auto.
    rewrite (TT_EqDom_Empty Rc R W HeqDom) in H.
    destruct H as [HEmp HEmp'].
    rewrite SRE.Ext.new_key_Empty; auto.
    rewrite ST.new_key_Empty; auto.
  - unfold RC.Add in H0; rewrite H0 in *.
    rewrite RC.Ext.new_key_add_max; auto.
    assert (HIn: (x ∈ Rc2)%rc).
    { rewrite H0, RC.add_in_iff; now left. }
    destruct (SRE.In_dec R x) as [HInS | HnInS].
    -- destruct (ST.In_dec x W) as [HInW | HnInW]. 
       + destruct HInS as [v Hfi].
         apply SRE.find_1 in Hfi.
         apply SRE.add_id in Hfi as Heq.
         rewrite <- Heq; clear Heq.
         rewrite <- SRE.add_remove_1.
         rewrite SRE.Ext.new_key_add_max.
         destruct W as [rW wW].
         destruct HInW as [HInrW | HInwW].
         ++ destruct (RM.In_dec wW x) as [[v1 HM] | HnInwW].
            * simpl in HInrW; unfold ST.new_key in *;
              simpl (Stock.readers (rW,wW));
              simpl (Stock.writers (rW,wW)).
              destruct HInrW as [v' Hfi'].
              apply SRE.find_1 in Hfi'.
              apply SRE.add_id in Hfi' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- SRE.add_remove_1.
              rewrite SRE.Ext.new_key_add_max.
              apply RM.find_1 in HM.
              apply RM.add_id in HM as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- RM.add_remove_1.
              rewrite RM.Ext.new_key_add_max.
              rewrite (IHRc1 (SRE.Raw.remove x R) (SRE.Raw.remove x rW,RM.Raw.remove x wW)).
              ** unfold ST.new_key. 
                 simpl (Stock.readers (SRE.Raw.remove x rW, RM.Raw.remove x wW));
                 simpl (Stock.writers (SRE.Raw.remove x rW, RM.Raw.remove x wW)); lia.
              ** intro r; split.
                 {
                  intro HInRc1.
                  destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                  - contradiction.
                  - rewrite <- RC.add_neq_in_iff in HInRc1; eauto.
                    unfold ST.In in *; simpl in *.
                    do 2 rewrite SRE.remove_in_iff.
                    rewrite RM.remove_in_iff.
                    specialize (HeqDom r); rewrite H0 in *; clear H0.
                    apply HeqDom in HInRc1 as [[HIn' | HIn'] | HIn'].
                    -- do 2 left; split; auto.
                    -- left; right; split; auto.
                    -- right; split; auto.
                 }
                 {
                  specialize (HeqDom r); rewrite H0 in *; clear H0.
                  unfold ST.In in *; simpl in *.
                  do 2 rewrite SRE.remove_in_iff.
                  rewrite RM.remove_in_iff.
                  intros [[[Hneq HIn'] | [HIn' Hneq]] | [Hneq HIn']];
                  rewrite <- RC.add_neq_in_iff; eauto;
                  rewrite HeqDom; auto.
                 }
            * simpl in HInrW; unfold ST.new_key in *;
              simpl (Stock.readers (rW,wW));
              simpl (Stock.writers (rW,wW)).
              destruct HInrW as [v' Hfi'].
              apply SRE.find_1 in Hfi'.
              apply SRE.add_id in Hfi' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- SRE.add_remove_1.
              rewrite SRE.Ext.new_key_add_max.
              rewrite (IHRc1 (SRE.Raw.remove x R) (SRE.Raw.remove x rW,wW)).
              ** simpl (Stock.readers (SRE.Raw.remove x rW, wW));
                 simpl (Stock.writers (SRE.Raw.remove x rW, wW)); lia.
              ** intro r; split.
                 {
                  intro HInRc1.
                  destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                  - contradiction.
                  - rewrite <- RC.add_neq_in_iff in HInRc1; eauto.
                    unfold ST.In in *; simpl in *.
                    do 2 rewrite SRE.remove_in_iff.
                    specialize (HeqDom r); rewrite H0 in *; clear H0.
                    apply HeqDom in HInRc1 as [[HIn' | HIn'] | HIn'].
                    -- do 2 left; split; auto.
                    -- left; right; auto.
                    -- right; split; auto.
                 }
                 {
                  specialize (HeqDom r); rewrite H0 in *; clear H0.
                  unfold ST.In in *; simpl in *.
                  do 2 rewrite SRE.remove_in_iff.
                  intros [[[Hneq HIn'] | HIn'] | [Hneq HIn']].
                  - rewrite <- RC.add_neq_in_iff; eauto.
                    rewrite HeqDom; auto.
                  - destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                    -- contradiction.
                    -- rewrite <- RC.add_neq_in_iff; eauto.
                       rewrite HeqDom; auto.
                  - rewrite <- RC.add_neq_in_iff; eauto.
                    rewrite HeqDom; auto.
                 }
         ++ destruct (SRE.In_dec rW x) as [HInrW | HnInrW].
            * simpl in HInwW; unfold ST.new_key in *;
              simpl (Stock.readers (rW,wW));
              simpl (Stock.writers (rW,wW)).
              destruct HInrW as [v' Hfi'].
              apply SRE.find_1 in Hfi'.
              apply SRE.add_id in Hfi' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- SRE.add_remove_1.
              rewrite SRE.Ext.new_key_add_max.
              destruct HInwW as [v'' Hfi''].
              apply RM.find_1 in Hfi''.
              apply RM.add_id in Hfi'' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- RM.add_remove_1.
              rewrite RM.Ext.new_key_add_max.
              rewrite (IHRc1 (SRE.Raw.remove x R) (SRE.Raw.remove x rW,RM.Raw.remove x wW)).
              ** unfold ST.new_key. 
                 simpl (Stock.readers (SRE.Raw.remove x rW, RM.Raw.remove x wW));
                 simpl (Stock.writers (SRE.Raw.remove x rW, RM.Raw.remove x wW)); lia.
              ** intro r; split.
                 {
                  intro HInRc1.
                  destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                  - contradiction.
                  - rewrite <- RC.add_neq_in_iff in HInRc1; eauto.
                    unfold ST.In in *; simpl in *.
                    do 2 rewrite SRE.remove_in_iff.
                    rewrite RM.remove_in_iff.
                    specialize (HeqDom r); rewrite H0 in *; clear H0.
                    apply HeqDom in HInRc1 as [[HIn' | HIn'] | HIn'].
                    -- do 2 left; split; auto.
                    -- left; right; split; auto.
                    -- right; split; auto.
                 }
                 {
                  specialize (HeqDom r); rewrite H0 in *; clear H0.
                  unfold ST.In in *; simpl in *.
                  do 2 rewrite SRE.remove_in_iff.
                  rewrite RM.remove_in_iff.
                  intros [[[Hneq HIn'] | [HIn' Hneq]] | [Hneq HIn']];
                  rewrite <- RC.add_neq_in_iff; eauto;
                  rewrite HeqDom; auto.
                 }
            * simpl in HInwW; unfold ST.new_key in *;
              simpl (Stock.readers (rW,wW));
              simpl (Stock.writers (rW,wW)).
              destruct HInwW as [v'' Hfi''].
              apply RM.find_1 in Hfi''.
              apply RM.add_id in Hfi'' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- RM.add_remove_1.
              rewrite RM.Ext.new_key_add_max.
              rewrite (IHRc1 (SRE.Raw.remove x R) (rW,RM.Raw.remove x wW)).
              ** simpl (Stock.readers (rW, RM.Raw.remove x wW));
                 simpl (Stock.writers (rW, RM.Raw.remove x wW)); lia.
              ** intro r; split.
                 {
                  intro HInRc1.
                  destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                  - contradiction.
                  - rewrite <- RC.add_neq_in_iff in HInRc1; eauto.
                    unfold ST.In in *; simpl in *.
                    rewrite SRE.remove_in_iff.
                    rewrite RM.remove_in_iff.
                    specialize (HeqDom r); rewrite H0 in *; clear H0.
                    apply HeqDom in HInRc1 as [[HIn' | HIn'] | HIn'].
                    -- do 2 left; auto.
                    -- left; right; split; auto.
                    -- right; split; auto.
                 }
                 {
                  specialize (HeqDom r); rewrite H0 in *; clear H0.
                  unfold ST.In in *; simpl in *.
                  rewrite SRE.remove_in_iff.
                  rewrite RM.remove_in_iff.
                  intros [[HIn' | [Hneq HIn']] | [Hneq HIn']].
                  - destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                    -- contradiction.
                    -- rewrite <- RC.add_neq_in_iff; eauto.
                       rewrite HeqDom; auto.
                  - rewrite <- RC.add_neq_in_iff; eauto.
                    rewrite HeqDom; auto.
                  - rewrite <- RC.add_neq_in_iff; eauto.
                    rewrite HeqDom; auto.
                 }
       + destruct HInS as [v Hfi].
         apply SRE.find_1 in Hfi.
         apply SRE.add_id in Hfi as Heq.
         rewrite <- Heq; clear Heq.
         rewrite <- SRE.add_remove_1.
         rewrite SRE.Ext.new_key_add_max.
         rewrite (IHRc1 (SRE.Raw.remove x R) W); try lia.
         intro r; split.
         ++ intro HInRc1.
            destruct (Resource.eq_dec r x) as [| Hneq]; subst.
            * contradiction.
            * rewrite SRE.remove_neq_in_iff; auto.
              rewrite <- HeqDom.
              rewrite H0, RC.add_in_iff; auto.
         ++ intros [HInW | HInS]; auto.
            * destruct (Resource.eq_dec r x) as [| Hneq]; subst.
              ** contradiction.
              ** rewrite <- RC.add_neq_in_iff; eauto.
                 specialize (HeqDom r).
                 rewrite H0 in HeqDom.
                 rewrite HeqDom; auto.
            * apply SRE.remove_in_iff in HInS as [Hneq HInS].
              rewrite <- RC.add_neq_in_iff; eauto.
              specialize (HeqDom r).
              rewrite H0 in HeqDom.
              rewrite HeqDom; auto.
    -- destruct (ST.In_dec x W) as [HInW | HnInW]. 
       + destruct W as [rW wW].
         destruct HInW as [HInrW | HInwW].
         ++ destruct (RM.In_dec wW x) as [HInwW | HnInwW].
            * simpl in HInrW; unfold ST.new_key in *;
              simpl (Stock.readers (rW,wW));
              simpl (Stock.writers (rW,wW)).
              destruct HInrW as [v' Hfi'].
              apply SRE.find_1 in Hfi'.
              apply SRE.add_id in Hfi' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- SRE.add_remove_1.
              rewrite SRE.Ext.new_key_add_max.
              destruct HInwW as [v'' Hfi''].
              apply RM.find_1 in Hfi''.
              apply RM.add_id in Hfi'' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- RM.add_remove_1.
              rewrite RM.Ext.new_key_add_max.
              rewrite (IHRc1 R (SRE.Raw.remove x rW,RM.Raw.remove x wW)).
              ** unfold ST.new_key. 
                 simpl (Stock.readers (SRE.Raw.remove x rW, RM.Raw.remove x wW));
                 simpl (Stock.writers (SRE.Raw.remove x rW, RM.Raw.remove x wW)); lia.
              ** intro r; split.
                 {
                  intro HInRc1.
                  destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                  - contradiction.
                  - rewrite <- RC.add_neq_in_iff in HInRc1; eauto.
                    unfold ST.In in *; simpl in *.
                    rewrite SRE.remove_in_iff.
                    rewrite RM.remove_in_iff.
                    specialize (HeqDom r); rewrite H0 in *; clear H0.
                    apply HeqDom in HInRc1 as [[HIn' | HIn'] | HIn'].
                    -- do 2 left; split; auto.
                    -- left; right; split; auto.
                    -- right; auto.
                 }
                 {
                  specialize (HeqDom r); rewrite H0 in *; clear H0.
                  unfold ST.In in *; simpl in *.
                  rewrite SRE.remove_in_iff.
                  rewrite RM.remove_in_iff.
                  intros [[[Hneq HIn'] | [HIn' Hneq]] | HIn'].
                  - rewrite <- RC.add_neq_in_iff; eauto.
                    rewrite HeqDom; auto.
                  - rewrite <- RC.add_neq_in_iff; eauto.
                    rewrite HeqDom; auto.
                  - destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                    -- contradiction.
                    -- rewrite <- RC.add_neq_in_iff; eauto.
                       rewrite HeqDom; auto.
                 }
            * simpl in HInrW; unfold ST.new_key in *;
              simpl (Stock.readers (rW,wW));
              simpl (Stock.writers (rW,wW)).
              destruct HInrW as [v' Hfi'].
              apply SRE.find_1 in Hfi'.
              apply SRE.add_id in Hfi' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- SRE.add_remove_1.
              rewrite SRE.Ext.new_key_add_max.
              rewrite (IHRc1 R (SRE.Raw.remove x rW,wW)).
              ** simpl (Stock.readers (SRE.Raw.remove x rW, wW));
                 simpl (Stock.writers (SRE.Raw.remove x rW, wW)); lia.
              ** intro r; split.
                 {
                  intro HInRc1.
                  destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                  - contradiction.
                  - rewrite <- RC.add_neq_in_iff in HInRc1; eauto.
                    unfold ST.In in *; simpl in *.
                    rewrite SRE.remove_in_iff.
                    specialize (HeqDom r); rewrite H0 in *; clear H0.
                    apply HeqDom in HInRc1 as [[HIn' | HIn'] | HIn'].
                    -- do 2 left; split; auto.
                    -- left; right; auto.
                    -- right; auto.
                 }
                 {
                  specialize (HeqDom r); rewrite H0 in *; clear H0.
                  unfold ST.In in *; simpl in *.
                  rewrite SRE.remove_in_iff.
                  intros [[[Hneq HIn'] | HIn'] | HIn'].
                  - rewrite <- RC.add_neq_in_iff; eauto.
                    rewrite HeqDom; auto.
                  - destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                    -- contradiction.
                    -- rewrite <- RC.add_neq_in_iff; eauto.
                       rewrite HeqDom; auto.
                  - destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                    -- contradiction.
                    -- rewrite <- RC.add_neq_in_iff; eauto.
                       rewrite HeqDom; auto.
                 }
         ++ destruct (SRE.In_dec rW x) as [HInrW | HnInrW].
            * simpl in HInwW; unfold ST.new_key in *;
              simpl (Stock.readers (rW,wW));
              simpl (Stock.writers (rW,wW)).
              destruct HInrW as [v' Hfi'].
              apply SRE.find_1 in Hfi'.
              apply SRE.add_id in Hfi' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- SRE.add_remove_1.
              rewrite SRE.Ext.new_key_add_max.
              destruct HInwW as [v'' Hfi''].
              apply RM.find_1 in Hfi''.
              apply RM.add_id in Hfi'' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- RM.add_remove_1.
              rewrite RM.Ext.new_key_add_max.
              rewrite (IHRc1 R (SRE.Raw.remove x rW,RM.Raw.remove x wW)).
              ** unfold ST.new_key. 
                 simpl (Stock.readers (SRE.Raw.remove x rW, RM.Raw.remove x wW));
                 simpl (Stock.writers (SRE.Raw.remove x rW, RM.Raw.remove x wW)); lia.
              ** intro r; split.
                 {
                  intro HInRc1.
                  destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                  - contradiction.
                  - rewrite <- RC.add_neq_in_iff in HInRc1; eauto.
                    unfold ST.In in *; simpl in *.
                    rewrite SRE.remove_in_iff.
                    rewrite RM.remove_in_iff.
                    specialize (HeqDom r); rewrite H0 in *; clear H0.
                    apply HeqDom in HInRc1 as [[HIn' | HIn'] | HIn'].
                    -- do 2 left; split; auto.
                    -- left; right; split; auto.
                    -- right; auto.
                 }
                 {
                  specialize (HeqDom r); rewrite H0 in *; clear H0.
                  unfold ST.In in *; simpl in *.
                  rewrite SRE.remove_in_iff.
                  rewrite RM.remove_in_iff.
                  intros [[[Hneq HIn'] | [HIn' Hneq]] | HIn'].
                  - rewrite <- RC.add_neq_in_iff; eauto;
                    rewrite HeqDom; auto.
                  - rewrite <- RC.add_neq_in_iff; eauto;
                    rewrite HeqDom; auto.
                  - destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                    -- contradiction.
                    -- rewrite <- RC.add_neq_in_iff; eauto.
                       rewrite HeqDom; auto.
                 }
            * simpl in HInwW; unfold ST.new_key in *;
              simpl (Stock.readers (rW,wW));
              simpl (Stock.writers (rW,wW)).
              destruct HInwW as [v'' Hfi''].
              apply RM.find_1 in Hfi''.
              apply RM.add_id in Hfi'' as Heq.
              rewrite <- Heq; clear Heq.
              rewrite <- RM.add_remove_1.
              rewrite RM.Ext.new_key_add_max.
              rewrite (IHRc1 R (rW,RM.Raw.remove x wW)).
              ** simpl (Stock.readers (rW, RM.Raw.remove x wW));
                 simpl (Stock.writers (rW, RM.Raw.remove x wW)); lia.
              ** intro r; split.
                 {
                  intro HInRc1.
                  destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                  - contradiction.
                  - rewrite <- RC.add_neq_in_iff in HInRc1; eauto.
                    unfold ST.In in *; simpl in *.
                    rewrite RM.remove_in_iff.
                    specialize (HeqDom r); rewrite H0 in *; clear H0.
                    apply HeqDom in HInRc1 as [[HIn' | HIn'] | HIn'].
                    -- do 2 left; auto.
                    -- left; right; split; auto.
                    -- right; auto.
                 }
                 {
                  specialize (HeqDom r); rewrite H0 in *; clear H0.
                  unfold ST.In in *; simpl in *.
                  rewrite RM.remove_in_iff.
                  intros [[HIn' | [Hneq HIn']] | HIn'].
                  - destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                    -- contradiction.
                    -- rewrite <- RC.add_neq_in_iff; eauto.
                       rewrite HeqDom; auto.
                  - rewrite <- RC.add_neq_in_iff; eauto.
                    rewrite HeqDom; auto.
                  - destruct (Resource.eq_dec r x) as [| Hneq]; subst.
                    -- contradiction.
                    -- rewrite <- RC.add_neq_in_iff; eauto.
                       rewrite HeqDom; auto.
                 }
       + exfalso.
         apply HeqDom in HIn as [|]; auto.
Qed. 
  
Lemma TT_EqDom_Empty' (V: 𝐕) (W: 𝐖) :
  (forall (r: resource), (r ∈ V) <-> (r ∈ W)%sk) ->
  RE.Empty V <-> ST.Empty W.
Proof.
  intro HeqDom; split.
  - intro HnEmp.
    apply ST.Empty_notin.
    intros r HIn.
    rewrite <- HeqDom in *.
    destruct HIn as [v HM].
    now apply (HnEmp r v HM).
  - intros HnEmp k v HM.
    apply (ST.Empty_notin_1 k) in HnEmp.
    apply HnEmp.
    rewrite <- HeqDom.
    now exists v.
Qed.

Lemma TT_EqDom_new' (V: 𝐕) (W: 𝐖) :
  (forall (r: resource), (r ∈ V) <-> (r ∈ W)%sk) ->
  (V⁺)%re = (W⁺)%sk.
Proof.
  revert W; induction V using RE.map_induction; intros W HeqDom.
  - rewrite RE.Ext.new_key_Empty; auto.
    rewrite (TT_EqDom_Empty' _ _ HeqDom) in H.
    rewrite ST.new_key_Empty; auto.
  - unfold RE.Add in H0; rewrite H0 in *.
    rewrite RE.Ext.new_key_add_max.

    destruct W as [rW wW]; unfold ST.In, ST.new_key in *.
    simpl in HeqDom.
    simpl (ST.readers (rW, wW)⁺)%sr.
    simpl (ST.writers (rW, wW)⁺)%rm.

    assert (HIn: (x ∈ ⌈ x ⤆ e ⌉ V1)).
    { rewrite RE.add_in_iff; auto. }

    rewrite <- H0 in HIn.
    apply HeqDom in HIn as HIn'.
    destruct HIn' as [[v HM] | [v' HM']].
    -- apply SRE.find_1 in HM.
       apply SRE.add_id in HM; rewrite <- HM; clear HM.
       rewrite <- SRE.add_remove_1.
       rewrite SRE.Ext.new_key_add_max.

       destruct (RM.In_dec wW x) as [[v' HM'] | HnInw].
       + apply RM.find_1 in HM'.
         apply RM.add_id in HM'; rewrite <- HM'; clear HM'.
         rewrite <- RM.add_remove_1.
         rewrite RM.Ext.new_key_add_max.
         rewrite (IHV1 (SRE.Raw.remove x rW, RM.Raw.remove x wW)).
         ++ simpl (ST.readers (SRE.Raw.remove x rW, RM.Raw.remove x wW)).
            simpl (ST.writers (SRE.Raw.remove x rW, RM.Raw.remove x wW)).
            lia.
         ++ intro r; split; simpl.
            * intro HInRc1.
              destruct (Resource.eq_dec r x); subst; try contradiction.
              rewrite SRE.remove_in_iff.
              rewrite RM.remove_in_iff.
              rewrite <- RE.add_neq_in_iff in HInRc1; eauto.
              rewrite <- H0 in HInRc1.
              apply HeqDom in HInRc1 as [|]; auto.
            * rewrite SRE.remove_in_iff.
              rewrite RM.remove_in_iff.
              intros [[Hneq HInr] | [HInw Hneq]].
              ** rewrite <- RE.add_neq_in_iff; eauto.
                 rewrite <- H0.
                 rewrite HeqDom; auto.
              ** rewrite <- RE.add_neq_in_iff; eauto.
                 rewrite <- H0.
                 rewrite HeqDom; auto.
       + rewrite (IHV1 (SRE.Raw.remove x rW, wW)).
         ++ simpl (ST.readers (SRE.Raw.remove x rW, wW)).
            simpl (ST.writers (SRE.Raw.remove x rW, wW)).
            lia.
         ++ intro r; split; simpl.
            * intro HInRc1.
              destruct (Resource.eq_dec r x); subst; try contradiction.
              rewrite SRE.remove_in_iff.
              rewrite <- RE.add_neq_in_iff in HInRc1; eauto.
              rewrite <- H0 in *.
              apply HeqDom in HInRc1 as [|]; auto.
            * rewrite SRE.remove_in_iff.
              intros [[Hneq HInr] | HInw].
              ** rewrite <- RE.add_neq_in_iff; eauto.
                 rewrite <- H0.
                 rewrite HeqDom; auto.
              ** destruct (Resource.eq_dec r x); subst; try contradiction.
                 rewrite <- RE.add_neq_in_iff; eauto.
                 rewrite <- H0 in *.
                 rewrite HeqDom; auto.
    -- apply RM.find_1 in HM'.
       apply RM.add_id in HM'; rewrite <- HM'; clear HM'.
       rewrite <- RM.add_remove_1.
       rewrite RM.Ext.new_key_add_max.

       destruct (SRE.In_dec rW x) as [HInr | HnInr].

       + destruct HInr as [v HM].
         apply SRE.find_1 in HM.
         apply SRE.add_id in HM; rewrite <- HM; clear HM.
         rewrite <- SRE.add_remove_1.
         rewrite SRE.Ext.new_key_add_max.
         rewrite (IHV1 (SRE.Raw.remove x rW, RM.Raw.remove x wW)).
         ++ simpl (ST.readers (SRE.Raw.remove x rW, RM.Raw.remove x wW)).
            simpl (ST.writers (SRE.Raw.remove x rW, RM.Raw.remove x wW)).
            lia.
         ++ intro r; split; simpl.
            * intro HInRc1.
              destruct (Resource.eq_dec r x); subst; try contradiction.
              rewrite SRE.remove_in_iff.
              rewrite RM.remove_in_iff.
              rewrite <- RE.add_neq_in_iff in HInRc1; eauto.
              rewrite <- H0 in *.
              apply HeqDom in HInRc1 as [|]; auto.
            * rewrite SRE.remove_in_iff.
              rewrite RM.remove_in_iff.
              intros [[Hneq HInr] | [HInw Hneq]].
              ** rewrite <- RE.add_neq_in_iff; eauto.
                 rewrite <- H0.
                 rewrite HeqDom; auto.
              ** rewrite <- RE.add_neq_in_iff; eauto.
                 rewrite <- H0.
                 rewrite HeqDom; auto.
       + rewrite (IHV1 (rW, RM.Raw.remove x wW)).
         ++ simpl (ST.readers (rW, RM.Raw.remove x wW)).
            simpl (ST.writers (rW, RM.Raw.remove x wW)).
            lia.
         ++ intro r; split; simpl.
            * intro HInRc1.
              destruct (Resource.eq_dec r x); subst; try contradiction.
              rewrite RM.remove_in_iff.
              rewrite <- RE.add_neq_in_iff in HInRc1; eauto.
              rewrite <- H0 in *.
              apply HeqDom in HInRc1 as [|]; auto.
            * rewrite RM.remove_in_iff.
              intros [HInr | [Hneq HInw]].
              ** destruct (Resource.eq_dec r x); subst; try contradiction.
                 rewrite <- RE.add_neq_in_iff; eauto.
                 rewrite <- H0 in *.
                 rewrite HeqDom; auto.
              ** rewrite <- RE.add_neq_in_iff; eauto.
                 rewrite <- H0 in *.
                 rewrite HeqDom; auto.
Qed.

(** *** [well_formed_in_ec] properties *)

(*
Lemma WF_tt_empty_locals (Rc: ℜ) (R: 𝐄) :
  (
    (forall (r : resource), (r ∈ Rc)%rc <-> (r ∈ R)%sr) /\ 
    (Rc⁺ ⊩ Rc)%rc /\  (R⁺ ⊩ R)%sr /\
    (forall (r : resource) (α : πΤ) (v : Λ), Rc⌊r⌋%rc = Some α -> 
                                             R⌊r⌋%sr = Some v -> (∅)%vc ⋅ Rc ⊢ v ∈ {snd α})
  ) 
  <-> 
   WFₜₜ(Rc, R, (∅)%sk).
Proof.
  split.
  - intros [HeqDom [HvRc [HvS Hwt]]].
    unfold well_formed_in_ec.
    split.
    -- intro r; split.
       + rewrite HeqDom; auto.
       + intros [Hc | HIn].
         ++ exfalso; revert Hc.
            apply ST.empty_in.
         ++ rewrite HeqDom; auto.
    -- split.
       + intro r; split.
         ++ intros Hc HIn; revert Hc.
            apply ST.empty_in.
         ++ intro Hc.
            apply ST.empty_in.
       + do 2 (split; auto); split.
         ++ apply ST.Wf_empty.
         ++ split.
            * intros r πα v HfRc.
              split; intro Hfi.
              ** replace (Nat.max (R⁺)%sr (∅⁺)%sk - (R⁺)%sr) with 0.
                 { 
                  rewrite Term.shift_zero_refl.
                  apply (Hwt r); auto.
                 }
                 { rewrite ST.new_key_empty; lia. }
              ** inversion Hfi.
            * split.
              ** intro Hc; exfalso.
                 apply Hc.
                 apply ST.Empty_empty.
              ** split. 
                 { 
                  simpl; intros r πα HIn.
                  inversion HIn.
                  apply RM.empty_mapsto_iff in H.
                  contradiction.
                 }
                 split.
                 { 
                  simpl; intros r [v HM].
                  apply SRE.empty_mapsto_iff in HM.
                  contradiction.
                 }
                 { intros r r' v [Hfi _]; inversion Hfi. }
  - intros [HeqDom [_ [HvRc [HvS [_ [Hwt _]]]]]].
    split.
    -- intro r; split; intro HIn.
       + rewrite HeqDom in HIn.
         destruct HIn as [HIn |]; auto.
         exfalso; revert HIn.
         apply ST.empty_in.
       + rewrite HeqDom; auto.
    -- do 2 (split; auto).
       intros r πα v HfRc HfS.
       apply (Hwt _ _ v) in HfRc as HI.
       destruct HI as [Hwt' _].
       replace (Nat.max (R⁺)%sr (∅⁺)%sk - (R⁺)%sr) with 0 in Hwt'.
       { 
        rewrite Term.shift_zero_refl in Hwt'.
        apply Hwt'; auto.
       }
       { rewrite ST.new_key_empty; lia. }
Qed.
*)

#[export] Instance WF_in_eq : Proper (RContext.eq ==> SRE.eq ==> ST.eq ==> iff) well_formed_tt.
Proof.
  intros Rc Rc1 HeqRe R R' HeqS W W' HeqW; split.
  - intros [HeqDom [HDisj [HvRc [HvS [HvW [Hwt [Hwt' [Hgt [Hwt'' [Hcorr Hinj]]]]]]]]]].  
    split.
    { intro r; rewrite <- HeqS, <- HeqW, <- HeqRe; auto. }
    split.
    { intro r; rewrite <- HeqS, <- HeqW; auto. }
    split; try (now rewrite <- HeqRe).
    split; try (now rewrite <- HeqS).
    split; try (now rewrite <- HeqW).
    split.
    {
      intros r πα v.
      rewrite <- HeqW, <- HeqS, <- HeqRe.
      apply Hwt.
    }
    split.
    {
      intros r πα v.
      rewrite <- HeqW, <- HeqRe.
      apply Hwt'.
    }
    split.
    { 
      intros HnEmp.
      rewrite <- HeqW, <- HeqRe, <- HeqS. 
      rewrite <- HeqW in HnEmp.
      now apply Hgt.
    }
    split.
    {
      intros r πα. 
      rewrite <- HeqW, <- HeqRe.
      apply (Hwt'' r πα).
    }
    split.
    { 
      intro r.
      rewrite <- HeqW.
      intro HIn.
      apply Hcorr in HIn as [r' Hfi].
      exists r'.
      now rewrite <- HeqW.
    }
    {
      intros r r' v [Hfi Hfi'].
      apply (Hinj _ _ v).
      now split; rewrite HeqW.
    }
  - intros [HeqDom [HDisj [HvRc [HvS [HvW [Hwt [Hwt' [Hgt [Hwt'' [Hcorr Hinj]]]]]]]]]].  
    split.
    { intro r; rewrite HeqS, HeqW, HeqRe; auto. }
    split.
    { intro r; rewrite HeqS, HeqW; auto. }
    split; try (now rewrite HeqRe).
    split; try (now rewrite HeqS).
    split; try (now rewrite HeqW).
    split.
    {
      intros r πα v.
      rewrite HeqW, HeqS, HeqRe.
      apply Hwt.
    }
    split.
    {
      intros r πα v.
      rewrite HeqW, HeqRe.
      apply Hwt'.
    }
    split.
    { 
      intros HnEmp.
      rewrite HeqW, HeqRe, HeqS. 
      rewrite HeqW in HnEmp.
      now apply Hgt.
    }
    split.
    {
      intros r πα. 
      rewrite HeqW, HeqRe.
      apply (Hwt'' r πα).
    }
    split.
    { 
      intro r.
      rewrite HeqW.
      intro HIn.
      apply Hcorr in HIn as [r' Hfi].
      exists r'.
      now rewrite HeqW.
    }
    {
      intros r r' v [Hfi Hfi'].
      apply (Hinj _ _ v).
      now split; rewrite <- HeqW.
    }
Qed.

Lemma WF_tt_new (Rc : ℜ) (R : 𝐄) (W : 𝐖) :
  WFₜₜ(Rc, R, W) -> (Rc⁺)%rc = max (R⁺)%sr (W⁺)%sk.
Proof.
  intros [HeqDom _].
  now apply TT_EqDom_new.
Qed.

Lemma WF_tt_Wf (Rc : ℜ) (R : 𝐄) (W : 𝐖) :
  WFₜₜ(Rc, R, W) -> (Rc⁺ ⊩ Rc)%rc /\ (R⁺ ⊩ R)%sr /\ (W⁺ ⊩ W)%sk.
Proof.
  intros [_ [_ [HwfRc [HwfS [HwfW _]]]]]; auto.
Qed.

Lemma WF_tt_to_WF_ec (Rc : ℜ) (R : 𝐄) (W : 𝐖) :
  WFₜₜ(Rc, R, W) -> WF(Rc,init_input_env R W).
Proof.
  intros [HeqDom [HneqDom [HvRe [HvS [HvW [Hwt [Hwt' [HnInW HeqWw]]]]]]]]; split.
  { intro x; rewrite <- init_input_env_in_iff; auto. }
  do 2 (split; auto).
  {
   apply init_input_env_Wf; auto.
   intro HnEmp.
   now apply HnInW in HnEmp as [].
  }
  { 
    intros r α β v Hfi HfV.
    apply ST.init_locals_find_inp in HfV as H.
    - destruct H as [v' Heq]; subst.
      apply ST.init_locals_find_1 in HfV as [HfW | HfW].
      -- simpl in *.
         apply Hwt' with (v := v') in Hfi as H.
          destruct H as [HwtW _]; auto.
          now unfold ST.find.
      -- apply RM.init_writers_find in HfW as H.
          destruct H as [HInW | HfS].
          + apply HeqWw with (α := (α,β)) in HInW as Heq; auto.
            simpl in *; subst.
            rewrite RM.init_writers_in in HfW; auto.
            inversion HfW; subst; constructor.
          + rewrite SRE.init_globals_shift in HfS. 
            apply RE.shift_find_e_1 in HfS as H.
            destruct H as [[r' Heq] [d Heqd]]; subst.
            destruct d as [t | t]; simpl in *; inversion Heqd; subst; clear Heqd.
            replace (Cell.inp <[[⧐{(R ⁺)%sr} – {(max (R⁺)%sr (W⁺)%sk) - (R ⁺)%sr}] t]>)
            with (Cell.shift (R⁺)%sr ((max (R⁺)%sr (W⁺)%sk) - (R⁺)%sr) (Cell.inp t)) 
            in HfS by now simpl.
            rewrite <- RE.shift_find_iff in HfS.
            rewrite SRE.init_globals_find_iff in HfS.
            rewrite Resource.shift_wf_refl in Hfi.
            ++ apply Hwt with (v := t) in Hfi; auto.
            ++ apply (SRE.Wf_find (R⁺)%sr) in HfS as [H _]; auto.
    - intros r' HfS.
      now apply SRE.init_globals_find_e in HfS.
  }
Qed.

(** ---- *)

(** ** Preservation - Temporal *)

Hypothesis all_arrow_halting : forall Rc t α β,
  ∅%vc ⋅ Rc ⊢ arr(t) ∈ (α ⟿ β ∣ ∅%s) -> forall v, ∅%vc ⋅ Rc ⊢ v ∈ α -> halts (Rc⁺)%rc <[t v]>.

Theorem temporal_preserves_typing (Rc : ℜ) (R R': 𝐄) (W W' : 𝐖) (P P' : Λ) (Rs : resources) :

         halts (Rc⁺)%rc P -> SRE.halts (R⁺)%sr R -> ST.halts (W⁺)%sk W -> 
                       (forall r v, (R⁺)%sr ⊩ put (r,v))%tm ->
                       (forall r v, halts (R⁺)%sr (put (r,v)))%tm ->
                       (forall r v α, Rc⌊r⌋%rc = Some α -> ∅%vc ⋅ Rc ⊢ {Term.shift (R⁺)%sr ((Rc⁺)%rc - (R⁺)%sr) (put (r,v))} ∈ {snd α}) ->

                  WFₜₜ(Rc,R,W) -> ∅%vc ⋅ Rc ⊢ P ∈ (𝟙 ⟿ 𝟙 ∣ Rs) -> 
                      
                      ⟦ R ; W ; P ⟧ ⟾ ⟦ R' ; W' ; P' ⟧ ->
  (* ------------------------------------------------------------------------ *)
       exists (Rc1 : ℜ) (Rs' : resources),
          (Rs ⊆ Rs')%s /\ (Rc ⊆ Rc1)%rc /\ WFₜₜ(Rc1,R',W') /\
          
          ∅%vc ⋅ Rc1 ⊢ P' ∈ (𝟙 ⟿ 𝟙 ∣ Rs') /\ 
     
          halts (Rc1⁺)%rc P' /\ SRE.halts (R'⁺)%sr R' /\ ST.halts (W'⁺)%sk W'.
Proof.
  intros HltP HltS HltW Hyput Hyput' Hyput'' HWF HwtP HTT.

  assert (HnEmp: ~ ST.Empty W -> (W ⁺)%sk > (R ⁺)%sr).
  {
   destruct HWF as [_ [_ [_ [_ [_ [_ [_ [HnEmp _]]]]]]]].
   intros Hn.
   now apply HnEmp in Hn as []. 
  }
  apply temporal_W_props in HTT as HI; auto.
  destruct HI as [HinclW HnEmp'].

  apply WF_tt_Wf in HWF as HI.
  destruct HI as [HwfRc [HwfS HwfW]].
  apply well_typed_implies_Wf in HwtP as HI; auto.
  destruct HI as [HwfP _].
  rewrite (WF_tt_new _ _ _ HWF) in HwfP.

  apply temporal_preserves_Wf in HTT as HI; auto.
  rewrite <- (WF_tt_new _ _ _ HWF) in HwfP.
  destruct HI as [HwfS' [HwfW' HwfP']].
  destruct HTT as [Vout [Wnew [_tv [fT [HeqS' HeqW']]]]].

  (* clean *)
  move Vout before R; move R' before R; move Wnew before W'; 
  move _tv before P'; move fT before HwtP;
  move HwfRc before Rs; move HwfS before HwfRc;
  move HwfW before HwfS; move HwfP before HwfW;
  move HeqS' before Rs; move HeqW' before HeqS';
  move HnEmp before HnEmp'; move HwfS' before HwfS;
  move HwfW' before HwfW; move HwfP' before HwfP; 
  move Hyput before Rs; move Hyput' before Hyput.
  (* clean *)

  apply WF_tt_to_WF_ec in HWF as HWF'; move HWF' before HWF.
  apply functional_W_props in fT as H.
  destruct H as [_ [_ [HeqD [HnEmpnew _]]]].

  assert (Hinp: fT_inputs_halts (Rc ⁺)%rc (init_input_env R W) <[ unit ]> P).
  {
    repeat split; auto.
    - unfold init_input_env.
      apply ST.halts_init_locals; auto.
      -- rewrite (TT_EqDom_new _ R W); auto;
         destruct HWF as [HIn [Hdisj [_ [_ [HvW [_ [HEmp _]]]]]]]; auto.
         destruct (ST.is_empty W) eqn:Heq.
         + apply ST.Empty_is_empty in Heq.
           now apply ST.halts_Empty.
         + apply ST.not_Empty_is_empty in Heq.
           apply HnEmp in Heq.
           now replace (Init.Nat.max (R⁺)%sr (W⁺)%sk) with (W⁺)%sk by lia.
      -- apply SRE.halts_init_globals.
         rewrite (TT_EqDom_new Rc R W) in * by (destruct HWF as [HIn [Hdisj _]]; auto).
         apply SRE.halts_weakening; auto; lia.
    - exists <[unit]>; split; auto; reflexivity.
  }

  apply (functional_preserves_typing_gen 
              all_arrow_halting Rc _ _ _ _ _ _ _ <[𝟙]> <[𝟙]> Rs) in fT as IH; auto.
  destruct IH as [Hunsd [Hlcl [Rc' [Rs' [HsubRc [HsubR [[HltVout [HltWnew [_ HltP']]] 
                        [Hwtv' [HwtP' [HWF'' [HwtW1 [HInR Husd1]]]]]]]]]]]].    
  apply WF_ec_Wf in HWF'' as HI.
  destruct HI as [HwfRc' HwfVout].

  (* clean *)
  move Rc' before Rc; move Rs' before Rs; move HltVout before HltP;
  move HltWnew before HltW; move HltP' before HltP; move Hwtv' before HwtP;
  move HwtP' before HwtP; move Hinp before HltWnew; move HWF'' before HWF';
  move HsubRc before HeqW'; move HsubR before HsubRc; move HeqD before HinclW;
  move HwfRc' before HwfRc; move HwfVout before HwfW'; move Hyput'' before Hyput'.
  (* clean *)

  exists Rc', Rs'.
  do 3 (split; auto).
  { 
    split.
    {
      intro r. 
      destruct HWF as [HeqDom _].
      rewrite HeqW', HeqS', ST.update_locals_in_iff, 
              <- puts_in_iff, ST.union_in_iff,
              ST.shift_new_key_in_iff, <- (HeqD r).
      rewrite or_assoc, <- or_comm, or_assoc,
             (or_comm (r ∈ R)%sr), <- HeqDom.
      rewrite RE.diff_in_iff, <- (WF_ec_In Rc' Vout HWF''),
              <- (WF_ec_In Rc _ HWF'), <- RC.diff_in_iff.
      now rewrite <- RC.diff_Submap_in; auto.
    }
    split.
    {
      intro r.
      destruct HWF as [HeqDom [Hdisj _]].
      rewrite HeqW', HeqS', ST.update_locals_in_iff, 
              <- puts_in_iff, ST.union_in_iff,
              ST.shift_new_key_in_iff, <- (HeqD r).
      rewrite RE.diff_in_iff, <- (WF_ec_In Rc' Vout HWF''),
              <- (WF_ec_In Rc _ HWF').
      specialize (Hdisj r).
      destruct Hdisj as [Hdisj1 Hdisj2].
      split.
      - intros [HIn | [HIn HnIn]]; auto.
        rewrite HeqDom in HnIn.
        intro Hc; apply HnIn; now right.
      - intros HIn [HInW | [HInRc' HnIn]].
        -- revert HInW; now apply Hdisj2.
        -- apply HnIn.
           rewrite HeqDom; auto. 
    }
    do 4 (split; auto).
    {
      destruct HWF as [HeqDom _].
      apply TT_EqDom_new in HeqDom as Hnew.
      intros r [α β] v HfiRc.
      rewrite HeqS', <- puts_new_key, HeqW', 
              ST.update_locals_new_key, ST.new_key_union.
      rewrite ST.shift_new_refl; auto; simpl.
      replace (max (R ⁺)%sr (max (W ⁺)%sk (Wnew ⁺)%sk))
      with    (max (max (R ⁺)%sr (W ⁺)%sk) (Wnew ⁺)%sk) by lia.
      rewrite <- Hnew.
      intro HfiR'.
      apply TT_EqDom_new' in HeqD as Hnew'.
      rewrite <- Hnew', (WF_ec_new _ _ HWF').
      replace (max (init_input_env R W ⁺) (RE.diff Vout (init_input_env R W) ⁺))
      with (max (RE.diff Vout (init_input_env R W) ⁺) (init_input_env R W ⁺)) by lia.
      rewrite <- RE.new_key_diff.
      - rewrite <- (WF_ec_new _ _ HWF'').
        apply puts_find in HfiR' as Heq.
        destruct Heq as [v' Heq]; subst.
        assert (HIn: (r ∈ Rc)%rc).
        {
          rewrite (WF_ec_In _ _ HWF'), <- init_input_env_in_iff.
          right.
          rewrite (puts_in_iff _ Vout).
          exists (put (r,v')).
          now apply SRE.find_2.
        }
        assert (HfiRc': (Rc⌊r⌋)%rc = Some (α, β)).
        {
          destruct HIn as [v Hfi].
          apply RC.find_1 in Hfi.
          apply (RC.Ext.Submap_find _ _ _ Rc') in Hfi as Hfi'; auto.
          rewrite Hfi' in HfiRc; inversion HfiRc; now subst.
        }
        apply (Hyput'' r v' _) in HfiRc'.
        apply (weakening_ℜ _ _ Rc') in HfiRc'; auto.
        rewrite (Term.shift_unfold_1) in HfiRc'; auto.
        -- rewrite (WF_ec_new _ _ HWF').
           rewrite init_input_env_new_key; lia.
        -- now apply RC.Ext.new_key_Submap.
      - apply functional_preserves_keys in fT as []; auto.
    }
    split.
    {
      intros r [α β] v HfiRc' HfiW'.
      rewrite HeqW' in HfiW'.
      admit. 
    }
    split.
    { 
      intro HnEmp1; split; auto; revert HnEmp1.
      rewrite HeqW', ST.update_locals_Empty, ST.Empty_union,
              <- ST.shift_Empty_iff, ST.update_locals_new_key,
              ST.new_key_union, ST.shift_new_refl; auto. 
      intro HEmp.
      apply Classical_Prop.not_and_or in HEmp as [HnEmp1 | HnEmp1].
      - apply HnEmp in HnEmp1 as Hgt.
        destruct (ST.is_empty Wnew) eqn:Hemp.
        -- apply ST.Empty_is_empty in Hemp. 
           rewrite (ST.new_key_Empty Wnew); auto.
           rewrite max_l by lia.
           assert (forall r, r ∈ Rc <-> r ∈ Rc')%rc.
            {
              intro r; split; intro HIn.
              - apply (RC.Submap_in _ Rc); auto.
              -  destruct (RC.In_dec Rc r) as [| HnIn]; auto.
                exfalso.
                apply Stock.Empty_unfold in Hemp.
                apply Hemp.
                exists r.
                rewrite <- HeqD.
                rewrite RE.diff_in_iff.
                rewrite <- (WF_ec_In Rc _ HWF'). 
                rewrite <- (WF_ec_In Rc' _ HWF'').
                split; auto. 
            }
           assert (Vout⁺ = (init_input_env R W)⁺).
            {  
              apply RE.new_key_in_eqDom.
              intro r.
              rewrite <- (WF_ec_In Rc' Vout); auto.
              rewrite <- (WF_ec_In Rc); auto.
              symmetry; auto.
            }
           rewrite (WF_ec_new _ _ HWF''), H0, init_input_env_new_key; lia.
        -- apply ST.not_Empty_is_empty in Hemp. 
           apply HnEmpnew in Hemp as [Heq Hgt'].
           rewrite init_input_env_new_key in Hgt'.
           rewrite max_r by lia.
           rewrite <- Heq.
           symmetry.
           now apply WF_ec_new.
      - apply HnEmpnew in HnEmp1 as [Heq Hgt].
        rewrite init_input_env_new_key in Hgt.
        rewrite max_r by lia.
        rewrite <- Heq.
        symmetry.
        now apply WF_ec_new.
    }
    split.
    {
      intros r [α β] HIn Hfi'.
      rewrite HeqW' in HIn.
      simpl in *.
      apply RM.extend_in_iff in HIn as [HIn | HIn].
      - admit. 
      - admit.
    }
    split.
    { admit. }
    {
      intros r r' v [Hfi Hfi'].
      rewrite HeqW' in Hfi, Hfi'.
      simpl in *.
      apply RM.find_2 in Hfi, Hfi'.
      apply RM.extend_mapsto_iff in Hfi, Hfi'.
      destruct Hfi as [Hfi | [Hfi HnIn]].
      - destruct Hfi' as [Hfi' | [Hfi' HnIn']].
        -- apply RM.find_1 in Hfi, Hfi'.
           apply functional_W_props in fT as 
           [_ [_ [_ [_ [_ [_ ]]]]]].
           apply (H r r' v); split; auto.
        -- assert (HIn: (r' ∈ W)%sk).
           { 
              unfold ST.In; right. 
              admit.
           }
           (* apply HinclW in HIn.
           rewrite HeqW' in HIn.
           rewrite ST.update_locals_in_iff in HIn.
           rewrite ST.union_in_iff in HIn.
           rewrite ST.shift_new_key_in_iff in HIn.
           destruct HIn as [HIn | HIn].
           + apply functional_W_props in fT as 
           [_ [_ [_ [_ [_ [_ ]]]]]]. *)
            admit.
      - destruct Hfi' as [Hfi' | [Hfi' HnIn']].
        -- admit.
        -- admit.
    }
  }
  do 3 (split; auto).
  {
    rewrite HeqS'.
    now apply puts_halts_1.
  }
  {
    rewrite HeqW', ST.update_locals_new_key, 
            ST.new_key_union, ST.shift_new_refl; auto.
    destruct (Stock.is_empty W) eqn:Hemp'.
    - apply ST.Empty_is_empty in Hemp'.
      rewrite ST.new_key_Empty at 1; simpl; auto. 
      destruct (Stock.is_empty Wnew) eqn:Hemp.
      -- apply ST.Empty_is_empty in Hemp.
         apply ST.halts_Empty.
         apply ST.update_locals_Empty.
         apply ST.Empty_union; split; auto.
         apply ST.shift_Empty_iff; auto.
      -- apply ST.not_Empty_is_empty in Hemp.
         apply HnEmpnew in Hemp as [Heq Hgt].
         rewrite <- Heq.
         rewrite <- (WF_ec_new Rc' Vout); auto.
         apply ST.halts_update_locals; auto.
         apply ST.halts_union; split; auto.
         apply ST.halts_weakening; auto.

         apply RC.Ext.new_key_Submap in HsubRc.
         rewrite (WF_ec_new Rc _ HWF') in HsubRc; auto.
         rewrite init_input_env_new_key in HsubRc; lia.
    - apply ST.not_Empty_is_empty in Hemp'.
      destruct (Stock.is_empty Wnew) eqn:Hemp.
      -- apply ST.Empty_is_empty in Hemp.
         rewrite (Stock.new_key_Empty Wnew); auto.
         rewrite Resource.max_l; try lia.

         assert (forall r, r ∈ Rc <-> r ∈ Rc')%rc.
         {
           intro r; split; intro HIn.
           - apply (RC.Submap_in _ Rc); auto.
           -  destruct (RC.In_dec Rc r) as [| HnIn]; auto.
             exfalso.
             apply Stock.Empty_unfold in Hemp.
             apply Hemp.
             exists r.
             rewrite <- HeqD.
             rewrite RE.diff_in_iff.
             rewrite <- (WF_ec_In Rc _ HWF'). 
             rewrite <- (WF_ec_In Rc' _ HWF'').
             split; auto. 
         }
         assert (Vout⁺ = (init_input_env R W)⁺).
         {  
           apply RE.new_key_in_eqDom.
           intro r.
           rewrite <- (WF_ec_In Rc' Vout); auto.
           rewrite <- (WF_ec_In Rc); auto.
           symmetry; auto.
         }
         rewrite H0.
         rewrite init_input_env_new_key. 

         destruct HWF as [_ [_ [_ [_ [_ [_ [_ [Hgt _]]]]]]]].
         apply Hgt in Hemp'.
         rewrite Resource.max_r by lia.
         replace (W⁺ - W⁺)%sk with 0 by lia.
         apply ST.halts_update_locals.
         + rewrite init_input_env_new_key in H0.
           rewrite Resource.max_r in H0 by lia.
           rewrite <- H0; auto.
           rewrite <- (WF_ec_new Rc'); auto.
         + apply ST.halts_union; split. 
           ++ rewrite ST.shift_zero_refl; auto.
           ++ now apply ST.halts_Empty.
      -- apply ST.not_Empty_is_empty in Hemp.
         apply HnEmpnew in Hemp as [Heq Hgt].
         rewrite <- Heq.
         assert ((W ⁺)%sk <= (Rc' ⁺)%rc).
         + apply RC.Ext.new_key_Submap in HsubRc.
           rewrite (WF_ec_new Rc _ HWF') in HsubRc; auto.
           rewrite init_input_env_new_key in HsubRc; lia.
         + rewrite <- (WF_ec_new Rc' Vout); auto.
           rewrite Resource.max_r by lia.
           apply ST.halts_update_locals; auto.
           apply ST.halts_union; split; auto.
           apply ST.halts_weakening; auto.
  }
Abort.

(*
(** ---- *)


(** ** Progress - Temporal *)

Theorem temporal_progress (Rc : ℜ) (R : 𝐄) (W: 𝐖) (P : Λ) (R : resources) :

         halts (Rc⁺)%rc P -> SRE.halts (R⁺)%sr R -> ST.halts (W⁺)%sk W -> 
                WFₜₜ(Rc,R,W) -> ∅%vc ⋅ Rc ⊢ P ∈ (𝟙 ⟿ 𝟙 ∣ R) ->
  (* ------------------------------------------------------------------------ *)
       exists (R' : o𝐄) (P': Λ) (W': 𝐖), ⟦ R ; W ; P ⟧ ⟾ ⟦ R' ; W' ; P' ⟧.
Proof.
  intros HltP HltS HltW HWF Hwt.
  eapply progress_of_functional 
  with (V := init_input_env R W) (tv := <[unit]>) in Hwt as HI; auto.
  - destruct HI as [V1 [_tv [P' [Wnew [fT _]]]]].
    exists (ORE.update_globals ([⧐ (R⁺)%sr – (V1⁺ - (R⁺)%sr)%re] R)%sr V1)%or.
    exists P'.
    exists (ST.update_locals (([⧐ (W⁺)%sk – (V1⁺ - (W⁺)%sk)%re] W) ∪ Wnew)%sk V1).
    unfold temporal.
    exists V1, Wnew, _tv; split; auto.
    split; try reflexivity.
  - repeat split; auto.
    -- unfold init_input_env.
       apply ST.halts_init_locals; auto.
       + rewrite (TT_EqDom_new _ R W); auto;
         destruct HWF as [HIn [Hdisj [_ [_ [HvW [_ [HEmp _]]]]]]]; auto.
         destruct (ST.is_empty W) eqn:Heq.
         ++ apply ST.Empty_is_empty in Heq.
            now apply ST.halts_Empty.
         ++ apply ST.not_Empty_is_empty in Heq.
            apply HEmp in Heq.
            replace (Init.Nat.max (R⁺)%sr (W⁺)%sk) with (W⁺)%sk by lia.
            assumption.
       + apply SRE.halts_init_globals.
         rewrite (TT_EqDom_new Rc R W) in * by (destruct HWF as [HIn [Hdisj _]]; auto).
         apply SRE.halts_weakening; auto; lia.
    -- exists <[unit]>; split; auto; reflexivity.
  - now apply WF_tt_to_WF_ec.
  - intros r HIn.
    apply WF_tt_to_WF_ec in HWF.
    apply WF_ec_Wf in HWF as H.
    destruct H as [HvRe HvV].
    destruct HltP as [P' [HmeT HvP']].
    apply multi_preserves_typing with (t' := P') in Hwt; auto.
    apply typing_Re_R with (r := r) in Hwt; auto.
    rewrite (WF_ec_In Rc (init_input_env R W)) in Hwt; auto.
    unfold init_input_env in *.
    apply ST.init_locals_in_iff in Hwt as [HIn' | HIn'].
    -- now apply ST.init_locals_in_unused.
    -- apply ST.init_locals_unused.
       apply SRE.init_globals_in_unused.
       now rewrite <- SRE.init_globals_in_iff.
Qed.
*)

End temporal. *)