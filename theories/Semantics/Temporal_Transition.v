From Coq Require Import Lia Morphisms Lists.List Arith Lists.Streams.
From Mecha Require Import Resource Term Typ Cell 
                          VContext RContext REnvironment Stock SREnvironment
                          Type_System Evaluation_Transition Functional_Transition 
                          SyntaxNotation EnvNotation.
Import ListNotations.

(** * Semantics - Temporal

  Wormholes’s dynamic semantics is split in three sets of transition rules: the evaluation transition, defined in [Evaluation_Transition.v], which extends standard β-reduction; the functional transition which performs the logical instant, defined in [Functional_Transition.v], and the temporal transition which corresponds to the reactivity of the program: it initializes the resources values, performs the instant via the functional transition and updates the system. In this file, we focus on the temporal transition.
*)


(** ** Definition - Temporal *)



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
  (forall (r r' : resource) (A B C D : Τ) (v : Λ),
      In (r,r',v) W ->
      Rc⌊r⌋%rc = Some (A,B) ->
      Rc⌊r'⌋%rc = Some (C,D) -> ∅%vc ⋅ Rc ⊢ v ∈ B /\ A = <[𝟙]> /\ C = B /\ A = D)
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

(** *** Halt property for temporal's inputs *)

Definition tT_inputs_halts n R W P :=
  halts n P /\ halts_sre (R⁺)%sr R /\ halts_sk (W⁺)%sk W.

(** *** Halt property for temporal's outputs *)

Definition tT_outputs_halts n W P :=
  halts n P /\ halts_sk (W⁺)%sk W.

(** *** Good behavior for external inputs *)

Definition put_good_behavior (put : resource * (option Λ) -> Λ) Rc R := 
  forall r v, (r ∈ R)%sr -> 
    (forall α β, Rc⌊r⌋%rc = Some (α,β) -> 
      (∅%vc ⋅ Rc ⊢ {Term.shift (R⁺)%sr ((Rc⁺)%rc - (R⁺)%sr) (put (r,v))} ∈ β
      )
    ) /\
    ((R⁺)%sr ⊩ put (r,v))%tm /\
    halts (R⁺)%sr (put (r,v))
.

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

(** Properties *)

(** *** [puts] properties *)

Section put_props.

Variable put : resource * (option Λ) -> Λ. 

#[export] Instance aux_eq (V: 𝐕) : Proper (eq ==> SRE.eq ==> SRE.eq) 
  (fun (k: resource) (acc : 𝐄) => (⌈k ⤆ put (k, put_aux k V) ⌉ acc)%sr).
Proof.
  intros r' r Heqr R R' HeqR; subst.
  now rewrite HeqR.
Qed.

Lemma aux_diamond  (V: 𝐕) : SRE.Diamond SRE.eq 
  (fun (k: resource) (_: Λ) (acc : 𝐄) => (⌈ k ⤆ put (k, put_aux k V) ⌉ acc)%sr).
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
  halts_sre k (puts put R V).
Proof.
  intro Hyput.
  induction R using SRE.map_induction.
  - apply halts_sre_Empty.
    now apply puts_Empty.
  - unfold SRE.Add in H0; rewrite H0 in *; clear H0.
    rewrite puts_add; auto.
    apply halts_sre_add; split; auto.
Qed.

Lemma puts_halts_1 (R : 𝐄)  (V: 𝐕) :
  (forall r v, halts (R⁺)%sr (put (r,v)))%tm ->
  halts_sre ((puts put R V)⁺)%sr (puts put R V).
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

(** *** [init_g] properties *)

#[export] Instance init_func_eq : 
  Proper (Logic.eq ==> Logic.eq ==> RE.eq ==> RE.eq) SRE.init_func.
Proof.
  intros k' k Heqk d' d Heqd V V' HeqV; subst; unfold SRE.init_func.
  now rewrite HeqV.
Qed.

Lemma init_func_diamond : SRE.Diamond RE.eq SRE.init_func.
Proof.
  unfold SRE.init_func; intros k k' d d' sr rs1 sr' Hneq Heq Heq'.
  rewrite <- Heq; rewrite <- Heq'.
  now rewrite RE.add_add_2; auto.
Qed.

#[local] Hint Resolve init_func_eq init_func_diamond RE.Equal_equiv : core.

Lemma init_g_Empty (sr: 𝐄) (V: 𝐕) :
  SRE.Empty sr -> RE.eq (SRE.init_g sr V) V.
Proof.
  intro Hemp; unfold SRE.init_g.
  rewrite SRE.fold_Empty with (eqA := RE.eq); now auto.
Qed.

Lemma init_g_add (r: resource) (v: Λ) (sr: 𝐄) (V: 𝐕) :
  (r ∉ sr)%sr ->
  RE.eq (SRE.init_g (SRE.Raw.add r v sr) V) (⌈ r ⤆ (⩽ v … ⩾)⌉ (SRE.init_g sr V))%re. 
Proof.
  unfold SRE.init_g; intro HnIn.
  rewrite SRE.fold_Add with (eqA := RE.eq); eauto.
  - unfold SRE.init_func at 1; reflexivity.
  - red; reflexivity.
Qed.

#[export] Instance init_g_proper : 
  Proper (SRE.eq ==> RE.eq ==> RE.eq) SRE.init_g.
Proof.
  intros sr sr' Heqrs V V' HeqV; unfold SRE.init_g.
  eapply SRE.fold_Proper with (eqA := RE.eq); eauto.
Qed.

Lemma init_g_find_1 (sr: 𝐄) (V: 𝐕) (r: resource) (v : 𝑣) :
  ((SRE.init_g sr V)⌊r⌋)%re = Some v -> 
  sr⌊r⌋%sr = Some (Cell.extract v) \/ V⌊r⌋%re = Some v.
Proof.
  revert r v; induction sr using SRE.map_induction; intros r v Hfi.
  - rewrite init_g_Empty in Hfi; auto.
  - unfold SRE.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_g_add in Hfi; auto.
    rewrite RE.add_o in Hfi; destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- inversion Hfi; subst; clear Hfi.
       left; rewrite SRE.add_eq_o; auto.
    -- apply IHsr1 in Hfi as [Hfi | Hfi]; auto.
       left; now rewrite SRE.add_neq_o.
Qed. 

Lemma init_g_find (sr: 𝐄) (V: 𝐕) (r: resource) (v : 𝑣) :
  ((SRE.init_g sr V)⌊r⌋)%re = Some v -> 
  (r ∈ sr)%sr \/ V⌊r⌋%re = Some v.
Proof.
  revert r v; induction sr using SRE.map_induction; intros r v Hfi.
  - rewrite init_g_Empty in Hfi; auto.
  - unfold SRE.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_g_add in Hfi; auto.
    rewrite RE.add_o in Hfi; destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- now rewrite SRE.add_in_iff; repeat left.
    -- rewrite SRE.add_in_iff.
       apply IHsr1 in Hfi as [HIn | Hfi]; auto.
Qed.

Lemma init_g_find_inp (sr: 𝐄) (V: 𝐕) (r: resource) (v : 𝑣) :
  (forall r, V⌊r⌋%re = Some v -> exists v', (v = Cell.inp v')%type) ->
  ((SRE.init_g sr V)⌊r⌋)%re = Some v -> exists v', (v = Cell.inp v')%type. 
Proof.
  revert r v; induction sr using SRE.map_induction; intros r v HV Hfi.
  - rewrite init_g_Empty in Hfi; auto.
    now apply (HV r).
  - unfold SRE.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_g_add in Hfi; auto.
    rewrite RE.add_o in Hfi; destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- inversion Hfi; subst; now exists e.
    -- apply IHsr1 in Hfi; auto.
Qed.

Lemma init_g_in_iff  (sr: 𝐄) (V: 𝐕) (r: resource) :
  (r ∈ (SRE.init_g sr V))%re <-> (r ∈ sr)%sr \/ (r ∈ V)%re.
Proof.
  revert r; induction sr using SRE.map_induction; intro r; split.
  - rewrite init_g_Empty; auto.
  - intros [HIn | HIn].
    -- destruct HIn as [v HM].
       exfalso; now apply (H r v).
    -- rewrite init_g_Empty; auto.
  - intro HIn.
    unfold SRE.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_g_add in HIn; auto.
    rewrite SRE.add_in_iff.
    apply RE.add_in_iff in HIn as [| HIn]; subst; auto.
    apply IHsr1 in HIn as [HIn | HIn]; auto.
  - unfold SRE.Add in H0; rewrite H0 in *; clear H0.
    rewrite SRE.add_in_iff.
    rewrite init_g_add; auto.
    rewrite RE.add_in_iff.
    intros [[Heq | HIn] | HIn]; subst; auto; 
    right; rewrite IHsr1; auto.
Qed.

Lemma init_g_in_unused (sr: 𝐄) (V: 𝐕) (r: resource) :
  (r ∈ sr)%sr -> REnvironment.unused r (SRE.init_g sr V).
Proof.
  revert r; induction sr using SRE.map_induction; intros r HIn.
  - exfalso; destruct HIn as [v HM]; now apply (H r v).
  - unfold SRE.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_g_add; auto; 
    apply SRE.add_in_iff in HIn as [| HIn]; subst.
    -- apply RE.unused_add_eq; now red.
    -- assert (Hneq : r <> x) by (intro; subst; contradiction).
       apply RE.unused_add_neq; auto.
Qed.

Lemma init_g_unused (r: resource) (V: 𝐕) (sr: 𝐄) :
  RE.unused r V -> RE.unused r (SRE.init_g sr V).
Proof.
  revert r; induction sr using SRE.map_induction; intros r Hunsd.
  - rewrite init_g_Empty; auto.
  - unfold SRE.Add in *; rewrite H0 in *; clear H0.
    rewrite init_g_add; auto.
    destruct (Resource.eq_dec r x) as [| Hneq]; subst.
    -- apply RE.unused_add_eq; now red.
    -- apply RE.unused_add_neq; auto.
Qed.

Lemma init_g_add_remove (r: resource) (v: Λ) (sr: 𝐄) (V: 𝐕) :
  RE.eq (SRE.init_g (SRE.Raw.add r v sr) V) 
        (SRE.init_g (SRE.Raw.add r v sr) (RE.Raw.remove r V)).
Proof.
  revert r v V; induction sr using SRE.map_induction; intros r v V.
  - rewrite init_g_add.
    -- rewrite init_g_add.
       + do 2 (rewrite init_g_Empty; auto).
         clear H sr; revert r v; induction V using RE.map_induction; intros r v.
         ++ assert (RE.eq (RE.Raw.remove r V) V).
            { 
              unfold RE.eq; rewrite RE.remove_id.
              intros [v1 HM]; now apply (H r v1).
            }
            now rewrite H0.
         ++ unfold RE.Add in H0; rewrite H0 in *; clear H0.
            destruct (Resource.eq_dec r x) as [| Hneq]; subst.
            * rewrite RE.add_shadow.
              rewrite RE.add_remove_1.
              now rewrite RE.add_shadow.
            * rewrite RE.add_add_2; auto.
              rewrite RE.remove_add_2; auto.
              symmetry.
              rewrite RE.add_add_2; auto.
              now rewrite IHV1.
       + intros [v1 HM]; now apply (H r v1).
    -- intros [v1 HM]; now apply (H r v1).
  - unfold SRE.Add in *; rewrite H0 in *; clear H0.
    destruct (Resource.eq_dec r x) as [| Hneq]; subst.
    -- rewrite SRE.add_shadow.
       now apply IHsr1.
    -- rewrite SRE.add_add_2; auto.
       rewrite init_g_add.
       + symmetry; rewrite init_g_add.
         ++ now rewrite <- IHsr1.
         ++ rewrite SRE.add_in_iff; intros [|]; subst; contradiction.
       + rewrite SRE.add_in_iff; intros [|]; subst; contradiction.
Qed.

Lemma init_g_add_1 (r: resource) (v : 𝑣) (sr: 𝐄) (V: 𝐕) :
  (r ∉ sr)%sr ->
  RE.eq (SRE.init_g sr (⌈r ⤆ v⌉ V))%re (⌈r ⤆ v⌉ (SRE.init_g sr V))%re. 
Proof.
  revert r v V; induction sr using SRE.map_induction; intros r v V HnIn.
  - now do 2 (rewrite init_g_Empty; auto).
  - unfold SRE.Add in H0; rewrite H0 in *; clear H0.
    assert (r <> x /\ (r ∉ sr1)%sr).
    { 
      split; intro; subst.
      - apply HnIn.
        rewrite SRE.add_in_iff; auto.
      - apply HnIn.
        rewrite SRE.add_in_iff; auto.
    }
    destruct H0 as [Hneq HnIn'].
    do 2 (rewrite init_g_add; auto).
    rewrite RE.add_add_2; auto.
    now rewrite IHsr1; auto.
Qed.

Lemma init_g_new_key (V: 𝐕) (t: 𝐄) : 
  ((SRE.init_g t V)⁺)%re = max (t⁺)%sr (V⁺)%re.
Proof.
  revert V.
  induction t using SRE.map_induction; intro V.
  - rewrite SRE.Ext.new_key_Empty; auto; simpl.
    rewrite init_g_Empty; auto.
  - unfold SRE.Add in *; rewrite H0 in *; clear H0.
    rewrite init_g_add_remove.
    rewrite init_g_add; auto.
    rewrite SRE.Ext.new_key_add_max; auto.
    rewrite RE.Ext.new_key_add_max.
    rewrite IHt1.
    destruct (RE.In_dec V x).
    + apply RE.new_key_in_remove_1 in i as HI.
      rewrite HI; lia.
    + apply RE.remove_id in n.
      rewrite n; lia.
Qed.

Lemma init_g_Wf (k : lvl) (V: 𝐕) (t : 𝐄) :
  (k ⊩ t)%sr /\ (k ⊩ V)%re -> (k ⊩ SRE.init_g t V)%re.
Proof.
  revert k V.
  induction t using SRE.map_induction; intros k V  [Hvt HvV].
  - rewrite init_g_Empty; auto.
  - unfold SRE.Add in H0; rewrite H0 in *; clear H0.
    apply SRE.Wf_add_notin in Hvt as [Hvx [Hve Hvt1]]; auto.
    rewrite init_g_add_remove.
    rewrite init_g_add; auto.
    apply RE.Wf_add_notin.
    -- rewrite init_g_in_iff; intros [|]; auto.
       apply RE.remove_in_iff in H0 as []; auto.
    -- do 2 (split; auto).
       apply IHt1; split; auto.
       now apply RE.Wf_remove.
Qed.

Lemma halts_sre_init_g (k : lvl) (sr: 𝐄) (V: 𝐕) :
  halts_sre k sr -> halts_re k V -> 
  halts_re k (SRE.init_g sr V).
Proof.
  induction sr using SRE.map_induction; intros Hltrs HltV.
  - now rewrite init_g_Empty.
  - unfold SRE.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_g_add; auto.
    apply halts_re_add; simpl.
    apply halts_sre_add_iff in Hltrs as [Hkte Htlrs1]; auto. 
Qed.

(** **** [init_globals] properties *)

Lemma init_globals_Empty (sr: 𝐄) :
  SRE.Empty sr -> RE.eq (SRE.init_globals sr) (∅)%re.
Proof. apply init_g_Empty. Qed.

Lemma init_globals_add (r: resource) (v: Λ) (sr: 𝐄) :
  (r ∉ sr)%sr ->
  RE.eq (SRE.init_globals (SRE.Raw.add r v sr)) 
        (⌈ r ⤆ (⩽ v … ⩾)⌉ (SRE.init_globals sr))%re. 
Proof. apply init_g_add. Qed.

#[export] Instance init_globals_eq : 
  Proper (SRE.eq ==> RE.eq) SRE.init_globals.
Proof. unfold SRE.init_globals; intros sr sr' Heqt; now rewrite Heqt. Qed.  

Lemma init_globals_find (sr: 𝐄) (r: resource) (v : 𝑣) :
  ((SRE.init_globals sr)⌊r⌋)%re = Some v -> (r ∈ sr)%sr.
Proof. 
  intros Hfi. 
  apply init_g_find in Hfi as [HIn | Hfi]; auto.
  inversion Hfi.
Qed.

Lemma init_globals_in_iff  (sr: 𝐄) (r: resource) :
  (r ∈ (SRE.init_globals sr))%re <-> (r ∈ sr)%sr.
Proof.
  split; intros HIn. 
  - apply init_g_in_iff in HIn as [HIn | HIn]; auto.
    inversion HIn; inversion H.
  - now apply init_g_in_iff; left.
Qed. 

Lemma init_globals_find_iff (sr: 𝐄) (v: Λ) (r: resource) : 
  ((SRE.init_globals sr)⌊r⌋)%re = Some (⩽v …⩾) <-> (sr⌊r⌋)%sr = Some v.
Proof.
  revert r v; induction sr using SRE.map_induction; intros r v; split; intro Hfi.
  - rewrite init_globals_Empty in Hfi; auto. 
    inversion Hfi.
  - apply SRE.Empty_eq in H.
    rewrite H in Hfi.
    inversion Hfi.
  - unfold SRE.Add in *; rewrite H0 in *; clear H0.
    rewrite init_globals_add in Hfi; auto.
    destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- rewrite RE.add_eq_o in Hfi; auto.
       inversion Hfi; subst; clear Hfi.
       now rewrite SRE.add_eq_o.
    -- rewrite RE.add_neq_o in Hfi; auto.
       rewrite SRE.add_neq_o; auto.
       now rewrite <- IHsr1.
  - unfold SRE.Add in *; rewrite H0 in *; clear H0.
    rewrite init_globals_add; auto.
    destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- rewrite SRE.add_eq_o in Hfi; auto.
       inversion Hfi; subst; clear Hfi.
       now rewrite RE.add_eq_o.
    -- rewrite SRE.add_neq_o in Hfi; auto.
       rewrite RE.add_neq_o; auto.
       now rewrite IHsr1.
Qed.

Lemma init_globals_in_unused (sr: 𝐄) (r: resource) :
  (r ∈ sr)%sr -> RE.unused r (SRE.init_globals sr).
Proof. apply init_g_in_unused. Qed.

Lemma init_globals_find_e (sr: 𝐄) (v : 𝑣) (r: resource) : 
  ((SRE.init_globals sr)⌊r⌋)%re = Some v -> exists v', (v = ⩽ v' … ⩾)%type.
Proof.
  revert r v; induction sr using SRE.map_induction; intros r v Hfi.
  - rewrite init_globals_Empty in Hfi; auto.
    inversion Hfi.
  - unfold SRE.Add in *; rewrite H0 in *; clear H0.
    rewrite init_globals_add in Hfi; auto.
    destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- rewrite RE.add_eq_o in Hfi; auto.
       inversion Hfi; subst; clear Hfi.
       now exists e.
    -- rewrite RE.add_neq_o in Hfi; auto.
       now apply (IHsr1 r v).
Qed.

Lemma init_globals_Wf (k : lvl) (sr: 𝐄) :
  (k ⊩ sr)%sr <-> (k ⊩ SRE.init_globals sr)%re.
Proof.
  induction sr using SRE.map_induction; split; intro Hvt.
  - rewrite init_globals_Empty; auto.
  - now apply SRE.Wf_Empty.
  - unfold SRE.Add in H0; rewrite H0 in *; clear H0.
    apply SRE.Wf_add_notin in Hvt as [Hvx [Hve Hvt]]; auto.
    rewrite init_globals_add; auto.
    apply RE.Wf_add_notin.
    -- now rewrite init_globals_in_iff.
    -- repeat split; auto.
       now rewrite <- IHsr1.
  - unfold SRE.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_globals_add in Hvt; auto.
    apply RE.Wf_add_notin in Hvt as [Hvx [Hve Hvt]]; auto.
    -- apply SRE.Wf_add_notin; auto.
       repeat split; auto.
       now rewrite IHsr1.
    -- now rewrite init_globals_in_iff.
Qed.

Lemma init_globals_shift (m n : lvl) (sr: 𝐄) :
  RE.eq (SRE.init_globals ([⧐ m – n] sr)%sr) 
        ([⧐ m – n] (SRE.init_globals sr))%re.
Proof.
  induction sr using SRE.map_induction.
  - rewrite SRE.shift_Empty; auto.
    rewrite init_globals_Empty; auto.
    rewrite RE.shift_Empty; try reflexivity.
    apply RE.empty_1.
  - unfold SRE.Add in *; rewrite H0; clear H0.
    rewrite SRE.shift_add.
    rewrite init_globals_add.
    -- rewrite init_globals_add; auto.
       rewrite RE.shift_add; simpl.
       now rewrite IHsr1.
    -- now rewrite <- SRE.shift_in_iff.
Qed.

Lemma init_globals_new_key (sr: 𝐄) : ((SRE.init_globals sr)⁺)%re = (sr⁺)%sr.
Proof.
  induction sr using SRE.map_induction.
  - rewrite SRE.Ext.new_key_Empty; auto.
    rewrite init_globals_Empty; auto.
  - unfold SRE.Add in *; rewrite H0 in *; clear H0.
    rewrite init_globals_add; auto.
    rewrite SRE.Ext.new_key_add_max.
    rewrite RE.Ext.new_key_add_max; lia.
Qed.

Lemma halts_sre_init_globals (k : lvl) (sr: 𝐄) :
  halts_sre k sr -> halts_re k (SRE.init_globals sr).
Proof.
  intro Hlt; apply halts_sre_init_g; auto.
  intros r d Hfi; inversion Hfi.
Qed.


(** *** [init_input_env] property *)

Lemma init_input_env_in_iff (R: 𝐄) (W: 𝐖) (r: resource) : 
  (In r (ST.keys W)) \/ (r ∈ R)%sr <-> r ∈ init_input_env R W.
Proof.
  unfold init_input_env.
  rewrite ST.init_locals_in_iff.
  rewrite init_globals_in_iff.
  now rewrite SRE.shift_in_new_key.
Qed.

Lemma init_input_env_new_key (R: 𝐄) (W: 𝐖) :
  (init_input_env R W)⁺ = max (R⁺)%sr (W⁺)%sk.
Proof.
  unfold init_input_env.
  rewrite ST.init_locals_new_key.
  replace (Nat.max (R⁺)%sr (W⁺)%sk) with (Nat.max (W ⁺)%sk (R⁺)%sr) by lia.
  f_equal.
  rewrite init_globals_new_key.
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
       apply init_globals_Wf.
       now rewrite SRE.shift_zero_refl.
  - assert (p :: W <> []) by (intro Hc; inversion Hc).
    apply HnEmp in H. 
    remember (p :: W) as W'.
    rewrite max_r by lia; split; auto.
    apply init_globals_Wf.
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
  now apply init_globals_find_e in Hfi.
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
  rewrite init_globals_in_iff.
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
  apply init_globals_find_iff in H0.
  apply SRE.shift_find_e_1 in H0 as HI.
  destruct HI as [[r' Heq] [v' Heq']]; subst.
  exists v'; split; auto.
  rewrite <- SRE.shift_find_iff in H0.
  assert (HIn : (r' ∈ R)%sr).
  { exists v'; now apply SRE.find_2. }
  apply SRE.Ext.new_key_in in HIn.
  rewrite Resource.shift_wf_refl; auto.
Qed. 

Lemma init_input_env_unused r R W :
  (R⁺ ⊩ R)%sr ->
  (r ∈ init_input_env R W)%re -> 
  RE.unused r (init_input_env R W).
Proof.
  intros Hwf HIn.
  rewrite <- init_input_env_in_iff in HIn.
  destruct HIn as [HIn|HIn];
  unfold init_input_env.
  - now apply ST.init_locals_unused.
  - destruct (List.In_dec (Resource.eq_dec) r (ST.keys W)).
    -- now apply ST.init_locals_unused.
    -- apply ST.init_locals_unused_not; auto.
       apply init_globals_in_unused.
       now rewrite SRE.shift_in_new_key.
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
  - intros [HeqDom [HDisj [HvRc [HvS [HvW [Hwt [Hwt' [HND HnEmp]]]]]]]].
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
    split; auto.
    { 
      rewrite <- HeqRe, <- HeqS; auto. 
    }
  - intros [HeqDom [HDisj [HvRc [HvS [HvW [Hwt [Hwt' [HND HnEmp]]]]]]]].
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
    split; auto.
    { 
      intros r r' ty ty' v Hfi HIn.
      rewrite HeqRe in *.
      eapply Hwt'; eauto.
    }
    split; auto. 
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
     apply init_globals_find_iff in HfiV.
     rewrite SRE.shift_zero_refl in HfiV.
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
          ++ apply ST.keys_In in HIn as HI.
             destruct HI as [HInr HInr'].
             assert (r' ∈ Rc)%rc.
             { rewrite HeqDom; auto. }
             destruct H1 as [[A B] HfiRc'].
             apply RC.find_1 in HfiRc'.  
             apply Hwt' with (A := ty) (B := ty') 
                             (C := A) (D := B) in HIn as [Hwt1 Heq]; auto.  
          ++ subst v.
             apply ST.keys_In in HIn as HI.
             destruct HI as [HInr HInr'].
             assert (r' ∈ Rc)%rc.
             { rewrite HeqDom; auto. }
             destruct H1 as [[A B] HfiRc'].
             apply RC.find_1 in HfiRc'.  
             apply Hwt' with (A := A) (B := B) 
                              (C := ty) (D := ty') in HIn as [Hwt1 [Heq []]]; auto.
             subst; constructor.
  }
Qed.

Lemma WF_ec_to_WF_tt_1 put (Rc : ℜ) (R R' : 𝐄) (W W' W1: 𝐖) V :
  (R' = puts put R V)%sr ->
  (W' = ST.update_locals (([⧐ W⁺ – (V⁺)%re - W⁺] W) ++ W1) V)%sk ->
  (forall r : resource, (r ∈ Rc)%rc <-> r ∈ V) ->
  (forall r : resource, r ∈ RE.diff V (init_input_env R W) <-> (r ∈ ST.keys W1)%sk) ->
  (forall r: resource, r ∈ init_input_env R W -> r ∈ V) ->
  (forall r : resource, (r ∈ Rc)%rc <-> (r ∈ ST.keys W')%sk \/ (r ∈ R')%sr).
Proof.
  intros HeqR HeqW HeqDom HeqDom' HSub r. 
  rewrite HeqR, HeqW.
  rewrite ST.update_locals_keys_In.
  rewrite <- puts_in_iff.
  rewrite ST.keys_in_app.
  rewrite ST.keys_in_shift_new_key.
  rewrite HeqDom.
  split.
  - intro HInV.
    specialize (HeqDom' r).
    rewrite RE.diff_in_iff in HeqDom'.
    rewrite <- init_input_env_in_iff in HeqDom'.
    destruct (List.In_dec Resource.eq_dec r (ST.keys W)) as [|HnInW]; auto.
    destruct (SRE.In_dec R r) as [|HnInR]; auto.
    left; right.
    rewrite <- HeqDom'; split; auto.
    now intros [|].
  - intros [[HInW|HInWnew]|HInR].
    -- apply HSub.
      rewrite <- init_input_env_in_iff; auto.
    -- rewrite <- HeqDom' in HInWnew.
      rewrite RE.diff_in_iff in HInWnew.
      now destruct HInWnew.
    -- apply HSub.
      rewrite <- init_input_env_in_iff; auto.
Qed.

Lemma WF_ec_to_WF_tt_2 put (Rc : ℜ) (R R' : 𝐄) (W W' W1: 𝐖) V :
  (R' = puts put R V)%sr ->
  (W' = ST.update_locals (([⧐ W⁺ – (V⁺)%re - W⁺] W) ++ W1) V)%sk ->
  (forall r : resource, r ∈ RE.diff V (init_input_env R W) <-> (r ∈ ST.keys W1)%sk) ->
  (forall r : resource, (r ∈ ST.keys W)%sk -> (r ∉ R)%sr) ->
  (forall r : resource, (r ∈ ST.keys W')%sk -> (r ∉ R')%sr).
Proof.
  intros HeqR HeqW HeqDom Hdiff r. 
  rewrite HeqW, HeqR.
  rewrite ST.update_locals_keys_In.
  rewrite <- puts_in_iff.
  rewrite ST.keys_in_app.
  rewrite ST.keys_in_shift_new_key.
  intros [HInW | HInWnew]; auto.
  rewrite <- HeqDom in HInWnew.
  rewrite RE.diff_in_iff in HInWnew.
  destruct HInWnew as [_ HIninp].
  rewrite <- init_input_env_in_iff in HIninp.
  intro c; apply HIninp; auto.
Qed.

Lemma WF_ec_to_WF_tt_3 (Rc : ℜ) (R : 𝐄) (W W' W1: 𝐖) V :
  (W⁺ ⊩ W)%sk ->
  V⁺ ⊩ V ->
  ((V⁺)%re ⊩ W1)%sk ->
  (init_input_env R W)⁺ <= V⁺ ->
  (W <> [] -> (W ⁺)%sk = (Rc ⁺)%rc /\ (W ⁺)%sk > (R ⁺)%sr) ->
  (W1 <> [] -> V⁺ = (W1⁺)%sk /\ (W1⁺)%sk > (init_input_env R W)⁺) ->
  (forall r: resource, r ∈ RE.diff V (init_input_env R W) <-> (r ∈ ST.keys W1)%sk) ->
  (W' = ST.update_locals (([⧐ W⁺ – (V⁺)%re - W⁺] W) ++ W1) V)%sk ->
  (W' ⁺ ⊩ W')%sk.
Proof.
  intros HwfW HwfV HwfW1 HleV HnEmp HnEmp' HeqDom HeqW.
  destruct W, W1.
  - simpl in *.
    rewrite HeqW.
    apply ST.Wf_nil.
  - remember (p :: W1) as W1'; clear HnEmp.
    simpl in *.
    rewrite HeqW.
    destruct HnEmp'.
    -- subst; intro c; inversion c.
    -- rewrite ST.update_locals_new_key.
        apply ST.update_locals_Wf; split;
        rewrite <- H; auto.
  - remember (p :: W) as W1; clear HnEmp'.
    simpl in *.
    rewrite HeqW.
    rewrite app_nil_r in *.
    assert (W1 <> []) by (subst; intro c; inversion c).
    apply HnEmp in H.
    assert (V⁺ <= (init_input_env R W1)⁺).
    { 
      apply RE.new_key_incl.
      now apply RE.diff_in_false.
    }
    rewrite init_input_env_new_key in *.
    rewrite max_r in * by lia.
    assert (V⁺ = W1⁺%sk) by lia.
    rewrite H1.
    rewrite ST.update_locals_new_key.
    replace (W1 ⁺ - W1 ⁺)%sk with 0 by lia.
    rewrite ST.shift_zero_refl.
    apply ST.update_locals_Wf; split; auto; rewrite <- H1; auto.
  - remember (p :: W) as W2.
    remember (p0 :: W1) as W1'.
    destruct HnEmp'.
    { subst; intro c; inversion c. }
    assert (W2 <> []) by (subst; intro c; inversion c).
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
Qed.

Lemma WF_ec_to_WF_tt_4 put (Rc Rc' : ℜ) (R R' : 𝐄) (W W' W1: 𝐖) V :
  put_good_behavior put Rc R ->
  (R' = puts put R V)%sr ->
  (W' = ST.update_locals (([⧐ W⁺ – (V⁺)%re - W⁺] W) ++ W1) V)%sk ->
  (V⁺) = max (Rc⁺)%rc (W1⁺)%sk ->
  (Rc⁺ ⊩ Rc)%rc ->
  (Rc ⊆ Rc')%rc ->
  (forall r, (r ∈ Rc)%rc <-> (r ∈ init_input_env R W)) ->
  (forall r, (r ∈ Rc')%rc <-> (r ∈ V)) ->
  forall (r : resource) (A : πΤ) (v : Λ),
  (Rc' ⌊ r ⌋)%rc = Some A ->
  (R' ⌊ r ⌋)%sr = Some v -> 
  ∅%vc ⋅ Rc' ⊢ [⧐{(R' ⁺)%sr} – {Init.Nat.max (R' ⁺)%sr (W' ⁺)%sk - (R' ⁺)%sr}] v ∈ {snd A}.
Proof.
  intros Hpwb HeqR HeqW HnewV HwfRc HsubRc HeqDom HeqDom' 
         r [A B] v HfiRc' HfiR'; simpl.
  rewrite HeqR in HfiR'.
  apply puts_find in HfiR' as HI.
  destruct HI as [v' ]; subst.
  assert (HInR: (r ∈ R)%sr).
  { 
    rewrite (puts_in_iff put R V).
    exists (put (r, v')).
    now apply SRE.find_2. 
  }
  apply (Hpwb r v') in HInR as Hwt'.
  assert (HInRc: (r ∈ Rc)%rc).
  { 
    now rewrite HeqDom, <- init_input_env_in_iff; auto. 
  }
  destruct HInRc as [[C D] HfiRc].
  apply RC.find_1 in HfiRc.
  apply RC.Submap_find with (m' := Rc') in HfiRc as HI; auto.
  rewrite HfiRc' in HI; inversion HI; subst; clear HI.
  destruct Hwt' as [Hwt _].
  apply Hwt in HfiRc; auto.
  apply (weakening_ℜ _ _ Rc') in HfiRc; auto.
  rewrite Term.shift_unfold_1 in HfiRc; auto.
  - rewrite HeqR.
    rewrite <- (puts_new_key put _ V).
    rewrite HeqW.
    rewrite ST.update_locals_new_key.
    rewrite ST.new_key_app.
    rewrite ST.new_key_shift_refl; auto.
    apply RE.eqDom_new in HeqDom' as Hnew'.
    rewrite Hnew', HnewV in HfiRc.
    apply RE.eqDom_new in HeqDom as Hnew.
    rewrite Hnew, init_input_env_new_key in HfiRc.
    now rewrite Nat.max_assoc.
  - apply RE.eqDom_new in HeqDom as Hnew.
    rewrite init_input_env_new_key in Hnew; lia.
  - now apply RC.Ext.new_key_Submap.  
Qed.

Lemma WF_ec_to_WF_tt_6 put (Rc Rc' : ℜ) (R R' : 𝐄) (W W' W1: 𝐖) V :
  (init_input_env R W)⁺ <= V⁺ ->
  (Rc'⁺)%rc = V⁺ ->
  (W <> [] -> (W ⁺)%sk = (Rc⁺)%rc /\ (W⁺)%sk > (R⁺)%sr) ->
  (W1 <> [] -> V⁺ = (W1⁺)%sk /\ (W1⁺)%sk > (init_input_env R W)⁺) ->
  (forall r: resource, r ∈ RE.diff V (init_input_env R W) <-> (r ∈ ST.keys W1)%sk) ->
  (R' = puts put R V)%sr ->
  (W' = ST.update_locals (([⧐ W⁺ – (V⁺)%re - W⁺] W) ++ W1) V)%sk ->
  W' <> [] -> (W'⁺)%sk = (Rc'⁺)%rc /\ (W'⁺)%sk > (R'⁺)%sr.
Proof.
  intros HleV Hnew HnEmp HnEmp' HeqDom HeqR HeqW.
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
    destruct W1.
    -- simpl in *.
        rewrite max_l by lia.
        assert (V⁺ <= (init_input_env R W)⁺).
        { 
        apply RE.new_key_incl.
        now apply RE.diff_in_false. 
        }
        assert (V⁺ = (init_input_env R W)⁺) by lia.
        rewrite Hnew, H0.
        rewrite init_input_env_new_key; lia.
    -- remember (p :: W1) as W1'.
        destruct HnEmp'.
        + subst; intro c; inversion c.
        + rewrite init_input_env_new_key in H0.
          now rewrite max_r,Hnew by lia.
  - apply HnEmp' in Hnnil as [Heq Hle']; rewrite <- Heq in *.
    rewrite init_input_env_new_key in Hle'.
    rewrite Hnew.
    split; lia.
Qed.

Lemma WF_ec_to_WF_tt put (Rc Rc' : ℜ) (R R' : 𝐄) (W W' W1: 𝐖) V :
  put_good_behavior put Rc R ->
  WFₜₜ(Rc, R, W) ->
  WF(Rc',V) ->
  (Rc ⊆ Rc')%rc ->
  NoDup (ST.keys W1) ->
  ((V⁺)%re ⊩ W1)%sk ->
  (V⁺) = max (Rc⁺)%rc (W1⁺)%sk ->
  (W1 <> [] -> V⁺ = (W1⁺)%sk /\ (W1⁺)%sk > (init_input_env R W)⁺) ->
  (forall r: resource, r ∈ RE.diff V (init_input_env R W) <-> (r ∈ ST.keys W1)%sk) ->
  (forall r: resource, r ∈ init_input_env R W -> r ∈ V) ->
  (forall (r r' : resource) (v : Λ),
      ((r, r', v) ∈ W1)%sk -> exists A : Τ, ∅%vc ⋅ Rc' ⊢ v ∈ A /\
      (Rc' ⌊ r ⌋)%rc = Some (<[ 𝟙 ]>, A) /\ (Rc' ⌊ r' ⌋)%rc = Some (A, <[ 𝟙 ]>)) ->
  (R' = puts put R V)%sr ->
  (W' = ST.update_locals (([⧐ W⁺ – (V⁺)%re - W⁺] W) ++ W1) V)%sk ->
  WFₜₜ(Rc', R', W').
Proof.
  intros Hpwb HWF HWF' Hsub HND' HwfW1 Heq HnEmp' HeqDom HIn HwW HeqR HeqW.
  assert (HWF'': WFₜₜ( Rc, R, W)) by assumption.
  destruct HWF'' as [HeqDom' [Hdiff [HwfRc [HwfR [HwfW [HwtR 
                        [HwtW [HND HnEmp]]]]]]]].
  assert (HWF'': WF(Rc', V)) by assumption.
  destruct HWF'' as [HeqDom'' [HwfRc' [HwfV HwtV]]].
  
  (* clean *)

  move HwfRc before HWF'; move HwfR before HwfRc; move HwfW before HwfR;
  move HwfRc' before HwfRc; move HwfV before HwfW; move HeqDom' before HeqDom;
  move HeqDom'' before HeqDom'; move HND before HwfV; move HnEmp before HND;
  move HeqR after Hpwb; move HeqW before HeqR; unfold RE.eqDom in *;
  move HnEmp' before HnEmp.

  (* clean *)

  split. 
  { now apply (WF_ec_to_WF_tt_1 put _ R _ W _ W1 V). }
  split. 
  { now apply (WF_ec_to_WF_tt_2 put Rc R _ W _ W1 V). }
  do 2 (split; auto). 
  {
    rewrite HeqR.
    rewrite <- puts_new_key.
    apply puts_Wf; auto.
    intros. 
    destruct (Hpwb r v); auto.
    now destruct H1.
  } 
  split. 
  { 
    apply (WF_ec_to_WF_tt_3 Rc R W _ W1 V); auto.
    rewrite Heq.
    rewrite (WF_tt_new _ R W); auto.
    rewrite init_input_env_new_key; lia.
  }
  split. 
  { 
    apply (WF_ec_to_WF_tt_4 put Rc _ R _ W _ W1 V); auto.
    intro r; now rewrite <- init_input_env_in_iff.
  }
  split. 
  {
    clear Hpwb HeqR HwfR.
    intros r r' A B C D v HInW' Hfi Hfi'.
    rewrite HeqW in HInW'.
    apply ST.update_locals_In in HInW' as [[HInW' Hnfi]|[v'[HInW' HfiVout]]].
    - apply List.in_app_or in HInW' as [HInW|HInWnew].
      -- apply ST.shift_in_e in HInW as [v' [Heq' HInW]].
         destruct v' as [[rr rw] v']; simpl in Heq'; inversion Heq'; subst; clear Heq'.
         simpl in HInW.
         rewrite <- ST.shift_in_iff in HInW.
         assert (rr ∈ Rc)%rc.
         { 
          rewrite HeqDom'.
          left.
          now apply ST.keys_In in HInW as []. 
         }
         destruct H as [[A' B'] HfiRc]; apply RC.find_1 in HfiRc.
         assert (rw ∈ Rc)%rc.
         { 
          rewrite HeqDom'.
          left.
          now apply ST.keys_In in HInW as []. 
         }
         destruct H as [[C' D'] HfiRc']; apply RC.find_1 in HfiRc'.
         apply (ST.Wf_in (W⁺)%sk) in HInW as HI; auto.
         destruct HI as [Hwfrr [Hwfrw _]].
         rewrite Resource.shift_wf_refl in *; auto.
         apply (RC.Submap_find _ _ _ Rc') in HfiRc as HI; auto.
         rewrite Hfi in HI; inversion HI; subst; clear HI.
         apply (RC.Submap_find _ _ _ Rc') in HfiRc' as HI; auto.
         rewrite Hfi' in HI; inversion HI; subst; clear HI.
         apply (HwtW _ _ A' B' C' D') in HInW as HI; auto.
         destruct HI as [Hwt [Heq' []]]; subst.
         split.
         + rewrite <- (WF_ec_new Rc' V); auto.
           apply (weakening_ℜ _ _ Rc') in Hwt; auto.
           destruct HnEmp.
           ++ intro; subst; inversion HInW.
           ++ now rewrite H.
         + repeat split; auto.
      -- apply HwW in HInWnew as [τ [Hwtv [HfiRc1 HfiRc1']]].
          rewrite Hfi in HfiRc1.
          inversion HfiRc1; subst; clear HfiRc1.
          rewrite Hfi' in HfiRc1'.
          inversion HfiRc1'; subst; clear HfiRc1'.
          split; auto.
    - apply List.in_app_or in HInW' as [HInW|HInWnew].
      -- apply ST.shift_in_e in HInW as [v1 [Heq' HInW]].
         destruct v1 as [[rr rw] v1]; simpl in Heq'; inversion Heq'; subst; clear Heq'.
         simpl in HInW.
         rewrite <- ST.shift_in_iff in HInW.
         assert (rw ∈ Rc)%rc.
         { 
          rewrite HeqDom'.
          left.
          now apply ST.keys_In in HInW as []. 
         }
         destruct H as [[C' D' ] HfiRc]; apply RC.find_1 in HfiRc.
         apply (ST.Wf_in (W⁺)%sk) in HInW as HI; auto.
         destruct HI as [Hwfrr [Hwfrw _]].
         rewrite Resource.shift_wf_refl in *; auto.
          assert (rr ∈ Rc)%rc.
         { 
          rewrite HeqDom'.
          left.
          now apply ST.keys_In in HInW as []. 
         }
         destruct H as [[A' B'] HfiRc1]; apply RC.find_1 in HfiRc1.
         apply (RC.Submap_find _ _ _ Rc') in HfiRc as HfiRc'; auto.
         apply (RC.Submap_find _ _ _ Rc') in HfiRc1 as HfiRc1'; auto.
         rewrite Hfi in HfiRc1';
         rewrite Hfi' in HfiRc'.
         inversion HfiRc'; inversion HfiRc1'; subst; clear HfiRc' HfiRc1'.
         apply (HwtV _ C' D') in HfiVout; auto.
         apply (HwtW _ _ A' B' C' D') in HInW; auto.
         destruct HInW as [_ [Heq' []]]; subst.
         split; auto.
      -- apply HwW in HInWnew as [τ [Hwtv [HfiRc1 HfiRc1']]].
          rewrite Hfi in HfiRc1.
          inversion HfiRc1; subst; clear HfiRc1.
          rewrite Hfi' in HfiRc1'.
          inversion HfiRc1'; clear HfiRc1'; subst.
          apply HwtV with (v := (Cell.out v)) in Hfi'; auto.
  } 
  split.
  { 
    rewrite HeqW.
    apply ST.update_locals_NoDup_keys.
    apply ST.NoDup_keys_app; auto.
    - now apply ST.NoDup_keys_shift.
    - intro r.
      rewrite <- HeqDom.
      rewrite RE.diff_in_iff; intros [HInVout HIninp].
      rewrite <- init_input_env_in_iff in HIninp.
      rewrite ST.keys_in_shift_new_key.
      intro c; apply HIninp; auto.
  }
  { 
    apply (WF_ec_to_WF_tt_6 put Rc _ R _ W _ W1 V); auto.
    - rewrite Heq, init_input_env_new_key.
      rewrite (WF_tt_new Rc R W); auto; lia. 
    - now apply (WF_ec_new Rc' V).
  }
Qed.

(** *** [tT_inputs_halts] properties *)

Lemma tT_inp_to_fT_inp Rc R W P :
  (Rc ⁺)%rc = Init.Nat.max (R ⁺)%sr (W ⁺)%sk ->
  (W <> [] -> (W⁺)%sk > (R⁺)%sr) ->
  tT_inputs_halts (Rc⁺)%rc R W P ->
  fT_inputs_halts (Rc⁺)%rc (init_input_env R W) <[ unit ]> P.
Proof.
  intros Heq HnEmp [HltP [HltR HltW]]; split.
  - unfold init_input_env.
    rewrite Heq.
    apply halts_sk_init_locals.
    -- destruct W eqn:HeqW'.
       + constructor.
       + rewrite <- HeqW'.
         assert (p :: t <> []) by (intro Hc; inversion Hc).
         apply HnEmp in H.
         rewrite <- HeqW' in *.
         now rewrite max_r by lia. 
    -- apply halts_sre_init_globals.
       apply halts_sre_weakening; auto; lia.
  - split; auto.
    exists <[unit]>; split; auto.
    reflexivity.
Qed.

(** *** [tT_outputs_halts] properties *)


Lemma fT_out_to_tT_out R Rc Rc1 V W1 W W' _t P P' :
  (Rc1⁺)%rc = V⁺ ->
  (W  <> [] -> (W⁺)%sk > (R⁺)%sr) ->
  (W1 <> [] -> V⁺ = (W1⁺)%sk /\ (W1⁺)%sk > (init_input_env R W)⁺) ->
  (init_input_env R W)⁺ <= V⁺ ->
  tT_inputs_halts (Rc ⁺)%rc R W P ->
  (forall r : resource, r ∈ RE.diff V (init_input_env R W) <-> (r ∈ ST.keys W1)%sk) ->
  (W' = ST.update_locals (([⧐ W⁺ – (V⁺)%re - W⁺] W) ++ W1) V)%sk ->
  fT_outputs_halts (Rc1⁺)%rc V W1 _t P' ->
  tT_outputs_halts (Rc1⁺)%rc W' P'.
Proof.
  intros Hnew HnEmp HnEmp' HleV Hinplt HeqDom HeqW Houtlt. 
  split; auto.
  - now destruct Houtlt as [_ [_ []]].
  - destruct W, W1.
    -- simpl in *; rewrite HeqW.
       apply halts_sk_nil.
    -- remember (p :: W1) as W1'.
       rewrite HeqW in *; simpl in *.
       destruct HnEmp'.
       + rewrite HeqW1'; intro Hc; inversion Hc.
       + rewrite ST.update_locals_new_key.
         rewrite <- H, <- Hnew.
         destruct Houtlt as [HoutV [HoutW ]].
         now apply halts_sk_update_locals.
    -- remember (p :: W) as W1.
       clear HnEmp'.
       rewrite HeqW in *; simpl in *.
       rewrite app_nil_r in *.
       assert (V⁺ <= (init_input_env R W1)⁺).
       { 
         apply RE.new_key_incl.
         now apply RE.diff_in_false.
       }
       assert (W1 <> []) by (subst; intro c; inversion c).
       apply HnEmp in H0.
       rewrite init_input_env_new_key in *.
       rewrite max_r in * by lia.
       replace ((V⁺)%re - W1⁺)%sk with 0 by lia.
       rewrite ST.update_locals_new_key.
       rewrite ST.shift_zero_refl.
       destruct Houtlt as [HoutV _].
       destruct Hinplt as [_ [HltR HltW1]].
       apply halts_sk_update_locals; auto.
       assert ((W1⁺)%sk = V⁺) by lia.
       now rewrite H1, <- Hnew.
    -- remember (p0 :: W1) as W1'.
       remember (p :: W) as W2.
       assert (W2 <> []).
       { subst; intro c; inversion c. }
       apply HnEmp in H; clear HnEmp.
       rewrite init_input_env_new_key in *.
       rewrite max_r in * by lia.
       assert (W1' <> []).
       { subst; intro c; inversion c. }
       apply HnEmp' in H0; clear HnEmp'.
       destruct H0 as [Heq Hlt].
       rewrite HeqW.
       rewrite ST.update_locals_new_key.
       rewrite ST.new_key_app.
       rewrite ST.new_key_shift_refl; auto.
       rewrite max_r by lia.
       destruct Houtlt as [HoutV [HoutW]].
       destruct Hinplt as [_ [HltR HltW1]].
       apply halts_sk_update_locals; auto.
       + now rewrite <- Heq, <- Hnew.
       + apply halts_sk_app; split.
         ++ rewrite Heq.
             apply halts_sk_weakening; auto; lia.
         ++ now rewrite <- Heq, <- Hnew.
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
       destruct HnEmp' as [Heq [Hnew Hlt]].
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



Theorem temporal_preserves_typing (put : resource * (option Λ) -> Λ)
                                  (Rc : ℜ) (R R': 𝐄) 
                                  (W W' : 𝐖) (P P' : Λ) (Rs : resources) :

       tT_inputs_halts (Rc⁺)%rc R W P -> halts_arr Rc P ->
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
    destruct HWF as [_ [_ [_ [_ [_ [_ [_ [_ ]]]]]]]].
    intro HI; apply H in HI as []; assumption.
  }
  apply tT_inp_to_fT_inp in Hinplt as Hinplt'; auto.
  assert (HTT': # put ⟦ R; W; P ⟧ ⟾ ⟦ R'; W'; P' ⟧) by assumption.
  destruct HTT as [Vout [Wnew [_tv [HfT [HeqR HeqW]]]]].
  apply functional_W_props in HfT as HI.
  destruct HI as [HND [HeqDom [HeqVout HnEmp']]].

  apply functional_preserves_keys in HfT as HI.
  destruct HI as [HIn Hle].

  apply functional_preserves_Wf in HfT as HI; auto.
  - destruct HI as [HwfVout [_ [HwfP' [HwfWnew HleVout]]]].

    apply Functional_Transition.functional_preserves_typing 
    with (Rc := Rc) (A := <[𝟙]>) (B := <[𝟙]>) (R := Rs)
    in HfT; auto.
    destruct HfT as [Hunsd [Hunsd' [Rc1 [Rs' [HsubRc [HsubRs 
                      [Hout [Harrlt' [Hwt [Hwt' [HWF'' [HwW [Hdisj Husd]]]]]]]]]]]]]. 
    exists Rc1, Rs'.
    do 3 (split; auto).
    { 
      apply (WF_ec_to_WF_tt put Rc _ R _ W _ Wnew Vout); auto. 
      rewrite (WF_tt_new Rc R W); auto.
      rewrite init_input_env_new_key in *; auto.
    } 
    do 2 (split; auto).
    { 
      apply (fT_out_to_tT_out R Rc _ Vout Wnew W _ _tv P); auto.
      now apply WF_ec_new.
    }
  - destruct HWF as [_ [_ [HwfRc [HwfR []]]]]. 
    apply init_input_env_Wf; auto.
  - constructor.
  - rewrite <- (WF_ec_new Rc); auto.
    apply well_typed_implies_Wf in HwtP as []; auto.
    now destruct HWF as [_ [_ []]].
Qed.

(** ---- *)


(** ** Progress - Temporal *)

Theorem temporal_reactivity (put : resource * (option Λ) -> Λ) 
                            (Rc : ℜ) (R : 𝐄) (W: 𝐖) (P : Λ) (Rs : resources) :

        tT_inputs_halts (Rc⁺)%rc R W P -> 
        halts_arr Rc P ->
        WFₜₜ(Rc,R,W) -> 
        put_good_behavior put Rc R ->
          
        ∅%vc ⋅ Rc ⊢ P ∈ (𝟙 ⟿ 𝟙 ∣ Rs) ->
  (* --------------------------------------------------- *)
       exists (P': Λ) (R' : 𝐄) (W': 𝐖) (Rc1: ℜ), 
       #put ⟦ R ; W ; P ⟧ ⟾ ⟦ R' ; W' ; P' ⟧ /\
       WFₜₜ(Rc1,R',W') /\
       tT_outputs_halts (Rc1⁺)%rc W' P' /\ 
       halts_arr Rc1 P'.
Proof.
  intros HIOlt Harrlt Hwf Hbh Hwt.
  apply WF_tt_to_WF_ec in Hwf as Hwf'.
  assert (Hinplt: fT_inputs_halts (Rc ⁺)%rc (init_input_env R W) <[ unit ]> P).
  {
    apply tT_inp_to_fT_inp; auto.
    - now apply WF_tt_new.
    - destruct Hwf as [_ [_ [_ [_ [_ [_ [_ []]]]]]]].
      intro.
      now apply H0 in H1 as [].
  }
  assert (HIn: forall r : resource, (r ∈ Rs)%s -> RE.unused r (init_input_env R W)).
  {
   intros r HIn.
   apply init_input_env_unused.
   - now destruct Hwf as [_ [_ [_ [H _]]]].
   - destruct Hwf as [HInRc [_ [HwfRc _]]].
     rewrite <- init_input_env_in_iff.
     rewrite <- HInRc.
     destruct HIOlt as [[P' [HmeT HvP]] _].
     eapply multi_preserves_typing in Hwt; eauto.
     apply typing_Re_R with (r := r) in Hwt; auto.
  }
  apply (progress_of_functional Rc  
                                (init_input_env R W)
                                <[unit]>
                                P
                                <[𝟙]>
                                <[𝟙]>) in Hwt as IH; eauto.
  destruct IH as [V1 [tv' [P' [W' [HfT Houtlt]]]]].

  apply functional_W_props in HfT as IH.
  destruct IH as [HND [HeqDom [HeqV1 HnEmp]]].

  apply functional_preserves_keys in HfT as IH.
  destruct IH as [Hincl Hle].

  assert (Hwfinit: init_input_env R W⁺ ⊩ init_input_env R W).
  {
   apply init_input_env_Wf.
   - destruct Hwf as [_ [_ [_ [_ [_ [_ [_ [_ ]]]]]]]].
     now eapply H.
   - now destruct Hwf as [_ [_ [_ [HwfR _]]]].
   - now destruct Hwf as [_ [_ [_ [_ [HwfW _]]]]].
  }
  assert (Hwfu: (init_input_env R W ⁺ ⊩ <[ unit ]>)%tm) by constructor.
  assert (HwfP: (init_input_env R W ⁺ ⊩ P)%tm).
  { 
    apply well_typed_implies_Wf in Hwt as []; auto.
    - rewrite <- (WF_ec_new Rc); auto.
    - now destruct Hwf' as [_ [HwfRc _]].
  }
  apply functional_preserves_Wf in HfT as HI; auto.
  destruct HI as [HwfV1 [_ [HwfP' [HwfW' HleV1]]]];
  clear Hwfinit Hwfu HwfP.

  apply functional_preserves_typing 
  with (Rc := Rc) (A := <[𝟙]>) (B := <[𝟙]>) (R := Rs)
  in HfT as IH; auto.
  destruct IH as [Hunsd [Hunsd' [Rc1 [Rs' [HsubRc [HsubRs 
                    [Hout [Harrlt' [Hwt' [Hwt'' [HWF'' [HwW [Hdisj Husd]]]]]]]]]]]]]. 
  exists P',
        (puts put R V1),
        (ST.update_locals (([⧐ (W⁺)%sk – (V1⁺ - (W⁺)%sk)%re] W) ++ W') V1)%sk,
        Rc1.
  split.
  - unfold temporal.
    exists V1, W', tv'.
    now repeat (split; auto).
  - split.
    -- remember (puts put R V1) as R'.
       remember (ST.update_locals (([⧐W ⁺ – (V1 ⁺)%re - W ⁺] W)%sk ++ W') V1) as W1.
       apply (WF_ec_to_WF_tt put Rc _ R _ W _ W' V1); auto.
       + rewrite HeqV1, init_input_env_new_key, (WF_tt_new Rc R W); auto.
       + subst; reflexivity.
    -- split; auto. 
       remember ((ST.update_locals (([⧐ W⁺ – (V1⁺)%re - W⁺] W)%sk ++ W') V1)) as W1.
       apply (fT_out_to_tT_out R Rc _ V1 W' W _ tv' P); auto.
       + now apply WF_ec_new.
       + destruct Hwf as [_ [_ [_ [_ [_ [_ [_ [_ Hlt]]]]]]]].
         intro.
         now eapply Hlt.
Qed.  