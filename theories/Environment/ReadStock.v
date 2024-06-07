From Coq Require Import Lia Arith.PeanoNat Classical_Prop.
From Mecha Require Import Resource Term REnvironment Cell.
From DeBrLevel Require Import LevelInterface MapLevelInterface MapLevel MapExtInterface MapExt.
From MMaps Require Import MMaps.
Import ResourceNotations TermNotations REnvironmentNotations CellNotations.


(** * Environment - Virtual Resource Environment - Reader

  W, defined in [Stock.v], is in charge of keeping bound resources
  and initial terms of each removed wh term. In the original paper,
  W is a set of triplets, which can be cumbersome to treat. We decide
  to split W into two data structures: a map and a set. The former,
  defined here, maps a resource name to a term.

*)
Module ReadStock <: IsLvlET.

Include MapLvlD.MakeLvlMapWLLVL Term.
Import Raw Ext.

(** ** Definition *)

Definition to_RS (st : ReadStock.t) (s : resources) : resources :=
  fold (fun r _ acc => r +: acc)%rs st s.

Definition init_virtual (st : ReadStock.t) (V : REnvironment.t) :=
  fold (fun r v acc => ⌈ r ⤆ ⩽ v … ⩾ ⌉ᵣᵦ acc) st V.

Definition map_union (st st' : ReadStock.t) := extend st st'.

Definition map_update (st : ReadStock.t) (V : REnvironment.t) :=
  fold (fun r v acc => match V ⌊r⌋ᵣᵦ with 
                        | Some (⩽ … v' ⩾) => add r v' acc
                        | _ => add r v acc
                       end) st empty.

Definition halts (k : Lvl.t) (st : ReadStock.t) := forall (r : resource) (v : Λ), 
 find r st = Some v -> ET_Definition.halts k v.

(** ** In *)

Lemma map_union_spec : forall W W' r, 
  In r (map_union W W') <-> In r W \/ In r W'.
Proof.
  split.
  - unfold map_union,extend; revert r W.
    induction W' using map_induction; intros.
    -- rewrite fold_Empty in H0; eauto.
    -- rewrite fold_Add in H1; eauto.
       + rewrite add_in_iff in H1; destruct H1; subst;
        unfold Add in H0; rewrite H0.
        ++ right; apply add_in_iff; now left.
        ++ apply IHW'1 in H1; destruct H1; auto.
          right; apply add_in_iff; now right.
       + repeat red; intros; subst; now rewrite H4.
       + apply diamond_add.
  - unfold map_union,extend; revert r W.
    induction W' using map_induction; intros.
    -- rewrite fold_Empty; eauto; destruct H0; auto.
       destruct H0; exfalso; now apply (H r x).
    -- rewrite fold_Add; eauto.
       + destruct (Resource.eq_dec r x); subst.
         ++ rewrite add_in_iff; now left.
         ++ rewrite add_in_iff; right. apply IHW'1.
            destruct H1; auto. unfold Add in H0. rewrite H0 in *.
            rewrite add_in_iff in H1; destruct H1; subst; try contradiction; auto.
       + repeat red; intros; subst; now rewrite H4.
       + apply diamond_add. 
Qed. 

(** ** Initialized *)

Lemma proper_init_virtual :
  Proper (Logic.eq ==> Logic.eq ==> REnvironment.eq ==> REnvironment.eq)
  (fun (r0 : key) (v : Λ) (acc : REnvironment.t) => ⌈ r0 ⤆ ⩽ v … ⩾ ⌉ᵣᵦ acc).
Proof.
  red; red; red; red; intros; subst. intro. now rewrite H1.
Qed.

Lemma diamond_init_virtual :
  Diamond REnvironment.eq 
  (fun (r0 : key) (v : Λ) (acc : REnvironment.t) => ⌈ r0 ⤆ ⩽ v … ⩾ ⌉ᵣᵦ acc).
Proof.
  unfold Diamond; intros; intro y. rewrite <- H0; rewrite <- H1.
  rewrite REnvironment.add_add_2; auto.
Qed.

#[local] Hint Resolve proper_init_virtual REnvironment.Equal_equiv diamond_init_virtual : core.

Lemma init_virtual_unused : forall rsk V,
  forall r, In r rsk ->
  REnvironment.unused r (init_virtual rsk V).
Proof.
  intro rsk; induction rsk using map_induction; intros V r HIn.
  - destruct HIn; now destruct (H r x).
  - unfold Add in H0. rewrite H0 in HIn. rewrite add_in_iff in HIn; destruct HIn; subst.
    -- exists e. unfold init_virtual. rewrite fold_Add; eauto; simpl in *.
       rewrite REnvironment.add_eq_o; auto.
    -- eapply IHrsk1 in H1; destruct H1.
       destruct (Resource.eq_dec x r); subst.
       + exists e. unfold init_virtual.
         rewrite fold_Add; eauto; simpl in *.
         rewrite REnvironment.add_eq_o; auto.
       + exists x0; unfold init_virtual. rewrite fold_Add; eauto; simpl in *.
         rewrite REnvironment.add_neq_o; eauto.
Qed.

Lemma init_virtual_in_spec : forall rsk V r,
  r ∈ᵣᵦ (init_virtual rsk V) -> In r rsk \/ r ∈ᵣᵦ V.
Proof.
  intros rsk; induction rsk using map_induction; intros.
  - unfold init_virtual in *. rewrite fold_Empty in H0; auto.
  - unfold init_virtual in H1. rewrite fold_Add in H1; eauto.
    rewrite REnvironment.add_in_iff in H1. destruct H1; subst.
    -- unfold Add in H0. left; rewrite H0. rewrite add_in_iff; now left.
    -- unfold Add in H0. rewrite H0. destruct (Resource.eq_dec r x); subst.
       + left; rewrite add_in_iff; now left.
       + apply IHrsk1 in H1; destruct H1; auto.
         left; rewrite add_in_iff; right; auto.
Qed. 

Lemma init_virtual_find_spec : forall rsk V r v,
  (init_virtual rsk V) ⌈ r ⩦ v ⌉ᵣᵦ -> In r rsk \/ V ⌈ r ⩦ v ⌉ᵣᵦ.
Proof.
  intros rsk; induction rsk using map_induction; intros.
  - unfold init_virtual in *. rewrite fold_Empty in H0; auto.
  - unfold init_virtual in H1. rewrite fold_Add in H1; eauto.
    rewrite REnvironment.add_o in H1. destruct (Resource.eq_dec x r); subst.
    -- inversion H1. left. unfold Add in H0; rewrite H0; rewrite add_in_iff; now left.
    -- apply IHrsk1 in H1; destruct H1; auto.
       unfold Add in H0. left; rewrite H0. rewrite add_in_iff; now right.
Qed. 

Lemma init_virtual_Forall_unused : forall rsk V,
  REnvironment.For_all (fun _ v => Cell.unused v) V ->
  REnvironment.For_all (fun _ v => Cell.unused v) (init_virtual rsk V).
Proof.
  unfold REnvironment.For_all in *; intros.
  apply init_virtual_find_spec in H0 as H0'; destruct H0'; auto.
  - eapply init_virtual_unused in H1; eauto.
    destruct H1; rewrite H0 in H1; inversion H1. now simpl.
  - eapply H; eauto.
Qed.

(** ** Morphism from RStock to Resources *)

Lemma proper_rktors :
  Proper (Logic.eq ==> Logic.eq ==> Resources.Equal ==> Resources.Equal)
  (fun (r0 : key) (_ : Term.raw) (acc : Resources.t) => (r0 +: acc)%rs).
Proof. red;red;red;red; intros; subst. now rewrite H1. Qed.

Lemma diamond_rktors :
  Diamond Resources.Equal
  (fun (r0 : key) (_ : Term.raw) (acc : Resources.t) => (r0 +: acc)%rs).
Proof.
  repeat red; intros; split; intros; rewrite <- H0 in *; rewrite <- H1 in *;
  repeat rewrite Resources.add_spec in *; destruct H2 as [H2 | [H2 | H2]]; auto.
Qed.

#[local] Hint Resolve Resources.eq_equiv proper_rktors diamond_rktors : core.

Lemma to_RS_empty_spec : forall R, to_RS empty R = R.
Proof.
  unfold to_RS; intros. rewrite fold_Empty; eauto. apply empty_1.
Qed.

Lemma to_RS_in_spec : forall st r R,
  In r st -> (r ∈ to_RS st R)%rs.
Proof.
  intros st; induction st using map_induction.
  - intros. unfold Empty in H; destruct H0; exfalso; now apply (H r x).
  - intros. unfold to_RS; rewrite fold_Add; eauto.
    unfold Add in H0; rewrite H0 in *. rewrite add_in_iff in H1; destruct H1; subst.
    -- rewrite Resources.add_spec; now left.
    -- rewrite Resources.add_spec; right; auto.
Qed. 

Lemma to_RS_in_spec_1 : forall st r R,
  (r ∈ to_RS st R)%rs -> In r st \/ (r ∈ R)%rs.
Proof.
  intros st; induction st using map_induction; intros.
  - unfold to_RS in *. rewrite fold_Empty with (eqA := Resources.Equal) in H0; auto.
  - unfold to_RS in H1; rewrite fold_Add with (eqA := Resources.Equal) in H1; eauto.
    rewrite Resources.add_spec in H1; destruct H1; subst; unfold Add in H0; rewrite H0 in *.
    -- left; rewrite add_in_iff; now left.
    -- apply IHst1 in H1; destruct H1; auto.
       left; rewrite add_in_iff; right; auto.
Qed. 

Lemma to_RS_in_spec_2 : forall st r R,
  (r ∈ to_RS st R)%rs <-> In r st \/ (r ∈ R)%rs.
Proof.
  split; intros.
  - now apply to_RS_in_spec_1.
  - destruct H.
    -- now apply to_RS_in_spec.
    -- revert r R H; induction st using map_induction; intros.
       + unfold to_RS in *. 
         rewrite fold_Empty with (eqA := Resources.Equal); auto. 
       + unfold to_RS; rewrite fold_Add with (eqA := Resources.Equal); eauto.
         rewrite Resources.add_spec; right; auto.
Qed. 

Lemma to_RS_shift_in_spec : forall st r R lb k,
  (r ∈ to_RS st R)%rs -> (([⧐ᵣ lb ≤ k] r) ∈ to_RS (shift lb k st) ([⧐ᵣₛ lb ≤ k] R))%rs.
Proof.
  intros st; induction st using map_induction; intros.
  - unfold to_RS in H0; rewrite fold_Empty with (eqA := Resources.Equal) in H0; eauto.
    eapply shift_Empty_iff in H; unfold to_RS; rewrite fold_Empty; eauto.
    now apply Resources.shift_in_spec.
  - unfold to_RS in H1; rewrite fold_Add with (eqA := Resources.Equal) in H1; eauto.
    unfold to_RS. eapply shift_Add_spec_1 in H0; eauto. 
    rewrite fold_Add with (k := ([⧐ᵣ lb ≤ k] x)); eauto. 
    -- clear H0. rewrite Resources.add_spec in *; destruct H1; subst.
       + now left.
       + right; auto.
    -- now rewrite <- shift_in_spec.
Qed.

Lemma to_RS_map_union_spec : forall r rsk rsk' R,
  (r ∈ to_RS (map_union rsk rsk') R)%rs <-> 
  (r ∈ (to_RS rsk R))%rs \/ (r ∈ (to_RS rsk' R))%rs.
Proof. 
  intros r rsk rsk'; revert r rsk; unfold map_union,extend; 
  induction rsk' using map_induction; split; intros.
  - rewrite fold_Empty in H0; eauto.
  - rewrite fold_Empty; eauto. destruct H0; auto.
    unfold to_RS in H0; 
    rewrite fold_Empty with (eqA := Resources.Equal) in H0; eauto.
    rewrite to_RS_in_spec_2; now right.
  - rewrite to_RS_in_spec_2 in H1; destruct H1.
    -- rewrite fold_Add in H1; eauto.
       + rewrite add_in_iff in H1; destruct H1; subst.
         ++ right; rewrite to_RS_in_spec_2. left.
            unfold Add in H0; rewrite H0; rewrite add_in_iff; now left.
         ++ destruct (Resource.eq_dec r x); subst.
            * right; rewrite to_RS_in_spec_2. left.
              unfold Add in H0; rewrite H0; rewrite add_in_iff; now left.
            * apply map_union_spec in H1; destruct H1.
              ** left; rewrite to_RS_in_spec_2. now left.
              ** right; rewrite to_RS_in_spec_2.
                 unfold Add in H0; rewrite H0; rewrite add_in_iff; left; now right.
       + repeat red; intros; subst; now rewrite H4.
       + unfold Diamond; intros; rewrite <- H3; rewrite <- H4.
         rewrite add_add_2; now auto.
    -- left; rewrite to_RS_in_spec_2; now right.
  - rewrite to_RS_in_spec_2; destruct H1; 
    rewrite to_RS_in_spec_2 in H1; destruct H1; auto; left.
    -- apply map_union_spec; auto.
    -- apply map_union_spec; auto.
Qed. 


(** ** Valid *)

Lemma valid_map_union_spec : forall st st' lb,
  valid lb st -> valid lb st' -> valid lb (map_union st st').
Proof.
  unfold map_union,extend. intros st st'; revert st.
  induction st' using map_induction; intros.
  - rewrite fold_Empty; auto.
  - eapply fold_Add with (eqA := eq) in H0 as H0'; eauto.
    -- eapply valid_eq; eauto; clear H0'. unfold Add in *. rewrite H0 in *.
       apply valid_add_notin_spec in H2 as [Hvk [Hvd Hv]]; auto.
       apply valid_add_spec; auto.
    -- red;red;red;red; intros; subst; auto. now rewrite H5.
    -- red; intros; subst. rewrite <- H4; rewrite <- H5. now apply add_add_2.
Qed.

#[local] Hint Resolve iff_equiv Equal_equiv logic_eq_equiv  valid_diamond valid_proper
shift_proper shift_diamond : core.


Lemma valid_in_spec_1 : forall V lb k r,
  valid lb V -> In r (shift lb k V) <-> In r V.
Proof.
  intro V; induction V using map_induction; intros; split; intros.
  - eapply shift_Empty_iff in H. destruct H1; exfalso; unfold Empty in *.
    apply (H r x); eauto.
  - destruct H1; unfold Empty in *; exfalso; now apply (H r x).
  - unfold Add in *; rewrite H0 in *. 
    apply valid_add_notin_spec in H1 as [Hvk [Hvd Hv]]; auto.
    rewrite shift_add_notin_spec in H2; auto.
    rewrite add_in_iff in *; destruct H2 as [Heq | HIn]; subst.
    -- left; rewrite Resource.shift_valid_refl; auto.
    -- right. rewrite <- IHV1; eauto.
  - unfold Add in *; rewrite H0 in *. 
    apply valid_add_notin_spec in H1 as [Hvk [Hvd Hv]]; auto.
    rewrite shift_add_notin_spec; auto.
    rewrite add_in_iff in *; destruct H2 as [Heq | HIn]; subst.
    -- left; rewrite Resource.shift_valid_refl; auto.
    -- right. rewrite IHV1; eauto.
Qed.

(** ** Shift *)

Lemma shift_new_in_spec : forall r V,
  In r V ->  r < new_key V.
Proof.
  intros r V; revert r; induction V using map_induction; intros.
  - exfalso; destruct H0; unfold Empty in H; now apply (H r x).
  - apply new_key_Add_spec in H0 as H0'; eauto. destruct H0' as [[Heq Hlt] | [Heq Hgt]]; subst.
    -- rewrite Heq. unfold Add in H0; rewrite H0 in *.
       rewrite add_in_iff in H1; destruct H1; subst; try lia.
       apply IHV1 in H1; lia.
    -- rewrite Heq. unfold Add in H0; rewrite H0 in *.
       rewrite add_in_iff in H1; destruct H1; subst; try lia.
       apply IHV1 in H1; lia.
Qed. 


Lemma shift_in_e_spec : forall lb k r V,
  In r (shift lb k V) -> exists r', r =  ([⧐ᵣ lb ≤ k] r').
Proof.
  intros lb k r V; revert lb k r; induction V using map_induction; intros.
  - eapply shift_Empty_iff in H. unfold Empty in *; exfalso.
    destruct H0; apply (H r x); eauto.
  - apply shift_Add_spec_1 with (lb := lb) (k := k) in H0 as H0'; auto.
    unfold Add in H0'. rewrite H0' in H1; clear H0'.
    rewrite add_in_iff in H1; destruct H1; subst.
    -- now exists x.
    -- auto.
Qed.

Lemma shift_find_e_spec_1 : forall lb k r v V,
  find r (shift lb k V) = Some v -> 
  (exists r', r = ([⧐ᵣ lb ≤ k] r')) /\ exists v', Term.eq v (Term.shift lb k v').
Proof.
  intros.
  assert (In r (shift lb k V)). { now exists v; apply find_2. }
  split.
  - now apply shift_in_e_spec in H0.
  - apply shift_in_e_spec in H0; destruct H0; subst. 
    eapply shift_find_e_spec; eauto. 
Qed.

(** ** Halts *)

Lemma halts_init_virtual : forall k W V,
  halts k W -> 
  REnvironment.halts k V ->
  REnvironment.halts k (init_virtual W V).
Proof.
  intros k W; induction W using map_induction; intros.
  - unfold init_virtual. rewrite fold_Empty; auto.
  - unfold init_virtual. unfold REnvironment.halts, halts in *; intros. 
    rewrite fold_Add in H3; eauto.
    destruct (Resource.eq_dec x r); subst.
    -- rewrite REnvironment.OP.P.add_eq_o in H3; auto.
       inversion H3; subst; simpl.
       apply (H1 r). unfold Add in H0. rewrite H0.
       rewrite add_eq_o; reflexivity.
    -- rewrite REnvironment.OP.P.add_neq_o in H3; auto.
       apply (IHW1 V) with (r := r); auto.
       intros. apply (H1 r0).
       unfold Add in H0. rewrite H0.
       rewrite add_neq_o; auto. intro; subst.
       apply H; exists v0. now apply find_2.
Qed.

Lemma diamond_map_update V:
  Diamond Equal (fun (r0 : key) (v0 : Λ) (acc : ReadStock.Raw.t Λ) => 
  match V ⌊ r0 ⌋ᵣᵦ with
  | Some (⩽ … v' ⩾) => add r0 v' acc
  | _ => add r0 v0 acc
  end).
Proof.
  repeat red; intros k k' e e' s s1 s2 Hneq Heqs1 Heqs2 x.
  destruct (V⌊k⌋ᵣᵦ) as [v |] eqn:HfV.
  - destruct (V⌊k'⌋ᵣᵦ) as [v' |] eqn:HfV'.
    -- destruct v,v';
       rewrite <- Heqs1; rewrite <- Heqs2;
       rewrite add_add_2; auto.
    -- destruct v;
       rewrite <- Heqs1; rewrite <- Heqs2;
       rewrite add_add_2; auto.
  - destruct (V⌊k'⌋ᵣᵦ) as [v' |] eqn:HfV'.
    -- destruct v';
       rewrite <- Heqs1; rewrite <- Heqs2;
       rewrite add_add_2; auto.
    -- rewrite <- Heqs1; rewrite <- Heqs2;
       rewrite add_add_2; auto.
Qed.

Lemma halts_update : forall k W V,
  REnvironment.halts k V ->
  halts k W ->
  halts k (map_update W V).
Proof.
  intros k W V. induction W using map_induction; intros.
  - unfold map_update. rewrite fold_Empty; auto.
    unfold halts; intros; inversion H2.
  - unfold map_update, halts; intros.
    rewrite fold_Add with (m1 := W1) (k := x) (e := e) in H3; auto.
    --  destruct (V ⌊ x ⌋ᵣᵦ) eqn:HfV.
       + destruct r0.
         ++ destruct (Resource.eq_dec r x); subst.
            * rewrite add_eq_o in H3; auto.
              inversion H3; subst.
              unfold halts in H2. apply (H2 x).
              unfold Add in H0. rewrite H0.
              rewrite add_eq_o; auto.
            * rewrite add_neq_o in H3; auto.
              unfold halts, map_update in *.
              apply IHW1 with (r := r); auto.
              intros r1 v1 HfW1.
              apply (H2 r1). unfold Add in H0.
              rewrite H0. rewrite add_neq_o in *; auto.
              intro. subst.
              apply H. exists v1. now apply find_2.
         ++ destruct (Resource.eq_dec r x); subst.
            * rewrite add_eq_o in H3; auto.
              inversion H3; subst. 
              unfold REnvironment.halts in H1.
              apply (H1 x) in HfV; now simpl in *.
            * rewrite add_neq_o in H3; auto.
              unfold halts, map_update in *.
              apply IHW1 with (r := r); auto.
              intros r1 v1 HfW1.
              apply (H2 r1). unfold Add in H0.
              rewrite H0. rewrite add_neq_o in *; auto.
              intro. subst.
              apply H. exists v1. now apply find_2.
       + destruct (Resource.eq_dec r x); subst.
         ++ rewrite add_eq_o in H3; auto.
            inversion H3; subst. unfold halts in H2.
            apply (H2 x); unfold Add in H0.
            rewrite H0. rewrite add_eq_o; reflexivity.
         ++ rewrite add_neq_o in H3; auto.
            unfold halts, map_update in *.
            apply IHW1 with (r := r); auto.
            intros r1 v1 HfW1.
            apply (H2 r1). unfold Add in H0.
            rewrite H0. rewrite add_neq_o in *; auto.
            intro. subst.
            apply H. exists v1. now apply find_2.
    -- repeat red; intros; subst. destruct (V⌊y⌋ᵣᵦ) eqn:HfV.
       + destruct r0; now rewrite H6.
       + now rewrite H6.
    -- apply diamond_map_update.
Qed.

Lemma halts_weakening : forall k k' t, k <= k' -> halts k t -> halts k' (shift k (k' - k) t).
Proof.
  intros k k' t Hle Hlt. unfold halts in *; intros r v HfV.
  apply shift_find_e_spec_1 in HfV as HI. destruct HI as [[r' Heqr'] [v' Heqv']]; subst.
  rewrite Heqv' in *; clear Heqv'; rewrite <- shift_find_spec in HfV.
  apply Hlt in HfV. apply ET_Props.halts_weakening; auto.
Qed.

Lemma halts_union_spec k s1 s2 :
  halts k s1 /\ halts k s2 -> halts k (map_union s1 s2).
Proof.
  unfold halts, map_union; intros [] r v Hf.
  apply find_2 in Hf. 
  apply extend_mapsto_iff in Hf as [HM | [HM _]];
  apply find_1 in HM.
  - now apply (H0 r).
  - now apply (H r).
Qed.

Lemma halts_add_spec k x v s :
  (ET_Definition.halts k v) /\ halts k s -> halts k (add x v s).
Proof.
  intros [Hltv Hlts]; unfold halts; intros r v' Hfi.
  rewrite add_o in Hfi; destruct (Resource.eq_dec x r); subst; inversion Hfi; subst; auto.
  apply Hlts in Hfi; auto.
Qed.

(** ** Morphism *)

#[export] 
Instance in_rk : 
  Proper (Logic.eq ==> eq ==> iff) In.
Proof.
  repeat red; intros; split; intros;
  apply Equal_Eqdom in H0; eapply In_m in H0; eauto;
  apply H0; eauto. 
Qed.

#[export] 
Instance find_rk : Proper (Logic.eq ==> eq ==> Logic.eq) find.
Proof. repeat red; intros; subst. now rewrite H0. Qed.

#[export] 
Instance Empty_rk : Proper (eq ==> iff) Empty.
Proof. red; red; intros; now apply Empty_eq_spec. Qed.

#[export] 
Instance Add_rk : 
Proper (Resource.eq ==> Term.eq ==> eq ==> eq ==> iff) (@Add Term.t).
Proof. 
  red; red; red; red; red; intros. apply Term.eq_leibniz in H0; subst.
  rewrite H. unfold Add in *. rewrite H1; rewrite H2. split; intros; auto.
Qed.

#[export] 
Instance add_rk : 
Proper (Resource.eq ==> Term.eq ==> ReadStock.eq ==> ReadStock.eq) 
                                                          (@ReadStock.Raw.add Term.t).
Proof. 
 red; red; red; red; red; intros; subst; apply Term.eq_leibniz in H0; subst.
 rewrite H1; now rewrite H. 
Qed. 

#[export] 
Instance Submap_rk : 
  Proper (ReadStock.eq ==> ReadStock.eq ==> iff) ReadStock.Submap.
Proof. 
  repeat red; intros; split; intros.
  - rewrite ReadStock.Submap_eq_left_spec in H1; eauto.
    rewrite ReadStock.Submap_eq_right_spec in H1; eauto.
  - rewrite <- ReadStock.Submap_eq_left_spec in H1; eauto.
    rewrite <- ReadStock.Submap_eq_right_spec in H1; eauto.
Qed.

#[export]
Instance halts_eq: 
 Proper (Logic.eq ==> ReadStock.eq ==> iff) halts.
Proof.
  repeat red; intros; subst; unfold halts in *. 
  split; intros; apply (H r).
  - now rewrite H0.
  - now rewrite <- H0.
Qed.

End ReadStock.

(** * Notation - Reading Virtual Resource Environment *)

Module ReadStockNotations.

(** ** Scope *)
Declare Scope rstock_scope.
Delimit Scope rstock_scope with rk.

(** ** Notations *)
Definition 𝐖ᵣ := ReadStock.t.


Infix "⊆ᵣₖ" := ReadStock.Submap (at level 20, no associativity). 
Infix "∈ᵣₖ" := ReadStock.Raw.In (at level 20, no associativity). 
Notation "r '∉ᵣₖ' Re" := (~ (ReadStock.Raw.In r Re)) (at level 20, no associativity). 
Notation "∅ᵣₖ" := ReadStock.Raw.empty (at level 20, no associativity). 
Notation "'isEmptyᵣₖ(' Re ')'" := (ReadStock.Empty Re) (at level 20, no associativity). 
Notation "'Addᵣₖ'" := (ReadStock.Add) (at level 20, no associativity). 
Notation "R '⌊' x '⌋ᵣₖ'"  := (ReadStock.Raw.find x R) (at level 15, x constr).
Notation "'maxᵣₖ(' R ')'"  := (ReadStock.Ext.max_key R) (at level 15).
Notation "'newᵣₖ(' R ')'"  := (ReadStock.Ext.new_key R) (at level 15).
Notation "⌈ x ⤆ v '⌉ᵣₖ' R"  := (ReadStock.Raw.add x v R) (at level 15, x constr, 
                                                                                v constr).
Notation "R ⌈ x ⩦ v '⌉ᵣₖ'"  := (ReadStock.Raw.find x R = Some v) (at level 15, 
                                                                          x constr, v constr).
Notation "R ⌈ x ⩦ ⊥ '⌉ᵣₖ'"  := (ReadStock.Raw.find x R = None) (at level 15, 
                                                                                x constr).

Infix "=" := ReadStock.eq : rstock_scope.
Infix "∪" := ReadStock.map_union : rstock_scope.

Notation "'[⧐ᵣₖ' lb '≤' k ']' t" := (ReadStock.shift lb k t) (at level 45, right associativity).
Infix "⊩ᵣₖ" := ReadStock.valid (at level 20, no associativity).

(** ** Morphisms *)
#[export] Instance rk_max : Proper (ReadStock.eq ==> Logic.eq) (ReadStock.Ext.max_key).
          Proof. apply ReadStock.Ext.max_key_eq. Qed.

#[export] Instance rk_new : Proper (ReadStock.eq ==> Logic.eq) (ReadStock.Ext.new_key).
          Proof. apply ReadStock.Ext.new_key_eq. Qed.

#[export] 
Instance in_rk : 
  Proper (Logic.eq ==> ReadStock.eq ==> iff) (ReadStock.Raw.In).
Proof. apply ReadStock.in_rk. Qed.

#[export] 
Instance find_rk : Proper (Logic.eq ==> ReadStock.eq ==> Logic.eq) 
                                                      (ReadStock.Raw.find).
Proof. apply ReadStock.find_rk. Qed.

#[export] 
Instance Empty_rk : Proper (ReadStock.eq ==> iff) (ReadStock.Empty).
Proof. apply ReadStock.Empty_rk. Qed.

#[export] 
Instance Add_rk : 
Proper (Resource.eq ==> Term.eq ==> ReadStock.eq ==> ReadStock.eq ==> iff) 
                                                  (@ReadStock.Add Term.t).
Proof. apply ReadStock.Add_rk. Qed. 

#[export] 
Instance add_rk : 
Proper (Resource.eq ==> Term.eq ==> ReadStock.eq ==> ReadStock.eq) 
                                                          (@ReadStock.Raw.add Term.t).
Proof. apply ReadStock.add_rk. Qed. 

#[export] 
Instance Submap_rk : 
  Proper (ReadStock.eq ==> ReadStock.eq ==> iff) ReadStock.Submap.
Proof. apply ReadStock.Submap_rk. Qed.

#[export] 
Instance Submap_rk_po : PreOrder ReadStock.Submap.
Proof. apply ReadStock.Submap_po. Qed. 

#[export] 
Instance valid_rk : Proper (Logic.eq ==> ReadStock.eq ==> iff) ReadStock.valid.
Proof. apply ReadStock.valid_eq. Qed.

#[export] 
Instance shift_rk : 
  Proper (Logic.eq ==> Logic.eq ==> ReadStock.eq ==> ReadStock.eq) ReadStock.shift.
Proof. apply ReadStock.shift_eq. Qed.

#[export]
Instance halts_rk: 
 Proper (Logic.eq ==> ReadStock.eq ==> iff) ReadStock.halts.
Proof. apply ReadStock.halts_eq. Qed.

End ReadStockNotations.