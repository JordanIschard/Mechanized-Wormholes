From Coq Require Import Lia Arith.PeanoNat Classical_Prop.
From Mecha Require Import Resource Resources Term REnvironment Cell.
From DeBrLevel Require Import LevelInterface MapLevelInterface MapLevel MapExtInterface MapExt.
From MMaps Require Import MMaps.
Import ResourceNotations TermNotations REnvironmentNotations CellNotations
       ResourcesNotations SetNotations.


(** * Environment - Virtual Resource Environment - Reader

  W, defined in [Stock.v], is in charge of keeping bound resources
  and initial terms of each removed wh term. In the original paper,
  W is a set of triplets, which can be cumbersome to treat. We decide
  to split W into two data structures: a map and a set. The former,
  defined here, maps a resource name to a term.

*)
Module ReadStock <: IsLvlET.

Include MapLvlD.MakeLvlMapLVLD Term.
Import Raw Ext.

(** ** Definition *)

Definition env_to_renv (st : ReadStock.t) (V : REnvironment.t) :=
  fold (fun r v acc => ⌈ r ⤆ ⩽ v … ⩾ ⌉ acc)%re st V.

Definition map_union (st st' : ReadStock.t) := extend st st'.

Definition env_from_renv (st : ReadStock.t) (V : REnvironment.t) :=
  fold (fun r v acc => match (V ⌊r⌋)%re with 
                        | Some (⩽ … v' ⩾) => add r v' acc
                        | _ => add r v acc
                       end) st empty.

Definition halts (k : Lvl.t) (st : ReadStock.t) := forall (r : resource) (v : Λ), 
 find r st = Some v -> ET_Definition.halts k v.

(** ** [union] property *)

Lemma map_union_spec : forall W W' r, 
  In r (map_union W W') <-> In r W \/ In r W'.
Proof.
  split.
  - unfold map_union,extend; revert r W.
    induction W' using map_induction; intros.
    -- rewrite fold_Empty in H0; eauto.
    -- rewrite fold_Add in H1; eauto.
       + rewrite add_in_iff in H1; destruct H1; subst;
         unfold ReadStock.Add in *; rewrite H0.
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
            destruct H1; auto. unfold ReadStock.Add in H0. 
            rewrite H0 in *. rewrite add_in_iff in H1; 
            destruct H1; subst; try contradiction; auto.
       + repeat red; intros; subst; now rewrite H4.
       + apply diamond_add. 
Qed. 

(** ** [env_to_renv] property *)

#[export] Instance env_to_renv_proper :
  Proper (Logic.eq ==> Logic.eq ==> REnvironment.eq ==> REnvironment.eq)
  (fun (r0 : key) (v : Λ) (acc : REnvironment.t) => ⌈ r0 ⤆ ⩽ v … ⩾ ⌉ acc)%re.
Proof. do 4 red; intros; subst. intro. apply add_renv; now try reflexivity. Qed.

Lemma env_to_renv_diamond :
  Diamond REnvironment.eq 
  (fun (r0 : key) (v : Λ) (acc : REnvironment.t) => ⌈ r0 ⤆ ⩽ v … ⩾ ⌉ acc)%re.
Proof.
  unfold Diamond; intros; intros y. destruct (Resource.eq_dec k y); subst.
  - rewrite REnvironment.add_eq_o; auto.
    symmetry. rewrite REnvironment.add_neq_o; auto. 
    rewrite <- H0. rewrite REnvironment.add_eq_o; auto.
  - rewrite REnvironment.add_neq_o; auto.
    rewrite <- H1. destruct (Resource.eq_dec k' y); subst.
    -- rewrite REnvironment.add_eq_o; auto.
       symmetry. rewrite REnvironment.add_eq_o; auto.
    -- rewrite REnvironment.add_neq_o; auto.
       symmetry. rewrite REnvironment.add_neq_o; auto.
       rewrite <- H0. rewrite REnvironment.add_neq_o; auto.
Qed.

#[local] Hint Resolve env_to_renv_proper env_to_renv_diamond REnvironment.Equal_equiv : core.

Lemma env_to_renv_find_spec : forall rsk V r v,
  ((env_to_renv rsk V)⌊r⌋)%re = Some v -> In r rsk \/ V⌊r⌋%re = Some v.
Proof.
  intros rsk; induction rsk using map_induction; intros.
  - unfold env_to_renv in *. rewrite fold_Empty in H0; auto.
  - unfold env_to_renv in H1. rewrite fold_Add in H1; eauto.
    rewrite REnvironment.add_o in H1. destruct (Resource.eq_dec x r); subst.
    -- inversion H1. left. unfold ReadStock.Add in H0; rewrite H0; rewrite add_in_iff; now left.
    -- apply IHrsk1 in H1; destruct H1; auto.
       unfold ReadStock.Add in H0. left; rewrite H0. rewrite add_in_iff; now right.
Qed. 

Lemma env_to_renv_in_iff : forall rsk V r,
  (r ∈ (env_to_renv rsk V))%re <-> In r rsk \/ (r ∈ V)%re.
Proof.
  intros rsk; induction rsk using map_induction; intros.
  - unfold env_to_renv. 
    rewrite fold_Empty; auto.
    split; auto.
    intros [HIn |]; auto.
    destruct HIn; exfalso; now apply (H r x).
  - unfold env_to_renv. rewrite fold_Add; eauto.
    split; intros HIn.
    -- apply REnvironment.add_in_iff in HIn as [| HIn]; subst; 
       unfold ReadStock.Add in *; rewrite H0.
       + left; rewrite add_in_iff; now left.
       + apply IHrsk1 in HIn as [HIn | HIn]; auto.
         left; rewrite add_in_iff; now right.
    -- destruct HIn as [HIn | HIn].
       + rewrite REnvironment.add_in_iff.
         unfold ReadStock.Add in *; rewrite H0 in *.
         apply add_in_iff in HIn as [| HIn]; auto.
         right. apply IHrsk1.
         now left.
       + rewrite REnvironment.add_in_iff; right.
         apply IHrsk1; now right.
Qed. 

Lemma env_to_renv_unused : forall rsk V r, 
  In r rsk -> REnvironment.unused r (env_to_renv rsk V).
Proof.
  intro rsk; induction rsk using map_induction; intros V r HIn.
  - destruct HIn; now destruct (H r x).
  - unfold ReadStock.Add in H0. rewrite H0 in HIn. 
    rewrite add_in_iff in HIn; destruct HIn; subst.
    -- exists e. unfold env_to_renv. rewrite fold_Add; eauto; simpl in *.
       rewrite REnvironment.add_eq_o; auto.
    -- eapply IHrsk1 in H1; destruct H1.
       destruct (Resource.eq_dec x r); subst.
       + exists e. unfold env_to_renv.
         rewrite fold_Add; eauto; simpl in *.
         rewrite REnvironment.add_eq_o; auto.
       + exists x0; unfold env_to_renv. rewrite fold_Add; eauto; simpl in *.
         rewrite REnvironment.add_neq_o; eauto.
Qed.

Lemma env_to_renv_Forall_unused : forall rsk V,
  REnvironment.For_all (fun _ v => Cell.unused v) V ->
  REnvironment.For_all (fun _ v => Cell.unused v) (env_to_renv rsk V).
Proof.
  unfold REnvironment.For_all in *; intros.
  apply env_to_renv_find_spec in H0 as H0'; destruct H0'; auto.
  - eapply env_to_renv_unused in H1; eauto.
    destruct H1; rewrite H0 in H1; inversion H1. now simpl.
  - eapply H; eauto.
Qed.

(** ** [valid] property *)

Lemma valid_map_union_spec : forall st st' lb,
  valid lb st -> valid lb st' -> valid lb (map_union st st').
Proof.
  unfold map_union,extend. intros st st'; revert st.
  induction st' using map_induction; intros.
  - rewrite fold_Empty; auto.
  - eapply fold_Add with (eqA := eq) in H0 as H0'; eauto.
    -- eapply valid_eq; eauto; clear H0'. unfold ReadStock.Add in *. rewrite H0 in *.
       apply valid_add_notin_spec in H2 as [Hvk [Hvd Hv]]; auto.
       apply valid_add_spec; auto.
    -- red;red;red;red; intros; subst; auto. now rewrite H5.
    -- red; intros; subst. rewrite <- H4; rewrite <- H5. now apply add_add_2.
Qed.

#[local] Hint Resolve iff_equiv Equal_equiv logic_eq_equiv valid_diamond valid_proper
shift_proper shift_diamond : core.

Lemma valid_in_spec_1 : forall V lb k r,
  valid lb V -> In r (shift lb k V) <-> In r V.
Proof.
  intro V; induction V using map_induction; intros; split; intros.
  - eapply shift_Empty_iff in H. destruct H1; exfalso; unfold Empty in *.
    apply (H r x); eauto.
  - destruct H1; unfold Empty in *; exfalso; now apply (H r x).
  - unfold ReadStock.Add in *; rewrite H0 in *. 
    apply valid_add_notin_spec in H1 as [Hvk [Hvd Hv]]; auto.
    rewrite shift_add_notin_spec in H2; auto.
    rewrite add_in_iff in *; destruct H2 as [Heq | HIn]; subst.
    -- left; rewrite Resource.shift_valid_refl; auto.
    -- right. rewrite <- IHV1; eauto.
  - unfold ReadStock.Add in *; rewrite H0 in *. 
    apply valid_add_notin_spec in H1 as [Hvk [Hvd Hv]]; auto.
    rewrite shift_add_notin_spec; auto.
    rewrite add_in_iff in *; destruct H2 as [Heq | HIn]; subst.
    -- left; rewrite Resource.shift_valid_refl; auto.
    -- right. rewrite IHV1; eauto.
Qed.

(** ** [shift] property *)

Lemma shift_new_in_spec : forall r V,
  In r V -> r < new_key V.
Proof.
  intros r V; revert r; induction V using map_induction; intros.
  - exfalso; destruct H0; unfold Empty in H; now apply (H r x).
  - apply new_key_Add_spec in H0 as H0'; eauto. destruct H0' as [[Heq Hlt] | [Heq Hgt]]; subst.
    -- rewrite Heq. unfold ReadStock.Add in H0; rewrite H0 in *.
       rewrite add_in_iff in H1; destruct H1; subst; try lia.
       apply IHV1 in H1; lia.
    -- rewrite Heq. unfold ReadStock.Add in H0; rewrite H0 in *.
       rewrite add_in_iff in H1; destruct H1; subst; try lia.
       apply IHV1 in H1; lia.
Qed. 

Lemma shift_in_e_spec : forall lb k r V,
  In r (shift lb k V) -> exists r', r = ([⧐ lb – k] r')%r.
Proof.
  intros lb k r V; revert lb k r; induction V using map_induction; intros.
  - eapply shift_Empty_iff in H. unfold Empty in *; exfalso.
    destruct H0; apply (H r x); eauto.
  - apply shift_Add_spec_1 with (lb := lb) (k := k) in H0 as H0'; auto.
    unfold ReadStock.Add in H0'. rewrite H0' in H1; clear H0'.
    rewrite add_in_iff in H1; destruct H1; subst; auto.
    now exists x.
Qed.

Lemma shift_find_e_spec_1 : forall lb k r v V,
  find r (shift lb k V) = Some v -> 
  (exists r', r = ([⧐ lb – k] r')%r) /\ exists v', (v = <[[⧐ lb – k] v']>)%tm.
Proof.
  intros.
  assert (In r (shift lb k V)). { now exists v; apply find_2. }
  split.
  - now apply shift_in_e_spec in H0.
  - apply shift_in_e_spec in H0; destruct H0; subst. 
    eapply shift_find_e_spec; eauto. 
    rewrite <- H0; eauto. 
Qed.


(** ** [halts] property *)

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

Lemma halts_weakening : forall k k' t, k <= k' -> halts k t -> halts k' (shift k (k' - k) t).
Proof.
  intros k k' t Hle Hlt. unfold halts in *; intros r v HfV.
  apply shift_find_e_spec_1 in HfV as HI. destruct HI as [[r' Heqr'] [v' Heqv']]; subst.
  rewrite Heqv' in *; rewrite Heqr' in *; clear Heqv' Heqr'. 
  rewrite <- shift_find_iff in HfV.
  apply Hlt in HfV. apply ET_Props.halts_weakening; auto.
Qed.

Lemma halts_env_to_renv : forall k W V,
  halts k W -> 
  REnvironment.halts k V -> REnvironment.halts k (env_to_renv W V).
Proof.
  intros k W; induction W using map_induction; intros.
  - unfold env_to_renv. rewrite fold_Empty; auto.
  - unfold env_to_renv. unfold REnvironment.halts, halts in *; intros. 
    rewrite fold_Add in H3; eauto.
    destruct (Resource.eq_dec x r); subst.
    -- rewrite REnvironment.OP.P.add_eq_o in H3; auto.
       inversion H3; subst; simpl.
       apply (H1 r). unfold ReadStock.Add in H0. rewrite H0.
       rewrite add_eq_o; reflexivity.
    -- rewrite REnvironment.OP.P.add_neq_o in H3; auto.
       apply (IHW1 V) with (r := r); auto.
       intros. apply (H1 r0).
       unfold ReadStock.Add in H0. rewrite H0.
       rewrite add_neq_o; auto. intro; subst.
       apply H; exists v0. now apply find_2.
Qed.

Lemma diamond_env_from_renv V:
  Diamond Equal (fun (r : key) (v : Λ) (acc : ReadStock.Raw.t Λ) => 
  match V⌊r⌋%re with
  | Some (⩽ … v' ⩾) => add r v' acc
  | _ => add r v acc
  end).
Proof.
  repeat red; intros k k' e e' s s1 s2 Hneq Heqs1 Heqs2 x.
  destruct (V⌊k⌋%re) as [v |] eqn:HfV.
  - destruct (V⌊k'⌋%re) as [v' |] eqn:HfV'.
    -- destruct v,v';
       rewrite <- Heqs1; rewrite <- Heqs2;
       rewrite add_add_2; auto.
    -- destruct v;
       rewrite <- Heqs1; rewrite <- Heqs2;
       rewrite add_add_2; auto.
  - destruct (V⌊k'⌋%re) as [v' |] eqn:HfV'.
    -- destruct v';
       rewrite <- Heqs1; rewrite <- Heqs2;
       rewrite add_add_2; auto.
    -- rewrite <- Heqs1; rewrite <- Heqs2;
       rewrite add_add_2; auto.
Qed.

Lemma halts_env_from_renv : forall k W V,
  REnvironment.halts k V -> halts k W -> halts k (env_from_renv W V).
Proof.
  intros k W V. induction W using map_induction; intros.
  - unfold env_from_renv. rewrite fold_Empty; auto.
    unfold halts; intros; inversion H2.
  - unfold env_from_renv, halts; intros.
    rewrite fold_Add with (m1 := W1) (k := x) (e := e) in H3; auto.
    --  destruct (V ⌊x⌋%re) eqn:HfV.
       + destruct r0.
         ++ destruct (Resource.eq_dec r x); subst.
            * rewrite add_eq_o in H3; auto.
              inversion H3; subst.
              unfold halts in H2. apply (H2 x).
              unfold ReadStock.Add in H0. rewrite H0.
              rewrite add_eq_o; auto.
            * rewrite add_neq_o in H3; auto.
              unfold halts, env_from_renv in *.
              apply IHW1 with (r := r); auto.
              intros r1 v1 HfW1.
              apply (H2 r1). unfold ReadStock.Add in H0.
              rewrite H0. rewrite add_neq_o in *; auto.
              intro. subst.
              apply H. exists v1. now apply find_2.
         ++ destruct (Resource.eq_dec r x); subst.
            * rewrite add_eq_o in H3; auto.
              inversion H3; subst. 
              unfold REnvironment.halts in H1.
              apply (H1 x) in HfV; now simpl in *.
            * rewrite add_neq_o in H3; auto.
              unfold halts, env_from_renv in *.
              apply IHW1 with (r := r); auto.
              intros r1 v1 HfW1.
              apply (H2 r1). unfold ReadStock.Add in H0.
              rewrite H0. rewrite add_neq_o in *; auto.
              intro. subst.
              apply H. exists v1. now apply find_2.
       + destruct (Resource.eq_dec r x); subst.
         ++ rewrite add_eq_o in H3; auto.
            inversion H3; subst. unfold halts in H2.
            apply (H2 x); unfold ReadStock.Add in H0.
            rewrite H0. rewrite add_eq_o; reflexivity.
         ++ rewrite add_neq_o in H3; auto.
            unfold halts, env_from_renv in *.
            apply IHW1 with (r := r); auto.
            intros r1 v1 HfW1.
            apply (H2 r1). unfold ReadStock.Add in H0.
            rewrite H0. rewrite add_neq_o in *; auto.
            intro. subst.
            apply H. exists v1. now apply find_2.
    -- repeat red; intros; subst. destruct (V⌊y⌋%re) eqn:HfV.
       + destruct r0; now rewrite H6.
       + now rewrite H6.
    -- apply diamond_env_from_renv.
Qed.


(** ** Morphism *)

#[export] Instance in_rk : Proper (Logic.eq ==> eq ==> iff) In.
Proof.
  repeat red; intros; split; intros;
  apply Equal_Eqdom in H0; eapply In_m in H0; eauto;
  apply H0; eauto. 
Qed.

#[export] Instance find_rk : Proper (Logic.eq ==> eq ==> Logic.eq) find := _.

#[export] Instance Empty_rk : Proper (eq ==> iff) Empty.
Proof. intros rs rs' Heq; now rewrite Heq. Qed.

#[export] Instance Add_rk : 
Proper (Resource.eq ==> Term.eq ==> eq ==> eq ==> iff) (@ReadStock.Add Term.t).
Proof. 
  do 5 red; intros. apply Term.eq_leibniz in H0; subst.
  rewrite H. unfold ReadStock.Add in *. rewrite H1; rewrite H2. split; intros; auto.
Qed.

#[export] Instance add_rk : 
Proper (Resource.eq ==> Term.eq ==> ReadStock.eq ==> ReadStock.eq) 
                                                          (@ReadStock.Raw.add Term.t).
Proof. 
 do 5 red; intros; subst; apply Term.eq_leibniz in H0; subst.
 rewrite H1; now rewrite H. 
Qed.

#[export] Instance halts_eq: Proper (Logic.eq ==> ReadStock.eq ==> iff) halts.
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

Infix "⊆" := ReadStock.Submap (at level 60, no associativity) : rstock_scope. 
Infix "∈" := ReadStock.Raw.In (at level 60, no associativity) : rstock_scope. 
Notation "r '∉' Re" := (~ (ReadStock.Raw.In r Re)) (at level 75, 
                                                      no associativity) : rstock_scope. 
Notation "∅" := ReadStock.Raw.empty (at level 0, no associativity) : rstock_scope. 
Notation "'isEmpty(' Re ')'" := (ReadStock.Empty Re) (at level 20, no associativity) : rstock_scope. 
Notation "'Add'" := (ReadStock.Add) (at level 20, no associativity) : rstock_scope. 
Notation "R '⌊' x '⌋'"  := (ReadStock.Raw.find x R) (at level 15, x constr) : rstock_scope.
Notation "'max(' R ')'"  := (ReadStock.Ext.max_key R) (at level 15) : rstock_scope.
Notation "⌈ x ⤆ v '⌉' R"  := (ReadStock.Raw.add x v R) (at level 15, 
                                                            x constr, v constr) : rstock_scope.
Notation "V '⁺'" := (ReadStock.Ext.new_key V) (at level 16) : rstock_scope.

Infix "=" := ReadStock.eq : rstock_scope.
Infix "∪" := ReadStock.map_union : rstock_scope.

Notation "'[⧐' lb '–' k ']' t" := (ReadStock.shift lb k t) (at level 65, 
                                                                right associativity) : rstock_scope.
Infix "⊩" := ReadStock.valid (at level 20, no associativity) : rstock_scope.

(** ** Morphisms *)

Import ReadStock.

#[export] Instance max_rk : Proper (eq ==> Logic.eq) (Ext.max_key) := Ext.max_key_eq.
#[export] Instance new_rk : Proper (eq ==> Logic.eq) (Ext.new_key) := Ext.new_key_eq.
#[export] Instance in_rk : Proper (Logic.eq ==> ReadStock.eq ==> iff) (ReadStock.Raw.In) := _.
#[export] Instance find_rk : Proper (Logic.eq ==> eq ==> Logic.eq) (Raw.find) := _.
#[export] Instance Empty_rk : Proper (ReadStock.eq ==> iff) (ReadStock.Empty) := _.
#[export] Instance Add_rk : 
  Proper (Resource.eq ==> Term.eq ==> eq ==> eq ==> iff) (@ReadStock.Add Term.t) := _.
#[export] Instance add_rk : 
  Proper (Resource.eq ==> Term.eq ==> eq ==> eq) (@Raw.add Term.t) := _.
#[export] Instance Submap_rk : Proper (eq ==> eq ==> iff) Submap := _.
#[export] Instance Submap_rk_po : PreOrder ReadStock.Submap := Submap_po.
#[export] Instance valid_rk : Proper (Logic.eq ==> ReadStock.eq ==> iff) ReadStock.valid := _.
#[export] Instance shift_rk : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.
#[export] Instance halts_rk: Proper (Logic.eq ==> ReadStock.eq ==> iff) ReadStock.halts := _.

End ReadStockNotations.