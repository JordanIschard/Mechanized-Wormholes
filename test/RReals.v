From Coq Require Import Lia Arith.PeanoNat Classical_Prop.
From Mecha Require Import Resource Term RReal Evaluation RReal.
From DeBrLevel Require Import LevelInterface MapLevelInterface MapLevel MapExtInterface 
               MapExt.
From MMaps Require Import MMaps.


(** * Environment between resources and cells *)
Module RReals <: IsLvlET.
Include MapLvlD.MakeLvlMapWLLVL RReal.

Import Raw Ext.

(** *** Definition *)
(*
Definition embeds_func V v := 
    add (new_key V) ([⧐ᵣₓ (new_key V) ≤ 1 ] ⩽ v … ⩾) (shift (new_key V) 1 V).

Definition embeds_func_revert v V := embeds_func V v. 

Definition embeds_gen (V : RReals.t) (l : list Λ) := 
  List.fold_left embeds_func l V.

Definition For_all (P : resource -> RReal.t -> Prop) (V : RReals.t) := 
  forall r v, find r V = Some v -> P r v. 

Definition embeds := embeds_gen empty. 

Definition extracts (V : RReals.t) : list (option Λ) :=
  List.map (fun x =>  match (find x V) with
                        | Some (⩽ … v ⩾) => Some v
                        | Some _ => None
                        | None   => None
                      end) (seq 0 (max_key V)).

Definition halts (k : Lvl.t) (V : RReals.t) := forall (r : resource) (v : 𝑣), 
 find r V = Some v -> halts k (RReal.extract v).

Definition used r (V : RReals.t) := exists v, find r V = Some (⩽ … v ⩾).
Definition unused r (V : RReals.t) := exists v, find r V = Some (⩽ v … ⩾).

(** *** Embedding *)

Lemma embedding_func_new_spec : forall V v,
 new_key (embeds_func_revert v V) = S (new_key V).
Proof.
  unfold embeds_func_revert, embeds_func; intros.
  rewrite new_key_add_spec_1; auto.
  - apply shift_new_notin_spec; lia.
  - rewrite shift_new_spec; lia.
Qed.

Lemma embedding_func_in_spec : forall V v r,
  In r (embeds_func_revert v V) <-> r = (new_key V) \/ In r V.
Proof. 
  split; intros; unfold embeds_func_revert,embeds_func in *.
  - rewrite add_in_iff in H; destruct H; auto.
    right. apply new_key_in_spec in H as H'.
    rewrite shift_new_spec in H'; auto.
    rewrite shift_in_spec with (lb := (new_key V)) (k := 1).
    rewrite Resource.shift_valid_refl; auto.
  - destruct H; rewrite add_in_iff; subst; auto.
    right. apply new_key_in_spec in H as H'.
    rewrite shift_in_spec with (lb := (new_key V)) (k := 1) in H.
    rewrite Resource.shift_valid_refl in H; auto.
Qed.

Lemma embedding_func_unused_spec : forall r x V,
  unused r V -> unused r (embeds_func_revert x V).
Proof.
  intros; unfold embeds_func_revert,embeds_func.
  destruct (Resource.eq_dec r (new_key V)); subst.
  - simpl. exists <[[⧐ₜₘ {new_key V} ≤ 1] x]>; rewrite add_eq_o; auto.
  - destruct H. exists <[[⧐ₜₘ {new_key V} ≤ 1] x0]>. rewrite add_neq_o; auto.
    assert (In r V). { exists (⩽ x0 … ⩾). now apply find_2. }
    apply new_key_in_spec in H0. rewrite shift_find_spec in H;
    rewrite Resource.shift_valid_refl in H; eauto.
Qed.

Lemma embedding_gen_new_spec : forall l V,
  (length l) + new_key V = new_key (embeds_gen V l).
Proof.
  intros; unfold embeds_gen; rewrite <- fold_left_rev_right. 
  fold embeds_func_revert. revert V.
  induction l using rev_ind; intro; simpl; auto.
  rewrite rev_unit; simpl. rewrite app_length; simpl.
  rewrite embedding_func_new_spec; rewrite <- IHl; lia.
Qed.

Lemma valid_embedding_gen_keys_spec : forall l V,
  forall r, In r (embeds_gen V l) -> (new_key (embeds_gen V l)) ⊩ᵣ r.
Proof.
  intros; unfold embeds_gen in *; rewrite <- fold_left_rev_right in *.
  fold embeds_func_revert in *. revert V r H.
  induction l using rev_ind; intros; simpl in *.
  - now apply new_key_in_spec.
  - rewrite rev_unit in *; simpl in *; rewrite embedding_func_new_spec.
    rewrite embedding_func_in_spec in H; destruct H; subst.
    -- unfold Resource.valid; lia.
    -- apply IHl in H. apply Resource.valid_weakening 
       with (k := new_key (fold_right embeds_func_revert V (List.rev l))); auto.
Qed.

Lemma embedding_gen_find_eq_spec : forall V x,
  find (new_key V) (embeds_func_revert x V) = Some (⩽ [⧐ₜₘ {new_key V} ≤ 1] x … ⩾).
Proof.
  unfold embeds_func_revert, embeds_func; intros.
  rewrite add_eq_o; auto.
Qed.

Lemma embedding_gen_unused : forall l V,
  (forall r, In r V -> unused r V) ->
  forall r, In r (embeds_gen V l) -> unused r (embeds_gen V l).
Proof.
  intros; unfold embeds_gen in *; rewrite <- fold_left_rev_right in *.
  fold embeds_func_revert in *. revert V r H H0.
  induction l using rev_ind; intros V r H HIn; simpl in *; auto.
  rewrite rev_unit in *; simpl in *.
  rewrite embedding_func_in_spec in HIn. destruct HIn; subst.
  - exists (Term.shift (new_key (fold_right embeds_func_revert V (List.rev l))) 1 x).
    apply embedding_gen_find_eq_spec.
  - apply IHl in H0 as H0'; auto. now apply embedding_func_unused_spec.
Qed.

Lemma embedding_unused : forall l,
  forall r, In r (embeds l) -> unused r (embeds l).
Proof. 
  intros; unfold embeds in *; apply embedding_gen_unused; auto.
  intros; inversion H0; inversion H1.
Qed.

Lemma embedding_Forall_unused : forall l V,
  For_all (fun _ v => RReal.unused v) V ->
  For_all (fun _ v => RReal.unused v) (embeds_gen V l).
Proof.
  unfold For_all; intros. assert (In r (embeds_gen V l)).
  { exists v; now apply find_2. }
  apply embedding_gen_unused in H1.
  - destruct H1. rewrite H0 in H1; now inversion H1.
  - intros. destruct H2. apply find_1 in H2. apply H in H2 as H2'.
    destruct x eqn:Heq.
    -- now exists λ.
    -- contradiction.
Qed. 

(** *** Valid *)


Lemma valid_wh_spec : forall m v v',
  valid (new_key m) m -> (new_key m) ⊩ᵣₓ v -> (new_key m) ⊩ᵣₓ v' -> 
  valid (S (S (new_key m))) (add (S (new_key m)) v (add (new_key m) v' m)).
Proof.
  intros. apply valid_add_notin_spec.
  - rewrite add_in_iff; intro. destruct H2; try lia.
    apply new_key_notin_spec in H2; auto.
  - split. 
    -- unfold Resource.valid; lia.
    -- split.
      * apply RReal.valid_weakening with (k := new_key m); auto.
      * apply valid_add_notin_spec.
        ** apply new_key_notin_spec; lia.
        ** split.
            + unfold Resource.valid; lia.
            + split.
              ++ apply RReal.valid_weakening with (k := new_key m); auto.
              ++ apply valid_weakening with (k := new_key m); auto.
Qed.

Lemma valid_wh_spec_1 : forall m v v',
  valid (new_key m) m -> (new_key m) ⊩ᵣₓ v -> (new_key m) ⊩ᵣₓ v' -> 
  valid (S (S (new_key m))) (add (S (new_key m)) v 
                              (add (new_key m) (RReal.shift (new_key m) 2 v') (shift (new_key m) 2 m))).
Proof.
  intros. apply valid_add_notin_spec.
  - apply new_key_notin_spec; rewrite new_key_add_spec_1; auto.
    * apply new_key_notin_spec; rewrite shift_new_spec; auto.
    * rewrite shift_new_spec; auto.
  - repeat split. 
    -- unfold Resource.valid; lia.
    -- apply RReal.valid_weakening with (k := new_key m); auto.
    -- apply valid_add_notin_spec.
       * apply new_key_notin_spec; auto; rewrite shift_new_spec; auto.
       * repeat split.
         + unfold Resource.valid; lia.
         + replace (S (S (new_key m))) with ((new_key m) + 2) by lia. 
           now apply RReal.shift_preserves_valid_1.
         + replace (S (S (new_key m))) with ((new_key m) + 2) by lia. 
           now apply shift_preserves_valid_1.  
Qed.

Lemma valid_update_spec : forall m r v k,
  In r m -> valid k m -> RReal.valid k v -> valid k (add r v m).
Proof.
  intro m; induction m using map_induction; intros r v k HIn Hvm Hvv.
  - unfold Empty in *; exfalso.
    destruct HIn as [z HM]; now apply (H r z).
  - rewrite <- valid_Add_spec in Hvm; eauto; destruct Hvm as [Hvx [Hve Hvm]].
    destruct (Resource.eq_dec x r); subst.
    -- unfold Add in *; rewrite H0 in *.
       assert (eq (add r v (add r e m1)) (add r v m1)).
       { 
        intro y. destruct (Resource.eq_dec y r); subst.
        - repeat rewrite add_eq_o; auto.
        - repeat rewrite add_neq_o; auto.
       }
       rewrite H1; clear H1. rewrite valid_add_notin_spec; auto.
    -- unfold Add in *; rewrite H0 in *. rewrite add_add_2; auto.
       rewrite valid_add_notin_spec; auto.
       + repeat split; auto. apply IHm1; auto. apply add_in_iff in HIn.
          destruct HIn; subst; auto; contradiction.
       + intro c; apply add_in_iff in c as [c | c]; auto.
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

(** *** Shift *)

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

Lemma shift_find_spec_3 : forall lb k r V V',
  lb ⊩ᵣ r -> In r V ->
  find r V = find r V' -> find r (shift lb k V) = find r (shift lb k V').
Proof.
  intros. destruct H0 as [v HfV]; apply find_1 in HfV.
  apply shift_find_spec with (lb := lb) (k := k) in HfV as HfV1.
  rewrite H1 in HfV. 
  apply shift_find_spec with (lb := lb) (k := k) in HfV as HfV2.
  rewrite Resource.shift_valid_refl in *; auto. now rewrite HfV1, HfV2. 
Qed.

Lemma shift_find_e_spec_1 : forall lb k r v V,
  find r (shift lb k V) = Some v -> 
  (exists r', r = ([⧐ᵣ lb ≤ k] r')) /\ exists v', RReal.eq v (RReal.shift lb k v').
Proof.
  intros.
  assert (In r (shift lb k V)). { now exists v; apply find_2. }
  split.
  - now apply shift_in_e_spec in H0.
  - apply shift_in_e_spec in H0; destruct H0; subst. 
    eapply shift_find_e_spec; eauto. 
Qed.


(** *** Halts *)

Lemma halts_add_spec : forall m k x v,
  (Evaluation.halts k (RReal.extract v)) /\ halts k m -> halts k (add x v m).
Proof.
  intros m k x v [Hltv Hltm]; unfold halts; intros r v' Hfi.
  rewrite add_o in Hfi; destruct (Resource.eq_dec x r); subst; inversion Hfi; subst; auto.
  apply Hltm in Hfi; auto.
Qed.

Lemma halts_weakening : forall k k' t, k <= k' -> halts k t -> halts k' (shift k (k' - k) t).
Proof.
  intros k k' t Hle Hlt. unfold halts in *; intros r v HfV.
  apply shift_find_e_spec_1 in HfV as HI. destruct HI as [[r' Heqr'] [v' Heqv']]; subst.
  rewrite Heqv' in *; clear Heqv'; rewrite <- shift_find_spec in HfV.
  apply Hlt in HfV.
  destruct v,v'; simpl in *; apply Evaluation.halts_weakening; auto.
Qed.

Lemma halts_weakening_1 : 
  forall k k' t, halts k t -> halts (k + k') (shift k k' t).
Proof.
  intros k k' t Hlt. 
  replace (shift k k' t) with (shift k ((k + k') - k) t) by (f_equal; lia).
  apply halts_weakening; auto; lia.
Qed.


Lemma max_key_wh_spec : forall (m : t) v v',
  max_key (add (S (S (max_key m))) v (add (S (max_key m)) v' m)) = S (S (max_key m)).
Proof.
  intros. assert (~In (S (max_key m)) m) by (apply max_key_notin_spec; lia).
  assert (~In (S (S (max_key m))) (add (S (max_key m)) v' m)).
  - apply max_key_notin_spec. rewrite max_key_add_spec_1; auto; lia.
  - rewrite max_key_add_spec_1; auto. rewrite max_key_add_spec_1; auto.
Qed.

Lemma new_key_wh_spec m v v' :
  new_key (add (S (new_key m)) v 
          (add (new_key m) (RReal.shift (new_key m) 2 v') 
                                      (shift (new_key m) 2 m))) = S (S (new_key m)).
Proof.
  rewrite new_key_add_spec_1; auto.
  + apply new_key_notin_spec; rewrite new_key_add_spec_1; auto.
    ++ apply new_key_notin_spec; rewrite shift_new_spec; auto.
    ++ rewrite shift_new_spec; auto.
  + rewrite new_key_add_spec_1; auto.
    ++ apply new_key_notin_spec; rewrite shift_new_spec; auto.
    ++ rewrite shift_new_spec; auto.
Qed.

(** *** Morphism *)
*)

#[global] 
Instance in_rreals : 
  Proper (Logic.eq ==> eq ==> iff) In.
Proof.
  repeat red; intros; split; intros;
  apply Equal_Eqdom in H0; eapply In_m in H0; eauto;
  apply H0; eauto. 
Qed.

#[global] 
Instance find_rreals : Proper (Logic.eq ==> eq ==> Logic.eq) find.
Proof. repeat red; intros; subst. now rewrite H0. Qed.

#[global] 
Instance Empty_rreals : Proper (eq ==> iff) Empty.
Proof. red; red; intros; now apply Empty_eq_spec. Qed.

#[export] 
Instance Add_rreals : 
Proper (Resource.eq ==> RReal.eq ==> eq ==> eq ==> iff) (@Add RReal.t).
Proof. 
  red; red; red; red; red; intros. apply RReal.eq_leibniz in H0; subst.
  rewrite H. unfold Add in *. rewrite H1; rewrite H2. split; intros; auto.
Qed.

#[global] 
Instance add_rreals : 
Proper (Resource.eq ==> RReal.eq ==> RReals.eq ==> RReals.eq) 
                                                          (@add RReal.t).
Proof. 
 red; red; red; red; red; intros; subst; apply RReal.eq_leibniz in H0; subst.
 rewrite H1; now rewrite H. 
Qed. 

#[global] 
Instance Submap_env : 
  Proper (RReals.eq ==> RReals.eq ==> iff) RReals.Submap.
Proof. 
  repeat red; intros; split; intros.
  - rewrite RReals.Submap_eq_left_spec in H1; eauto.
    rewrite RReals.Submap_eq_right_spec in H1; eauto.
  - rewrite <- RReals.Submap_eq_left_spec in H1; eauto.
    rewrite <- RReals.Submap_eq_right_spec in H1; eauto.
Qed.

End RReals.


(** *** Scope and Notations *)

Declare Scope rreals_scope.
Delimit Scope rreals_scope with rf.

Definition 𝐅 := RReals.t.

Infix "⊆ᵣₔ" := RReals.Submap (at level 20, no associativity). 
Infix "∈ᵣₔ" := RReals.Raw.In (at level 20, no associativity). 
Notation "r '∉ᵣₔ' Re" := (~ (RReals.Raw.In r Re)) (at level 20, 
                                                                        no associativity). 
Notation "∅ᵣₔ" := RReals.Raw.empty (at level 20, no associativity). 
Notation "'isEmptyᵣₔ(' Re ')'" := (RReals.Empty Re) (at level 20, no associativity). 
Notation "'Addᵣₔ'" := (RReals.Add) (at level 20, no associativity). 
Notation "R '⌊' x '⌋ᵣₔ'"  := (RReals.Raw.find x R) (at level 15, x constr).
Notation "'maxᵣₔ(' R ')'"  := (RReals.Ext.max_key R) (at level 15).
Notation "⌈ x ⤆ v '⌉ᵣₔ' R"  := (RReals.Raw.add x v R) (at level 15, 
                                                                          x constr, v constr).
Notation "R ⌈ x ⩦ v '⌉ᵣₔ'"  := (RReals.Raw.find x R = Some v) (at level 15, 
                                                                                  x constr, 
                                                                                  v constr).
Notation "R ⌈ x ⩦ ⊥ '⌉ᵣₔ'"  := (RReals.Raw.find x R = None) (at level 15, 
                                                                                    x constr).

Infix "=" := RReals.eq : rreals_scope.

Notation "V '⁺ᵣₔ'" := (RReals.Ext.new_key V) (at level 16).

Notation "'[⧐ᵣₔ' lb '≤' k ']' t" := (RReals.shift lb k t) (at level 45, 
                                                                      right associativity).
Infix "⊩ᵣₔ" := RReals.valid (at level 20, no associativity).

#[global]
Instance eq_equiv_re : Equivalence RReals.eq.
Proof. apply RReals.Equal_equiv. Qed.

#[global] Instance max_rreals : Proper (RReals.eq ==> Logic.eq) (RReals.Ext.max_key).
          Proof. apply RReals.Ext.max_key_eq. Qed.

#[global] Instance new_rreals : Proper (RReals.eq ==> Logic.eq) (RReals.Ext.new_key).
          Proof. apply RReals.Ext.new_key_eq. Qed.

#[global] 
Instance in_rreals : 
  Proper (Logic.eq ==> RReals.eq ==> iff) (RReals.Raw.In).
Proof. apply RReals.in_rreals. Qed.

#[global] 
Instance find_rreals : Proper (Logic.eq ==> RReals.eq ==> Logic.eq) 
                                                      (RReals.Raw.find).
Proof. apply RReals.find_rreals. Qed.

#[global] 
Instance Empty_rreals : Proper (RReals.eq ==> iff) (RReals.Empty).
Proof. apply RReals.Empty_rreals. Qed.

#[global] 
Instance Add_rreals : 
Proper (Resource.eq ==> RReal.eq ==> RReals.eq ==> RReals.eq ==> iff) 
                                                  (@RReals.Add RReal.t).
Proof. apply RReals.Add_rreals. Qed. 

#[global] 
Instance add_rreals : 
Proper (Resource.eq ==> RReal.eq ==> RReals.eq ==> RReals.eq) 
                                                          (@RReals.Raw.add RReal.t).
Proof. apply RReals.add_rreals. Qed. 

#[global] 
Instance Submap_env : 
  Proper (RReals.eq ==> RReals.eq ==> iff) RReals.Submap.
Proof. apply RReals.Submap_env. Qed.

#[global] 
Instance Submap_env_po : PreOrder RReals.Submap.
Proof. apply RReals.Submap_po. Qed. 

#[global] 
Instance valid_rreals : Proper (Logic.eq ==> RReals.eq ==> iff) RReals.valid.
Proof. apply RReals.valid_eq. Qed.

#[global] 
Instance shift_rreals : 
  Proper (Logic.eq ==> Logic.eq ==> RReals.eq ==> RReals.eq) RReals.shift.
Proof. apply RReals.shift_eq. Qed.

