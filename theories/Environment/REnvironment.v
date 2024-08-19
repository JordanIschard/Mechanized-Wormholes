From Coq Require Import Lia Arith.PeanoNat Classical_Prop.
From Mecha Require Import Resource Resources Term Cell.
From Mecha Require ET_Definition ET_Props.
From DeBrLevel Require Import LevelInterface MapLevelInterface MapLevel MapExtInterface 
               MapExt.
From MMaps Require Import MMaps.
Import ResourceNotations TermNotations CellNotations 
       ResourcesNotations SetNotations.



(** * Environment - Resource Environment

  The functional transition requires two environments. The first one, defined here, is the
  resource environment. It maps resources to cells. 

*)
Module REnvironment <: IsLvlET.

Include MapLvlD.MakeLvlMapLVLD Cell.
Import Raw Ext.
Open Scope cell_scope.
Open Scope term_scope.

(** ** Definition *)

(** *** ForAll property

  MMaps does not have a 'forall' property, consequently we define it.
*)
Definition For_all (P : resource -> Cell.t -> Prop) (V : REnvironment.t) := 
  forall r v, find r V = Some v -> P r v. 

(** *** Create an environment from a list

  An initial environment can be created from a list of terms.
*)

(** **** Adding new value *)
Definition add_new V v := 
    add (new_key V) ([⧐ (new_key V) – 1 ] ⩽ v … ⩾) (shift (new_key V) 1 V).

Definition add_new_revert v V := add_new V v. 

Definition env_from_list_gen (V : REnvironment.t) (l : list Λ) := 
  List.fold_left add_new l V.

Definition env_from_list := env_from_list_gen empty.

(** *** Create a list from an environment *)

Definition env_to_list (V : REnvironment.t) : list (option Λ) :=
  List.map (fun x =>  match (find x V) with
                        | Some (⩽ … v ⩾) => Some v
                        | Some _ => None
                        | None   => None
                      end) (seq 0 (max_key V)).

(** *** Create an environment from a set

  An initial environment can be created from a set of resources with
  only unit terms in it.
*)

Definition init_env_from_set (rs : resources) (V : REnvironment.t) :=
  Resources.St.fold (fun r acc => add r (⩽ unit … ⩾) acc) rs V.

(** *** Halts 

  An environment has the halting property if and only if each term in it halts. 
*)

Definition halts (k : Lvl.t) (V : REnvironment.t) := forall (r : resource) (v : 𝑣), 
 find r V = Some v -> ET_Definition.halts k (Cell.extract v).

(** *** To be used or not to be *)

Definition   used r (V : REnvironment.t) : Prop := exists v, Logic.eq (find r V) (Some (⩽ … v ⩾)).
Definition unused r (V : REnvironment.t) : Prop := exists v, Logic.eq (find r V) (Some (⩽ v … ⩾)).

(** ** [add_new] property *)

Lemma add_new_new_spec : forall V v,
 new_key (add_new_revert v V) = S (new_key V).
Proof.
  unfold add_new_revert, add_new; intros.
  rewrite new_key_add_ge_spec; auto.
  - apply shift_new_notin_spec; lia.
  - rewrite shift_new_spec; lia.
Qed.

Lemma add_new_in_iff : forall V v r,
  In r (add_new_revert v V) <-> r = (new_key V) \/ In r V.
Proof. 
  split; intros; unfold add_new_revert,add_new in *.
  - rewrite add_in_iff in H; destruct H; auto.
    right. apply new_key_in_spec in H as H'.
    rewrite shift_new_spec in H'; auto.
    rewrite shift_in_iff with (lb := (new_key V)) (k := 1).
    rewrite Resource.shift_valid_refl; auto.
  - destruct H; rewrite add_in_iff; subst; auto.
    right. apply new_key_in_spec in H as H'.
    rewrite shift_in_iff with (lb := (new_key V)) (k := 1) in H.
    rewrite Resource.shift_valid_refl in H; auto.
Qed.

Lemma add_new_unused_spec : forall r x V,
  unused r V -> unused r (add_new_revert x V).
Proof.
  intros; unfold add_new_revert,add_new.
  destruct (Resource.eq_dec r (new_key V)); subst.
  - simpl. exists <[[⧐ {new_key V} – 1] x]>; rewrite add_eq_o; auto.
  - destruct H. exists <[[⧐ {new_key V} – 1] x0]>. rewrite add_neq_o; auto.
    assert (In r V). { exists (⩽ x0 … ⩾). now apply find_2. }
    apply new_key_in_spec in H0. rewrite shift_find_iff in H;
    rewrite Resource.shift_valid_refl in H; eauto.
Qed.

Lemma add_new_find_eq : forall V x,
  find (new_key V) (add_new_revert x V) = Some (⩽ [⧐ {new_key V} – 1] x … ⩾).
Proof. unfold add_new_revert, add_new; intros. rewrite add_eq_o; auto. Qed.

(** ** [env_from_list] property *)

Lemma env_from_list_new_spec : forall l V,
  (length l) + new_key V = new_key (env_from_list_gen V l).
Proof.
  intros; unfold env_from_list_gen; rewrite <- fold_left_rev_right. 
  fold add_new_revert. revert V.
  induction l using rev_ind; intro; simpl; auto.
  rewrite rev_unit; simpl. rewrite app_length; simpl.
  rewrite add_new_new_spec; rewrite <- IHl; lia.
Qed.

Lemma env_from_list_keys_spec : forall l V r,
  In r (env_from_list_gen V l) -> ((new_key (env_from_list_gen V l)) ⊩ r)%r.
Proof.
  intros; unfold env_from_list_gen in *; rewrite <- fold_left_rev_right in *.
  fold add_new_revert in *. revert V r H.
  induction l using rev_ind; intros; simpl in *.
  - now apply new_key_in_spec.
  - rewrite rev_unit in *; simpl in *; 
    rewrite add_new_new_spec.
    rewrite add_new_in_iff in H; destruct H; subst.
    -- unfold Resource.valid; lia.
    -- apply IHl in H. apply Resource.valid_weakening 
       with (k := new_key (fold_right add_new_revert V (List.rev l))); auto.
Qed.

Lemma env_from_list_gen_unused : forall l V,
  (forall r, In r V -> unused r V) ->
  forall r, In r (env_from_list_gen V l) -> unused r (env_from_list_gen V l).
Proof.
  intros; unfold env_from_list_gen in *; rewrite <- fold_left_rev_right in *.
  fold add_new_revert in *. revert V r H H0.
  induction l using rev_ind; intros V r H HIn; simpl in *; auto.
  rewrite rev_unit in *; simpl in *.
  rewrite add_new_in_iff in HIn. destruct HIn; subst.
  - exists (Term.shift (new_key (fold_right add_new_revert V (List.rev l))) 1 x).
    apply add_new_find_eq.
  - apply IHl in H0 as H0'; auto. now apply add_new_unused_spec.
Qed.

Lemma env_from_list_Forall_unused : forall l V,
  For_all (fun _ v => Cell.unused v) V ->
  For_all (fun _ v => Cell.unused v) (env_from_list_gen V l).
Proof.
  unfold For_all; intros. assert (In r (env_from_list_gen V l)).
  { exists v; now apply find_2. }
  apply env_from_list_gen_unused in H1.
  - destruct H1. rewrite H0 in H1; now inversion H1.
  - intros. destruct H2. apply find_1 in H2. apply H in H2 as H2'.
    destruct x eqn:Heq.
    -- now exists λ.
    -- contradiction.
Qed. 

Corollary env_from_list_unused : forall l,
  forall r, In r (env_from_list l) -> unused r (env_from_list l).
Proof. 
  intros; unfold env_from_list in *; 
  apply env_from_list_gen_unused; auto.
  intros; inversion H0; inversion H1.
Qed.

(** ** [env_from_set] property *)
Section envFromset.


#[export] Instance proper_init_env_from_set : 
  Proper (Logic.eq ==> eq ==> eq)
  (fun r (acc : REnvironment.t) => add r (⩽ unit … ⩾) acc).
Proof. do 3 red; intros; subst. intro z; now rewrite H0. Qed.

Lemma transpose_init_env_from_set :
  SetoidList.transpose REnvironment.eq
  (fun r (acc : REnvironment.t) => add r (⩽ unit … ⩾) acc).
Proof.
  red; intros. destruct (Resource.eq_dec x y); subst.
  - reflexivity.
  - rewrite REnvironment.add_add_2; auto; reflexivity.
Qed.

#[local] Hint Resolve proper_init_env_from_set transpose_init_env_from_set : core.
Import Resources.

Lemma init_env_from_set_unused : forall rs V,
  forall r, (r ∈ rs)%s -> unused r (init_env_from_set rs V).
Proof.
  intro rs; induction rs using St.set_induction; intros V r HIn.
  - unfold Empty in H; exfalso; now apply (H r).
  - apply St.Add_inv in H0; subst. rewrite St.add_spec in HIn; 
    destruct HIn as [Heq | HIn]; subst.
    -- exists <[unit]>; unfold init_env_from_set; 
       rewrite St.fold_add; auto.
       rewrite add_eq_o; auto.
    -- destruct (Resource.eq_dec x r); subst.
       + exists <[unit]>; unfold init_env_from_set.
         rewrite St.fold_add; auto.
         rewrite add_eq_o; auto.
       + apply IHrs1 with (V := V) in HIn.
         destruct HIn. exists x0.
         unfold init_env_from_set; 
         rewrite St.fold_add; auto; 
         rewrite add_neq_o; auto.
Qed.

Lemma init_env_from_set_find_spec : forall rs V r v,
  find r (init_env_from_set rs V) = Some v -> (r ∈ rs)%s \/ find r V = Some v.
Proof.
  intros rs; induction rs using St.set_induction; intros.
  - unfold init_env_from_set in *. apply St.empty_is_empty_1 in H; 
    apply eq_leibniz in H; subst. rewrite St.fold_empty in H0; auto.
  - unfold init_env_from_set in H1. apply St.Add_inv in H0; subst. 
    rewrite St.fold_add in H1; eauto.
    rewrite add_o in H1. destruct (Resource.eq_dec x r); subst.
    -- inversion H1. left. rewrite St.add_spec; now left.
    -- apply IHrs1 in H1; destruct H1; auto.
       left; rewrite St.add_spec; now right.
Qed. 

Lemma init_env_from_set_in_iff : forall rs V r,
  In r (init_env_from_set rs V) <-> (r ∈ rs)%s \/ In r V.
Proof.
  intros rs; induction rs using St.set_induction; intros.
  - split; unfold init_env_from_set in *; intros.
    -- apply St.empty_is_empty_1 in H; 
       apply eq_leibniz in H; subst. rewrite St.fold_empty in H0; auto.
    -- destruct H0.
       + exfalso. now apply (H r).
       + apply St.empty_is_empty_1 in H; 
         apply eq_leibniz in H; subst. rewrite St.fold_empty; auto.
  - unfold init_env_from_set. 
    apply St.Add_inv in H0; subst. split; intros.
    -- rewrite St.fold_add in H0; eauto.
       rewrite add_in_iff in H0; destruct H0; subst.
       + left. rewrite St.add_spec; now left.
       + apply IHrs1 in H0; destruct H0; auto.
         left; rewrite St.add_spec; now right.
    -- destruct H0.
       + rewrite St.fold_add; eauto.
         rewrite St.add_spec in H0; destruct H0; subst.
         ++ rewrite add_in_iff; now left.
         ++ rewrite add_in_iff; right.
            eapply IHrs1; now left.
       + rewrite St.fold_add; eauto.
         destruct (Resource.eq_dec x r); subst.
         ++ rewrite add_in_iff; now left.
         ++ rewrite add_in_iff; right.
            eapply IHrs1; now right.
Qed. 
       
Lemma init_env_from_set_Forall_unused : forall rs V,
  For_all (fun _ v => Cell.unused v) V ->
  For_all (fun _ v => Cell.unused v) (init_env_from_set rs V).
Proof.
  unfold For_all in *; intros.
  apply init_env_from_set_find_spec in H0 as H0'; destruct H0'; auto.
  - eapply init_env_from_set_unused in H1; eauto.
    destruct H1; rewrite H0 in H1; inversion H1. now simpl.
  - eapply H; eauto.
Qed.

End envFromset.

(** *** [valid] property *)

Lemma valid_wh_spec : forall m v v',
  valid (new_key m) m -> ((new_key m) ⊩ v)%cl -> ((new_key m) ⊩ v')%cl -> 
  valid (S (S (new_key m))) (add (S (new_key m)) v (add (new_key m) v' m)).
Proof.
  intros. apply valid_add_notin_spec.
  - rewrite add_in_iff; intro. destruct H2; try lia.
    apply new_key_notin_spec in H2; auto.
  - split. 
    -- unfold Resource.valid; lia.
    -- split.
      * apply Cell.valid_weakening with (k := new_key m); auto.
      * apply valid_add_notin_spec.
        ** apply new_key_notin_spec; lia.
        ** split.
            + unfold Resource.valid; lia.
            + split.
              ++ apply Cell.valid_weakening with (k := new_key m); auto.
              ++ apply valid_weakening with (k := new_key m); auto.
Qed.

Lemma valid_wh_spec_1 : forall m v v',
  valid (new_key m) m -> ((new_key m) ⊩ v)%cl -> ((new_key m) ⊩ v')%cl -> 
  valid (S (S (new_key m))) (add (S (new_key m)) v 
                              (add (new_key m) (Cell.shift (new_key m) 2 v') (shift (new_key m) 2 m))).
Proof.
  intros. apply valid_add_notin_spec.
  - apply new_key_notin_spec; rewrite new_key_add_ge_spec; auto.
    * apply new_key_notin_spec; rewrite shift_new_spec; auto.
    * rewrite shift_new_spec; auto.
  - repeat split. 
    -- unfold Resource.valid; lia.
    -- apply Cell.valid_weakening with (k := new_key m); auto.
    -- apply valid_add_notin_spec.
       * apply new_key_notin_spec; auto; rewrite shift_new_spec; auto.
       * repeat split.
         + unfold Resource.valid; lia.
         + replace (S (S (new_key m))) with ((new_key m) + 2) by lia. 
           now apply Cell.shift_preserves_valid_1.
         + replace (S (S (new_key m))) with ((new_key m) + 2) by lia. 
           now apply shift_preserves_valid_1.  
Qed.

Lemma valid_update_spec : forall m r v k,
  In r m -> valid k m -> Cell.valid k v -> valid k (add r v m).
Proof.
  intro m; induction m using map_induction; intros r v k HIn Hvm Hvv.
  - unfold Empty in *; exfalso.
    destruct HIn as [z HM]; now apply (H r z).
  - rewrite <- valid_Add_iff in Hvm; eauto; destruct Hvm as [Hvx [Hve Hvm]].
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

(** *** [shift] property *)


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
  In r (shift lb k V) -> exists r', Logic.eq r ([⧐ lb – k] r')%r.
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
  (lb ⊩ r)%r -> In r V ->
  find r V = find r V' -> find r (shift lb k V) = find r (shift lb k V').
Proof.
  intros. destruct H0 as [v HfV]; apply find_1 in HfV.
  apply shift_find_iff with (lb := lb) (k := k) in HfV as HfV1.
  rewrite H1 in HfV. 
  apply shift_find_iff with (lb := lb) (k := k) in HfV as HfV2.
  rewrite Resource.shift_valid_refl in *; auto. now rewrite HfV1, HfV2. 
Qed.

Lemma shift_find_e_spec_1 : forall lb k r v V,
  find r (shift lb k V) = Some v -> 
  (exists r', Logic.eq r ([⧐ lb – k] r')%r) /\ exists v', (v = [⧐ lb – k] v')%cl.
Proof.
  intros.
  assert (In r (shift lb k V)). { now exists v; apply find_2. }
  split.
  - now apply shift_in_e_spec in H0.
  - apply shift_in_e_spec in H0; destruct H0; subst. 
    eapply shift_find_e_spec; eauto. 
Qed.

(** *** [halts] property *)

#[export] Hint Resolve proper_init_env_from_set transpose_init_env_from_set : core.

Lemma halts_add_spec : forall m k x v,
  (ET_Definition.halts k (Cell.extract v)) /\ halts k m -> halts k (add x v m).
Proof.
  intros m k x v [Hltv Hltm]; unfold halts; intros r v' Hfi.
  rewrite add_o in Hfi; destruct (Resource.eq_dec x r); subst; inversion Hfi; subst; auto.
  apply Hltm in Hfi; auto.
Qed.

Lemma halts_init_env_from_set : forall k W V,
  halts k V -> halts k (init_env_from_set W V).
Proof.
  intros k W; induction W using Resources.St.set_induction; 
  intros.
  - unfold init_env_from_set.
    apply Resources.St.empty_is_empty_1 in H. 
    apply Resources.eq_leibniz in H. 
    rewrite H. now rewrite Resources.St.fold_empty.
  - unfold init_env_from_set in *.
    apply Resources.St.Add_inv in H0. subst.
    unfold halts; intros r v Hfi.
    rewrite Resources.St.fold_add in Hfi; auto.
    destruct (Resource.eq_dec x r); subst.
    -- rewrite REnvironment.add_eq_o in Hfi; auto.
       inversion Hfi; subst; simpl. exists <[unit]>.
       split; auto. apply rt1n_refl.
    -- unfold halts in *. 
       rewrite REnvironment.add_neq_o in Hfi; auto.
       apply (IHW1 V) with (r := r); auto.
Qed.

Lemma halts_weakening : forall k k' t, k <= k' -> halts k t -> halts k' (shift k (k' - k) t).
Proof.
  intros k k' t Hle Hlt. unfold halts in *; intros r v HfV.
  apply shift_find_e_spec_1 in HfV as HI. destruct HI as [[r' Heqr'] [v' Heqv']]; subst.
  apply Cell.eq_leibniz in Heqv'; subst.
  rewrite <- shift_find_iff in HfV; destruct v'; simpl in *;
  apply ET_Props.halts_weakening; auto;
  apply Hlt in HfV; now simpl in *.
Qed.

Lemma halts_weakening_1 : 
  forall k k' t, halts k t -> halts (k + k') (shift k k' t).
Proof.
  intros k k' t Hlt. 
  replace (shift k k' t) with (shift k ((k + k') - k) t) by (f_equal; lia).
  apply halts_weakening; auto; lia.
Qed.

(** *** [new_key] property *)

Lemma max_key_wh_spec : forall (m : t) v v',
  max_key (add (S (S (max_key m))) v (add (S (max_key m)) v' m)) = S (S (max_key m)).
Proof.
  intros. assert (~In (S (max_key m)) m) by (apply max_key_notin_spec; lia).
  assert (~In (S (S (max_key m))) (add (S (max_key m)) v' m)).
  - apply max_key_notin_spec. rewrite max_key_add_ge_spec; auto; lia.
  - repeat rewrite max_key_add_ge_spec; auto.
Qed.

Lemma new_key_wh_spec m v v' :
  new_key (add (S (new_key m)) v 
          (add (new_key m) (Cell.shift (new_key m) 2 v') 
                                      (shift (new_key m) 2 m))) = S (S (new_key m)).
Proof.
  rewrite new_key_add_ge_spec; auto.
  + apply new_key_notin_spec; rewrite new_key_add_ge_spec; auto.
    ++ apply new_key_notin_spec; rewrite shift_new_spec; auto.
    ++ rewrite shift_new_spec; auto.
  + rewrite new_key_add_ge_spec; auto.
    ++ apply new_key_notin_spec; rewrite shift_new_spec; auto.
    ++ rewrite shift_new_spec; auto.
Qed.

(** *** Morphism *)

#[export] Instance in_renv : Proper (Logic.eq ==> eq ==> iff) In.
Proof.
  repeat red; intros; split; intros;
  apply Equal_Eqdom in H0; eapply In_m in H0; eauto;
  apply H0; eauto. 
Qed.

#[export] Instance find_renv : Proper (Logic.eq ==> eq ==> Logic.eq) find := _.

#[export] Instance Add_renv : 
Proper (Resource.eq ==> Cell.eq ==> eq ==> eq ==> iff) (@Add Cell.t).
Proof. 
  do 5 red; intros. apply Cell.eq_leibniz in H0; subst.
  rewrite H. unfold Add in *. rewrite H1; rewrite H2. split; intros; auto.
Qed.

#[export] Instance add_renv : 
Proper (Resource.eq ==> Cell.eq ==> REnvironment.eq ==> REnvironment.eq) 
                                                          (@add Cell.t).
Proof.
  do 5 red; intros; subst; apply Cell.eq_leibniz in H0; subst.
  rewrite H1; now rewrite H. 
Qed. 

#[export] Instance unused_renv :
  Proper (Logic.eq ==> REnvironment.eq ==> iff) REnvironment.unused.
Proof. 
  repeat red; intros; subst; split; intros.
  - destruct H. exists x. now rewrite <- H0.
  - destruct H. exists x. now rewrite H0.
Qed.

#[export] Instance halts_renv :
  Proper (Logic.eq ==> REnvironment.eq ==> iff) halts. 
Proof.
  repeat red; intros; subst; split; intros.
  - unfold halts; intros. rewrite <- H0 in H1.
    now apply (H r v).
  - unfold halts; intros. rewrite H0 in H1.
    now apply (H r v).
Qed.

End REnvironment.

(** * Notation - Resource Environment *)

Module REnvironmentNotations.

(** ** Scope *)
Declare Scope renvironment_scope.
Delimit Scope renvironment_scope with re.

(** ** Notation *)
Definition 𝐕 := REnvironment.t.

Infix "⊆" := REnvironment.Submap (at level 60, no associativity) : renvironment_scope. 
Infix "∈" := REnvironment.Raw.In (at level 60, no associativity) : renvironment_scope. 
Notation "r '∉' Re" := (~ (REnvironment.Raw.In r Re)) (at level 75, 
                                                      no associativity) : renvironment_scope. 
Notation "∅" := REnvironment.Raw.empty (at level 0, no associativity) : renvironment_scope. 
Notation "'isEmpty(' Re ')'" := (REnvironment.Empty Re) (at level 20, no associativity) : renvironment_scope. 
Notation "'Add'" := (REnvironment.Add) (at level 20, no associativity) : renvironment_scope. 
Notation "R '⌊' x '⌋'"  := (REnvironment.Raw.find x R) (at level 15, x constr) : renvironment_scope.
Notation "'max(' R ')'"  := (REnvironment.Ext.max_key R) (at level 15) : renvironment_scope.
Notation "⌈ x ⤆ v '⌉' R"  := (REnvironment.Raw.add x v R) (at level 15, 
                                                            x constr, v constr) : renvironment_scope.

Infix "=" := REnvironment.eq : renvironment_scope.

Notation "V '⁺'" := (REnvironment.Ext.new_key V) (at level 16) : renvironment_scope.

Notation "'[⧐' lb '–' k ']' t" := (REnvironment.shift lb k t) (at level 65, 
                                                                right associativity) : renvironment_scope.
Infix "⊩" := REnvironment.valid (at level 20, no associativity) : renvironment_scope.

(** ** Morphisms *)


Import REnvironment.

#[export] Instance equiv_renv : Equivalence REnvironment.eq := _.
#[export] Instance max_renv : Proper (eq ==> Logic.eq) (Ext.max_key) := Ext.max_key_eq.
#[export] Instance new_renv : Proper (eq ==> Logic.eq) (Ext.new_key) := Ext.new_key_eq. 
#[export] Instance in_renv :  Proper (Logic.eq ==> eq ==> iff) (Raw.In) := _.
#[export] Instance find_renv : Proper (Logic.eq ==> eq ==> Logic.eq) (Raw.find) := _.
#[export] Instance Empty_renv : Proper (eq ==> iff) (Empty) := _.
#[export] Instance Add_renv : 
  Proper (Resource.eq ==> Cell.eq ==> eq ==> eq ==> iff) (@REnvironment.Add Cell.t) := _.
#[export] Instance add_renv : 
  Proper (Resource.eq ==> Cell.eq ==> REnvironment.eq ==> REnvironment.eq) (@Raw.add Cell.t) := _.
#[export] Instance Submap_env : Proper (eq ==> eq ==> iff) Submap := _.
#[export] Instance Submap_env_po : PreOrder Submap := Submap_po.
#[export] Instance valid_renv : Proper (Logic.eq ==> eq ==> iff) valid := _.
#[export] Instance shift_renv : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.
#[export] Instance halts_renv : Proper (Logic.eq ==> eq ==> iff) halts := _. 
#[export] Instance unused_renv : Proper (Logic.eq ==> eq ==> iff) unused := _.

End REnvironmentNotations.