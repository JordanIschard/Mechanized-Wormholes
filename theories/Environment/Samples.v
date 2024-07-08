From Mecha Require Import Term ET_Definition Resource REnvironment Cell Sample.
From Coq Require Import Lia.
From DeBrLevel Require Import LevelInterface MapLevelInterface MapLevel MapExtInterface MapExt.
From MMaps Require Import MMaps.
Import ResourceNotations TermNotations REnvironmentNotations CellNotations.

(** * Environment - I/O Sampling 

TODO

*)
Module Samples <: IsLvlET.
Include MapLvlD.MakeLvlMapLVLD Sample.

Import Raw Ext.
Open Scope renvironment_scope.

(** ** Definition *)

Definition nexts_func x v V := ⌈x ⤆ (Cell.inp (Sample.next v))⌉ V.

Definition nexts_func_1 v := (Cell.inp (Sample.next v)).

Definition nexts (fl : Samples.t) : REnvironment.t := 
  fold nexts_func fl ∅.

Definition puts_func V x v fl := 
  match V⌊x⌋ with 
    | Some (⩽ … v' ⩾) =>  add x (Sample.put (Some v') v) fl
    |  _ => add x (Sample.put None v) fl 
  end.

Definition puts_func_1 V x v :=
  match V⌊x⌋ with 
    | Some (⩽ … v' ⩾) =>  (Sample.put (Some v') v)
    |  _ => (Sample.put None v) 
  end.

Definition puts (Vout : REnvironment.t) (fl : Samples.t) : Samples.t :=
  fold (puts_func Vout) fl empty.

Definition halts (k : nat) (fl : Samples.t) := forall (r : resource) v, 
 find r fl = Some v -> Sample.halts k v.

Hint Resolve REnvironment.eq_equiv : core.

(** ** [nexts] property *)

#[export]
Instance nexts_prop : 
  Proper (Logic.eq ==> Logic.eq ==> REnvironment.eq ==> REnvironment.eq) nexts_func.
Proof.
  repeat red; intros; subst. unfold nexts_func.
  destruct (Resource.eq_dec y y2); subst.
  - rewrite REnvironment.add_eq_o; auto.
    rewrite REnvironment.add_eq_o; auto.
  - rewrite REnvironment.add_neq_o; auto.
    rewrite REnvironment.add_neq_o; auto.
Qed.

Lemma nexts_diamond : Diamond REnvironment.eq nexts_func.
Proof.
 repeat red; intros. rewrite <- H0. rewrite <- H1.
 unfold nexts_func. rewrite REnvironment.OP.P.add_add_2; auto.
Qed.

#[export] Hint Resolve nexts_prop nexts_diamond : core.

Lemma nexts_Empty t : Empty t -> ((nexts t) = ∅).
Proof. 
  intros; unfold nexts. rewrite fold_Empty; auto.
Qed.

Lemma nexts_Add_spec x v t t' : 
  ~ In x t ->
  Samples.Add x v t t' -> ((nexts t') = ⌈x ⤆ (Cell.inp (Sample.next v))⌉ (nexts t))%re.
Proof.
  intros. unfold nexts. 
  apply fold_Add with (A := REnvironment.t) (eqA := REnvironment.eq) 
                      (f := nexts_func) (i := ∅) in H0; auto.
Qed.

#[export] Instance nexts_eq : Proper (eq ==> REnvironment.eq) nexts.
Proof.
  repeat red; intros; revert y0 y H. induction x using map_induction; intros.
  - assert (Empty y). { now rewrite H0 in *. }
    rewrite nexts_Empty; auto. rewrite nexts_Empty; auto.
  - destruct (In_dec y x3).
    -- destruct i; apply find_1 in H2. rewrite <- add_id in H2.
       rewrite <- add_remove_1 in H2. assert (~ In x3 (remove x3 y)).
       { intro. rewrite remove_in_iff in H3. destruct H3. now apply H3. }
       rewrite <- H2 in H1. assert (x = e).
       { 
        apply mapsto_fun with (x := x3) (m := x2). 
        - rewrite H1. apply add_mapsto_new; auto.
        - unfold Samples.Add in H0. rewrite H0. apply add_mapsto_new; auto.
       }
       subst. assert (Samples.Add x3 e (remove x3 y) y).
       { unfold Samples.Add. now rewrite H2. }
       rewrite (nexts_Add_spec x3 e x1 x2); auto.
       rewrite (nexts_Add_spec x3 e (remove x3 y) y); auto.
       destruct (Resource.eq_dec x3 y0); subst.
       + repeat rewrite REnvironment.OP.P.add_eq_o; auto.
       + repeat rewrite REnvironment.OP.P.add_neq_o; auto.
         apply IHx1.
         unfold eq. unfold eq in H1. rewrite Equal_mapsto_iff in *; intros.
         destruct (Resource.eq_dec k x3); subst.
         ++ split; intros.
            * exfalso. apply H. now exists e0.
            * exfalso; apply H3. now exists e0.
         ++ split; intros.
            * rewrite <- add_neq_mapsto_iff; eauto.
              rewrite <- H1. unfold Samples.Add in H0. rewrite H0.
              rewrite add_neq_mapsto_iff; auto.
            * rewrite <- add_neq_mapsto_iff; eauto.
              unfold Samples.Add in H0. rewrite <- H0. rewrite H1.
              rewrite add_neq_mapsto_iff; auto.
    -- assert (Samples.Add x3 e x1 y). 
       { unfold Samples.Add in *; rewrite <- H1; assumption. }
       rewrite (nexts_Add_spec x3 e x1 x2); auto.
       rewrite (nexts_Add_spec x3 e x1 y); auto. 
Qed.

Lemma nexts_in_iff r fl : In r fl <-> r ∈ (nexts fl).
Proof.
  revert r; induction fl using map_induction; split; intros.
  - exfalso. destruct H0. now apply (H r x).
  - rewrite nexts_Empty in H0; auto. inversion H0; inversion H1.
  - destruct (Resource.eq_dec x r); subst.
    -- rewrite nexts_Add_spec; eauto. 
       rewrite REnvironment.OP.P.add_in_iff; now left.
    -- rewrite nexts_Add_spec; eauto.
       rewrite REnvironment.OP.P.add_in_iff; right.
       unfold Samples.Add in *. rewrite H0 in *.
       rewrite add_in_iff in H1; destruct H1; try (contradiction).
       now rewrite <- IHfl1.
  - destruct (Resource.eq_dec x r); subst.
    -- unfold Samples.Add in *; rewrite H0. rewrite add_in_iff; now left.
    -- rewrite nexts_Add_spec in *; eauto.
       unfold Samples.Add in *. rewrite H0 in *.
       rewrite add_in_iff; right. 
       rewrite REnvironment.OP.P.add_in_iff in H1; 
       destruct H1; try (contradiction).
       now rewrite IHfl1.
Qed. 

Lemma nexts_Empty_eq fl : Empty fl <-> REnvironment.OP.P.Empty (nexts fl).
Proof.
  split; intros HEmp.
  - apply nexts_Empty in HEmp; rewrite HEmp.
    apply empty_1.
  - intros x v. intro HMap. 
    assert (HIn: In x fl) by (now exists v).
    rewrite nexts_in_iff in HIn. destruct HIn.
    now apply (HEmp x x0).
Qed.

Lemma nexts_remove_spec x t: 
  (REnvironment.Raw.remove x (nexts t) = (nexts (remove x t)))%re.
Proof.
 revert x; induction t using map_induction; intros.
 - unfold nexts; rewrite fold_Empty; auto.
   rewrite fold_Empty; auto.
   -- apply REnvironment.OP.P.remove_id.
      intro c; inversion c; inversion H0.
   -- intro. intro; intro. 
      apply remove_mapsto_iff in H0 as [_ H0].
      apply (H x0 e H0).
 - unfold nexts.
   apply REnvironment.OP.P.Equal_mapsto_iff; split; intros.
   -- apply REnvironment.OP.P.remove_mapsto_iff in H1 as [Hneq HM].
      apply REnvironment.OP.P.find_1 in HM.
      rewrite (nexts_Add_spec x e t1 t2) in HM; auto.
      destruct (Resource.eq_dec k x); subst.
      + rewrite REnvironment.OP.P.add_eq_o in HM; auto.
        inversion HM; subst; clear HM.
        assert (Samples.Add x e (remove x0 t1) (remove x0 t2)).
        { unfold Samples.Add in *; rewrite H0. rewrite remove_add_2; auto. reflexivity. }
        {
         apply REnvironment.OP.P.find_2.
         rewrite fold_Add with (m1 := remove x0 t1); eauto.
         - unfold nexts_func; fold nexts_func.
           rewrite REnvironment.OP.P.add_eq_o; reflexivity.
         - intro. apply remove_in_iff in H2 as [_ H2]. contradiction.
        }
      + rewrite REnvironment.OP.P.add_neq_o in HM; auto.
        apply REnvironment.OP.P.find_2 in HM.
        destruct (Resource.eq_dec x x0); subst.
        ++ assert (nexts (remove x0 t2) = nexts t1)%re. 
           { 
            eapply nexts_eq.
            unfold Samples.Add,eq in *. rewrite H0.
            rewrite remove_add_1. 
            now erewrite (remove_id t1 x0).
           }
           assert (k = k) by reflexivity.
           assert (e0 = e0) by reflexivity.
           eapply (REnvironment.OP.P.MapsTo_m H2 H3 H1); eauto.
        ++ rewrite <- (REnvironment.OP.P.remove_neq_mapsto_iff) in HM; eauto.
           apply REnvironment.OP.P.find_1 in HM.
           rewrite IHt1 in HM. 
           assert (nexts (remove x0 t2) = nexts (add x e (remove x0 t1)))%re. 
           { 
            eapply nexts_eq.
            unfold Samples.Add,eq in *. rewrite H0.
            rewrite remove_add_2; auto; reflexivity.
           }
           assert (k = k) by reflexivity.
           assert (e0 = e0) by reflexivity.
           eapply (REnvironment.OP.P.MapsTo_m H2 H3 H1); eauto.
           eapply REnvironment.OP.P.find_2.
           rewrite (nexts_Add_spec x e (remove x0 t1)); eauto.
           * rewrite REnvironment.OP.P.add_neq_o; eauto.
           * intro. apply remove_in_iff in H4 as [_ H4]. contradiction.
           * unfold Samples.Add; reflexivity.
  -- destruct (Resource.eq_dec x0 k); subst.
     + exfalso.
       destruct (Resource.eq_dec k x); subst.
       ++ assert ((nexts t1) = (nexts (remove x t2)))%re.
          {
            eapply nexts_eq. 
            unfold Samples.Add in *; rewrite H0.
            rewrite remove_add_1; auto.
            symmetry; unfold eq.
            now rewrite remove_id.
          }
          assert (x = x) by reflexivity.
          assert (e0 = e0) by reflexivity.
          eapply (REnvironment.OP.P.MapsTo_m H3 H4 H2) in H1; eauto.
          rewrite nexts_in_iff in H.
          apply H. now exists e0.
       ++ assert (Samples.Add x e (remove k t1) (remove k t2)).
          { unfold Samples.Add in *; rewrite H0. rewrite remove_add_2; auto. reflexivity. }
          apply REnvironment.OP.P.find_1 in H1.
          apply (nexts_Add_spec x e) in H2.
          * rewrite H2 in H1.
            rewrite REnvironment.OP.P.add_neq_o in H1; auto.
            rewrite <- IHt1 in *.
            rewrite REnvironment.OP.P.remove_eq_o in H1; auto.
            inversion H1.
          * intro. apply remove_in_iff in H3 as [_ H3]. contradiction.
     + apply REnvironment.OP.P.remove_mapsto_iff; split; auto.
       apply REnvironment.OP.P.find_2.
       rewrite (nexts_Add_spec x e t1 t2); auto.
       destruct (Resource.eq_dec k x); subst.
       ++ rewrite REnvironment.OP.P.add_eq_o; auto; f_equal. 
          assert (Samples.Add x e (remove x0 t1) (remove x0 t2)).
          { unfold Samples.Add in *; rewrite H0. rewrite remove_add_2; auto. reflexivity. }
          {
          apply REnvironment.OP.P.find_1 in H1.
          rewrite fold_Add with (m1 := remove x0 t1) in H1; eauto.
          - unfold nexts_func in *; fold nexts_func in *.
            rewrite REnvironment.OP.P.add_eq_o in *; auto; now inversion H1.
          - intro. apply remove_in_iff in H3 as [_ H3]. contradiction.
          }
       ++ rewrite REnvironment.OP.P.add_neq_o; auto.
          apply REnvironment.OP.P.find_1.
          destruct (Resource.eq_dec x x0); subst.
          * assert (nexts (remove x0 t2) = nexts t1)%re. 
            { 
              eapply nexts_eq.
              unfold Samples.Add,eq in *. rewrite H0.
              rewrite remove_add_1. 
              now erewrite (remove_id t1 x0).
            }
            assert (k = k) by reflexivity.
            assert (e0 = e0) by reflexivity.
            eapply (REnvironment.OP.P.MapsTo_m H3 H4 H2); eauto.
          * rewrite <- (REnvironment.OP.P.remove_neq_mapsto_iff); eauto.
            apply REnvironment.OP.P.find_2.
            rewrite IHt1. 
            assert (nexts (remove x0 t2) = nexts (add x e (remove x0 t1)))%re. 
            { 
              eapply nexts_eq.
              unfold Samples.Add,eq in *. rewrite H0.
              rewrite remove_add_2; auto; reflexivity.
            }
            assert (k = k) by reflexivity.
            assert (e0 = e0) by reflexivity.
            eapply (REnvironment.OP.P.MapsTo_m H3 H4 H2) in H1; eauto.
            eapply REnvironment.OP.P.find_1 in H1.
            rewrite (nexts_Add_spec x e (remove x0 t1)) in H1; eauto.
            ** rewrite REnvironment.OP.P.add_neq_o in H1; eauto.
            ** intro. apply remove_in_iff in H5 as [_ H5]. contradiction.
            ** unfold Samples.Add; reflexivity.       
Qed.

Lemma nexts_Add_spec_1 x v t t' : 
  Samples.Add x v t t' -> ((nexts t') = ⌈x ⤆ (Cell.inp (Sample.next v))⌉ (nexts t))%re.
Proof.
  intros. destruct (In_dec t x).
  - unfold Samples.Add in *. rewrite H.
    transitivity (nexts (add x v (remove x t))).
    -- now rewrite add_remove_1.
    -- unfold nexts. rewrite fold_Add with (m1 := (remove x t)) (k := x) (e := v); eauto.
       + unfold nexts_func; fold nexts_func; simpl. intro.
         assert (fold nexts_func (remove x t) ∅ = 
                  REnvironment.Raw.remove x (fold nexts_func t ∅))%re.
         { now rewrite <- (nexts_remove_spec x t). }

         assert 
         (forall d, 
          (⌈ x ⤆ d ⌉ fold nexts_func (remove x t) ∅ = 
           ⌈ x ⤆ d ⌉ REnvironment.Raw.remove x (fold nexts_func t ∅))%re).
         { 
          intros. apply add_renv; eauto; try reflexivity.
          unfold Cell.eq; destruct d; reflexivity. 
         }
         rewrite H1.
         now rewrite REnvironment.OP.P.add_remove_1.
       + intro. apply remove_in_iff in H0 as [H0 _]. now apply H0.
       + unfold Samples.Add; reflexivity. 
  - now apply nexts_Add_spec.
Qed.

Lemma nexts_find_e_spec Fl r v :
  (nexts Fl)⌊r⌋ = Some v -> exists rf, (v = nexts_func_1 rf)%type.
Proof.
  revert r v; induction Fl using map_induction; intros.
  - apply nexts_Empty_eq in H.
    exfalso; apply (H r v).
    now apply REnvironment.OP.P.find_2.
  - rewrite nexts_Add_spec in H1; eauto.
    destruct (Resource.eq_dec x r); subst.
    -- rewrite REnvironment.OP.P.add_eq_o in H1; auto.
       inversion H1; subst; clear H1.
       now exists e; unfold nexts_func_1.
    -- rewrite REnvironment.OP.P.add_neq_o in H1; auto.
       now apply (IHFl1 r).
Qed.

Lemma nexts_find_spec Fl r rf :
  find r Fl = Some rf -> (nexts Fl)⌊r⌋ = Some (nexts_func_1 rf).
Proof.
  revert r rf; induction Fl using map_induction; intros.
  - exfalso; apply (H r rf).
    now apply find_2.
  - rewrite nexts_Add_spec in *; eauto.
    unfold Samples.Add in *. rewrite H0 in *.
    destruct (Resource.eq_dec r x); subst.
    -- rewrite add_eq_o in H1; auto; inversion H1; subst; clear H1.
       rewrite REnvironment.OP.P.add_eq_o; auto.
    -- rewrite add_neq_o in H1; auto.
       rewrite REnvironment.OP.P.add_neq_o; auto.
Qed.

Lemma nexts_unused r fl : In r fl -> REnvironment.unused r (nexts fl).
Proof.
  revert r; induction fl using map_induction; unfold REnvironment.unused; intros.
  - exfalso. destruct H0. now apply (H r x).
  - destruct H1. apply find_1 in H1. rewrite H0 in *.
    destruct (Resource.eq_dec r x); subst.
    -- rewrite add_eq_o in H1; auto. inversion H1; subst; clear H1.
       exists (Sample.next x0); rewrite nexts_Add_spec; eauto.
       rewrite REnvironment.OP.P.add_eq_o; auto.
    -- assert (In r fl1). 
       { rewrite add_neq_o in H1; auto. exists x0. now apply find_2. }
       apply IHfl1 in H2; destruct H2. exists x1.
       rewrite nexts_Add_spec; eauto.
       rewrite REnvironment.OP.P.add_neq_o; auto.
Qed.   

Lemma nexts_new_key fl : (new_key fl) = (REnvironment.Ext.new_key (nexts fl)).
Proof.
  induction fl using map_induction.
  - rewrite Ext.new_key_Empty_spec; auto. rewrite nexts_Empty; auto.
  - rewrite (nexts_Add_spec x e fl1 fl2); auto.
    unfold Samples.Add in H0. rewrite H0.
    apply (new_key_add_spec fl1 x e) in H as IH.
    rewrite nexts_in_iff in H. 
    apply (REnvironment.Ext.new_key_add_spec _ x (Cell.inp (Sample.next e))) in H as IH'.
    destruct IH as [[Hnk Hle] | [Hnk Hgt]]; 
    destruct IH' as [[Hnk' Hle'] | [Hnk' Hgt']]; try lia.
Qed.

(** ** [puts] property *)

#[export]
Instance puts_prop V : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) (puts_func V).
Proof.
  repeat red; intros; subst; unfold puts_func. destruct (V⌊y⌋); auto.
  - destruct r; auto; now rewrite H1.
  - now rewrite H1.
Qed.

Lemma puts_diamond V : Diamond Equal (puts_func V).
Proof. 
  repeat red; intros; unfold puts_func. 
  destruct (V⌊k⌋) eqn:HfV; destruct (V⌊k'⌋) eqn:HfV'.
  - destruct r,r0;
    rewrite <- H1; rewrite <- H0; unfold puts_func; 
    rewrite HfV,HfV'; now rewrite add_add_2.
  - destruct r;
    rewrite <- H1; rewrite <- H0; unfold puts_func; 
    rewrite HfV,HfV'; now rewrite add_add_2.
  - destruct r;
    rewrite <- H1; rewrite <- H0; unfold puts_func; 
    rewrite HfV,HfV'; now rewrite add_add_2.
  - rewrite <- H1; rewrite <- H0; unfold puts_func.
    rewrite HfV', HfV; now rewrite add_add_2.
Qed.

Hint Resolve puts_prop puts_diamond : core.

Lemma puts_Empty V fl : Empty fl -> eq (puts V fl) empty.
Proof.
  intros; unfold puts,eq. rewrite fold_Empty; auto; reflexivity.
Qed.

Lemma puts_Add_spec r v V fl fl' : 
  ~ In r fl -> Samples.Add r v fl fl' -> eq (puts V fl') ((puts_func V) r v (puts V fl)).
Proof. intros. unfold puts, eq. now rewrite fold_Add; eauto. Qed.

Lemma puts_Add_spec_1 r v V fl fl' : 
  ~ In r fl -> 
  Samples.Add r v fl fl' -> Samples.Add r (puts_func_1 V r v) (puts V fl) (puts V fl').
Proof.
  intros. apply puts_Add_spec with (V := V) in H0; auto.
  unfold Samples.Add. rewrite H0. unfold puts_func,puts_func_1; destruct (V⌊r⌋);
  try reflexivity.
  destruct r0; reflexivity.
Qed.

Lemma puts_Empty_iff V fl : Empty fl <-> Empty (puts V fl).
Proof.
  split; intros HEmp.
  - apply puts_Empty with (V := V) in HEmp; rewrite HEmp.
    apply empty_1.
  - revert V HEmp; induction fl using map_induction; 
    intros V HEmp; auto.
    unfold Empty in *; intros. intro. destruct (V⌊x⌋) eqn:HfV.
    -- destruct r.
       + apply (HEmp x (Sample.put None e)).
         apply find_2. rewrite puts_Add_spec; eauto. 
         unfold puts_func. rewrite HfV. now rewrite add_eq_o. 
       + apply (HEmp x (Sample.put (Some λ) e)).
         apply find_2. rewrite puts_Add_spec; eauto. 
         unfold puts_func. rewrite HfV. now rewrite add_eq_o.
    -- apply (HEmp x (Sample.put None e)).
        apply find_2. rewrite puts_Add_spec; eauto. 
        unfold puts_func. rewrite HfV. now rewrite add_eq_o.
Qed.

Lemma puts_is_empty_eq V fl : is_empty fl = is_empty (puts V fl).
Proof.
  destruct (is_empty fl) eqn:H.
  - symmetry. apply is_empty_2 in H. apply is_empty_1. 
    now apply puts_Empty_iff.
  - symmetry. apply not_true_is_false. intro.
    apply is_empty_2 in H0. rewrite <- puts_Empty_iff in H0.
    revert H. apply eq_true_false_abs. now apply is_empty_1.
Qed.

Lemma puts_In_iff r V fl : In r fl <-> In r (puts V fl).
Proof.
  revert r V; induction fl using map_induction; intros r V.
  - split; intro HIn.
    -- exfalso. destruct HIn as [v HMap]. now apply (H r v).
    -- exfalso. destruct HIn as [v HMap].
       rewrite puts_Empty_iff with (V := V) in H.
       now apply (H r v).
  - split; intro HIn.
    -- rewrite puts_Add_spec; eauto.
       unfold Samples.Add in H0. rewrite H0 in *. rewrite add_in_iff in HIn.
       destruct HIn as [Heq | HIn]; subst.
       + unfold puts_func; destruct(V⌊r⌋).
         ++ destruct r0; rewrite add_in_iff; now left.
         ++ rewrite add_in_iff; now left.
       + unfold puts_func; destruct(V⌊x⌋).
         ++ destruct r0; rewrite add_in_iff; right; now rewrite <- IHfl1.
         ++ rewrite add_in_iff; right; now rewrite <- IHfl1.
    -- rewrite puts_Add_spec in HIn; eauto.
       unfold Samples.Add in *; rewrite H0. rewrite add_in_iff.
       unfold puts_func in *. destruct(V⌊x⌋).
       ++ destruct r0; 
          apply add_in_iff in HIn as [Heq | HIn]; subst; auto;
          right; now rewrite (IHfl1 r V).
       ++ apply add_in_iff in HIn as [Heq | HIn]; subst; auto.
          right; now rewrite (IHfl1 r V).
Qed. 

Lemma puts_max_spec V fl : max_key fl = max_key (puts V fl).
Proof.
  revert V. induction fl using map_induction; intro V.
  - apply max_key_Empty_spec in H as Hmax; rewrite Hmax.
    symmetry. rewrite puts_Empty_iff with (V := V) in H.
    apply max_key_Empty_spec in H; now rewrite H.
  - apply max_key_Add_spec in H0 as HI; auto.
    destruct HI as [[Heq Hle] | [Heq Hgt]]; subst.
    -- rewrite puts_Add_spec; eauto. unfold puts_func.
       destruct (V⌊max_key fl2⌋) eqn:HfV.
       + destruct r; rewrite max_key_add_spec_1; auto;
         try (now rewrite <- IHfl1);
         now rewrite <- puts_In_iff.
       + rewrite max_key_add_spec_1; auto.
         ++ now rewrite <- puts_In_iff.
         ++ now rewrite <- IHfl1.
    -- rewrite puts_Add_spec; eauto. unfold puts_func.
       destruct (V⌊x⌋) eqn:HfV; rewrite Heq.
       + destruct r; rewrite max_key_add_spec_2; auto;
         try (now rewrite <- IHfl1);
         now rewrite <- puts_In_iff.
       + rewrite max_key_add_spec_2; auto.
         ++ now rewrite <- puts_In_iff.
         ++ now rewrite <- IHfl1.
Qed.

Lemma puts_new_spec V fl : new_key fl = new_key (puts V fl).
Proof.
  unfold new_key; destruct (is_empty fl) eqn:Hempt.
  - rewrite puts_is_empty_eq with (V := V) in Hempt.
    rewrite Hempt; reflexivity.
  - rewrite puts_is_empty_eq with (V := V) in Hempt.
    rewrite Hempt; f_equal; apply puts_max_spec.
Qed.

Lemma puts_find_spec V fl r v :
 find r fl = Some v -> find r (puts V fl) = Some (puts_func_1 V r v).
Proof.
  revert r v; induction fl using map_induction; intros r v HfFl.
  - exfalso; apply (H r v); now apply find_2.
  - rewrite puts_Add_spec; eauto. unfold Samples.Add in H0; rewrite H0 in *.
    destruct (Resource.eq_dec r x); subst.
    -- rewrite add_eq_o in HfFl; auto; inversion HfFl; subst; clear HfFl.
       unfold puts_func,puts_func_1; destruct (V⌊x⌋) eqn:HfV.
       + destruct r; rewrite add_eq_o; auto.
       + rewrite add_eq_o; auto.
    -- rewrite add_neq_o in *; auto. 
       unfold puts_func; destruct (V⌊x⌋) eqn:HfV.
       + destruct r0; rewrite add_neq_o; auto.
       + rewrite add_neq_o; auto.
Qed.


(** ** [shift] property *)

Lemma shift_new_in_spec : forall r S,
  In r S -> r < new_key S.
Proof.
  intros r S; revert r; induction S using map_induction; intros.
  - exfalso; destruct H0; unfold Empty in H; now apply (H r x).
  - apply new_key_Add_spec in H0 as H0'; eauto. 
    destruct H0' as [[Heq Hlt] | [Heq Hgt]]; subst.
    -- rewrite Heq. unfold Samples.Add in H0; rewrite H0 in *.
       rewrite add_in_iff in H1; destruct H1; subst; try lia.
       apply IHS1 in H1; lia.
    -- rewrite Heq. unfold Samples.Add in H0; rewrite H0 in *.
       rewrite add_in_iff in H1; destruct H1; subst; try lia.
       apply IHS1 in H1; lia.
Qed. 

Lemma shift_in_e_spec : forall lb k r S,
  In r (shift lb k S) -> exists r', (r =  ([⧐ lb – k] r')%r)%type.
Proof.
  intros lb k r S; revert lb k r; induction S using map_induction; intros.
  - eapply shift_Empty_iff in H. unfold Empty in *; exfalso.
    destruct H0; apply (H r x); eauto.
  - apply shift_Add_spec_1 with (lb := lb) (k := k) in H0 as H0'; auto.
    unfold Samples.Add in H0'. rewrite H0' in H1; clear H0'.
    rewrite add_in_iff in H1; destruct H1; subst.
    -- now exists x.
    -- auto.
Qed.

Lemma shift_find_spec_3 : forall lb k r S S',
  (lb ⊩ r)%r -> In r S ->
  find r S = find r S' -> find r (shift lb k S) = find r (shift lb k S').
Proof.
  intros. destruct H0 as [v HfS]; apply find_1 in HfS.
  apply shift_find_iff with (lb := lb) (k := k) in HfS as HfS1.
  rewrite H1 in HfS. 
  apply shift_find_iff with (lb := lb) (k := k) in HfS as HfS2.
  rewrite Resource.shift_valid_refl in *; auto. now rewrite HfS1, HfS2. 
Qed.

Lemma shift_find_e_spec_1 : forall lb k r v S,
  find r (shift lb k S) = Some v -> 
  (exists r', (r = ([⧐ lb – k] r')%r)%type) /\ 
   exists v', Sample.eq v (Sample.shift lb k v').
Proof.
  intros.
  assert (In r (shift lb k S)). { now exists v; apply find_2. }
  split.
  - now apply shift_in_e_spec in H0.
  - apply shift_in_e_spec in H0; destruct H0; subst. 
    eapply shift_find_e_spec; eauto. 
Qed.

(** ** [halts] property *)

#[export] Instance halts_eq : Proper (Logic.eq ==> eq ==> iff) halts.
Proof.
  repeat red; intros; split; intros; subst.
  - unfold eq,halts in *; intros. rewrite <- H0 in *.
    eapply H1; eauto.
  - unfold eq,halts in *; intros. rewrite H0 in *.
    eapply H1; eauto.
Qed.

Lemma halts_add_spec : forall m k x v,
  (Sample.halts k v) /\ halts k m -> halts k (add x v m).
Proof.
  intros m k x v. intros [Hltv Hltm]; 
  unfold halts; intros r v' Hfi.
  rewrite OP.P.add_o in Hfi; destruct (Resource.eq_dec x r); 
  subst; inversion Hfi; subst; auto.
  apply Hltm in Hfi; auto.
Qed.

Lemma halts_add_spec_1 : forall m k x v,
  ~ In x m -> halts k (add x v m) -> (Sample.halts k v) /\ halts k m.
Proof.
  intros; split.
  - unfold halts in *. apply (H0 x v). now rewrite add_eq_o.
  - unfold halts in *. intros r v' HfV. destruct (Resource.eq_dec x r).
    -- subst. exfalso. apply H. exists v'; now apply find_2.
    -- apply (H0 r). rewrite add_neq_o; auto.
Qed.

Lemma halts_weakening : forall k k' t, 
  k <= k' -> halts k t -> halts k' (shift k (k' - k) t).
Proof.
  intros k k' t Hle Hlt. unfold halts in *; intros r v HfV.
  apply shift_find_e_spec_1 in HfV as HI. destruct HI as [[r' Heqr'] [v' Heqv']]; subst.
  eapply Sample.halts_eq; eauto.
  apply Sample.halts_weakening; auto.
  apply (Hlt r'). apply Sample.eq_leibniz in Heqv'; subst.
  now apply shift_find_iff in HfV.
Qed.

Lemma halts_nexts k t : 
  halts k t -> REnvironment.halts k (nexts t).
Proof.
  induction t using map_induction; intros Hlt0; unfold REnvironment.halts; intros.
  - unfold nexts in *. rewrite fold_Empty in H0; auto.
   inversion H0.
  - rewrite nexts_Add_spec in H1; eauto. 
    unfold Samples.Add in H0; rewrite H0 in *. 
    apply halts_add_spec_1 in Hlt0 as [Hle Hlt1]; auto.
    apply IHt1 in Hlt1 as IH; clear IHt1.
    destruct (Resource.eq_dec x r); subst.
    -- rewrite REnvironment.OP.P.add_eq_o in H1; auto.
       inversion H1; subst; clear H1; simpl.
       now apply Sample.halts_next.
    -- rewrite REnvironment.OP.P.add_neq_o in H1; auto.
       now apply IH in H1.
Qed.

Lemma halts_puts k t V :
  halts k t -> REnvironment.halts k V -> halts k (puts V t).
Proof.
  revert V. induction t using map_induction; intros.
  - rewrite puts_Empty; auto; unfold halts; intros; inversion H2.
  - rewrite puts_Add_spec; eauto. unfold Samples.Add in H0; rewrite H0 in *.
    apply halts_add_spec_1 in H1 as [Hle Hlt1]; auto.
    apply (IHt1 V) in Hlt1; auto. unfold puts_func.
    destruct (V⌊x⌋) eqn:HfV; auto.
    -- destruct r; apply halts_add_spec; split; auto.
       + apply Sample.halts_put_None; auto.
       + apply Sample.halts_put_Some; auto.  
         apply H2 in HfV; now simpl in *.
    -- apply halts_add_spec; split; auto.
       apply Sample.halts_put_None; auto.
Qed.

(** ** Morphism *)

#[export] 
Instance in_rsamples : 
  Proper (Logic.eq ==> Samples.eq ==> iff) In.
Proof.
  repeat red; intros; split; intros;
  apply OP.P.Equal_Eqdom in H0; eapply OP.P.In_m in H0; eauto;
  apply H0; eauto. 
Qed.

#[export] Instance find_rsamples : Proper (Logic.eq ==> eq ==> Logic.eq) find.
Proof. repeat red; intros; subst. now rewrite H0. Qed.

#[export] Instance Empty_rsamples : Proper (Samples.eq ==> iff) OP.P.Empty.
Proof. red; red; intros; now apply Empty_eq_spec. Qed.

#[export] Instance Add_rsamples : 
  Proper (Resource.eq ==> Logic.eq ==> eq ==> eq ==> iff) (@OP.P.Add Sample.t).
Proof.
  do 5 red; intros; subst; rewrite H. 
  split; intros; unfold Samples.Add in *.
  - rewrite <- H2; rewrite H0. now rewrite H1.
  - rewrite H1. now rewrite H2.
Qed.

#[export] Instance add_rsamples : 
  Proper (Resource.eq ==> Logic.eq ==> eq ==> eq) (@add Sample.t).
Proof. repeat red; intros; subst; rewrite H1; now rewrite H. Qed. 

#[export] Instance Submap_env : Proper (eq ==> eq ==> iff) Submap.
Proof. 
  repeat red; intros; split; intros.
  - rewrite Submap_eq_left_spec in H1; eauto.
    rewrite Submap_eq_right_spec in H1; eauto.
  - rewrite <- Submap_eq_left_spec in H1; eauto.
    rewrite <- Submap_eq_right_spec in H1; eauto.
Qed.

#[export] Instance halts_samples : Proper (Logic.eq ==> eq ==> iff) halts. 
Proof.
  repeat red; intros; subst; split; intros.
  - unfold halts; intros. rewrite <- H0 in H1.
    now apply (H r v).
  - unfold halts; intros. rewrite H0 in H1.
    now apply (H r v).
Qed.

End Samples.

(** * Notation - I/O Sampling *)
Module SamplesNotations.

(** ** Scope *)
Declare Scope samples_scope.
Delimit Scope samples_scope with rf.

(** ** Notations *)
Definition 𝐒 := Samples.t.

Infix "⊆" := Samples.Submap (at level 60, no associativity) : samples_scope. 
Infix "∈" := Samples.Raw.In (at level 60, no associativity) : samples_scope. 
Notation "r '∉' Re" := (~ (Samples.Raw.In r Re)) (at level 75, 
                                                      no associativity) : samples_scope. 
Notation "∅" := Samples.Raw.empty (at level 0, no associativity) : samples_scope. 
Notation "'isEmpty(' Re ')'" := (Samples.Empty Re) (at level 20, no associativity) : samples_scope. 
Notation "'Add'" := (Samples.Add) (at level 20, no associativity) : samples_scope. 
Notation "R '⌊' x '⌋'"  := (Samples.Raw.find x R) (at level 15, x constr) : samples_scope.
Notation "'max(' R ')'"  := (Samples.Ext.max_key R) (at level 15) : samples_scope.
Notation "⌈ x ⤆ v '⌉' R"  := (Samples.Raw.add x v R) (at level 15, 
                                                            x constr, v constr) : samples_scope.

Infix "=" := Samples.eq : samples_scope.

Notation "V '⁺'" := (Samples.Ext.new_key V) (at level 16) : samples_scope.

Notation "'[⧐' lb '–' k ']' t" := (Samples.shift lb k t) (at level 65, 
                                                                right associativity) : samples_scope.
Infix "⊩" := Samples.valid (at level 20, no associativity) : samples_scope.

(** ** Morphisms *)

Import Samples.

#[export] Instance eq_equiv_samples : Equivalence Samples.eq := _.
#[export] Instance max_samples : Proper (eq ==> Logic.eq) (Ext.max_key) := Ext.max_key_eq.
#[export] Instance new_samples : Proper (eq ==> Logic.eq) (Ext.new_key) := Ext.new_key_eq.
#[export] Instance in_samples : Proper (Logic.eq ==> eq ==> iff) (Raw.In) := _.
#[export] Instance find_samples : Proper (Logic.eq ==> eq ==> Logic.eq) (Raw.find) := _.
#[export] Instance Empty_samples : Proper (eq ==> iff) (OP.P.Empty) := _.
#[export] Instance Add_samples : 
  Proper (Resource.eq ==> Logic.eq ==> eq ==> eq ==> iff) (@OP.P.Add Sample.t) := _.
#[export] Instance add_rsamples : 
  Proper (Resource.eq ==> Logic.eq ==> eq ==> eq) (@Raw.add Sample.t) := _.
#[export] Instance Submap_samples : Proper (eq ==> eq ==> iff) Submap := _.
#[export] Instance Submap_samples_po : PreOrder Samples.Submap := Submap_po.
#[export] Instance halts_samples : Proper (Logic.eq ==> eq ==> iff) halts := _.

End SamplesNotations.