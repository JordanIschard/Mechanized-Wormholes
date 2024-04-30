From Mecha Require Import Term Evaluation Resource REnvironment Cell RFlow.
From DeBrLevel Require Import MapExtInterface MapExt.
From MMaps Require Import MMaps.

Module RFlows <: EqualityType.

Module Raw := MMaps.OrdList.Make Resource.
Module Ext := MapETLVL RFlow Raw.

Include Ext.
Import Raw OP.P.

Definition nexts_func x v V := ⌈x ⤆ (Cell.inp (RFlow.next v))⌉ᵣᵦ V.

Definition nexts (fl : RFlows.t) : REnvironment.t := 
  fold nexts_func fl (∅ᵣᵦ).

Definition puts_func V x v fl := 
  match V⌊x⌋ᵣᵦ with 
    | Some (⩽ … v' ⩾) =>  add x (RFlow.put v' v) fl
    |  _ => fl 
  end.

Definition puts (Vout : REnvironment.t) (fl : RFlows.t) : RFlows.t :=
  fold (puts_func Vout) fl empty.

Definition halts (fl : RFlows.t) := forall (r : resource) v, 
 find r fl = Some v -> RFlow.halts v.



Hint Resolve REnvironment.eq_equiv : core.

(** *** Nexts *)

#[export]
Instance nexts_prop : 
  Proper (Logic.eq ==> Logic.eq ==> REnvironment.eq ==> REnvironment.eq) nexts_func.
Proof.
  repeat red; intros; subst. unfold nexts_func; now rewrite H1.
Qed.

Lemma nexts_diamond : Diamond REnvironment.eq nexts_func.
 repeat red; intros. rewrite <- H0. rewrite <- H1.
 unfold nexts_func. rewrite REnvironment.OP.P.add_add_2; auto.
Qed.

Hint Resolve nexts_prop nexts_diamond : core.

Lemma nexts_Empty t : Empty t -> ((nexts t) = ∅ᵣᵦ)%re.
Proof. 
  intros; unfold nexts. rewrite fold_Empty; auto. reflexivity. 
Qed.

Lemma nexts_Add_spec x v t t' : 
  ~ In x t ->
  Add x v t t' -> ((nexts t') = ⌈x ⤆ (Cell.inp (RFlow.next v))⌉ᵣᵦ (nexts t))%re.
Proof.
  intros. unfold nexts. 
  apply fold_Add with (A := REnvironment.t) (eqA := REnvironment.eq) 
                      (f := nexts_func) (i := ∅ᵣᵦ) in H0; auto.
Qed.

#[export]
Instance nexts_eq : Proper (eq ==> REnvironment.eq) nexts.
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
        - unfold Add in H0. rewrite H0. apply add_mapsto_new; auto.
       }
       subst. assert (Add x3 e (remove x3 y) y).
       { unfold Add. now rewrite H2. }
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
              rewrite <- H1. unfold Add in H0. rewrite H0.
              rewrite add_neq_mapsto_iff; auto.
            * rewrite <- add_neq_mapsto_iff; eauto.
              unfold Add in H0. rewrite <- H0. rewrite H1.
              rewrite add_neq_mapsto_iff; auto.
    -- assert (Add x3 e x1 y). { unfold Add in *; rewrite <- H1; assumption. }
       rewrite (nexts_Add_spec x3 e x1 x2); auto.
       rewrite (nexts_Add_spec x3 e x1 y); auto. 
Qed.

Lemma nexts_in_iff r fl : In r fl <-> r ∈ᵣᵦ (nexts fl).
Proof.
  revert r; induction fl using map_induction; split; intros.
  - exfalso. destruct H0. now apply (H r x).
  - rewrite nexts_Empty in H0; auto. inversion H0; inversion H1.
  - destruct (Resource.eq_dec x r); subst.
    -- rewrite nexts_Add_spec; eauto. 
       rewrite REnvironment.OP.P.add_in_iff; now left.
    -- rewrite nexts_Add_spec; eauto.
       rewrite REnvironment.OP.P.add_in_iff; right.
       unfold Add in *. rewrite H0 in *.
       rewrite add_in_iff in H1; destruct H1; try (contradiction).
       now rewrite <- IHfl1.
  - destruct (Resource.eq_dec x r); subst.
    -- unfold Add in *; rewrite H0. rewrite add_in_iff; now left.
    -- rewrite nexts_Add_spec in *; eauto.
       unfold Add in *. rewrite H0 in *.
       rewrite add_in_iff; right. 
       rewrite REnvironment.OP.P.add_in_iff in H1; 
       destruct H1; try (contradiction).
       now rewrite IHfl1.
Qed. 

Lemma nexts_unused r fl : In r fl -> REnvironment.unused r (nexts fl).
Proof.
  revert r; induction fl using map_induction; unfold REnvironment.unused; intros.
  - exfalso. destruct H0. now apply (H r x).
  - destruct H1. apply find_1 in H1. rewrite H0 in *.
    destruct (Resource.eq_dec r x); subst.
    -- rewrite add_eq_o in H1; auto. inversion H1; subst; clear H1.
       exists (RFlow.next x0); rewrite nexts_Add_spec; eauto.
       rewrite REnvironment.OP.P.add_eq_o; auto.
    -- assert (In r fl1). 
       { rewrite add_neq_o in H1; auto. exists x0. now apply find_2. }
       apply IHfl1 in H2; destruct H2. exists x1.
       rewrite nexts_Add_spec; eauto.
       rewrite REnvironment.OP.P.add_neq_o; auto.
Qed.   

(** *** Puts *)

#[export]
Instance puts_prop V :
  Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) (puts_func V).
Proof.
  repeat red; intros; subst; unfold puts_func. destruct (V⌊y⌋ᵣᵦ); auto.
  destruct r; auto. now rewrite H1.
Qed.

Lemma puts_diamond V : Diamond Equal (puts_func V).
Proof. 
  repeat red; intros; unfold puts_func. 
  destruct (V⌊k⌋ᵣᵦ) eqn:HfV; destruct (V⌊k'⌋ᵣᵦ) eqn:HfV'.
  -- destruct r,r0; try 
     (rewrite <- H1; rewrite <- H0; unfold puts_func;
      now rewrite HfV', HfV).
     rewrite <- H1; rewrite <- H0; unfold puts_func.
     rewrite HfV',HfV. rewrite add_add_2; auto.
  -- destruct r; try 
     (rewrite <- H1; rewrite <- H0; unfold puts_func;
      now rewrite HfV', HfV).
  -- destruct r; try 
     (rewrite <- H1; rewrite <- H0; unfold puts_func;
      now rewrite HfV', HfV).
  -- rewrite <- H1; rewrite <- H0; unfold puts_func.
     now rewrite HfV', HfV.
Qed.

Hint Resolve puts_prop puts_diamond : core.

Lemma puts_Empty V fl : Empty fl -> eq (puts V fl) empty.
Proof.
  intros; unfold puts,eq. rewrite fold_Empty; auto; reflexivity.
Qed.

Lemma puts_Add_spec r v V fl fl' : 
  ~ In r fl -> Add r v fl fl' -> eq (puts V fl') ((puts_func V) r v (puts V fl)).
Proof.
  intros. unfold puts, eq. now rewrite fold_Add; eauto.
Qed.


(** *** Halts *)

#[export]
Instance halts_eq : Proper (eq ==> iff) halts.
Proof.
  repeat red; intros; split; intros.
  - unfold eq,halts in *; intros. rewrite <- H in *.
    eapply H0; eauto.
  - unfold eq,halts in *; intros. rewrite H in *.
    eapply H0; eauto.
Qed.

Lemma halts_add_spec : forall m x v,
  (RFlow.halts v) /\ halts m -> halts (add x v m).
Proof.
  intros m x v. intros [Hltv Hltm]; unfold halts; intros r v' Hfi.
  rewrite OP.P.add_o in Hfi; destruct (Resource.eq_dec x r); subst; inversion Hfi; subst; auto.
  apply Hltm in Hfi; auto.
Qed.

Lemma halts_add_spec_1 : forall m x v,
  ~ In x m -> halts (add x v m) -> (RFlow.halts v) /\ halts m.
Proof.
  intros; split.
  - unfold halts in *. apply (H0 x v). now rewrite add_eq_o.
  - unfold halts in *. intros r v' HfV. destruct (Resource.eq_dec x r).
    -- subst. exfalso. apply H. exists v'; now apply find_2.
    -- apply (H0 r). rewrite add_neq_o; auto.
Qed.

Lemma halts_nexts t : 
  halts t -> REnvironment.halts (nexts t).
Proof.
  induction t using map_induction; intros Hlt0; unfold REnvironment.halts; intros.
  - unfold nexts in *. rewrite fold_Empty in H0; auto.
   inversion H0.
  - rewrite nexts_Add_spec in H1; eauto. 
    unfold Add in H0; rewrite H0 in *. 
    apply halts_add_spec_1 in Hlt0 as [Hle Hlt1]; auto.
    apply IHt1 in Hlt1 as IH; clear IHt1.
    destruct (Resource.eq_dec x r); subst.
    -- rewrite REnvironment.OP.P.add_eq_o in H1; auto.
       inversion H1; subst; clear H1; simpl.
       now apply RFlow.halts_next.
    -- rewrite REnvironment.OP.P.add_neq_o in H1; auto.
       now apply IH in H1.
Qed.

Lemma halts_puts t V :
  halts t -> REnvironment.halts V -> halts (puts V t).
Proof.
  revert V. induction t using map_induction; intros.
  - rewrite puts_Empty; auto; unfold halts; intros; inversion H2.
  - rewrite puts_Add_spec; eauto. unfold Add in H0; rewrite H0 in *.
    apply halts_add_spec_1 in H1 as [Hle Hlt1]; auto.
    apply (IHt1 V) in Hlt1; auto. unfold puts_func.
    destruct (V⌊x⌋ᵣᵦ) eqn:HfV; auto. destruct r; auto.
    apply halts_add_spec; split; auto.
    apply RFlow.halts_put; auto. apply H2 in HfV; now simpl in *. 
Qed.




(** *** Morphism *)

#[global] 
Instance in_rflow : 
  Proper (Logic.eq ==> RFlows.eq ==> iff) In.
Proof.
  repeat red; intros; split; intros;
  apply OP.P.Equal_Eqdom in H0; eapply OP.P.In_m in H0; eauto;
  apply H0; eauto. 
Qed.

#[global] 
Instance find_rflow : Proper (Logic.eq ==> RFlows.eq ==> Logic.eq) find.
Proof. repeat red; intros; subst. now rewrite H0. Qed.

#[global] 
Instance Empty_rflow : Proper (RFlows.eq ==> iff) OP.P.Empty.
Proof. red; red; intros; now apply Empty_eq_spec. Qed.

#[export] 
Instance Add_rflow : 
Proper (Resource.eq ==> Logic.eq ==> RFlows.eq ==> RFlows.eq ==> iff) 
            (@OP.P.Add RFlow.t).
Proof. 
  red; red; red; red; red; intros; subst; rewrite H. 
  split; intros; unfold Add in *.
  - rewrite <- H2; rewrite H0. now rewrite H1.
  - rewrite H1. now rewrite H2.
Qed.

#[global] 
Instance add_rflow : 
Proper (Resource.eq ==> Logic.eq ==> RFlows.eq ==> RFlows.eq) 
                                                          (@add RFlow.t).
Proof.
  repeat red; intros; subst; rewrite H1; now rewrite H.
Qed. 

#[global] 
Instance Submap_env : 
  Proper (RFlows.eq ==> RFlows.eq ==> iff) Submap.
Proof. 
  repeat red; intros; split; intros.
  - rewrite Submap_eq_left_spec in H1; eauto.
    rewrite Submap_eq_right_spec in H1; eauto.
  - rewrite <- Submap_eq_left_spec in H1; eauto.
    rewrite <- Submap_eq_right_spec in H1; eauto.
Qed.

End RFlows.

(** *** Scope and Notations *)

Declare Scope rflow_scope.
Delimit Scope rflow_scope with rf.

Definition 𝐅 := RFlows.t.

Infix "⊆ᵣₔ" := RFlows.Submap (at level 20, no associativity). 
Infix "∈ᵣₔ" := RFlows.Raw.In (at level 20, no associativity). 
Notation "r '∉ᵣₔ' Re" := (~ (RFlows.Raw.In r Re)) (at level 20, 
                                                                        no associativity). 
Notation "∅ᵣₔ" := RFlows.Raw.empty (at level 20, no associativity). 
Notation "'isEmptyᵣₔ(' Re ')'" := (RFlows.OP.P.Empty Re) (at level 20, no associativity). 
Notation "'Addᵣₔ'" := (RFlows.OP.P.Add) (at level 20, no associativity). 
Notation "'maxᵣₔ(' R ')'"  := (RFlows.Ext.max_key R) (at level 15).
Notation "'newᵣₔ(' R ')'"  := (RFlows.Ext.new_key R) (at level 15).
Notation "R '⌊' x '⌋ᵣₔ'"  := (RFlows.Raw.find x R) (at level 15, x constr).
Notation "⌈ x ⤆ v '⌉ᵣₔ' R"  := (RFlows.Raw.add x v R) (at level 15, 
                                                                          x constr, v constr).
Notation "R ⌈ x ⩦ v '⌉ᵣₔ'"  := (RFlows.Raw.find x R = Some v) (at level 15, 
                                                                                  x constr, 
                                                                                  v constr).
Notation "R ⌈ x ⩦ ⊥ '⌉ᵣₔ'"  := (RFlows.Raw.find x R = None) (at level 15, 
                                                                                    x constr).

Infix "=" := RFlows.eq : rflow_scope.

#[global]
Instance eq_equiv_re : Equivalence RFlows.eq.
Proof. apply RFlows.OP.P.Equal_equiv. Qed.

#[global] Instance max_re : Proper (RFlows.eq ==> Logic.eq) (RFlows.Ext.max_key).
          Proof. apply RFlows.Ext.max_key_eq. Qed.

#[global] Instance new_re : Proper (RFlows.eq ==> Logic.eq) (RFlows.Ext.new_key).
          Proof. apply RFlows.Ext.new_key_eq. Qed.
          
#[global] 
Instance in_rflow : 
  Proper (Logic.eq ==> RFlows.eq ==> iff) (RFlows.Raw.In).
Proof. apply RFlows.in_rflow. Qed.

#[global] 
Instance find_rflow : Proper (Logic.eq ==> RFlows.eq ==> Logic.eq) 
                                                      (RFlows.Raw.find).
Proof. apply RFlows.find_rflow. Qed.

#[global] 
Instance Empty_rflow : Proper (RFlows.eq ==> iff) (RFlows.OP.P.Empty).
Proof. apply RFlows.Empty_rflow. Qed.

#[global] 
Instance Add_rflow : 
Proper (Resource.eq ==> Logic.eq ==> RFlows.eq ==> RFlows.eq ==> iff) 
                                                  (@RFlows.OP.P.Add RFlow.t).
Proof. apply RFlows.Add_rflow. Qed. 

#[global] 
Instance add_rflow : 
Proper (Resource.eq ==> Logic.eq ==> RFlows.eq ==> RFlows.eq) 
                                                          (@RFlows.Raw.add RFlow.t).
Proof. apply RFlows.add_rflow. Qed. 

#[global] 
Instance Submap_env : 
  Proper (RFlows.eq ==> RFlows.eq ==> iff) RFlows.Submap.
Proof. apply RFlows.Submap_env. Qed.

#[global] 
Instance Submap_env_po : PreOrder RFlows.Submap.
Proof. apply RFlows.Submap_po. Qed. 