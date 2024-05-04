From Coq Require Import Lia.
From Mecha Require Import Typ Resource.
From DeBrLevel Require Import LevelInterface MapLevelInterface MapLevel MapExtInterface MapExt.
From MMaps Require Import MMaps.

(** * Context between resources and pairs of types *)
Module RContext <: IsBdlLvlET.

Include MapLvlD.MakeBdlLvlMapWLLVL PairTyp.
Import Raw Ext.

Lemma max_key_wh_spec : forall (m : t) v v',
  max_key (add (S (S (max_key m))) v (add (S (max_key m)) v' m)) = S (S (max_key m)).
Proof.
  intros. assert (~In (S (max_key m)) m) by (apply max_key_notin_spec; lia).
  assert (~In (S (S (max_key m))) (add (S (max_key m)) v' m)).
  - apply max_key_notin_spec. rewrite max_key_add_spec_1; auto; lia.
  - rewrite max_key_add_spec_1; auto. rewrite max_key_add_spec_1; auto.
Qed.

Lemma new_key_wh_spec : forall (m : t) v v',
  new_key (add (S (new_key m)) v (add (new_key m) v' m)) = S (S (new_key m)).
Proof.
  intros; unfold new_key; rewrite is_empty_add_spec; destruct (is_empty m) eqn:Heq.
  - rewrite max_key_add_spec_1; auto.
    -- apply is_empty_iff in Heq; unfold Empty,not in *; 
      intros. destruct H. apply (Heq 1 x). apply add_mapsto_iff in H.
      destruct H; destruct H; try lia; assumption.
    -- rewrite max_key_add_spec_1; auto.
      + apply is_empty_iff in Heq; unfold Empty,not in *; 
        intros; destruct H; now apply (Heq 0 x).
      + rewrite max_key_Empty_spec; auto. now apply is_empty_iff.
  - f_equal. apply max_key_wh_spec.
Qed.

Lemma valid_wh_spec : forall m v v',
  valid (new_key m) m -> (new_key m) ⊩ₚₜ v -> (new_key m) ⊩ₚₜ v' -> 
  valid (S (S (new_key m))) (add (S (new_key m)) v 
                                        (add (new_key m) v' m)).
Proof.
  intros. apply valid_add_notin_spec.
  - rewrite add_in_iff; intro. destruct H2; try lia.
    apply new_key_notin_spec in H2; auto.
  - split. 
    -- unfold Resource.valid; lia.
    -- split.
      * apply PairTyp.valid_weakening with (k := new_key m); auto.
      * apply valid_add_notin_spec.
        ** apply new_key_notin_spec; lia.
        ** split.
            + unfold Resource.valid; lia.
            + split.
              ++ apply PairTyp.valid_weakening with (k := new_key m); auto.
              ++ apply valid_weakening with (k := new_key m); auto.
Qed.

#[global] 
Instance in_rctx : 
  Proper (Logic.eq ==> eq ==> iff) In.
Proof.
  repeat red; intros; split; intros;
  apply Equal_Eqdom in H0; eapply In_m in H0; eauto;
  apply H0; eauto. 
Qed.

#[global] 
Instance find_rctx : Proper (Logic.eq ==> eq ==> Logic.eq) find.
Proof. repeat red; intros; subst. now rewrite H0. Qed.

#[global] 
Instance Empty_rctx : Proper (eq ==> iff) Empty.
Proof. red; red; intros; now apply Empty_eq_spec. Qed.

#[export] 
Instance Add_rctx : 
Proper (Resource.eq ==> PairTyp.eq ==> eq ==> eq ==> iff) (@Add PairTyp.t).
Proof. 
  red; red; red; red; red; intros. apply PairTyp.eq_leibniz in H0; subst.
  rewrite H. unfold OP.P.Add in *. rewrite H1; rewrite H2. split; intros; auto.
Qed.

#[global] 
Instance add_rctx : 
Proper (Resource.eq ==> PairTyp.eq ==> eq ==> eq) (@add PairTyp.t).
Proof. 
 red; red; red; red; red; intros; subst; apply PairTyp.eq_leibniz in H0; subst.
 rewrite H1; now rewrite H. 
Qed. 

#[global] 
Instance Submap_rctx : 
  Proper (eq ==> eq ==> iff) Submap.
Proof. 
  repeat red; intros; split; intros.
  - rewrite Submap_eq_left_spec in H1; eauto.
    rewrite Submap_eq_right_spec in H1; eauto.
  - rewrite <- Submap_eq_left_spec in H1; eauto.
    rewrite <- Submap_eq_right_spec in H1; eauto.
Qed.

End RContext.

(** *** Scope and Notations *)
Declare Scope rcontext_scope.
Delimit Scope rcontext_scope with rc.

Definition ℜ := RContext.t.

Infix "⊆ᵣᵪ" := RContext.Submap (at level 20, no associativity). 
Infix "∈ᵣᵪ" := RContext.Raw.In (at level 20, no associativity). 
Notation "r '∉ᵣᵪ' Re" := (~ (RContext.Raw.In r Re)) (at level 20, no associativity). 
Notation "∅ᵣᵪ" := RContext.Raw.empty (at level 20, no associativity). 
Notation "'isEmptyᵣᵪ(' Re ')'" := (RContext.Empty Re) (at level 20, no associativity). 
Notation "'Addᵣᵪ'" := (RContext.Add) (at level 20, no associativity). 
Notation "R '⌊' x '⌋ᵣᵪ'"  := (RContext.Raw.find x R) (at level 15, x constr).
Notation "'maxᵣᵪ(' R ')'"  := (RContext.Ext.max_key R) (at level 15).
Notation "'newᵣᵪ(' R ')'"  := (RContext.Ext.new_key R) (at level 15).
Notation "⌈ x ⤆ v '⌉ᵣᵪ' R"  := (RContext.Raw.add x v R) (at level 15, x constr, 
                                                                                v constr).
Notation "R ⌈ x ⩦ v '⌉ᵣᵪ'"  := (RContext.Raw.find x R = Some v) (at level 15, 
                                                                          x constr, v constr).
Notation "R ⌈ x ⩦ ⊥ '⌉ᵣᵪ'"  := (RContext.Raw.find x R = None) (at level 15, 
                                                                                x constr).
Notation "R '⁺ᵣᵪ'" := (RContext.Ext.new_key R) (at level 16).

Infix "=" := RContext.eq : rcontext_scope.

Notation "'[⧐ᵣᵪ' lb '≤' k ']' t" := (RContext.shift lb k t) (at level 45, right associativity).
Infix "⊩ᵣᵪ" := RContext.valid (at level 20, no associativity).


(** *** Morphisms *)

#[global] Instance eq_equiv : Equivalence RContext.eq.
          Proof. apply RContext.Equal_equiv. Qed.

#[global] Instance max_rctx : Proper (RContext.eq ==> Logic.eq) (RContext.Ext.max_key).
          Proof. apply RContext.Ext.max_key_eq. Qed.

#[global] Instance new_rctx : Proper (RContext.eq ==> Logic.eq) (RContext.Ext.new_key).
          Proof. apply RContext.Ext.new_key_eq. Qed.

#[global] 
Instance in_rctx : 
  Proper (Logic.eq ==> RContext.eq ==> iff) (RContext.Raw.In).
Proof. apply RContext.in_rctx. Qed.

#[global] 
Instance find_rctx : Proper (Logic.eq ==> RContext.eq ==> Logic.eq) 
                                                      (RContext.Raw.find).
Proof. apply RContext.find_rctx. Qed.

#[global] 
Instance Empty_rctx : Proper (RContext.eq ==> iff) (RContext.Empty).
Proof. apply RContext.Empty_rctx. Qed.

#[global] 
Instance Add_rctx : 
Proper (Resource.eq ==> PairTyp.eq ==> RContext.eq ==> RContext.eq ==> iff) 
                                                  (@RContext.Add PairTyp.t).
Proof. apply RContext.Add_rctx. Qed. 

#[global] 
Instance add_rctx : 
Proper (Resource.eq ==> PairTyp.eq ==> RContext.eq ==> RContext.eq) 
                                                          (@RContext.Raw.add PairTyp.t).
Proof. apply RContext.add_rctx. Qed. 

#[global] 
Instance Submap_rctx : 
  Proper (RContext.eq ==> RContext.eq ==> iff) RContext.Submap.
Proof. apply RContext.Submap_rctx. Qed.

#[global] 
Instance Submap_po : PreOrder RContext.Submap.
Proof. apply RContext.Submap_po. Qed. 

#[global] 
Instance valid_eq : Proper (Logic.eq ==> RContext.eq ==> iff) RContext.valid.
Proof. apply RContext.valid_eq. Qed.

#[global] 
Instance shift_eq : 
  Proper (Logic.eq ==> Logic.eq ==> RContext.eq ==> RContext.eq) RContext.shift.
Proof. apply RContext.shift_eq. Qed.