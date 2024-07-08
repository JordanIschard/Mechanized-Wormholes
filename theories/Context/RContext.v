From Coq Require Import Lia Classes.Morphisms.
From Mecha Require Import Typ Resource.
From DeBrLevel Require Import LevelInterface MapLevelInterface MapLevel.
Import ResourceNotations TypNotations.

(** * Context - Resource Context

 A Wormholes term is typed by a type defined in [Typ.v] regards of two contexts:
 the common variable context and the resource context. The latter is defined here.
 It maps two types [(ty,ty')] to a resource [r]. These types represent respectively
 the input type and the output type of the rsf term that contains [r].

*)
Module RContext <: IsBdlLvlET.

Include MapLvlD.MakeBdlLvlMapLVLD PairTyp.
Import Raw Ext.
Open Scope ptyp_scope.

(** ** Wormholes specification *)

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
  valid (new_key m) m -> (new_key m) ⊩ v -> (new_key m) ⊩ v' -> 
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

(** ** Morphisms *)

#[export] 
Instance in_rctx : 
  Proper (Logic.eq ==> eq ==> iff) In.
Proof.
  repeat red; intros; split; intros;
  apply Equal_Eqdom in H0; eapply In_m in H0; eauto;
  apply H0; eauto. 
Qed.

#[export] 
Instance find_rctx : Proper (Logic.eq ==> eq ==> Logic.eq) find.
Proof. repeat red; intros; subst. now rewrite H0. Qed.

#[export] 
Instance Empty_rctx : Proper (eq ==> iff) Empty.
Proof. red; red; intros; now apply Empty_eq_spec. Qed.

#[export] 
Instance Add_rctx : 
Proper (Resource.eq ==> PairTyp.eq ==> eq ==> eq ==> iff) (@Add PairTyp.t).
Proof. 
  red; red; red; red; red; intros. apply PairTyp.eq_leibniz in H0; subst.
  rewrite H. unfold OP.P.Add in *. rewrite H1; rewrite H2. split; intros; auto.
Qed.

#[export] 
Instance add_rctx : 
Proper (Resource.eq ==> PairTyp.eq ==> eq ==> eq) (@add PairTyp.t).
Proof. 
 red; red; red; red; red; intros; subst; apply PairTyp.eq_leibniz in H0; subst.
 rewrite H1; now rewrite H. 
Qed. 

#[export] 
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

(** * Notation - Resource Context *)
Module RContextNotations.

(** ** Scope *)
Declare Scope rcontext_scope.
Delimit Scope rcontext_scope with rc.


(** ** Notations *)
Definition ℜ := RContext.t.

Infix "⊆" := RContext.Submap (at level 60, no associativity) : rcontext_scope. 
Infix "∈" := RContext.Raw.In (at level 60, no associativity) : rcontext_scope. 
Notation "r '∉' Re" := (~ (RContext.Raw.In r Re)) (at level 75, no associativity) : rcontext_scope. 
Notation "∅" := RContext.Raw.empty (at level 0, no associativity) : rcontext_scope. 
Notation "'isEmpty(' Re ')'" := (RContext.Empty Re) (at level 20, no associativity) : rcontext_scope. 
Notation "'Add'" := (RContext.Add) (at level 20, no associativity) : rcontext_scope. 
Notation "R '⌊' x '⌋'"  := (RContext.Raw.find x R) (at level 15, x constr) : rcontext_scope.
Notation "'max(' R ')'"  := (RContext.Ext.max_key R) (at level 15) : rcontext_scope.
Notation "⌈ x ⤆ v '⌉' R"  := (RContext.Raw.add x v R) (at level 15, x constr, 
                                                                                v constr) : rcontext_scope.
(* Notation "R ⌈ x ⩦ v '⌉'"  := (RContext.Raw.find x R = Some v) (at level 15, 
                                                                          x constr, v constr) : rcontext_scope.
Notation "R ⌈ x ⩦ ⊥ '⌉'"  := (RContext.Raw.find x R = None) (at level 15, 
                                                                                x constr) : rcontext_scope. *)
Notation "R '⁺'" := (RContext.Ext.new_key R) (at level 16) : rcontext_scope.

Infix "=" := RContext.eq : rcontext_scope.

Notation "'[⧐' lb '–' k ']' t" := (RContext.shift lb k t) (at level 65, right associativity) : rcontext_scope.
Infix "⊩" := RContext.valid (at level 20, no associativity) : rcontext_scope.

(** ** Morphisms *)

Import RContext.

#[export] Instance eq_equiv : Equivalence RContext.eq := Equal_equiv.
#[export] Instance max_rctx : Proper (eq ==> Logic.eq) (RContext.Ext.max_key) := Ext.max_key_eq.
#[export] Instance new_rctx : Proper (eq ==> Logic.eq) (Ext.new_key) := Ext.new_key_eq.
#[export] Instance in_rctx : Proper (Logic.eq ==> eq ==> iff) (Raw.In) := _.
#[export] Instance find_rctx : Proper (Logic.eq ==> eq ==> Logic.eq) (Raw.find) := _.
#[export] Instance Empty_rctx : Proper (eq ==> iff) (Empty) := _.
#[export] Instance Add_rctx : 
  Proper (Resource.eq ==> PairTyp.eq ==> eq ==> eq ==> iff) (@RContext.Add PairTyp.t) := _.
#[export] Instance add_rctx : 
  Proper (Resource.eq ==> PairTyp.eq ==> eq ==> eq) (@Raw.add PairTyp.t) := _.
#[export] Instance Submap_rctx : Proper (eq ==> eq ==> iff) Submap := _.
#[export] Instance Submap_po : PreOrder Submap := Submap_po.
#[export] Instance valid_eq : Proper (Logic.eq ==> eq ==> iff) valid := _.
#[export] Instance shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.

End RContextNotations.