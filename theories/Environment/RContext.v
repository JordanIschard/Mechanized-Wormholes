From Coq Require Import Lia Classes.Morphisms.
From Mecha Require Import Typ Resource.
From DeBrLevel Require Import LevelInterface Level MapLevelInterface MapLevel.
Import ResourceNotations TypNotations.

(** * Context - Resource Context

  The type system, defined in [Type_System.v], requires two contexts: a variable context and a resource context. The former is defined in [VContext.v] and the latter is defined here. It is a map which binds resource names with pair types. We use the module [MapLvlD] defined by the library [DeBrLevel].
*)

(** ** Module - Resource Context *)
Module RContext <: IsBdlLvlET.

(** *** Definition *)

Include MapLvlD.MakeBdlLvlMapLVLD PairTyp.
Import Raw Ext.

Open Scope ptyp_scope.

(** *** Property *)

(** **** [shift] extra property *)

Lemma shift_max_key_gt (m n x : lvl) (c : t) :
  max_key c > x <-> max_key (shift m n c) > ([⧐m – n] x)%r.
Proof.
  revert x; induction c using map_induction; intro y.
  - split; intros.
    -- rewrite max_key_Empty_spec in H0; auto. lia.
    -- rewrite shift_Empty_spec in H0; auto.
       rewrite max_key_Empty_spec in H0; auto. lia.
  - split; intros.
    -- unfold Add in *; rewrite H0 in *; clear H0.
       apply (max_key_add_spec) with (v := e) in H as H'.
       destruct H' as [[Heq Hle] | [Heq Hgt]].
       + rewrite Heq in *; clear Heq.
         rewrite (shift_in_iff m n) in H.
         apply (max_key_add_spec) with (v := <[ [⧐m – n] e ]>) in H as H''.
         destruct H'' as [[Heq Hle'] | [Heq Hgt']].
         ++ rewrite shift_add_spec. 
            rewrite Heq.
            unfold Level.shift.
            destruct (Level.leb_spec m x); destruct (Level.leb_spec m y); lia.
         ++ rewrite <- IHc1 in Hgt'. lia.
       + rewrite IHc1 in Hgt.
         rewrite shift_add_spec.
         rewrite max_key_add_lt_spec; auto.
         ++ now rewrite <- IHc1; rewrite <- Heq.
         ++ now rewrite <- shift_in_iff.
    -- unfold Add in *; rewrite H0 in *; clear H0.
       rewrite shift_add_spec in *.
       apply (max_key_add_spec) with (v := e) in H as H'.
       destruct H' as [[Heq Hle] | [Heq Hgt]].
       + rewrite Heq in *; clear Heq.
         rewrite (shift_in_iff m n) in H.
         apply (max_key_add_spec) with (v := <[ [⧐m – n] e ]>) in H as H''.
         destruct H'' as [[Heq Hle'] | [Heq Hgt']].
         ++ rewrite Heq in *.
            unfold Level.shift in *.
            destruct (Level.leb_spec m x); destruct (Level.leb_spec m y); lia.
         ++ rewrite <- IHc1 in Hgt'. lia.
       + rewrite IHc1 in Hgt.
         rewrite max_key_add_lt_spec in H1; auto.
         ++ now rewrite Heq; rewrite IHc1.
         ++ now rewrite <- shift_in_iff.
Qed. 

Lemma shift_max_key_le (m n : Lvl.t) (c1 : t) :
  max_key c1 <= max_key (shift m n c1).
Proof.
  induction c1 using map_induction.
  - now rewrite shift_Empty_spec.
  - unfold Add in H0; rewrite H0; clear H0. 
    rewrite shift_add_spec.
    apply (max_key_add_spec) with (v := e) in H as H'.
    rewrite (shift_in_iff m n) in H.
    apply (max_key_add_spec) with (v := <[ [⧐m – n] e ]>) in H as H''.
    destruct H' as [[Heq Hle] | [Heq Hgt]].
    -- rewrite Heq; clear Heq.
       destruct H'' as [[Heq Hle'] | [Heq Hgt']].
       + rewrite Heq; clear Heq.
         unfold Level.shift; destruct (Level.leb m x); lia.
       + rewrite Heq; clear Heq. 
         rewrite <- shift_max_key_gt in Hgt'.
         lia.
    -- rewrite Heq; clear Heq.
       destruct H'' as [[Heq Hle'] | [Heq Hgt']].
       + rewrite Heq; clear Heq. lia.
       + now rewrite Heq; clear Heq.
Qed.
       
Lemma shift_new_key_le (m n : Lvl.t) (c1 : t) :
  new_key c1 <= new_key (shift m n c1).
Proof.
  unfold new_key; destruct (is_empty c1) eqn:Hemp.
  - lia.
  - destruct (is_empty (shift m n c1)) eqn:Hemp'.
    -- apply is_empty_2 in Hemp'. 
       rewrite <- (shift_Empty_iff m n) in Hemp'.
       apply is_empty_1 in Hemp'.
       rewrite Hemp in Hemp'; now inversion Hemp'.
    -- assert (max_key c1 <= max_key (shift m n c1)).
       + apply shift_max_key_le.
       + lia.
Qed.


(** **** Wormholes specification *)

Lemma max_key_wh_spec : forall (m : t) (v v' : πΤ),
  max_key (add (S (S (max_key m))) v (add (S (max_key m)) v' m)) = S (S (max_key m)).
Proof.
  intros m v v'.
  apply max_key_add_ge_spec.
  - apply max_key_notin_spec. 
    rewrite max_key_add_ge_spec; auto.
    apply max_key_notin_spec; auto.
  - rewrite max_key_add_ge_spec; auto.
    apply max_key_notin_spec; auto.
Qed.

Lemma new_key_wh_spec : forall (m : t) (v v' : πΤ),
  new_key (add (S (new_key m)) v (add (new_key m) v' m)) = S (S (new_key m)).
Proof.
  intros m v v'; unfold new_key; 
  rewrite is_empty_add_spec; destruct (is_empty m) eqn:Heq.
  - rewrite max_key_add_ge_spec; auto.
    -- apply is_empty_iff in Heq; unfold Empty,not in *; 
      intros. destruct H. apply (Heq 1 x). apply add_mapsto_iff in H.
      destruct H; destruct H; try lia; assumption.
    -- rewrite max_key_add_ge_spec; auto.
      + apply is_empty_iff in Heq. unfold Empty,not in *; 
        intros; destruct H; now apply (Heq 0 x).
      + rewrite max_key_Empty_spec; auto. now apply is_empty_iff.
  - f_equal. apply max_key_wh_spec.
Qed.

Lemma valid_wh_spec : forall (m : t) (v v' : πΤ),
  valid (new_key m) m -> 
  (new_key m) ⊩ v -> (new_key m) ⊩ v' -> 
  valid (S (S (new_key m))) (add (S (new_key m)) v (add (new_key m) v' m)).
Proof.
  intros m v v' Hvm Hvv Hvv'. 
  apply valid_add_notin_spec.
  - rewrite add_in_iff; intro Ha. 
    destruct Ha as [Heq | HIn]; try lia.
    apply new_key_notin_spec in HIn; auto.
  - repeat split. 
    -- unfold Resource.valid; lia.
    -- apply PairTyp.valid_weakening with (k := new_key m); auto.
    -- apply PairTyp.valid_weakening with (k := new_key m); auto.
    -- apply valid_add_notin_spec.
       + apply new_key_notin_spec; lia.
       + repeat split.
         ++ unfold Resource.valid; lia.
         ++ apply PairTyp.valid_weakening with (k := new_key m); auto.
         ++ apply PairTyp.valid_weakening with (k := new_key m); auto.
         ++ apply valid_weakening with (k := new_key m); auto.
Qed.

(** **** Morphism *)

#[export] Instance in_rctx : Proper (Logic.eq ==> eq ==> iff) In.
Proof. intros x y Heqx c c' Heqc; subst; now rewrite Heqc. Qed.

#[export] Instance find_rctx : Proper (Logic.eq ==> eq ==> Logic.eq) find.
Proof. repeat red; intros; subst. now rewrite H0. Qed.

#[export] Instance Empty_rctx : Proper (eq ==> iff) Empty.
Proof. intros c c' Heq; now rewrite Heq. Qed.

#[export] Instance Add_rctx : Proper (Resource.eq ==> PairTyp.eq ==> eq ==> eq ==> iff) (@Add PairTyp.t).
Proof. 
  intros x x' HeqV ty ty' HeqT c c' Heq c1 c1' Heq1.
  apply PairTyp.eq_leibniz in HeqT; subst.
  unfold Add; now rewrite HeqV, Heq, Heq1.
Qed.

#[export] Instance add_rctx : Proper (Resource.eq ==> PairTyp.eq ==> eq ==> eq) (@add PairTyp.t).
Proof. 
  intros x x' HeqV ty ty' HeqT c c' Heq.
  apply PairTyp.eq_leibniz in HeqT; subst.
  now rewrite HeqV, Heq. 
Qed. 

End RContext.

(** ---- *)

(** ** Notation - Resource Context *)
Module RContextNotations.

(** *** Scope *)
Declare Scope rcontext_scope.
Delimit Scope rcontext_scope with rc.


(** *** Notation *)
Definition ℜ := RContext.t.

Notation "∅" := RContext.Raw.empty (at level 0, no associativity) : rcontext_scope. 
Notation "R '⁺'" := (RContext.Ext.new_key R) (at level 16) : rcontext_scope.
Notation "r '∉' Re" := (~ (RContext.Raw.In r Re)) (at level 75, no associativity) : rcontext_scope. 
Notation "'isEmpty(' Re ')'" := (RContext.Empty Re) (at level 20, no associativity) : rcontext_scope. 
Notation "'Add'" := (RContext.Add) (at level 20, no associativity) : rcontext_scope. 
Notation "R '⌊' x '⌋'"  := (RContext.Raw.find x R) (at level 15, x constr) : rcontext_scope.
Notation "'max(' R ')'" := (RContext.Ext.max_key R) (at level 15) : rcontext_scope.
Notation "⌈ x ⤆ v '⌉' R" := (RContext.Raw.add x v R) 
                             (at level 15, x constr, v constr) : rcontext_scope.
Notation "'[⧐' lb '–' k ']' t" := (RContext.shift lb k t) 
                                   (at level 65, right associativity) : rcontext_scope.

Infix "⊆" := RContext.Submap (at level 60, no associativity) : rcontext_scope. 
Infix "∈" := RContext.Raw.In (at level 60, no associativity) : rcontext_scope. 
Infix "⊩" := RContext.valid (at level 20, no associativity) : rcontext_scope.
Infix "=" := RContext.eq : rcontext_scope.

(** *** Morphisms *)

Import RContext.

#[export] Instance eq_equiv_rctx : Equivalence RContext.eq := Equal_equiv.
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