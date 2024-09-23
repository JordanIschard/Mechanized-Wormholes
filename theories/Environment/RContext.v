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

(** **** Wormholes specification *)


Lemma Submap_wh_spec (m : t) (v v' : πΤ) :
  Submap m (add (S (new_key m)) v (add (new_key m) v' m)).
Proof.
  repeat apply Submap_add_spec_1; try reflexivity.
  - apply new_key_notin_spec.
    rewrite new_key_add_ge_spec; auto.
    apply new_key_notin_spec; lia.
  - apply new_key_notin_spec; lia. 
Qed.

Lemma Submap_wh_spec_1 (m m' : t) (v v' : πΤ) :
  Submap (add (S (new_key m)) v (add (new_key m) v' m)) m' -> Submap m m'.
Proof.
  intro HSub.
  apply Submap_Add_spec 
  with (m := (add (new_key m) v' m)) (x := (S (new_key m))) (v := v) in HSub.
  - apply Submap_Add_spec with (m := m) (x := (new_key m)) (v := v') in HSub; auto.
    -- apply new_key_notin_spec; auto.
    -- unfold Add; reflexivity.
  - apply new_key_notin_spec.
    rewrite new_key_add_ge_spec; auto.
    apply new_key_notin_spec; lia.
  - unfold Add; reflexivity. 
Qed.

Lemma new_key_wh_spec (m : t) (v v' : πΤ) :
  new_key (add (S (new_key m)) v (add (new_key m) v' m)) = S (S (new_key m)).
Proof.
  repeat rewrite new_key_add_ge_spec; auto.
  - apply new_key_notin_spec; 
    rewrite new_key_add_ge_spec; auto.
    apply new_key_notin_spec; auto.
  - apply new_key_notin_spec; auto.
Qed.

Lemma valid_wh_spec (m : t) (v v' : πΤ) :
  valid (new_key m) m -> (new_key m) ⊩ v -> (new_key m) ⊩ v' -> 
  valid (S (S (new_key m))) (add (S (new_key m)) v (add (new_key m) v' m)).
Proof.
  intros Hvm Hvv Hvv'. 
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

Lemma valid_wh_full_spec (m : t) (v v' : πΤ) :
  valid (new_key m) m -> (new_key m) ⊩ v -> (new_key m) ⊩ v' -> 
  valid (new_key (add (S (new_key m)) v (add (new_key m) v' m)))
        (add (S (new_key m)) v (add (new_key m) v' m)).
Proof.
  intros Hvm Hvv Hvv'.
  rewrite new_key_wh_spec; now apply valid_wh_spec.
Qed.

(** **** Morphism *)

#[export] Instance in_rctx : Proper (Logic.eq ==> eq ==> iff) In.
Proof. intros x y Heqx c c' Heqc; subst; now rewrite Heqc. Qed.

#[export] Instance find_rctx : Proper (Logic.eq ==> eq ==> Logic.eq) find.
Proof. intros x y Heqx c c' Heqc; subst; now rewrite Heqc. Qed.

#[export] Instance Empty_rctx : Proper (eq ==> iff) Empty.
Proof. intros c c' Heq; now rewrite Heq. Qed.

#[export] Instance Add_rctx : 
  Proper (Resource.eq ==> PairTyp.eq ==> eq ==> eq ==> iff) (@Add PairTyp.t).
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