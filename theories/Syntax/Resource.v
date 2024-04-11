From Coq Require Import Structures.Orders Structures.OrdersEx.
From DeBrLevel Require Import LevelInterface.

Module Resource <: OrderedTypeWithLeibniz.
  
  Include Nat_as_OT.

  Lemma eq_leibniz : forall t t', eq t t' -> t = t'.
  Proof. intros; now unfold eq in *. Qed.

End Resource.

(** * Syntax - Pair of resources *)
Module PairResource <: OrderedTypeWithLeibniz.

  Include PairOrderedType Resource Resource. 


  Lemma eq_leibniz : forall t t', eq t t' -> t = t'.
  Proof. 
    intros; destruct t0,t'. repeat red in H. destruct H. unfold RelationPairs.RelCompFun in *.
    simpl in *; now subst.
  Qed.

End PairResource.

(** *** Scope and Notations *)
Declare Custom Entry rsf.
Declare Scope resource_scope.
Delimit Scope resource_scope with r.
Definition resource := Resource.t.
Definition πresource := PairResource.t.

Notation "<[ e ]>" := e (e custom rsf at level 99).
Notation "( x )"   := x (in custom rsf, x at level 99).
Notation "x"       := x (in custom rsf at level 0, x constr at level 0).
Notation "{ x }"   := x (in custom rsf at level 1, x constr).

Infix "<"  := Resource.lt : resource_scope.
Infix "=" := Resource.eq : resource_scope.
Infix "<?"  := Resource.ltb (at level 70) : resource_scope.
Infix "=?" := Resource.eqb  (at level 70) : resource_scope.