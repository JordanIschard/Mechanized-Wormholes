From Coq Require Import Structures.Orders Structures.OrdersEx Lia.
From DeBrLevel Require Import LevelInterface.

(** * Syntax - Variable

  We represent variables with [nat]. 
*)
Module Var <: OrderedTypeWithLeibniz.

Include Nat_as_OT.

Lemma eq_leibniz : forall x y, eq x y -> x = y. 
Proof. auto. Qed.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y. 
Proof. intros; lia. Qed.

Lemma gt_neq_nlt : forall x y, ~ eq x y -> ~ lt x y -> lt y x.
Proof. intros; lia. Qed.

End Var.

(** *** Scope and Notations *)
Definition variable := Var.t.
Declare Scope var_scope.
Delimit Scope var_scope with v.

#[export] Hint Resolve Var.eq_refl Var.eq_sym Var.eq_trans : core.
#[export] Instance var_eq_rr : RewriteRelation Var.eq := {}.   
#[export] Instance var_eq_equiv : Equivalence Var.eq. Proof. split; auto. Qed.

Infix "<"  := Var.lt : var_scope.
Infix "=" := Var.eq : var_scope.
Infix "<?"  := Var.ltb (at level 70) : var_scope.
Infix "=?" := Var.eqb  (at level 70) : var_scope.