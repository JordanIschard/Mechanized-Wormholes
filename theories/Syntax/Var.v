From Coq Require Import Structures.Orders Structures.OrdersEx.
From DeBrLevel Require Import LevelInterface.

(** * Syntax - Variable

  We represent variables with [nat]. 
*)

(** ** Module - Variable *)
Module Var <: OrderedTypeWithLeibniz.

Include Nat_as_OT.

Lemma eq_leibniz (x y: t): eq x y -> x = y. 
Proof. auto. Qed.

End Var.

(** ---- *)

(** ** Notation - Variable *)
Module VarNotations.

(** *** Scope *)
Declare Scope var_scope.
Delimit Scope var_scope with v.

(** *** Notations *)
Definition variable := Var.t.

Infix "<"  := Var.lt : var_scope.
Infix "="  := Var.eq : var_scope.
Infix "<?" := Var.ltb (at level 70) : var_scope.
Infix "=?" := Var.eqb (at level 70) : var_scope.

(** *** Morphisms *)
#[export] Hint Resolve Var.eq_refl Var.eq_sym Var.eq_trans : core.

#[export] Instance var_eq_rr : RewriteRelation Var.eq := _.

#[export] Instance var_eq_equiv : Equivalence Var.eq := _.

#[export] Instance var_leibniz_eq : Proper Logic.eq Var.eq := _.

End VarNotations.