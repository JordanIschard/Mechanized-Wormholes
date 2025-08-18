From Coq Require Import Structures.Orders Structures.OrdersEx.
From DeBrLevel Require Import LevelInterface.

(** * Syntax - Variable

  In our mechanization, a variable is a [nat]. Consequently we use [Nat_as_OT] in order to represent the countable infinite set of variables.  
*)
Module Var <: OrderedTypeWithLeibniz.

Include Nat_as_OT.

Lemma eq_leibniz (x y: t) : eq x y -> x = y. 
Proof. auto. Qed.

End Var.