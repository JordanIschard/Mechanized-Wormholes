From Coq Require Import MSets Lia.
Require Import Resource.

Module Resources <: OrderedTypeWithLeibniz :=  MSetList.MakeWithLeibniz Resource.


(** *** Scope and Notations *)
Definition resources := Resources.t.
Declare Scope resources_scope.
Delimit Scope resources_scope with rs.

Notation "∅ᵣₛ" := (Resources.empty).
Notation "'\{{' x '}}'" := (Resources.singleton x).
Notation "'\{{' x ';' y ';' .. ';' z '}}'" := (Resources.add x (Resources.add y .. (Resources.add z Resources.empty) .. )).
Infix "∉" := (fun x s => ~ Resources.In x s) (at level 75) : resources_scope.
Infix "∈" := (Resources.In)  (at level 60, no associativity) : resources_scope.
Infix "+:" := (Resources.add)  (at level 60, no associativity) : resources_scope.
Infix "∪" := (Resources.union) (at level 50, left associativity) : resources_scope.
Infix "∩" := (Resources.inter) (at level 50, left associativity) : resources_scope.
Infix "\" := (Resources.diff) (at level 50, left associativity) : resources_scope.
Infix "⊆" := Resources.Subset (at level 60, no associativity) : resources_scope.
Infix "⊈" := (fun s s' => ~ (Resources.Subset s s')) (at level 60, no associativity) : resources_scope.

Infix "<"  := Resources.lt : resources_scope.
Infix "=" := Resources.eq : resources_scope.
Infix "=?" := Resources.equal (at level 70) : resources_scope.