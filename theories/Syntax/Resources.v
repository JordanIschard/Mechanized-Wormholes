(* From Coq Require Import Lia.
From DeBrLevel Require Import Level Levels SetLevelInterface.

(** * Syntax - Resources

  Wormholes types contains a "reactive" arrow that carries a set of resources used
  by the signal function.
  Types in Wotmholes language is composed with basic types of a lambda-calculus with
  a new arrow which carries a set of used resources. In order to define this type
  we define a set of resources identifiers.
*)
Module Resources <: IsBdlLvlFullSetOTWLInterface Level.

Include Levels.

Definition multi_shift (lbs : list nat) (ks : list nat) (t : t) :=
  List.fold_right (fun (x : nat * nat) acc => let (lb,k) := x in shift lb k acc) t (List.combine lbs ks).


Lemma valid_wh_spec : forall s lb,
  valid (S (S lb)) s -> valid lb (diff s (add lb (add (S lb) empty))).
Proof.
  intros; rewrite valid_unfold in *; unfold For_all in *; 
  intros. rewrite diff_spec in H0; destruct H0.
  rewrite add_notin_spec in H1; destruct H1; 
  rewrite add_notin_spec in H2; destruct H2; clear H3.
  unfold Level.valid in *; apply H in H0; lia.
Qed.

End Resources.

(** *** Scope and Notations *)
Definition resources := Resources.t.
Declare Scope resources_scope.
Delimit Scope resources_scope with rs.

Notation "∅ᵣₛ" := (Resources.empty).
Notation "'\{{' x '}}'" := (Resources.singleton x).
Notation "'\{{' x ';' y ';' .. ';' z '}}'" := (Resources.add x (Resources.add y .. (Resources.add z Resources.empty) .. )).
Infix "∉"  := (fun x s => ~ Resources.In x s) (at level 75) : resources_scope.
Infix "∈"  := (Resources.In)  (at level 60, no associativity) : resources_scope.
Infix "+:" := (Resources.add)  (at level 60, no associativity) : resources_scope.
Infix "∪"  := (Resources.union) (at level 50, left associativity) : resources_scope.
Infix "∩"  := (Resources.inter) (at level 50, left associativity) : resources_scope.
Infix "\"  := (Resources.diff) (at level 50, left associativity) : resources_scope.
Infix "⊆"  := Resources.Subset (at level 60, no associativity) : resources_scope.
Infix "⊈"  := (fun s s' => ~ (Resources.Subset s s')) (at level 60, no associativity) : resources_scope.

Infix "<"  := Resources.lt : resources_scope.
Infix "<?" := Resources.ltb (at level 70) : resources_scope.
Infix "="  := Resources.eq : resources_scope.
Infix "=?" := Resources.equal (at level 70) : resources_scope.

Infix "⊩ᵣₛ" := Resources.valid (at level 20, no associativity). 
Infix "⊩?ᵣₛ" := Resources.validb (at level 20, no associativity). 
Notation "'[⧐ᵣₛ' lb '≤' k ']' t" := (Resources.shift lb k t) (at level 65, right associativity).
Notation "'[⧐⧐ᵣₛ' lb '≤' k ']' t" := (Resources.multi_shift lb k t) (at level 65, right associativity). *)