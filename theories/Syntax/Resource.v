From Coq Require Import Lia PeanoNat.
From DeBrLevel Require Import LevelInterface Level Levels SetLevelInterface.

(** * Syntax - Resource

  Resources are names that are either bound to I/O or introduced by the binder wh as local references.
  The original paper defines a resource as an element taken from an infinite countable set.
  We choose De-Bruijn level as representation which avoid captures issues. Consequently, a resource is 
  a level. It is a direct use of the [Level] module.
*)
Module Resource <: IsBdlLvlFullOTWL.

Include Level.

(** ** Multi shift 

During the functional transition, defined in [FT_Definition], the signal function is updated multiple 
times with different lower bound and shift value. Thus, we define a [multi_shift] function that applies
[n] shifts for two lists [lbs] and [ks] of length [n].

*)
Definition multi_shift (lbs : list nat) (ks : list nat) (t : t) :=
  List.fold_right (fun (x : nat * nat) acc => let (lb,k) := x in shift lb k acc) t (List.combine lbs ks).

Lemma multi_shift_valid_refl lbs ks lb t:
  valid lb t -> (forall i, List.In i lbs -> lb <= i) ->
  multi_shift lbs ks t = t.
Proof.
  revert ks lb t. induction lbs.
  - intros; unfold multi_shift; now simpl in *.
  - intros; unfold multi_shift in *; destruct ks; simpl; auto.
    rewrite IHlbs with (lb := lb); auto.
    -- rewrite shift_valid_refl; auto.
       unfold valid in *.
       assert (lb <= a). { apply H0; simpl; now left. }
       lia.
    -- intros. apply H0; simpl; now right.
Qed.

End Resource.

(** * Syntax - Resources

  Wormholes types contains a "reactive" arrow that carries a set of resources used
  by the signal function. We define a set of resource directly via the [Levels] 
  implementation contained in the library.
*)
Module Resources <: IsBdlLvlFullSetOTWLInterface Level.

Include Levels.

(** ** Multi shift 

During the functional transition, defined in [FT_Definition], the signal function is updated multiple 
times with different lower bound and shift value. Thus, we define a [multi_shift] function that applies
[n] shifts for two lists [lbs] and [ks] of length [n].

*)
Definition multi_shift (lbs : list nat) (ks : list nat) (t : t) :=
  List.fold_right (fun (x : nat * nat) acc => let (lb,k) := x in shift lb k acc) t (List.combine lbs ks).

(** ** Wormholes specifcation *)

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

(** * Notation - Resource *)
Module ResourceNotations.

(** ** Scope *)
Declare Custom Entry wh.
Declare Scope resource_scope.
Delimit Scope resource_scope with r.
Declare Scope resources_scope.
Delimit Scope resources_scope with rs.

(** ** Notations *)
Definition resource := Resource.t.
Definition resources := Resources.t.

Notation "<[ e ]>" := e (e custom wh at level 99).
Notation "( x )"   := x (in custom wh, x at level 99).
Notation "x"       := x (in custom wh at level 0, x constr at level 0).
Notation "{ x }"   := x (in custom wh at level 1, x constr).

Infix "<"  := Resource.lt : resource_scope.
Infix "="  := Resource.eq : resource_scope.
Infix "<?" := Resource.ltb (at level 70) : resource_scope.
Infix "=?" := Resource.eqb  (at level 70) : resource_scope.
Infix "⊩ᵣ" := Resource.valid (at level 20, no associativity). 
Infix "⊩?ᵣ" := Resource.validb (at level 20, no associativity). 
Notation "'[⧐ᵣ' lb '≤' k ']' t" := (Resource.shift lb k t) (at level 65, right associativity).
Notation "'[⧐⧐ᵣ' lb '≤' k ']' t" := (Resource.multi_shift lb k t) (at level 65, right associativity).

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
Notation "'[⧐⧐ᵣₛ' lb '≤' k ']' t" := (Resources.multi_shift lb k t) (at level 65, right associativity).

End ResourceNotations.