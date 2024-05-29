From Coq Require Import Lia PeanoNat.
From DeBrLevel Require Import LevelInterface Level PairLevel.

(** * Syntax - Resource

  A resource is a kind of reference defined in the Wormholes language. Like a variable,
  we need identifiers for resources. Thus, we choose De Bruijn level as representation in
  order to avoid capture variables. It is a direct use of the [Level] module.
*)
Module Resource <: IsBdlLvlFullOTWL.

Include Level.

Definition multi_shift (lbs : list nat) (ks : list nat) (t : t) :=
  List.fold_right (fun (x : nat * nat) acc => let (lb,k) := x in shift lb k acc) t (List.combine lbs ks).

Lemma shift_unfold_2 lb lb' k k' r:
  lb' <= lb -> lb' <= k' -> lb <= k' -> 
  shift lb k (shift lb' (k' - lb') r) = shift lb' (k + (k' - lb')) r.
Proof.
  intros.
  unfold shift; destruct (Nat.leb_spec0 lb' r).
  - replace (lb <=? r + (k' - lb')) with true; try lia.
    symmetry. apply Nat.leb_le. lia.
  - replace (lb <=? r) with false; auto.
    symmetry. apply Nat.leb_nle; lia.
Qed.

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

(** * Syntax - Pair of resources *)
Module PairResource <: IsBdlLvlFullETWL := IsBdlLvlFullPairOTWL Resource Resource.

(** *** Scope and Notations *)
Declare Custom Entry wormholes.
Declare Scope resource_scope.
Delimit Scope resource_scope with r.
Definition resource := Resource.t.
Definition πresource := PairResource.t.

Notation "<[ e ]>" := e (e custom wormholes at level 99).
Notation "( x )"   := x (in custom wormholes, x at level 99).
Notation "x"       := x (in custom wormholes at level 0, x constr at level 0).
Notation "{ x }"   := x (in custom wormholes at level 1, x constr).

Infix "<"  := Resource.lt : resource_scope.
Infix "=" := Resource.eq : resource_scope.
Infix "<?"  := Resource.ltb (at level 70) : resource_scope.
Infix "=?" := Resource.eqb  (at level 70) : resource_scope.
Infix "⊩ᵣ" := Resource.valid (at level 20, no associativity). 
Infix "⊩?ᵣ" := Resource.validb (at level 20, no associativity). 
Notation "'[⧐ᵣ' lb '≤' k ']' t" := (Resource.shift lb k t) (at level 65, right associativity).
Notation "'[⧐⧐ᵣ' lb '≤' k ']' t" := (Resource.multi_shift lb k t) (at level 65, right associativity).

Notation "'[⧐ₚᵣ' lb '≤' k ']' t" := (PairResource.shift lb k t) (in custom wormholes at level 45, 
                                                                            right associativity).
Infix "⊩ₚᵣ" := PairResource.valid (at level 20, no associativity). 
Infix "⊩?ₚᵣ" := PairResource.valid (at level 20, no associativity). 