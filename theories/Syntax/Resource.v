From Coq Require Import Lia PeanoNat Classes.Morphisms.
From DeBrLevel Require Import LevelInterface Level.

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
  revert ks lb t; unfold multi_shift. 
  induction lbs; intros ks lb t Hvt Hvl; simpl; try reflexivity.
  destruct ks; simpl; try reflexivity.
  rewrite IHlbs with (lb := lb); auto.
  - rewrite shift_valid_refl; auto. unfold valid in *.
    assert (lb <= a). { apply Hvl; simpl; now left. }
    lia.
  - intros. apply Hvl; simpl; now right.
Qed.

End Resource.



(** * Notation - Resource *)
Module ResourceNotations.

(** ** Scope *)
Declare Custom Entry wh.
Declare Scope resource_scope.
Delimit Scope resource_scope with r.


(** ** Notations *)
Definition resource := Resource.t.

Notation "<[ e ]>" := e (e custom wh at level 99).
Notation "( x )"   := x (in custom wh, x at level 99).
Notation "x"       := x (in custom wh at level 0, x constr at level 0).
Notation "{ x }"   := x (in custom wh at level 1, x constr).

Infix "<"  := Resource.lt : resource_scope.
Infix "="  := Resource.eq : resource_scope.
Infix "<?" := Resource.ltb (at level 70) : resource_scope.
Infix "=?" := Resource.eqb  (at level 70) : resource_scope.
Infix "⊩" := Resource.valid (at level 20, no associativity) : resource_scope. 
Infix "⊩?" := Resource.validb (at level 20, no associativity) : resource_scope. 
Notation "'[⧐' lb '–' k ']' t" := (Resource.shift lb k t) (at level 65, right associativity) : resource_scope.
Notation "'[⧐⧐' lb '–' k ']' t" := (Resource.multi_shift lb k t) (at level 65, right associativity) : resource_scope.


(** ** Morphism *)
#[export] Instance resource_leibniz_eq : Proper Logic.eq Resource.eq := _.

End ResourceNotations.