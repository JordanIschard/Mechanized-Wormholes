From DeBrLevel Require Import LevelInterface Level PairLevel.

(** * Syntax - Resource

  A resource is a kind of reference defined in the Wormholes language. Like a variable,
  we need identifiers for resources. Thus, we choose De Bruijn level as representation in
  order to avoid capture variables. It is a direct use of the [Level] module.
*)
Module Resource <: IsBdlLvlFullOTWL := Level.

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

Notation "'[⧐ₚᵣ' lb '≤' k ']' t" := (PairResource.shift lb k t) (in custom wormholes at level 45, 
                                                                            right associativity).
Infix "⊩ₚᵣ" := PairResource.valid (at level 20, no associativity). 
Infix "⊩?ₚᵣ" := PairResource.valid (at level 20, no associativity). 