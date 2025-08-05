From Coq Require Import Lia Classes.Morphisms.
From DeBrLevel Require Import LevelInterface Level.

(** * Syntax - Resource

  Resources are names that are either bound to I/O or introduced by the binder, named wormhole. In the original paper, a resource is an element taken from a certain infinite countable set. We choose De-Bruijn level as representation to avoid captures issues. Consequently, in this formalization, a resource name is a level. It is a direct use of the [Level] module of [DeBrLevel] library.
*)

(** ** Module - Resource *)
Module Resource <: IsBdlLvlFullOTWL.

(** *** Definitions *)

Include Level.

(** **** Multi shift 

  During the functional transition, defined in [Functional_Transition.v], the signal function is updated multiple times for different well-formed levels through shift applications. Consequently, we define a [multi_shift] function that applies [n] shifts for two lists [lbs] and [ks] of length [n].
*)
Definition multi_shift (lbs: list Lvl.t) (ks: list Lvl.t) (t: t) :=
  List.fold_right (fun lbk acc => shift (fst lbk) (snd lbk) acc) t (List.combine lbs ks).

(** *** Properties *)

Lemma multi_shift_wf_refl (lbs ks: list Lvl.t) (lb: Lvl.t) (t: t) :
  Wf lb t -> (forall i, List.In i lbs -> lb <= i) -> multi_shift lbs ks t = t.
Proof.
  revert ks; unfold multi_shift. 
  induction lbs; intros ks Hvt Hvl; auto. 
  destruct ks as [| k ks]; simpl; auto.
  rewrite IHlbs; auto.
  - rewrite shift_wf_refl; auto. unfold Wf in *.
    destruct (Hvl a); try lia.
    simpl; now left.
  - intros. apply Hvl; simpl; now right.
Qed.

End Resource.

(** ---- *)

(** ** Notation - Resource *)
Module ResourceNotations.

(** *** Scope *)
Declare Custom Entry wh.
Declare Scope resource_scope.
Delimit Scope resource_scope with r.


(** *** Notations *)
Definition resource := Resource.t.
Definition lvl := Level.t.

Notation "<[ x ]>" := x (x custom wh at level 99).
Notation "( x )"   := x (in custom wh, x at level 99).
Notation "x"       := x (in custom wh at level 0, x constr at level 0).
Notation "{ x }"   := x (in custom wh at level 1, x constr).

Infix "<"  := Resource.lt : resource_scope.
Infix "="  := Resource.eq : resource_scope.
Infix "⊩" := Resource.Wf (at level 20, no associativity) : resource_scope. 

Notation "'[⧐' lb '–' k ']' t" := (Resource.shift lb k t) 
                                   (at level 65, right associativity) : resource_scope.
Notation "'[⧐⧐' lb '–' k ']' t" := (Resource.multi_shift lb k t) 
                                    (at level 65, right associativity) : resource_scope.


(** *** Morphisms *)

#[export] Instance resource_leibniz_eq : Proper Logic.eq Resource.eq := _.

#[export] Instance resource_Wf_iff : Proper (Level.eq ==> Resource.eq ==> iff) Resource.Wf := _.

#[export] Instance resource_shift_eq :
  Proper (Level.eq ==> Level.eq ==> Resource.eq ==> Logic.eq) Resource.shift := _.

#[export] Instance resource_multi_shift_eq : 
  Proper (Logic.eq ==> Logic.eq ==> Resource.eq ==> Logic.eq) Resource.multi_shift := _.

End ResourceNotations.