From Coq Require Import Lia Classes.Morphisms.
From Mecha Require Import Resource OverlaySet.
From DeBrLevel Require Import LevelInterface Level Levels SetLevelInterface.
Import ResourceNotations.

(** * Environment - Resources

  Wormholes types contains a signal function arrow that carries a set of resources used by the signal function during the functional transition. We define a set of resource directly via the [Levels] contained in [DeBrLevel] library. The set module is based on [MSet].
*)

(** ** Module - Resources *)
Module Resources <: IsBdlLvlFullOTWL.

(** *** Definition *)

Include OverlaySet.
Import St.

(** **** Multi shift 

  As said in [Resource.v], the proof of progress of the functional transition requires multiple
  shift with different well-formedness level and shifts. Thus we also define [multi_shift] here. 
*)
Definition multi_shift (lbs : list lvl) (ks : list lvl) (t : t) :=
  List.fold_right (fun lbk acc => shift (fst lbk) (snd lbk) acc) t (List.combine lbs ks).

(** *** Property *)

(** **** [multi_shift] property *)

#[export] Instance multi_shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> Logic.eq) multi_shift.
Proof.
  intros lbs' lbs Heqlbs ks' ks Heqks r1 r2 Heqr; subst.
  unfold eq in Heqr; apply eq_leibniz in Heqr. 
  now rewrite Heqr.
Qed.

(** **** [valid] Wormholes specification *)

Lemma valid_wh_spec (lb : lvl) (s : t):
  valid (S (S lb)) s -> valid lb (diff s (add lb (add (S lb) empty))).
Proof.
  intros; rewrite valid_unfold in *; unfold For_all in *; 
  intros. rewrite diff_spec in H0; destruct H0.
  rewrite add_notin_spec in H1; destruct H1; 
  rewrite add_notin_spec in H2; destruct H2; clear H3.
  unfold Level.valid in *; apply H in H0; lia.
Qed.

End Resources.

(** ---- *)

(** ** Notation - Set *)
Module SetNotations.

(** *** Scope *)
Declare Scope set_scope.
Delimit Scope set_scope with s.

(** *** Notation *)

Notation "∅" := (Resources.St.empty) : set_scope.
Notation "'\{{' x '}}'" := (Resources.St.singleton x).
Notation "'\{{' x ';' y ';' .. ';' z '}}'" := (Resources.St.add x (Resources.St.add y .. (Resources.St.add z Resources.St.empty) .. )).
Infix "∉"  := (fun x s => ~ Resources.St.In x s) (at level 75) : set_scope.
Infix "∈"  := (Resources.St.In)  (at level 60, no associativity) : set_scope.
Infix "+:" := (Resources.St.add)  (at level 60, no associativity) : set_scope.
Infix "∪"  := (Resources.St.union) (at level 50, left associativity) : set_scope.
Infix "∩"  := (Resources.St.inter) (at level 50, left associativity) : set_scope.
Infix "\"  := (Resources.St.diff) (at level 50, left associativity) : set_scope.
Infix "⊆"  := Resources.St.Subset (at level 60, no associativity) : set_scope.
Infix "⊈"  := (fun s s' => ~ (Resources.St.Subset s s')) (at level 60, no associativity) : set_scope.
Infix "<"  := Resources.lt : set_scope.
Infix "<?" := Resources.St.ltb (at level 70) : set_scope.
Infix "="  := Resources.eq : set_scope.
Infix "=?" := Resources.St.equal (at level 70) : set_scope.

End SetNotations.

(** ---- *)

(** ** Notation - Resources *)
Module ResourcesNotations.

(** *** Scope *)
Declare Scope resources_scope.
Delimit Scope resources_scope with rs.


(** *** Notation *)
Definition resources := Resources.t.

Infix "⊩" := Resources.valid (at level 20, no associativity) : resources_scope. 
Notation "'[⧐' lb '–' k ']' t" := (Resources.shift lb k t) (at level 65, right associativity) : resources_scope.
Notation "'[⧐⧐' lb '–' k ']' t" := (Resources.multi_shift lb k t) (at level 65, right associativity) : resources_scope.


(** *** Morphism *)
Import Resources.

#[export] Instance resources_leibniz_eq : Proper Logic.eq eq := _.
#[export] Instance resources_valid_proper :  Proper (Level.eq ==> eq ==> iff) valid := _.
#[export] Instance resources_shift_proper : Proper (Level.eq ==> Level.eq ==> eq ==> eq) shift := shift_eq.
#[export] Instance resources_multi_shift_proper : Proper (Logic.eq ==> Logic.eq ==> eq ==> Logic.eq) multi_shift := _.

End ResourcesNotations.