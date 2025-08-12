From Coq Require Import Lia Classes.Morphisms.
From DeBrLevel Require Import LevelInterface Level Levels SetLevelInterface.

(** * Syntax - Resource

  Resources are names that are either bound to I/O or introduced by the binder, named wormhole. In the original paper, a resource is an element taken from a certain infinite countable set. We choose De-Bruijn level as representation to avoid captures issues. Consequently, in this formalization, a resource name is a level. It is a direct use of the [Level] module of [DeBrLevel] library.
*)

Module Resource <: IsBdlLvlFullOTWL.

(** ** Definitions *)

Include Level.

(** *** Multi shift 

  During the functional transition, defined in [Functional_Transition.v], the signal function is updated multiple times for different well-formed levels through shift applications. Consequently, we define a [multi_shift] function that applies [n] shifts for two lists [lbs] and [ks] of length [n].
*)
Definition multi_shift (lbs: list Lvl.t) (ks: list Lvl.t) (t: t) :=
  List.fold_right (fun lbk acc => shift (fst lbk) (snd lbk) acc) t (List.combine lbs ks).

(** ** Properties *)

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

(** * Syntax - Resources

  Wormholes types contains a signal function arrow that carries a resource set. We define a set of resource directly via the [Levels] contained in [DeBrLevel] library. The set module is based on [MSet].
*)

Module Resources <: IsBdlLvlFullOTWL.

(** ** Definition *)

Include MakeLVL.
Import St.

(** *** Multi shift 

  As said in [Resource.v], the proof of progress of the functional transition requires multiple
  shift with different well-formedness level and shifts. Thus, we also define [multi_shift] here. 
*)
Definition multi_shift (lbs : list Lvl.t) (ks : list Lvl.t) (t : t) :=
  List.fold_right (fun lbk acc => shift (fst lbk) (snd lbk) acc) t (List.combine lbs ks).


(** ** Properties *)

(** *** [multi_shift] properties *)

#[export] Instance multi_shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> Logic.eq) multi_shift.
Proof.
  intros lbs' lbs Heqlbs ks' ks Heqks r1 r2 Heqr; subst.
  unfold eq in Heqr; apply eq_leibniz in Heqr. 
  now rewrite Heqr.
Qed.

(** *** [Wf] specific Wormholes properties *)

Lemma Wf_wh (lb : Lvl.t) (s : t):
  Wf (S (S lb)) s -> Wf lb (diff s (add lb (add (S lb) empty))).
Proof.
  intros; rewrite Wf_unfold in *; unfold For_all in *; 
  intros. rewrite diff_spec in H0; destruct H0.
  rewrite add_notin_spec in H1; destruct H1; 
  rewrite add_notin_spec in H2; destruct H2; clear H3.
  unfold Level.Wf in *; apply H in H0; lia.
Qed.

(** *** [new_key] properties *)

Lemma new_key_union (s s': t) :
  new_key (union s s') = max (new_key s) (new_key s').
Proof.
  revert s'.
  induction s using set_induction; intro s'.
  - rewrite empty_union_1; auto.
    rewrite (new_key_Empty s); auto; lia.
  - apply Add_inv in H0; subst.
    rewrite union_add.
    do 2 rewrite new_key_add_max.
    rewrite IHs1; lia.
Qed.

Lemma new_key_Wf (k: Lvl.t) (s: t) : Wf k s -> new_key s <= k.
Proof.
  induction s using set_induction; intro Hwf.
  - rewrite new_key_Empty; auto; lia.
  - apply Add_inv in H0; subst.
    apply Wf_add_iff in Hwf as [Hwfx Hwf]; auto.
    apply IHs1 in Hwf.
    unfold Resource.Wf in Hwfx.
    rewrite new_key_add_max; lia.
Qed.

End Resources.