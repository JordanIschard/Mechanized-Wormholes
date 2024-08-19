From Coq Require Import Lia PeanoNat Classes.Morphisms.
From Mecha Require Import Resource.
From DeBrLevel Require Import LevelInterface Level Levels SetLevelInterface.

(** * Environment - Resources

  Wormholes types contains a "reactive" arrow that carries a set of resources used
  by the signal function. We define a set of resource directly via the [Levels] 
  implementation contained in the library.
*)
Module Resources <: IsBdlLvlFullOTWL.

Include Levels.
Import St.

(** ** Multi shift 

During the functional transition, defined in [FT_Definition], the signal function is updated multiple 
times with different lower bound and shift value. Thus, we define a [multi_shift] function that applies
[n] shifts for two lists [lbs] and [ks] of length [n].

*)
Definition multi_shift (lbs : list nat) (ks : list nat) (t : t) :=
  List.fold_right (fun (x : nat * nat) acc => let (lb,k) := x in shift lb k acc) t (List.combine lbs ks).

(** ** [valid] property *)

Lemma valid_in_spec_1 : forall (s : t) lb k r,
  valid lb s -> In r (shift lb k s) <-> In r s.
Proof.
  intro s. induction s using set_induction; intros lb k r Hv; split.
  - intro HIn; rewrite shift_Empty_spec in *; auto; inversion HIn.
  - intro HIn; unfold Empty in *; exfalso; now apply (H r).
  - intro HIn; apply Add_inv in H0; subst. rewrite shift_add_notin_spec in *; auto.
    apply valid_add_spec in Hv as [Hvr Hv]. rewrite add_spec in HIn; destruct HIn; subst.
    -- rewrite Resource.shift_valid_refl; auto; rewrite add_spec; now left.
    -- rewrite add_spec; right. rewrite <- IHs1; eauto.
  - intro HIn; apply Add_inv in H0; subst. rewrite shift_add_notin_spec in *; auto.
    apply valid_add_spec in Hv as [Hvr Hv]. rewrite add_spec in HIn; destruct HIn; subst.
    -- rewrite Resource.shift_valid_refl; auto; rewrite add_spec; now left.
    -- rewrite add_spec; right. rewrite IHs1; eauto.
Qed.

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


(** * Notation - Set *)
Module SetNotations.

(** ** Scope *)
Declare Scope set_scope.
Delimit Scope set_scope with s.

(** ** Notations *)

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

(** * Notation - Resources *)
Module ResourcesNotations.

(** ** Scope *)
Declare Scope resources_scope.
Delimit Scope resources_scope with rs.


(** ** Notations *)
Definition resources := Resources.t.

Infix "⊩" := Resources.valid (at level 20, no associativity) : resources_scope. 
Infix "⊩?" := Resources.validb (at level 20, no associativity) : resources_scope. 
Notation "'[⧐' lb '–' k ']' t" := (Resources.shift lb k t) (at level 65, right associativity) : resources_scope.
Notation "'[⧐⧐' lb '–' k ']' t" := (Resources.multi_shift lb k t) (at level 65, right associativity) : resources_scope.


(** ** Morphism *)
#[export] Instance resources_leibniz_eq : Proper Logic.eq Resources.eq := _.

End ResourcesNotations.