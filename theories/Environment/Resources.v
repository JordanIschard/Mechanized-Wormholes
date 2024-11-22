From Coq Require Import Lia Classes.Morphisms.
From Mecha Require Import Resource.
From DeBrLevel Require Import LevelInterface Level Levels SetLevelInterface.
Import ResourceNotations.

(** * Environment - Resources

  Wormholes types contains a signal function arrow that carries a set of resources used by the signal function during the functional transition. We define a set of resource directly via the [Levels] contained in [DeBrLevel] library. The set module is based on [MSet].
*)

(** ** Module - Resources *)
Module Resources <: IsBdlLvlFullOTWL.

(** *** Definition *)

Include Levels.
Import St.

(** **** Multi shift 

  As said in [Resource.v], the proof of progress of the functional transition requires multiple
  shift with different well-formedness level and shifts. Thus we also define [multi_shift] here. 
*)
Definition multi_shift (lbs : list lvl) (ks : list lvl) (t : t) :=
  List.fold_right (fun lbk acc => shift (fst lbk) (snd lbk) acc) t (List.combine lbs ks).

(** **** New key *)

Definition max_key (t : t) := fold (Nat.max) t 0.

Definition new_key (t : t) := 
  if is_empty t then 0 else S (max_key t).

(** *** Property *)

(** **** [multi_shift] property *)

#[export] Instance multi_shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> Logic.eq) multi_shift.
Proof.
  intros lbs' lbs Heqlbs ks' ks Heqks r1 r2 Heqr; subst.
  unfold eq in Heqr; apply eq_leibniz in Heqr. 
  now rewrite Heqr.
Qed.

(** **** [max_key] property *)

#[export] Instance max_key_eq : Proper (eq ==> Logic.eq) max_key.
Proof.
  intros x y Heq.
  apply eq_leibniz in Heq; now subst.
Qed.

Lemma max_key_Empty_spec (m : t) : Empty m -> max_key m = 0.
Proof. 
  intro HEmp; unfold max_key.
  rewrite fold_1; auto.
  constructor; auto.
  intros x y z Heq Heq'; now subst.
Qed.

Lemma max_key_empty_spec : max_key empty = 0.
Proof.
  unfold max_key; now rewrite fold_empty.
Qed.

Lemma max_key_Add_spec (m m' : t) x :
  ~ In x m -> Add x m m' ->
  (max_key m' = x /\ max_key m <= x) \/ (max_key m' = max_key m /\ max_key m > x).
Proof.
  intros HnIn HAdd; unfold max_key.
  apply Add_inv in HAdd; subst.
  rewrite fold_add; eauto; try lia.
  - constructor; auto.
    intros w y z H H1; now subst.
  - intros n' n Heqn p' p Heqp; now subst.
  - intros n p q; lia.
Qed.

Lemma max_key_Add_ge_spec (m m' : t) x :
  ~ In x m -> Add x m m' ->  max_key m <= x -> max_key m' = x.
Proof.
  intros HnIn HAdd Hmax.
  apply max_key_Add_spec in HAdd; auto.
  destruct HAdd as [[Heq Hle] | [Heq Hgt]]; auto.
  lia.
Qed.

Lemma max_key_Add_lt_spec (m m' : t) x :
  ~ In x m -> Add x m m' ->  max_key m > x -> max_key m' = max_key m.
Proof.
  intros HnIn HAdd Hmax.
  apply max_key_Add_spec in HAdd; auto.
  destruct HAdd as [[Heq Hle] | [Heq Hgt]]; auto.
  lia.
Qed.

Lemma max_key_add_spec (m : t) x :
  ~ In x m -> (max_key (add x m) = x /\ max_key m <= x) \/ 
              (max_key (add x m) = max_key m /\ max_key m > x).
Proof.
  intro HnIn.
  eapply max_key_Add_spec; auto.
Qed.

Lemma max_key_add_ge_spec (m : t) x :
  ~ In x m -> max_key m <= x -> max_key (add x m) = x.
Proof.
  intro HnIn.
  eapply max_key_Add_ge_spec; auto.
Qed.

Lemma max_key_add_lt_spec (m : t) x :
  ~ In x m -> max_key m > x -> max_key (add x m) = max_key m.
Proof.
  intro HnIn.
  eapply max_key_Add_lt_spec; auto.
Qed.

Lemma max_key_add_spec_1 (m m' : t) x :
  ~ In x m -> ~ In x m' ->
  max_key m = max_key m' -> max_key (add x m) = max_key (add x m').
Proof.
  intros HnIn HnIn'. 
  apply max_key_add_spec in HnIn as HI. 
  apply max_key_add_spec in HnIn' as HI'.
  destruct HI as [[Heq1 Hleb1] | [Heq1 Hgt1]];
  destruct HI' as [[Heq2 Hleb2] | [Heq2 Hgt2]]; subst; try lia.
Qed.

(** **** [new_key] property *)

Lemma new_key_empty_spec : new_key empty = 0.
Proof. now unfold new_key; simpl. Qed.

#[export] Instance new_key_eq : Proper (eq ==> Logic.eq) new_key.
Proof. 
  intros s1 s2 Heq.
  apply eq_leibniz in Heq; now subst.
Qed.

Lemma new_key_add_spec (x: lvl) (t : t) :
  ~In x t -> (new_key (add x t) = S x /\ new_key t <= S x) \/ 
               (new_key (add x t) = new_key t /\ new_key t > S x).
Proof.
  intro HnIn.
  unfold new_key.
  assert (is_empty (add x t) = false).
  - apply Bool.not_true_is_false.
    intro Hc.
    rewrite is_empty_spec in Hc.
    apply (Hc x).
    apply add_spec; auto.
  - rewrite H.
    apply max_key_add_spec in HnIn as [[Heq Hle] | [Heq Hgt]].
    -- left; split; auto.
       destruct (is_empty t); lia.
    -- rewrite Heq.
       destruct (is_empty t) eqn:Hemp.
       + rewrite max_key_Empty_spec in Hgt; try lia.
         now rewrite <- is_empty_spec.
       + right; split; auto; lia.
Qed.

Lemma new_key_add_lt_spec (x: lvl) (t : t) :
  ~ In x t -> new_key t > S x -> new_key (add x t) = new_key t.
Proof.
  intros HnIn Hgt.
  apply new_key_add_spec in HnIn as [[Heq Hlt] | [Heq Hgt']]; auto.
  lia.
Qed. 

Lemma new_key_add_ge_spec (x: lvl) (t : t) :
  ~ In x t -> new_key t <= S x -> new_key (add x t) = S x.
Proof.
  intros HnIn Hgt.
  apply new_key_add_spec in HnIn as [[Heq Hlt] | [Heq Hgt']]; auto.
  lia.
Qed.

Lemma new_key_max_spec (x: lvl) (t : t) :
  ~ In x t -> new_key (add x t) = max (new_key t) (S x).
Proof.
  intro HnIn.
  apply new_key_add_spec in HnIn as [[Heq Hlt] | [Heq Hgt']]; lia.
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
Notation "t '⁺'" := (Resources.new_key t) (at level 16) : resources_scope.
Notation "'[⧐' lb '–' k ']' t" := (Resources.shift lb k t) (at level 65, right associativity) : resources_scope.
Notation "'[⧐⧐' lb '–' k ']' t" := (Resources.multi_shift lb k t) (at level 65, right associativity) : resources_scope.


(** *** Morphism *)
Import Resources.

#[export] Instance resources_leibniz_eq : Proper Logic.eq eq := _.
#[export] Instance resources_valid_proper :  Proper (Level.eq ==> eq ==> iff) valid := _.
#[export] Instance resources_shift_proper : Proper (Level.eq ==> Level.eq ==> eq ==> eq) shift := shift_eq.
#[export] Instance resources_multi_shift_proper : Proper (Logic.eq ==> Logic.eq ==> eq ==> Logic.eq) multi_shift := _.
#[export] Instance resources_new_key_proper : Proper (eq ==> Logic.eq) new_key := _.

End ResourcesNotations.