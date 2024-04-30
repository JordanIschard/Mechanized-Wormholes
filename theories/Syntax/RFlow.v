From Coq Require Import Lists.Streams Structures.Equalities.
From Mecha Require Import Term Evaluation Resource.
From DeBrLevel Require Import LevelInterface.

Module RFlow <: EqualityType.

Import Streams.

Definition t : Type := (Stream Λ * Stream Λ).

Definition eq (t t' : t) := (EqSt (fst t) (fst t')) /\ (EqSt (snd t) (snd t')). 

Definition next (rr : t) : Λ := 
  let (inp,_) := rr in hd inp.

Definition put (v : Λ) (rr : t) : t :=
  let (inp,out) := rr in (tl inp,Cons v out).

Definition put_opt (v : option Λ) (rr : t) : t :=
  match v with
    | Some v' => put v' rr
    | _ => rr
  end.

Definition halts (rr : t) := 
  ForAll (fun st => halts (Streams.hd st)) (fst rr) /\
  ForAll (fun st => halts (Streams.hd st)) (snd rr).

Lemma halts_next t : 
  halts t -> Evaluation.halts (next t).
Proof.
  intros. destruct t; simpl; destruct H; simpl in *.
  destruct s; simpl in *; inversion H; now simpl in *.
Qed.

Lemma halts_put t v :
  halts t -> Evaluation.halts v -> halts (put v t).
Proof.
  intros; unfold put; destruct t; destruct H; split; simpl in *.
  - inversion H; auto.
  - split; simpl; auto.
Qed. 

Lemma halts_put_opt t v :
  halts t -> match v with Some v => Evaluation.halts v | _ => True end -> halts (put_opt v t).
Proof.
  intros. destruct v; auto. unfold put_opt; now apply halts_put.
Qed. 

#[export]
Instance eq_equiv : Equivalence eq.
Proof.
  split; unfold eq.
  - red; intros; destruct x; simpl in *; split; apply EqSt_reflex.
  - red; intros; destruct x,y; simpl in *; destruct H; split;
    apply sym_EqSt; auto.
  - red; intros; destruct x,y,z; simpl in *; destruct H,H0; split.
    -- eapply trans_EqSt; eauto.
    -- eapply trans_EqSt; eauto.
Qed.

End RFlow.