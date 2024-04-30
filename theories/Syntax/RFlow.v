From Coq Require Import Lists.Streams Structures.Equalities.
From Mecha Require Import Term Typ Evaluation Resource VContext RContext Typing.
From DeBrLevel Require Import LevelInterface.

Module RFlow <: EqualityType.

Import Streams.

Definition t : Type := (Stream Λ * Stream (option Λ)).

Definition eq (t t' : t) := (EqSt (fst t) (fst t')) /\ (EqSt (snd t) (snd t')). 

Definition next (rr : t) : Λ := 
  let (inp,_) := rr in hd inp.

Definition put (v : option Λ) (rr : t) : t :=
  let (inp,out) := rr in (tl inp,Cons v out).

Definition update (rr : t) : t :=
  let (inp,out) := rr in (tl inp,out).

Definition halts (rr : t) := 
  ForAll (fun st => halts (Streams.hd st)) (fst rr) /\
  ForAll (fun st => match (Streams.hd st) with Some st' => halts st' | _ => True end) (snd rr).

Definition inp_wt Re (τ : Τ) (rr : t) :=
      Streams.ForAll (fun v => ∅ᵥᵪ ⋅ Re ⊫ {Streams.hd v} ∈ τ) (fst rr).

Definition out_wt Re (τ : Τ) (rr : t) :=
  Streams.ForAll (fun v => match (Streams.hd v) with 
                            | Some v' => ∅ᵥᵪ ⋅ Re ⊫ v' ∈ τ
                            | _ => True 
                           end) (snd rr).


Lemma halts_next t : 
  halts t -> Evaluation.halts (next t).
Proof.
  intros. destruct t; simpl; destruct H; simpl in *.
  destruct s; simpl in *; inversion H; now simpl in *.
Qed.

Lemma halts_put_Some t v :
  halts t -> Evaluation.halts v -> halts (put (Some v) t).
Proof.
  intros; unfold put; destruct t; destruct H; split; simpl in *.
  - inversion H; auto.
  - split; simpl; auto.
Qed. 

Lemma halts_put_None t :
  halts t -> halts (put None t).
Proof.
  intros; unfold put; destruct t; destruct H; split; simpl in *.
  - inversion H; auto.
  - split; simpl; auto.
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