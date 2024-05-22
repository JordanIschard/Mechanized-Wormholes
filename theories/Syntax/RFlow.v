From Coq Require Import Lists.Streams Structures.Equalities Classes.Morphisms.
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

Definition well_typed_rflow (Γ : Γ) (Re : ℜ) (s : t) (α β : Τ) :=
  let (is,os) := s in 
  ForAll (fun v => Γ ⋅ Re ⊫ {Streams.hd v} ∈ α) is /\
  Streams.ForAll (fun v => match (Streams.hd v) with 
                            | Some v' => Γ ⋅ Re ⊫ v' ∈ β
                            | _ => True 
                           end) os.

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

Lemma wt_EqSt_left  Γ Re α : forall (s s1: Stream Λ),
  EqSt s s1 ->
  ForAll (fun v : Stream Λ => Γ ⋅ Re ⊫ {hd v} ∈ α) s ->
  ForAll (fun v : Stream Λ => Γ ⋅ Re ⊫ {hd v} ∈ α) s1.
cofix wt_EqSt_left.
  intros; destruct H,s,s1; simpl in *.
  destruct H0; split; simpl in *.
  - now rewrite <- H.
  - apply (wt_EqSt_left s s1); auto.
Qed.

Lemma wt_EqSt_left_bis  Γ Γ' Re Re' α: forall (s s1: Stream Λ),
  (Γ = Γ')%vc ->
  (Re = Re')%rc ->
  EqSt s s1 ->
  ForAll (fun v : Stream Λ => Γ ⋅ Re ⊫ {hd v} ∈ α) s ->
  ForAll (fun v : Stream Λ => Γ' ⋅ Re' ⊫ {hd v} ∈ α) s1.
cofix wt_EqSt_left.
  intros. destruct H1,s,s1. simpl in *.
  destruct H2; split; simpl in *.
  - subst. rewrite <- H. now rewrite <- H0.
  - apply (wt_EqSt_left s s1); auto.
Qed.

Lemma wt_EqSt_right  Γ Re α : forall (s s1: Stream (option Λ)),
  EqSt s s1 ->
  ForAll (fun v => match (Streams.hd v) with 
                            | Some v' => Γ ⋅ Re ⊫ v' ∈ α
                            | _ => True 
                           end) s ->
  ForAll (fun v => match (Streams.hd v) with 
                            | Some v' => Γ ⋅ Re ⊫ v' ∈ α
                            | _ => True 
                           end) s1.
cofix wt_EqSt_right.
  intros; destruct H,s,s1; simpl in *.
  destruct H0; split; simpl in *.
  - now rewrite <- H.
  - apply (wt_EqSt_right s s1); auto.
Qed.

Lemma wt_EqSt_right_bis  Γ  Γ' Re Re' α : forall (s s1: Stream (option Λ)),
  (Γ = Γ')%vc ->
  (Re = Re')%rc ->
  EqSt s s1 ->
  ForAll (fun v => match (Streams.hd v) with 
                            | Some v' => Γ ⋅ Re ⊫ v' ∈ α
                            | _ => True 
                           end) s ->
  ForAll (fun v => match (Streams.hd v) with 
                            | Some v' => Γ' ⋅ Re' ⊫ v' ∈ α
                            | _ => True 
                           end) s1.
cofix wt_EqSt_right.
  intros; destruct H1,s,s1; simpl in *.
  destruct H2; split; simpl in *.
  - destruct o0; subst.
    -- rewrite <- H. now rewrite <- H0.
    -- auto.
  - apply (wt_EqSt_right s s1); auto.
Qed.

#[export]
Instance wt_rflow_eq :
  Proper (VContext.eq ==> RContext.eq ==> eq ==> Typ.eq ==> Typ.eq ==> iff) well_typed_rflow.
Proof.
  repeat red; intros. apply Typ.eq_leibniz in H2,H3; subst.
  split; intros.
  - unfold well_typed_rflow in *. destruct x1,H2,y1.
    unfold eq in *. simpl in *; destruct H1. split.
    -- eapply wt_EqSt_left_bis; eauto.
    -- eapply wt_EqSt_right_bis; eauto. 
  - unfold well_typed_rflow in *. destruct y1,H2,x1.
    unfold eq in *. simpl in *; destruct H1. split.
    -- eapply wt_EqSt_left_bis; eauto; try (now symmetry).
       now apply sym_EqSt.
    -- eapply wt_EqSt_right_bis; eauto; try (now symmetry).
       now apply sym_EqSt.
Qed.

Lemma rflow_well_typed_next : forall Γ Re s α β,
  well_typed_rflow Γ Re s α β ->
  Γ ⋅ Re ⊫ {RFlow.next s} ∈ α.
Proof.
  intros. unfold well_typed_rflow in H. destruct s; simpl.
  destruct H as [H _]. now inversion H.
Qed.

Lemma rflow_weakening_Γ : forall Γ Γ' Re s α β,
  Γ ⊆ᵥᵪ Γ' ->
  well_typed_rflow Γ Re s α β ->
  well_typed_rflow Γ' Re s α β.
Proof.
  intros. unfold well_typed_rflow in *; destruct s,H0; split.
  - clear H1. revert H0. apply ForAll_coind; intros.
    -- destruct x. inversion H0; simpl in *.
       apply weakening_Γ with (Γ := Γ); assumption.
    -- destruct x; inversion H0; simpl in *; assumption.
  - clear H0. revert H1. apply ForAll_coind; intros.
    -- destruct x; inversion H0; simpl in *; destruct o; auto.
       apply weakening_Γ with (Γ := Γ); assumption.
    -- destruct x; inversion H0; simpl in *; assumption.
Qed.

Lemma rflow_weakening_ℜ : forall Γ Re Re' s α β,
  Re ⊆ᵣᵪ Re' ->
  well_typed_rflow Γ Re s α β ->
  well_typed_rflow Γ Re' s α β.
Proof.
  intros. unfold well_typed_rflow in *; destruct s,H0; split.
  - clear H1. revert H0. apply ForAll_coind; intros.
    -- destruct x. inversion H0; simpl in *.
       apply weakening_ℜ with (Re := Re); assumption.
    -- destruct x; inversion H0; simpl in *; assumption.
  - clear H0. revert H1. apply ForAll_coind; intros.
    -- destruct x; inversion H0; simpl in *; destruct o; auto.
       apply weakening_ℜ with (Re := Re); assumption.
    -- destruct x; inversion H0; simpl in *; assumption.
Qed.

Lemma rflow_well_typed_None : forall Γ Re s α β,
  well_typed_rflow Γ Re s α β ->
  well_typed_rflow Γ Re (RFlow.put None s) α β.
Proof.
  intros. unfold well_typed_rflow in *; destruct s; unfold put.
  destruct H; split.
  - now inversion H.
  - constructor; simpl; auto.
Qed.

Lemma rflow_well_typed_Some : forall Γ Re s v α β,
  well_typed_rflow Γ Re s α β ->
  Γ ⋅ Re ⊫ v ∈ β ->
  well_typed_rflow Γ Re (RFlow.put (Some v) s) α β.
Proof.
  intros. unfold well_typed_rflow in *; destruct s; unfold put.
  destruct H; split.
  - now inversion H.
  - constructor; simpl; auto.
Qed.

End RFlow.