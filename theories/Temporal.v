From Coq Require Import Lists.Streams micromega.Lia Relations.Relation_Definitions 
                        Classes.RelationClasses Relations.Relation_Operators Program.
Require Import Term Typ Var Substitution Typing Evaluation 
               Functional Context.

Module Reference.

Definition t : Type := (Stream Λ * Stream Λ).

Definition next (rf : t) : Λ * t := (Streams.hd (fst rf), (Streams.tl (fst rf),snd rf)).

Definition put (v : Λ) (rf : t) : t := (fst rf,Streams.Cons v (snd rf)).

Definition ForAllIn (P : Stream Λ -> Prop) (rf : t) : Prop := Streams.ForAll P (fst rf).
Definition ForAllOut (P : Stream Λ -> Prop) (rf : t) : Prop := Streams.ForAll P (snd rf).

End Reference.

(** * Transition - Temporal

Wormholes's semantics are divided in three sub semantics:
- evaluation transition
- functional transition
- temporal transition <--

*)



(** *** Definition *)

Reserved Notation "⟦ R ; P ⟧ ⟾ ⟦ R' ; P' ⟧" (at level 57, R constr, R' constr,
                                                           P custom arrow, P' custom arrow,
                                                           no associativity).
Reserved Notation "⟦ R ; P ⟧ ⟾⋆ ⟦ R' ; P' ⟧" (at level 57, R constr, R' constr,
                                                           P custom arrow, P' custom arrow,
                                                           no associativity).

Inductive temporal : Reference.t * Λ -> Reference.t * Λ -> Prop :=
  | TT_step : forall (St St' : Reference.t) (P P' v' : Λ),
  
                  let (v,St1) := Reference.next St in
                          ⪡ v ; P ⪢ ⭆ ⪡ v' ; P' ⪢ ->
                         St' =  Reference.put v' St1 -> 
              (*-----------------------------------------------*)
                       ⟦ St ; P ⟧ ⟾ ⟦ St' ; P' ⟧

where  "⟦ R ; P ⟧ ⟾ ⟦ R' ; P' ⟧" := (temporal (R,P) (R',P')).

(** **** Multi transition step *)
Inductive temporal_multi : Reference.t * Λ -> Reference.t * Λ -> Prop :=
  | mTT_TT   :  forall R R' P P', ⟦ R ; P ⟧ ⟾ ⟦ R' ; P' ⟧ -> ⟦ R ; P ⟧ ⟾⋆ ⟦ R' ; P' ⟧
  | mTT_step :  forall R R' R'' P P' P'', 
                    ⟦ R ; P ⟧ ⟾ ⟦ R' ; P' ⟧ -> ⟦ R' ; P' ⟧ ⟾⋆ ⟦ R'' ; P'' ⟧ -> 
                (*-----------------------------------------------------------------*)  
                                 ⟦ R ; P ⟧ ⟾⋆ ⟦ R'' ; P'' ⟧

where "⟦ R ; P ⟧ ⟾⋆ ⟦ R' ; P' ⟧" := (temporal_multi (R,P) (R',P')).



Lemma temporal_multi_trans : Transitive temporal_multi.
Proof.
 repeat red; intros; destruct x,y,z; simpl in *.
 revert t1 λ1 H0; induction H; intros; eapply mTT_step; eauto.
Qed.


(** ** Preservation *)


(**
  *** General proof of preservation of typing through temporal transition

*)
Theorem temporal_preserves_typing : 
  forall (St St' : Reference.t) (P P' : Λ) (α β : Τ),
    ∅ᵧ ⊫ P ∈ (α ⟿ β) ->

    Reference.ForAllIn (fun st => ∅ᵧ ⊫ {Streams.hd st} ∈ α) St ->
    Reference.ForAllOut (fun st => ∅ᵧ ⊫ {Streams.hd st} ∈ β) St ->

    ⟦ St ; P ⟧ ⟾ ⟦ St' ; P' ⟧ -> 


    ∅ᵧ ⊫ P' ∈ (α ⟿ β) /\
    Reference.ForAllIn (fun st => ∅ᵧ ⊫ {Streams.hd st} ∈ α) St' /\
    Reference.ForAllOut (fun st => ∅ᵧ ⊫ {Streams.hd st} ∈ β) St'.
Proof.
  intros St St' P P' α β HwP HFinSt HFoutSt HtT.
  inversion HtT; subst; clear HtT.
  destruct St; unfold Reference.ForAllIn, Reference.ForAllOut in *; simpl in *.
  rewrite (Streams.unfold_Stream s) in *; destruct s; simpl in *.
  inversion HFinSt; subst; simpl in *.

  eapply functional_preserves_typing in H; eauto; destruct H as [Hwv' HwP'].
  split; auto; split; auto. constructor; simpl; auto.
Qed.

Theorem multi_temporal_preserves_typing : 
  forall (St St' : Reference.t) (P P' : Λ) (α β : Τ),
    ∅ᵧ ⊫ P ∈ (α ⟿ β) ->

    Reference.ForAllIn (fun st => ∅ᵧ ⊫ {Streams.hd st} ∈ α) St ->
    Reference.ForAllOut (fun st => ∅ᵧ ⊫ {Streams.hd st} ∈ β) St ->

    ⟦ St ; P ⟧ ⟾⋆ ⟦ St' ; P' ⟧ -> 


    ∅ᵧ ⊫ P' ∈ (α ⟿ β) /\
    Reference.ForAllIn (fun st => ∅ᵧ ⊫ {Streams.hd st} ∈ α) St' /\
    Reference.ForAllOut (fun st => ∅ᵧ ⊫ {Streams.hd st} ∈ β) St'.
Proof.
  intros St St' P P' α β HwP HFinSt HFoutSt HmTT.
  revert α β HwP HFinSt HFoutSt; dependent induction HmTT; intros.
  - apply temporal_preserves_typing with (α := α) (β := β) in H; auto.
  - eapply temporal_preserves_typing in H; eauto. destruct H as [HwP' [HFinSt' HFoutSt']].
    eapply IHHmTT; auto.
Qed.


(** ** Progress *)

Theorem progress_of_temporal : 
  forall St (P : Λ) (α β : Τ),
    Reference.ForAllIn (fun st => ∅ᵧ ⊫ {Streams.hd st} ∈ α) St ->
    Reference.ForAllOut (fun st => ∅ᵧ ⊫ {Streams.hd st} ∈ β) St ->
    ∅ᵧ ⊫ P ∈ (α ⟿ β) -> 

    Reference.ForAllIn (fun st => halts (Streams.hd st)) St ->
    Reference.ForAllOut (fun st => halts (Streams.hd st)) St ->
    halts P ->
    all_arrow_halting ->

    exists St' (P' : Λ), 
      ⟦ St ; P ⟧ ⟾ ⟦ St' ; P' ⟧ /\
      Reference.ForAllIn (fun st => halts (Streams.hd st)) St' /\
      Reference.ForAllOut (fun st => halts (Streams.hd st)) St' /\
      halts P'.
Proof. 
  intros. destruct St; unfold Reference.ForAllIn, Reference.ForAllOut in *; simpl in *.
  rewrite (Streams.unfold_Stream s) in *; destruct s; simpl in *.
  inversion H; subst; simpl in *; inversion H2; subst; simpl in *.
  eapply (progress_of_functional λ P α β) in H1; eauto.
  destruct H1 as [sv' [P' [HfT [Hlt Hlt']]]].

  exists (Reference.put sv' (snd (Reference.next ((Cons λ s), s0)))); 
  exists P'; simpl in *; split.
  - eapply TT_step; simpl in *; auto. apply HfT.
  - split; auto; split; auto. constructor; auto.
Qed.