From Coq Require Import Lists.Streams micromega.Lia Relations.Relation_Definitions 
                        Classes.RelationClasses Relations.Relation_Operators.
Require Import Resource Resources Term Typ Var Substitution 
               Typing VContext RContext Evaluation REnvironment 
               Functional Stock Cell ReadStock WriteStock.

Module Reference.

Definition t : Type := (Stream Λ * Stream Λ).

Definition next (rf : t) : Λ * t := (Streams.hd (fst rf), (Streams.tl (fst rf),snd rf)).

Definition put (v : Λ) (rf : t) : t := (fst rf,Streams.Cons v (snd rf)).

End Reference.

(** * Transition - Temporal

Wormholes's semantics are divided in three sub semantics:
- evaluation transition
- functional transition
- temporal transition <--

*)

Module Re := REnvironment.
Module Sk := Stock.


(** *** Definition *)

Definition ℝ := list Reference.t.

Definition nexts (fl : ℝ) : list Λ * ℝ := List.split (List.map Reference.next fl).

Definition puts (vl : list (option Λ)) (fl : ℝ) : ℝ := 
  List.map (fun vf => match (fst vf) with Some v => Reference.put v (snd vf) | _ => snd vf end) (List.combine vl fl).

Reserved Notation "⟦ R ; W ; P ⟧ ⟾ ⟦ R' ; W' ; P' ⟧" (at level 57, R constr, R' constr, W constr, W' constr,
       P custom wormholes, P' custom wormholes, no associativity).

Inductive temporal : ℝ -> ℝ -> 𝐖 -> 𝐖 -> Λ -> Λ -> Prop :=
  | TT_init : forall Fl Fl' W' P P' Vin Vout Wnew,
                
                      (Vin = Re.embeds (fst (nexts Fl)))%re ->

                ⪡ Vin ; unit ; P ⪢ ⭆ ⪡ Vout ; unit ; P' ; Wnew ⪢ ->

                      Fl' = puts (Re.extracts Vout) (snd (nexts Fl)) ->
                       (W' = Sk.update Wnew Vout)%sk ->
              (*------------------------------------------------------*)
                      ⟦ Fl ; ∅ₛₖ ; P ⟧ ⟾ ⟦ Fl' ; W' ; P' ⟧

  | TT_step : forall Fl Fl' Fl'' W W' W'' P P' P'' Vin Vout Wnew,

                          ⟦ Fl ; W ; P ⟧ ⟾ ⟦ Fl' ; W' ; P' ⟧ ->
                  (Vin =  Sk.init_virtual W' (Re.embeds (fst (nexts Fl'))))%re ->

                      ⪡ Vin ; unit ; P' ⪢ ⭆ ⪡ Vout ; unit ; P'' ; Wnew ⪢ ->

                            Fl'' = puts (Re.extracts Vout) (snd (nexts Fl')) ->
                          (W'' = Sk.update (W' ∪ Wnew) Vout)%sk ->
              (*----------------------------------------------------------------*)
                      ⟦ Fl' ; W' ; P' ⟧ ⟾ ⟦ Fl'' ; W'' ; P'' ⟧

where  "⟦ R ; W ; P ⟧ ⟾ ⟦ R' ; W' ; P' ⟧" := (temporal R R' W W' P P').

(** *** Notations *)

Notation "⟦ R ; W ; P ⟧ ⟾ ⟦ R' ; W' ; P' ⟧" := (temporal R R' W W' P P') 
                                                      (at level 57, R constr, R' constr, W constr, W' constr,
                                                           P custom wormholes, P' custom wormholes, no associativity).
                                                              
(** *** Initialization *)

Theorem initialization_unused : forall W l,
  REnvironment.For_all (fun _ v => Cell.unused v) (Sk.init_virtual W (Re.embeds l)).
Proof.
  intros.
  apply Sk.init_virtual_unused; apply Re.embedding_Forall_unused.
  unfold Re.For_all; intros. inversion H.
Qed.

Lemma resource_used_init_unused : forall Re t α β R l W V,
  ∅ᵥᵪ ⋅ Re ⊫ t ∈ (α ⟿ β ∣ R) ->
  value(t) ->
  Instᵣₜ(Re,V) ->
  (V = (Sk.init_virtual W (Re.embeds l)))%re ->
  
  (forall r, (r ∈ R)%rs -> Re.unused r V).
Proof.
  intros. apply typing_Re_R with (r := r) in H; auto.
  apply instantiation_in with (V := V) in H; auto.
  rewrite H2 in *. destruct H; apply RE.OP.P.find_1 in H.
  apply initialization_unused in H as H'; destruct x; inversion H'.
  exists λ. now rewrite H2.
Qed. 
