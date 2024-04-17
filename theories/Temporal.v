
Require Import RealResource REnvironment Term Functional Resource Cell Typing VContext Typ
               Resources Evaluation.

(** * Transition - Temporal

rsf's semantics are divided in three sub semantics:
- evaluation transition
- functional transition
- temporal transition <--

*)

Module RE := REnvironment.


(** *** Definition *)

Definition temporal (R R' : RealResources.t) (P P' : Λ) : Prop :=
  let (sample,tl) := RealResources.nexts R in
  forall Vin Vout,

    (Vin = RE.embeds sample)%re /\

    ⪡ Vin ; unit ; P ⪢ ⭆ ⪡ Vout ; unit ; P' ⪢ /\

    R' = RealResources.puts (RE.extracts Vout) tl.

Notation "'⟦' R ';' P '⟧' '⟾' '⟦' R1 ';' P1 '⟧'" := (temporal R R1 P P1) 
                                                     (at level 30, R constr, R1 constr,
                                                         P custom rsf, P1 custom rsf, 
                                                        no associativity).

Inductive multi_temporal : RealResources.t -> RealResources.t -> Λ -> Λ -> Prop :=
  TT_step : forall R R' R'' (P P' P'' : Λ), 
                  ⟦ R ; P ⟧ ⟾ ⟦ R' ; P' ⟧ -> 
                  multi_temporal R' R'' P' P'' -> 
                  multi_temporal R R'' P P''.

Notation "'⟦' R ';' P '⟧' '⟾⋆' '⟦' R1 ';' P1 '⟧'" := (multi_temporal R R1 P P1) 
                                                     (at level 30, R constr, R1 constr,
                                                         P custom rsf, P1 custom rsf, 
                                                        no associativity).

(** *** Initialization *)

Theorem initialization_unused : forall l,
  RE.For_all (fun _ v => Cell.unused v) (RE.embeds l).
Proof.
  intros. apply RE.embedding_Forall_unused.
  unfold RE.For_all; intros. inversion H.
Qed.

Lemma resource_used_init_unused : forall Re t α β R l V,
  ∅ᵥᵪ ⋅ Re ⊫ t ∈ (α ⟿ β ∣ R) ->
  halts t ->
  Instᵣₜ(Re,V) ->
  (V = (RE.embeds l))%re ->
  
  (forall r, (r ∈ R)%rs -> RE.unused r V).
Proof.
  intros. destruct H0 as [t' [HmeT Hvt']].
  apply multi_preserves_typing with (t' := t') in H; auto.
  apply typing_Re_R with (r := r) in H; auto.
  apply instantiation_in with (V := V) in H; auto.
  rewrite H2 in *. destruct H; apply RE.OP.P.find_1 in H.
  apply initialization_unused in H as H'; destruct x; inversion H'.
  exists λ. now rewrite H2.
Qed. 