From Coq Require Import Lists.List.
From Mecha Require Import RealResource REnvironment Term Functional Resource Cell Typing VContext Typ
               Resources Evaluation RContext.

(** * Transition - Temporal

rsf's semantics are divided in three sub semantics:
- evaluation transition
- functional transition
- temporal transition <--

*)

Module RE := REnvironment.
Reserved Notation "'Instₜₜ(' Re , Rf )" (at level 50).

(** *** Definition *)

Inductive temporal : RealResources.t -> RealResources.t -> Λ -> Λ -> Prop :=
 TT_instant : forall Vin Vout (R R' : RealResources.t) (P P' : Λ),

                    (Vin = RE.embeds (fst (RealResources.nexts R)))%re ->
                    ⪡ Vin ; unit ; P ⪢ ⭆ ⪡ Vout ; unit ; P' ⪢ ->
                    R' = RealResources.puts (RE.extracts Vout) (snd (RealResources.nexts R)) -> 
                    
                    temporal R R' P P'.

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

Inductive instantiation_temp : ℜ -> RealResources.t -> Prop :=
  | itTT_empty  : forall (Re : ℜ) (Fl : RealResources.t), 
                     isEmptyᵣᵪ(Re) -> Instₜₜ(Re,nil)

  | itTT_init   : forall (Re Re' : ℜ) (Fl : RealResources.t) (τ τ' : Τ) (r : RealResource.t),
      Instₜₜ(Re,Fl) ->
      Addᵣᵪ (newᵣᵪ(Re)) (τ,τ') Re Re' ->
      Streams.ForAll (fun v => ∅ᵥᵪ ⋅ Re ⊫ {Streams.hd v} ∈ τ) (fst r) -> 
      Streams.ForAll (fun v => ∅ᵥᵪ ⋅ Re ⊫ {Streams.hd v} ∈ τ') (snd r) -> 
      Instₜₜ(Re',Fl ++ (r :: nil))
(*
  | itfT_update : forall (Re : ℜ) (V V' : 𝓥) r (τ τ' : Τ) (v : Λ),
                    Instᵣₜ(Re,V) -> Re ⌈r ⩦ (τ,τ')⌉ᵣᵪ -> 
                    r ∈ᵣᵦ V -> Addᵣᵦ r ((⩽ … v ⩾)) V V' -> 
                    ∅ᵥᵪ ⋅ Re ⊫ v ∈ τ -> Instᵣₜ(Re,V')
*)
where "'Instₜₜ(' Re , Fl )" := (instantiation_temp Re Fl).

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

(** *** Proof of typing preservation through the temporal transition *)
Theorem temporal_preserves_typing (Re : ℜ) Rf Rf' (P P' : Λ) (R : resources) :

    (* (1) *) ∅ᵥᵪ ⋅ Re ⊫ P ∈ (𝟙 ⟿ 𝟙 ∣ R) ->
    (* (3) *) ⟦ Rf ; P ⟧ ⟾ ⟦ Rf' ; P' ⟧ ->
              Instₜₜ(Re,Rf) ->

  (*---------------------------------------------------------------------------------------------*)
      ∅ᵥᵪ ⋅ Re ⊫ P' ∈ (𝟙 ⟿ 𝟙 ∣ R) /\ Instₜₜ(Re,Rf').
Proof.
  intros HwP HTT Hinst; inversion HTT; subst. 
  (*
  destruct (RealResources.nexts Rf) as [sample tail]; simpl in *.
  eapply functional_preserves_typing in H0; eauto.
  - split; destruct H0 as [_ [_ [HinstV [_ [_ HwP']]]]].
    -- assumption.
    -- 
  - now constructor.
  - now rewrite H.
Qed.*)
Admitted.

(*
(** *** Proof of typing preservation through multi temporal transitions *)
Theorem multi_temporal_preserves_typing (Re : ℜ) Rf Rf' (P P' : Λ) (R : resources) :

    (* (1) *) ∅ᵥᵪ ⋅ Re ⊫ P ∈ (𝟙 ⟿ 𝟙 ∣ R) ->
    (* (3) *) ⟦ Rf ; P ⟧ ⟾⋆ ⟦ Rf' ; P' ⟧ ->
              Instᵣₜ(Re,RE.embeds (fst (RealResources.nexts Rf))) ->

  (*---------------------------------------------------------------------------------------------*)
      ∅ᵥᵪ ⋅ Re ⊫ P' ∈ (𝟙 ⟿ 𝟙 ∣ R).
Proof.
  intros HwP HTT Hinst; induction HTT; subst.
  eapply temporal_preserves_typing in H; eauto; apply IHHTT; auto.  
  destruct (RealResources.nexts Rf) as [sample tail]; simpl in *.
  eapply functional_preserves_typing in H0; eauto.
  - now destruct H0 as [_ [_ [_ [_ [_ HwP']]]]].
  - now constructor.
  - now rewrite H.
Qed.
*)

Theorem progress_of_temporal (Re : ℜ) (Rf : RealResources.t) (P : Λ) (R : resources) :

  (* (1) *) halts P -> (* (2) *) RealResources.halts Rf -> (* (3) *) all_arrow_halting ->

  (* (4) *) ∅ᵥᵪ ⋅ Re ⊫ P ∈ (𝟙 ⟿ 𝟙 ∣ R) -> (* (5) *) Instₜₜ(Re,Rf) ->
  
  (*-------------------------------------------------------------------------------------------------*)
    exists Rf' P',  (* (6) *) ⟦ Rf ; P ⟧ ⟾⋆ ⟦ Rf' ; P' ⟧ /\ 
                    (* (7) *) halts P' /\ (* (8) *) RealResources.halts Rf.
Proof. 
Admitted.