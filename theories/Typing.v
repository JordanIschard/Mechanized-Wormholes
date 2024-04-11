From Coq Require Import Lia Arith.PeanoNat Program Bool.Bool Classes.Morphisms.
Require Import Typ Resource Resources Term Var VContext RContext.


(** * Typing 

  Definition of rsf typing rules.
*)

(** *** Definition *)

Reserved Notation "G '⋅' R '⊫' t '∈' T" (at level 40, t custom rsf, T custom rsf).

Inductive well_typed : Γ -> ℜ -> Λ -> Τ -> Prop :=
  | wt_var    : forall Γ R (x : Var.t) τ,
                            Γ ⌈x ⩦ τ⌉ᵥᵪ -> 
                (*------------------------------- WT-Var *)
                    Γ ⋅ R ⊫ {Term.tm_var x} ∈ τ

  | wt_abs    : forall Γ Re x τ2 τ1 t1,
                    (⌈x ⤆ τ1⌉ᵥᵪ Γ) ⋅ Re ⊫ t1 ∈ τ2 ->
                (*---------------------------------- WT-Abs *)
                  Γ ⋅ Re ⊫ (\x:τ1, t1) ∈ (τ1 → τ2)

  | wt_app    : forall Γ Re (τ2 τ : Τ) t1 t2,
                  Γ ⋅ Re ⊫ t1 ∈ (τ2 → τ) -> Γ ⋅ Re ⊫ t2 ∈ τ2 -> 
                (*----------------------------------------------- WT-App *)
                                Γ ⋅ Re ⊫ t1 t2 ∈ τ

  | wt_unit   : forall Γ Re, 
                (*------------------- WT-Unit *)
                  Γ ⋅ Re ⊫ unit ∈ 𝟙       

  | wt_pair   : forall Γ Re t1 t2 τ1 τ2,
                  Γ ⋅ Re ⊫ t1 ∈ τ1 -> Γ ⋅ Re ⊫ t2 ∈ τ2 -> 
                (*----------------------------------------- WT-Pair *)
                      Γ ⋅ Re ⊫ ⟨t1, t2⟩ ∈ (τ1 × τ2)

  | wt_fst    : forall Γ Re t (τ1 τ2 : Τ),
                  Γ ⋅ Re ⊫ t ∈ (τ1 × τ2) -> 
                (*--------------------------- WT-Fst *)
                    Γ ⋅ Re ⊫ t.fst ∈ τ1

  | wt_snd    : forall Γ Re t (τ1 τ2 : Τ),
                  Γ ⋅ Re ⊫ t ∈ (τ1 × τ2) -> 
                (*--------------------------- T-Snd *)
                    Γ ⋅ Re ⊫ t.snd ∈ τ2

  | wt_fix    : forall Γ Re t (τ : Τ),
                    Γ ⋅ Re ⊫ t ∈ (τ → τ) ->
                (*----------------------------- WT-Fix *)
                    Γ ⋅ Re ⊫ Fix t ∈ τ

  | wt_arr    : forall Γ Re t (τ1 τ2 : Τ),
                      Γ ⋅ Re ⊫ t ∈ (τ1 → τ2) -> 
                (*---------------------------------- WT-Arr *)
                  Γ ⋅ Re ⊫ arr(t) ∈ (τ1 ⟿ τ2 ∣ ∅ᵣₛ)

  | wt_first  : forall Γ Re R t (τ1 τ2 τ : Τ),
                          Γ ⋅ Re ⊫ t ∈ (τ1 ⟿ τ2 ∣ R) ->
                (*------------------------------------------------ WT-First *)
                  Γ ⋅ Re ⊫ first(τ:t) ∈ ((τ1 × τ) ⟿ (τ2 × τ) ∣ R)

  | wt_comp   : forall Γ Re (R R1 R2 : resources) t1 t2 (τ1 τ τ2 : Τ),
                  Γ ⋅ Re ⊫ t1 ∈ (τ1 ⟿ τ ∣ R1) -> (R   = (R1 ∪ R2))%rs -> 
                  Γ ⋅ Re ⊫ t2 ∈ (τ ⟿ τ2 ∣ R2) -> (∅ᵣₛ = (R1 ∩ R2))%rs -> 
                (*----------------------------------------------------- WT-Comp *)
                      Γ ⋅ Re ⊫ (t1 >>> t2) ∈ (τ1 ⟿ τ2 ∣ R)

  | wt_rsf    : forall Γ (Re : ℜ) (r : resource) τin τout,
                        Re ⌈ r ⩦ (τin,τout) ⌉ᵣᵪ ->
                (*------------------------------------------ WT-Rsf *)
                  Γ ⋅ Re ⊫ rsf[r] ∈ (τin ⟿ τout ∣ \{{r}})

where "G '⋅' R '⊫' t '∈' T" := (well_typed G R t T).

Notation "G '⋅' R '⊫' t '∈' T" := (well_typed G R t T) (at level 40, 
                                                            t custom rsf, 
                                                            T custom rsf).

(** *** Some facts *)

#[global] 
Instance well_typed_rc :
  Proper (VContext.eq ==> RContext.eq ==> Term.eq ==> Typ.eq ==> iff) well_typed.
Proof.
  repeat red; intros Γ Γ' HΓeq Re Re' Hℜeq t t' HΛeq τ τ' HΤeq; split; 
  unfold Term.eq,Typ.eq in *; subst.
  - revert Γ Γ' τ' Re Re' HΓeq Hℜeq. induction t'; intros Γ Γ' τ' Re Re' HΓeq Hℜeq Hwt;
    inversion Hwt; subst; try (econstructor; now eauto).
    -- constructor; now rewrite <- HΓeq.
    -- apply wt_abs; try (now rewrite <- Hℜeq).
       apply IHt' with (Re := Re) (Γ := ⌈ v ⤆ τ ⌉ᵥᵪ Γ); auto.
       now rewrite <- HΓeq.
    -- apply wt_rsf; now rewrite <- Hℜeq.
  - revert Γ Γ' τ' Re Re' HΓeq Hℜeq; induction t'; intros Γ Γ' τ' Re Re' HΓeq Hℜeq Hwt;
    inversion Hwt; subst; try (econstructor; now eauto).
    -- constructor; now rewrite HΓeq.
    -- apply wt_abs; try (now rewrite Hℜeq).
       apply IHt' with (Re' := Re') (Γ' := ⌈ v ⤆ τ ⌉ᵥᵪ Γ'); auto.
       now rewrite HΓeq.
    -- apply wt_rsf; now rewrite Hℜeq.
Qed.

Fact ill_typed_rsf : forall Γ (τ : Τ) r, ~ Γ ⋅ ∅ᵣᵪ ⊫ rsf[r] ∈ τ.
Proof. intros; intro; inversion H; subst; inversion H3. Qed.

Fact well_typed_rsf_implies_notEmpty : forall Γ (Re : ℜ) (τ : Τ) r,
  Γ ⋅ Re ⊫ rsf[r] ∈ τ -> ~ isEmptyᵣᵪ(Re).
Proof.
  intros; intro; inversion H; subst.
  unfold RContext.OP.P.Empty in *; destruct (H0 r (τin,τout)).
  now apply RContext.OP.P.find_2.
Qed.

Fact context_invariance : forall Γ Γ' Re t τ, 
  (forall x, isFV(x,t) -> Γ ⌊x⌋ᵥᵪ = Γ' ⌊x⌋ᵥᵪ) ->
  Γ ⋅ Re ⊫ t ∈ τ -> Γ' ⋅ Re ⊫ t ∈ τ.
Proof.
  intros Γ Γ' Re t τ Hc Hwt.
  generalize dependent Γ'.
  dependent induction Hwt; intros; try (now eauto); try (econstructor; now eauto).
  (* var *)
  - constructor. rewrite <- H; symmetry; now apply Hc.
  (* abs *)
  - constructor; auto. apply IHHwt; intros x1 Hafi. destruct (Var.eq_dec x x1).
    -- repeat rewrite VContext.OP.P.add_eq_o; auto.
    -- repeat rewrite VContext.OP.P.add_neq_o; auto.
Qed.

Fact free_in_context : forall x t τ Γ Re,
  isFV(x,t) -> Γ ⋅ Re ⊫ t ∈ τ -> x ∈ᵥᵪ Γ.
Proof with eauto.
  intros x t τ Γ Re Hafi Htyp; induction Htyp; inversion Hafi; subst; eauto.
  - exists τ; now apply VContext.OP.P.find_2.
  - apply IHHtyp in H4. rewrite VContext.OP.P.add_in_iff in H4; 
    destruct H4; subst; auto. contradiction.
  - inversion H1.
Qed.

Fact well_typed_empty_closed : forall Re t τ,
  ∅ᵥᵪ ⋅ Re ⊫ t ∈ τ -> clₜₘ(t).
Proof.
  intros. unfold Term.closed. intros x H1.
  eapply free_in_context in H; eauto. inversion H.
  apply VContext.OP.P.empty_mapsto_iff in H0; contradiction.
Qed.

Fact canonical_form : forall Γ Re t α β R,
  value(t) -> Γ ⋅ Re ⊫ t ∈ (α ⟿ β ∣ R) -> 

  (exists t', t = <[arr(t')]>)        \/ 
  (exists τ t', t = <[first(τ:t')]>)  \/ 
  (exists r, t = <[rsf[r]]>)          \/ 
  (exists t' t'', t = <[t' >>> t'']>).
Proof.
  intros Γ Re t; revert Γ Re; induction t; intros Γ Re α β R Hvt Hwt;
  inversion Hvt; inversion Hwt; subst.
  - left; now exists t.
  - right; left; exists τ;now exists t.
  - right; right; right; exists t1; now exists t2.
  - right; right; left; now exists r.
Qed.

(** *** Proof of determinism 

  If a term is well typed according to the same contexts with two types τ and τ';
  then τ and τ' are equivalent.    
*)
Lemma typing_deterministic : forall t Γ Re τ τ',
  Γ ⋅ Re ⊫ t ∈ τ  -> 
  Γ ⋅ Re ⊫ t ∈ τ' -> 

  (τ = τ')%typ.
Proof.
  intro t; induction t; intros Γ Re τ1 τ1' Hwt Hwt'; inversion Hwt; inversion Hwt'; subst. 
  - rewrite H2 in *; inversion H7; subst; reflexivity.
  - apply IHt1 with (τ := <[τ2 → τ1]>) in H10; auto.
    inversion H10; subst; reflexivity.
  - inversion H3.
  - inversion H9.
  - apply IHt2 with (τ := <[τ1 → τ1]>) in H10; auto.
    inversion H10; subst; reflexivity.
  - apply IHt with (τ := τ2) in H12; auto.
    inversion H12; subst; reflexivity.
  - apply IHt1 with (τ := τ0) in H10; auto.
    apply IHt2 with (τ := τ2) in H12; auto. now rewrite H10,H12.
  - apply IHt with (τ := <[τ1 × τ2]>) in H7; auto.
    inversion H7; subst; reflexivity.
  - apply IHt with (τ := <[τ0 × τ1]>) in H7; auto.
    inversion H7; subst; reflexivity.
  - apply IHt with (τ := <[τ0 → τ2]>) in H7; auto.
    inversion H7; subst; reflexivity.
  - apply IHt with (τ := <[τ0 ⟿ τ2 ∣ R]>) in H10; auto.
    inversion H10; subst; reflexivity.
  - apply IHt1 with (τ := <[τ0 ⟿ τ ∣ R1]>) in H10; auto.
    apply IHt2 with (τ := <[τ ⟿ τ2 ∣ R2]>) in H14; auto.
    inversion H10; inversion H14; subst.
    apply Resources.eq_leibniz in H2,H11; now subst.
  - rewrite H2 in H7; inversion H7; now subst.
  - reflexivity.
Qed.

(** *** Proof that the used resources set is in the resource context

  If a well typed value is reactive and, consequently, has a set of used resources R;
  then all resources identifiers contained in R are also in Re.
*)
Lemma typing_Re_R : forall t Γ Re τ τ' R,
  value(t) -> 
  Γ ⋅ Re ⊫ t ∈ (τ ⟿ τ' ∣ R) -> 

  (forall (r : resource), r ∈ R -> r ∈ᵣᵪ Re)%rs.
Proof.
  intro t; induction t; intros Γ Re τ1 τ1' R Hvt Hwt r1 HIn; inversion Hvt; subst; 
  inversion Hwt; subst.
  - inversion HIn.
  - eapply IHt; eauto.
  - apply Resources.eq_leibniz in H9. rewrite H9 in HIn. rewrite Resources.union_spec in HIn.
    destruct HIn; eauto.
  - rewrite Resources.singleton_spec in HIn; subst; apply RContext.OP.P.in_find; intro.
    rewrite H3 in H; inversion H.
Qed.

(** *** Proof of variable context weakening *)
Theorem weakening_Γ : forall t Γ Γ' Re τ,
  Γ ⊆ᵥᵪ Γ' -> 
  Γ ⋅ Re ⊫ t ∈ τ -> 
  
  Γ' ⋅ Re ⊫ t ∈ τ .
Proof.
  intros t Γ Γ' Re τ HSub wtt. generalize dependent Γ'.
  dependent induction wtt; intros Γ' HSub; try (econstructor; now eauto).
  - constructor. eapply VContext.Submap_find_spec; eauto.
  - econstructor; eauto; eapply IHwtt. now apply VContext.Submap_add_spec.
Qed.

(** *** General proof of resource context weakening *)
Theorem weakening_ℜ : forall Γ (Re Re' : ℜ) t (τ : Τ),
  Re ⊆ᵣᵪ Re' -> Γ ⋅ Re ⊫ t ∈ τ -> 

  Γ ⋅ Re' ⊫ t ∈ τ.
Proof.
  simpl; intros Γ Re Re' t τ Hsub wt; revert Re' Hsub.
  dependent induction wt; intros Re' Hsub; simpl; try (econstructor; now eauto); eauto.
  (* rsf *)
  constructor. apply RContext.Submap_find_spec with (m := Re); auto.
Qed. 

(** *** Weakening corollaries *)

Corollary weakening_Γ_empty : forall Γ Re t τ,
  ∅ᵥᵪ ⋅ Re ⊫ t ∈ τ -> 
  
  Γ ⋅ Re ⊫ t ∈ τ.
Proof. intros Γ Re t τ; eapply weakening_Γ. apply VContext.Submap_empty_spec. Qed.