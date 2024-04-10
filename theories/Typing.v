From Coq Require Import Lia Arith.PeanoNat Program Bool.Bool Classes.Morphisms.
Require Import Typ Term Var Context.


(** * Typing 

  Definition of arrow typing rules.
*)

(** *** Definition *)

Reserved Notation "G '⊫' t '∈' T" (at level 40, t custom arrow, T custom arrow).

Inductive well_typed : Γ -> Λ -> Τ -> Prop :=
  | wt_var    : forall Γ (x : Var.t) τ,
                          Γ ⌈x ⩦ τ⌉ᵧ -> 
                (*---------------------------- WT-Var *)
                    Γ ⊫ {Term.tm_var x} ∈ τ

  | wt_abs    : forall Γ x τ2 τ1 t1,
                    (⌈x ⤆ τ1⌉ᵧ Γ) ⊫ t1 ∈ τ2 ->
                (*-------------------------------- WT-Abs *)
                    Γ ⊫ (\x:τ1, t1) ∈ (τ1 → τ2)

  | wt_app    : forall Γ (τ2 τ : Τ) t1 t2,
                  Γ ⊫ t1 ∈ (τ2 → τ) -> Γ ⊫ t2 ∈ τ2 -> 
                (*-------------------------------------- WT-App *)
                           Γ ⊫ t1 t2 ∈ τ

  | wt_unit   : forall Γ, 
                (*----------------- WT-Unit *)
                    Γ ⊫ unit ∈ 𝟙       

  | wt_pair   : forall Γ t1 t2 τ1 τ2,
                    Γ ⊫ t1 ∈ τ1 -> Γ ⊫ t2 ∈ τ2 -> 
                (*---------------------------------- WT-Pair *)
                      Γ ⊫ ⟨t1, t2⟩ ∈ (τ1 × τ2)

  | wt_fst    : forall Γ t (τ1 τ2 : Τ),
                  Γ ⊫ t ∈ (τ1 × τ2) -> 
                (*----------------------- WT-Fst *)
                    Γ ⊫ t.fst ∈ τ1

  | wt_snd    : forall Γ t (τ1 τ2 : Τ),
                  Γ ⊫ t ∈ (τ1 × τ2) -> 
                (*---------------------- T-Snd *)
                    Γ ⊫ t.snd ∈ τ2

  | wt_fix    : forall Γ t (τ : Τ),
                    Γ ⊫ t ∈ (τ → τ) ->
                (*----------------------- WT-Fix *)
                    Γ ⊫ Fix t ∈ τ

  | wt_arr    : forall Γ t (τ1 τ2 : Τ),
                     Γ ⊫ t ∈ (τ1 → τ2) -> 
                (*---------------------------- WT-Arr *)
                    Γ ⊫ arr(t) ∈ (τ1 ⟿ τ2)

  | wt_first  : forall Γ t (τ1 τ2 τ : Τ),
                            Γ ⊫ t ∈ (τ1 ⟿ τ2) ->
                (*---------------------------------------------- WT-First *)
                    Γ ⊫ first(τ:t) ∈ ((τ1 × τ) ⟿ (τ2 × τ))

  | wt_comp   : forall Γ t1 t2 (τ1 τ τ2 : Τ),
                   Γ ⊫ t1 ∈ (τ1 ⟿ τ) -> Γ ⊫ t2 ∈ (τ ⟿ τ2) ->
                (*------------------------------------------------ WT-Comp *)
                      Γ ⊫ (t1 >>> t2) ∈ (τ1 ⟿ τ2)
where "G '⊫' t '∈' T" := (well_typed G t T).

Notation "G '⊫' t '∈' T" := (well_typed G t T) (at level 40, 
                                                            t custom arrow, 
                                                            T custom arrow).

(** *** Some facts *)

#[global] 
Instance well_typed_rc :
  Proper (Context.eq ==> Term.eq ==> Typ.eq ==> iff) well_typed.
Proof.
  repeat red; intros Γ Γ' HΓeq t t' HΛeq τ τ' HΤeq; split; 
  unfold Term.eq,Typ.eq in *; subst.
  - revert Γ Γ' τ' HΓeq. induction t'; intros Γ Γ' τ' HΓeq Hwt;
    inversion Hwt; subst; try (econstructor; now eauto).
    -- constructor; now rewrite <- HΓeq.
    -- apply wt_abs. apply IHt' with (Γ := ⌈ v ⤆ τ ⌉ᵧ Γ); auto.
       now rewrite <- HΓeq.
  - revert Γ Γ' τ' HΓeq; induction t'; intros Γ Γ' τ' HΓeq Hwt;
    inversion Hwt; subst; try (econstructor; now eauto).
    -- constructor; now rewrite HΓeq.
    -- apply wt_abs; apply IHt' with (Γ' := ⌈ v ⤆ τ ⌉ᵧ Γ'); auto.
       now rewrite HΓeq.
Qed.

Fact context_invariance : forall Γ Γ' t τ, 
  (forall x, isFV(x,t) -> Γ ⌊x⌋ᵧ = Γ' ⌊x⌋ᵧ) ->
  Γ ⊫ t ∈ τ -> Γ' ⊫ t ∈ τ.
Proof.
  intros Γ Γ' t τ Hc Hwt. generalize dependent Γ'.
  dependent induction Hwt; intros; try (now eauto); try (econstructor; now eauto).
  (* var *)
  - constructor. rewrite <- H; symmetry; now apply Hc.
  (* abs *)
  - constructor; auto. apply IHHwt; intros x1 Hafi. destruct (Var.eq_dec x x1).
    -- repeat rewrite Context.OP.P.add_eq_o; auto.
    -- repeat rewrite Context.OP.P.add_neq_o; auto.
Qed.

Fact free_in_context : forall x t τ Γ,
  isFV(x,t) -> Γ ⊫ t ∈ τ -> x ∈ᵧ Γ.
Proof with eauto.
  intros x t τ Γ Hafi Htyp; induction Htyp; inversion Hafi; subst; eauto.
  - exists τ; now apply Context.OP.P.find_2.
  - apply IHHtyp in H4. rewrite Context.OP.P.add_in_iff in H4; 
    destruct H4; subst; auto. contradiction.
  - inversion H1.
Qed.

Fact well_typed_empty_closed : forall t τ,
  ∅ᵧ ⊫ t ∈ τ -> clₜₘ(t).
Proof.
  intros. unfold Term.closed. intros x H1.
  eapply free_in_context in H; eauto. inversion H.
  apply Context.OP.P.empty_mapsto_iff in H0; contradiction.
Qed.

Fact canonical_form : forall Γ t α β,
  value(t) -> Γ ⊫ t ∈ (α ⟿ β) -> 

  (exists t', t = <[arr(t')]>)        \/ 
  (exists τ t', t = <[first(τ:t')]>)  \/ 
  (exists t' t'', t = <[t' >>> t'']>).
Proof.
  intros Γ t; revert Γ; induction t; intros Γ α β Hvt Hwt;
  inversion Hvt; inversion Hwt; subst.
  - left; now exists t.
  - right; left; exists τ;now exists t.
  - right; right. exists t1; now exists t2.
Qed.

(** *** Proof of determinism 

  If a term is well typed according to the same contexts with two types τ and τ';
  then τ and τ' are equivalent.    
*)
Lemma typing_deterministic : forall t Γ τ τ',
  Γ ⊫ t ∈ τ  -> 
  Γ ⊫ t ∈ τ' -> 

  (τ = τ')%typ.
Proof.
  intro t; induction t; intros Γ τ1 τ1' Hwt Hwt'; inversion Hwt; inversion Hwt'; subst; auto. 
  - rewrite H1 in *. inversion H5; subst; reflexivity.
  - apply IHt1 with (τ := <[τ2 → τ1]>) in H8; auto.
    inversion H8; subst; reflexivity.
  - inversion H2.
  - inversion H7.
  - apply IHt2 with (τ := <[τ1 → τ1]>) in H8; auto.
    inversion H8; subst; reflexivity.
  - apply IHt with (τ := τ2) in H10; auto.
    inversion H10; subst; reflexivity.
  - apply IHt1 with (τ := τ0) in H8; auto.
    apply IHt2 with (τ := τ2) in H10; auto. now rewrite H8,H10.
  - apply IHt with (τ := <[τ1 × τ2]>) in H5; auto.
    inversion H5; subst; reflexivity.
  - apply IHt with (τ := <[τ0 × τ1]>) in H5; auto.
    inversion H5; subst; reflexivity.
  - apply IHt with (τ := <[τ0 → τ2]>) in H5; auto.
    inversion H5; subst; reflexivity.
  - apply IHt with (τ := <[τ0 ⟿ τ2]>) in H8; auto.
    inversion H8; subst; reflexivity.
  - apply IHt1 with (τ := <[τ0 ⟿ τ]>) in H8; auto.
    apply IHt2 with (τ := <[τ ⟿ τ2]>) in H10; auto.
    inversion H8; inversion H10; subst; auto.
Qed.

(** *** Proof of variable context weakening *)
Theorem weakening_Γ : forall t Γ Γ' τ,
  Γ ⊆ᵧ Γ' -> 
  Γ ⊫ t ∈ τ -> 
  
  Γ' ⊫ t ∈ τ .
Proof.
  intros t Γ Γ' τ HSub wtt. generalize dependent Γ'.
  dependent induction wtt; intros Γ' HSub; try (econstructor; now eauto).
  - constructor. eapply Context.Submap_find_spec; eauto.
  - econstructor; eauto; eapply IHwtt. now apply Context.Submap_add_spec.
Qed.

(** *** Weakening corollaries *)

Corollary weakening_Γ_empty : forall Γ t τ,
  ∅ᵧ ⊫ t ∈ τ -> Γ ⊫ t ∈ τ.
Proof. intros Γ t τ; eapply weakening_Γ. apply Context.Submap_empty_spec. Qed.