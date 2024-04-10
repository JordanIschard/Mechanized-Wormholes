From Coq Require Import Lia Arith.PeanoNat Program Bool.Bool Classes.Morphisms.
Require Import Typ Resource Resources Term Var VContext RContext.


(** * Typing 

  Definition of Wormholes typing rules.
*)

(** *** Definition *)

Reserved Notation "G '⋅' R '⊫' t '∈' T" (at level 40, t custom wormholes, T custom wormholes).

Inductive well_typed : Γ -> ℜ -> Λ -> Τ -> Prop :=
  | wt_var    : forall Γ R (x : Var.t) τ,
                            Γ ⌈x ⩦ τ⌉ᵥᵪ -> 
                (*------------------------------- WT-Var *)
                    Γ ⋅ R ⊫ {Term.tm_var x} ∈ τ

  | wt_abs    : forall Γ Re x τ2 τ1 t1,
                    (⌈x ⤆ τ1⌉ᵥᵪ Γ) ⋅ Re ⊫ t1 ∈ τ2 -> 
                         newᵣᵪ(Re) ⊩ₜ τ1 ->
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
                          Γ ⋅ Re ⊫ t ∈ (τ1 ⟿ τ2 ∣ R) -> newᵣᵪ(Re) ⊩ₜ τ ->
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

  | wt_wh     : forall Γ (Re : ℜ) i t (R R' : resources) (τ τ1 τ2 : Τ),
                    let k := (newᵣᵪ(Re)) in
                    Γ ⋅ Re ⊫ i ∈ τ ->
                    (R = R' \ \{{ k; (S k) }})%rs -> k ⊩ₜ τ1 -> k ⊩ₜ τ2 ->
                    Γ ⋅ (⌈(S k) ⤆ (τ,<[𝟙]>)⌉ᵣᵪ ⌈k ⤆ (<[𝟙]>,τ)⌉ᵣᵪ Re) ⊫ t ∈ (τ1 ⟿ τ2 ∣ R') ->
                (*-------------------------------------------------------------------- WT-Wh *)
                                  Γ ⋅ Re ⊫ wormhole(i;t) ∈ (τ1 ⟿ τ2 ∣ R)

where "G '⋅' R '⊫' t '∈' T" := (well_typed G R t T).

Notation "G '⋅' R '⊫' t '∈' T" := (well_typed G R t T) (at level 40, 
                                                            t custom wormholes, 
                                                            T custom wormholes).

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
    -- apply wt_first; try (now rewrite <- Hℜeq).
       apply IHt' with (Re := Re) (Γ := Γ); auto.
    -- apply wt_rsf; now rewrite <- Hℜeq.
    -- unfold k in *; apply wt_wh with (R' := R') (τ := τ).
       + eapply IHt'1; eauto.
       + now rewrite <- Hℜeq.
       + now rewrite <- Hℜeq.
       + now rewrite <- Hℜeq.
       + eapply IHt'2; eauto; now rewrite Hℜeq.
  - revert Γ Γ' τ' Re Re' HΓeq Hℜeq; induction t'; intros Γ Γ' τ' Re Re' HΓeq Hℜeq Hwt;
    inversion Hwt; subst; try (econstructor; now eauto).
    -- constructor; now rewrite HΓeq.
    -- apply wt_abs; try (now rewrite Hℜeq).
       apply IHt' with (Re' := Re') (Γ' := ⌈ v ⤆ τ ⌉ᵥᵪ Γ'); auto.
       now rewrite HΓeq.
    -- apply wt_first; try (now rewrite Hℜeq).
       apply IHt' with (Re' := Re') (Γ' := Γ'); auto.
    -- apply wt_rsf; now rewrite Hℜeq.
    -- unfold k in *; apply wt_wh with (R' := R') (τ := τ).
       + eapply IHt'1; eauto.
       + now rewrite Hℜeq.
       + now rewrite Hℜeq.
       + now rewrite Hℜeq.
       + eapply IHt'2; eauto; now rewrite Hℜeq.
Qed.

Fact ill_typed_rsf : forall Γ (τ : Τ) r, ~ Γ ⋅ ∅ᵣᵪ ⊫ rsf[r] ∈ τ.
Proof. intros; intro; inversion H; subst; inversion H3. Qed.

Fact well_typed_rsf_implies_notEmpty : forall Γ (Re : ℜ) (τ : Τ) r,
  Γ ⋅ Re ⊫ rsf[r] ∈ τ -> ~ isEmptyᵣᵪ(Re).
Proof.
  intros; intro; inversion H; subst.
  unfold RContext.Empty in *; destruct (H0 r (τin,τout)).
  now apply RContext.find_2.
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
    -- repeat rewrite VContext.add_eq_o; auto.
    -- repeat rewrite VContext.add_neq_o; auto.
Qed.

Fact free_in_context : forall x t τ Γ Re,
  isFV(x,t) -> Γ ⋅ Re ⊫ t ∈ τ -> x ∈ᵥᵪ Γ.
Proof with eauto.
  intros x t τ Γ Re Hafi Htyp; induction Htyp; inversion Hafi; subst; eauto.
  - exists τ; now apply VContext.find_2.
  - apply IHHtyp in H5. rewrite VContext.add_in_iff in H5; 
    destruct H5; subst; auto. contradiction.
  - inversion H1.
Qed.

Fact well_typed_empty_closed : forall Re t τ,
  ∅ᵥᵪ ⋅ Re ⊫ t ∈ τ -> clₜₘ(t).
Proof.
  intros. unfold Term.closed. intros x H1.
  eapply free_in_context in H; eauto. inversion H.
  apply VContext.empty_mapsto_iff in H0; contradiction.
Qed.

Fact canonical_form : forall Γ Re t α β R,
  value(t) -> Γ ⋅ Re ⊫ t ∈ (α ⟿ β ∣ R) -> 

  (exists t', t = <[arr(t')]>)        \/ 
  (exists τ t', t = <[first(τ:t')]>)  \/ 
  (exists r, t = <[rsf[r]]>)          \/ 
  (exists t' t'', t = <[t' >>> t'']>) \/ 
  (exists t' t'', t = <[wormhole(t';t'')]>).
Proof.
  intros Γ Re t; revert Γ Re; induction t; intros Γ Re α β R Hvt Hwt;
  inversion Hvt; inversion Hwt; subst.
  - left; now exists t.
  - right; left; exists τ;now exists t.
  - right; right; right; left; exists t1; now exists t2.
  - right; right; left; now exists r.
  - repeat right; exists t1; now exists t2.
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
  - apply IHt with (τ := τ2) in H13; auto.
    inversion H13; subst; reflexivity.
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
  - apply IHt1 with (τ := τ) in H11; auto. unfold Typ.eq in *; subst.
    apply IHt2 with (τ := <[τ0 ⟿ τ2 ∣ R']>) in H18; auto.
    inversion H18; subst. unfold k,k0 in *; apply Resources.eq_leibniz in H2,H12; now subst.
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
  - rewrite H9 in HIn; rewrite Resources.union_spec in HIn.
    destruct HIn; eauto.
  - rewrite Resources.singleton_spec in HIn; subst; apply RContext.in_find; intro.
    rewrite H3 in H; inversion H.
  - rewrite H9 in HIn; rewrite Resources.diff_spec in HIn; destruct HIn.
    eapply IHt2 in H12; eauto. repeat rewrite Resources.add_notin_spec in *;
    destruct H0 as [Hneq [Hneq' _]]. repeat rewrite RContext.add_in_iff in H12.
    destruct H12 as [Heq | [Heq | HIn]]; subst; try contradiction; assumption. 
Qed.

(** *** Proof that well typing implies validity 

  **** Hypothesis

  Knowing that contexts are valid regards of the new key of the resource context [lb] (1,2) and
  the term [t] is well typed by [τ] (3);

  **** Results

  We can state that the term [t](4) and the type [τ](5) is also valid regards of [lb].
*)
Theorem well_typed_implies_valid : forall Γ Re t τ,
  let lb := newᵣᵪ(Re) in
  (* (1) *) lb ⊩ᵥᵪ Γ -> 
  (* (2) *) lb ⊩ᵣᵪ Re -> (* (3) *) Γ ⋅ Re ⊫ t ∈ τ ->
(*---------------------------------------------------*)
      (* (4) *) lb ⊩ₜₘ t /\ (* (5) *) lb ⊩ₜ τ.
Proof.
  intros Γ Re t; revert Γ Re; induction t; intros Γ Re τ'; simpl; intros HvΓ HvRe Hwt;
  inversion Hwt; subst.
  (* variable *)
  - split; try constructor. eapply VContext.valid_find_spec in H2; eauto.
  (* application *)
  - apply IHt1 in H3; eauto; destruct H3; inversion H0; subst.
    apply IHt2 in H5; eauto; destruct H5; split; auto; constructor; auto.
  (* Fix *)
  - apply IHt2 in H4; eauto. destruct H4; inversion H0; subst.
    split; auto. constructor; auto.
  (* abstraction *)
  - apply IHt in H5; eauto.
    -- destruct H5; split; constructor; auto.
    -- now apply VContext.valid_add_spec.
  (* pair *) 
  - split; constructor; apply IHt1 in H3; apply IHt2 in H5; auto; destruct H3,H5; assumption.
  (* fst *)
  - apply IHt in H2; auto; destruct H2; inversion H0; subst; split; auto; constructor; assumption.
  (* snd *)
  - apply IHt in H2; auto; destruct H2; inversion H0; subst; split; auto; constructor; assumption.
  (* arr *)
  - apply IHt in H2; auto; destruct H2; inversion H0; subst; split; constructor; auto.
    apply Resources.valid_empty_spec.
  (* first *)
  - apply IHt in H3; auto; destruct H3. inversion H0; subst. split. constructor; auto.
    repeat constructor; eauto.
  (* comp *)
  - apply IHt1 in H1; auto; destruct H1; inversion H0; subst.
    apply IHt2 in H5; auto; destruct H5; inversion H3; subst; split; repeat constructor; auto.
    apply Resources.eq_leibniz in H2; subst. rewrite Resources.valid_union_spec; split; auto.
  (* rsf *)
  - apply RContext.valid_find_spec with (lb := newᵣᵪ(Re)) in H2 as []; auto.
    destruct H0; simpl in *. split; constructor; auto. now apply Resources.valid_singleton_spec.
  (* wormhole *)
  - apply IHt1 in H1; auto; destruct H1; apply IHt2 in H8; eauto.
    -- unfold k in *; clear k; destruct H8; inversion H4; subst.
      rewrite RContext.new_key_wh_spec in *; split; 
      repeat constructor; eauto. apply Resources.eq_leibniz in H2; subst. now apply Resources.valid_wh_spec.
    -- apply VContext.valid_weakening with (k := newᵣᵪ(Re)); auto. unfold k in *; rewrite RContext.new_key_wh_spec in *; lia.
    -- unfold k in *; rewrite RContext.new_key_wh_spec. rewrite RContext.valid_add_notin_spec.
      + repeat split.
        ++ unfold Resource.valid; lia.
        ++ simpl; apply Typ.valid_weakening with (k := newᵣᵪ( Re)); auto.
        ++ simpl; constructor.
        ++ rewrite RContext.valid_add_notin_spec; repeat split; simpl.
            * unfold Resource.valid; lia.
            * constructor.
            * apply Typ.valid_weakening with (k := newᵣᵪ( Re)); auto.
            * apply RContext.valid_weakening with (k := newᵣᵪ( Re)); auto.
            * apply RContext.Ext.new_key_notin_spec; lia.
      + apply RContext.Ext.new_key_notin_spec; 
        rewrite RContext.Ext.new_key_add_spec_1; auto.
        apply RContext.Ext.new_key_notin_spec; lia. 
  (* unit *)
  - repeat constructor.
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
Theorem weakening_ℜ_gen : forall Γ (Re Re' : ℜ) t (τ : Τ) (k k' : nat),
  k <= newᵣᵪ(Re) -> 
  k' <= newᵣᵪ(Re') -> 
  k <= k' -> 
  newᵣᵪ(Re) <= newᵣᵪ(Re') ->
  k' - k = newᵣᵪ(Re') - newᵣᵪ(Re) ->
  ([⧐ᵣᵪ k ≤ (k' - k)] Re) ⊆ᵣᵪ Re' -> Γ ⋅ Re ⊫ t ∈ τ -> 

  ([⧐ᵥᵪ k ≤ (k' - k)] Γ) ⋅ Re' ⊫ [⧐ₜₘ k ≤ {k' - k}] t ∈ [⧐ₜ k ≤ {k' - k}] τ.
Proof.
  simpl; intros Γ Re Re' t τ k k' Hle Hle' Hle'' Hlen Heq Hsub wt.
  revert Re' k k' Hle' Hsub Hle  Hle'' Heq Hlen.
  dependent induction wt; intros Re' n m Hle' Hsub Hle  Hle'' Heq Hlen; simpl; 
  try (econstructor; now eauto); eauto.
  (* variable *)
  - constructor; now apply VContext.shift_find_spec.
  (* abstraction *) 
  - constructor.
    -- rewrite <- VContext.shift_add_spec. apply IHwt; auto.
    -- apply Typ.shift_preserves_valid_2 with (newᵣᵪ(Re)); auto.
  (* arr *)
  - rewrite Resources.shift_empty_spec. econstructor; eauto.
  (* first *)
  - econstructor; eauto. apply Typ.shift_preserves_valid_2 with (newᵣᵪ(Re)); auto.
  (* comp *)
  - econstructor; eauto.
    -- apply Resources.eq_leibniz in H; subst.
      now rewrite Resources.shift_union_spec.
    -- rewrite <- Resources.shift_inter_spec. apply Resources.eq_leibniz in H0; rewrite <- H0.
      rewrite Resources.shift_empty_spec; reflexivity.
  (* rsf *)
  - rewrite Resources.shift_singleton_spec; constructor.
    apply RContext.Submap_find_spec with (m :=  ([⧐ᵣᵪ n ≤ m - n] Re)); auto.
    apply RContext.shift_find_spec with (lb := n) (k := m - n) in H; 
    unfold Typ.PairTyp.shift in *; simpl in *; assumption.
  (* wormholes*)
  - 
    eapply wt_wh with (τ := <[[⧐ₜ n ≤ {m - n}] τ]>) (R' := [⧐ᵣₛ n ≤ m - n] R'); eauto.
    -- apply Resources.eq_leibniz in H; subst; unfold k.
      rewrite Resources.shift_diff_spec. repeat rewrite Resources.shift_add_notin_spec.
      + unfold Resource.shift. rewrite <- Nat.leb_le in Hle; rewrite Hle.
        replace (n <=? S (newᵣᵪ( Re))) with true.
        ++ rewrite Resources.shift_empty_spec. rewrite Heq; simpl.
            replace (newᵣᵪ( Re) + (newᵣᵪ( Re') - newᵣᵪ( Re))) with (newᵣᵪ(Re')); try reflexivity.
            apply RContext.Ext.new_key_Submap_spec in Hsub; lia.
        ++ symmetry; rewrite Nat.leb_le in *; lia.
      + intro; inversion H.
      + rewrite Resources.add_notin_spec; split; auto. intro; inversion H.
    -- apply Typ.shift_preserves_valid_2 with (newᵣᵪ(Re)); auto.
    -- apply Typ.shift_preserves_valid_2 with (newᵣᵪ(Re)); auto.
    -- apply IHwt2; unfold k in *; try (rewrite RContext.new_key_wh_spec in *);
        try lia.
      + assert ((([⧐ᵣᵪ n ≤ (m - n)] ⌈ S (newᵣᵪ( Re)) ⤆ (τ,<[ 𝟙 ]>) ⌉ᵣᵪ 
                                  (⌈ newᵣᵪ( Re) ⤆ (<[ 𝟙 ]>,τ) ⌉ᵣᵪ Re)) = 
                  ( ⌈ ([⧐ᵣ n ≤ (m - n)] S (newᵣᵪ( Re))) ⤆ ( <[[⧐ₜ n ≤ {m - n}] τ]>,<[ 𝟙 ]>) ⌉ᵣᵪ 
                  (⌈ ([⧐ᵣ n ≤ (m - n)] newᵣᵪ( Re)) ⤆ (<[ 𝟙 ]>,<[[⧐ₜ n ≤ {m - n}] τ]>) ⌉ᵣᵪ ([⧐ᵣᵪ n ≤ (m - n)] Re))))%rc).
        ++ rewrite RContext.shift_add_notin_spec; eauto.
            * unfold PairTyp.shift; simpl.
              rewrite RContext.shift_add_notin_spec.
              ** unfold PairTyp.shift; simpl. reflexivity.
              ** apply RContext.Ext.new_key_notin_spec; lia.
            * rewrite RContext.add_in_iff. intro. destruct H2; try lia.
              apply RContext.Ext.new_key_notin_spec in H2; auto.
        ++ eapply RContext.Submap_eq_left_spec; eauto. unfold Resource.shift; simpl.
            replace (n <=? S (newᵣᵪ( Re))) with true; replace (n <=? newᵣᵪ( Re)) with true;
            try (symmetry; rewrite Nat.leb_le; lia). rewrite Heq; simpl.
            replace (newᵣᵪ( Re) + (newᵣᵪ( Re') - newᵣᵪ( Re))) with (newᵣᵪ( Re')) by lia.
            repeat apply RContext.Submap_add_spec. rewrite <- Heq. assumption.
      + rewrite RContext.new_key_wh_spec; lia.
      + rewrite RContext.new_key_wh_spec; lia.
Qed. 

(** *** Proof of resource context weakening *)
Corollary weakening_ℜ : forall Γ (Re Re' : ℜ) t (τ : Τ),
  let k := newᵣᵪ(Re) in let k' := newᵣᵪ(Re') in
  k ⊩ᵣᵪ Re -> 
  Re ⊆ᵣᵪ Re' ->
  Γ ⋅ Re ⊫ t ∈ τ -> 

  ([⧐ᵥᵪ k ≤ (k' - k)] Γ) ⋅ Re' ⊫ [⧐ₜₘ k ≤ {k' - k}] t ∈ [⧐ₜ k ≤ {k' - k}] τ.
Proof. 
  simpl; intros; apply weakening_ℜ_gen with (Re := Re); auto;
  try (apply RContext.Ext.new_key_Submap_spec in H0; assumption).
  assert ((([⧐ᵣᵪ newᵣᵪ( Re) ≤ newᵣᵪ( Re') - newᵣᵪ( Re)] Re) = Re)%rc) 
  by now apply RContext.shift_valid_refl.
  eapply RContext.Submap_eq_left_spec; eauto. 
Qed.

(** *** Weakening corollaries *)

Corollary weakening_Γ_empty : forall Γ Re t τ,
  ∅ᵥᵪ ⋅ Re ⊫ t ∈ τ -> 
  
  Γ ⋅ Re ⊫ t ∈ τ.
Proof. intros Γ Re t τ; eapply weakening_Γ. apply VContext.Submap_empty_spec. Qed.

Corollary weakening_ℜ_1 : forall Γ (Re Re' : ℜ) t (τ : Τ),
  let k := newᵣᵪ(Re) in let k' := newᵣᵪ(Re') in
  k ⊩ᵥᵪ Γ -> 
  k ⊩ᵣᵪ Re -> 
  Re ⊆ᵣᵪ Re' ->
  Γ ⋅ Re ⊫ t ∈ τ -> 
  
  Γ ⋅ Re' ⊫ [⧐ₜₘ k ≤ {k' - k}] t ∈ τ.
Proof. 
  simpl; intros. apply well_typed_implies_valid in H2 as H2'; try assumption.
  destruct H2'. 
  rewrite <- VContext.shift_valid_refl with (lb := newᵣᵪ(Re)) (t := Γ) 
                                            (k := newᵣᵪ(Re') - newᵣᵪ(Re)); try assumption.
  rewrite <- Typ.shift_valid_refl with (lb := newᵣᵪ(Re)) (τ := τ) 
                                        (k := newᵣᵪ(Re') - newᵣᵪ(Re)); try assumption.
  apply weakening_ℜ with (Re := Re); auto.
Qed.