From Coq Require Import Lia Arith.PeanoNat Program Bool.Bool Classes.Morphisms.
From Mecha Require Import Typ Resource Term Var VContext RContext Resources.
Import ResourceNotations TypNotations TermNotations RContextNotations 
       VContextNotations VarNotations ResourcesNotations SetNotations.

Open Scope rcontext_scope. 
Open Scope set_scope.

(** * Typing 

  Definition of Wormholes typing rules.
*)

(** *** Definition *)
Section definition.

Reserved Notation "G '⋅' R '⊫' t '∈' T" (at level 40, t custom wh, T custom wh).

Inductive well_typed : Γ -> ℜ -> Λ -> Τ -> Prop :=
  | wt_var    : forall (Γ : Γ) (Re : ℜ) (x : variable) (τ : Τ),

                        (Γ ⌊x⌋)%vc = Some τ -> 
                (*--------------------------------- WT-Var *)
                    Γ ⋅ Re ⊫ {Term.tm_var x} ∈ τ

  | wt_abs    : forall (Γ : Γ) (Re : ℜ) (x : variable) (t : Λ) (α β : Τ),

                    (⌈x ⤆ α⌉ Γ)%vc ⋅ Re ⊫ t ∈ β -> (Re⁺ ⊩ α)%ty ->
                (*---------------------------------------------------- WT-Abs *)
                              Γ ⋅ Re ⊫ (\x:α, t) ∈ (α → β)

  | wt_app    : forall (Γ : Γ) (Re : ℜ) (t1 t2 : Λ) (α β : Τ),

                    Γ ⋅ Re ⊫ t1 ∈ (α → β) -> Γ ⋅ Re ⊫ t2 ∈ α -> 
                (*-------------------------------------------------- WT-App *)
                                 Γ ⋅ Re ⊫ t1 t2 ∈ β

  | wt_unit   : forall (Γ : Γ) (Re : ℜ), 

                (*---------------------- WT-Unit *)
                    Γ ⋅ Re ⊫ unit ∈ 𝟙       

  | wt_pair   : forall (Γ : Γ) (Re : ℜ) (t1 t2 : Λ) (α β : Τ),

                    Γ ⋅ Re ⊫ t1 ∈ α -> Γ ⋅ Re ⊫ t2 ∈ β -> 
                (*------------------------------------------- WT-Pair *)
                        Γ ⋅ Re ⊫ ⟨t1, t2⟩ ∈ (α × β)

  | wt_fst    : forall (Γ : Γ) (Re : ℜ) (t : Λ) (α β : Τ),

                    Γ ⋅ Re ⊫ t ∈ (α × β) -> 
                (*---------------------------- WT-Fst *)
                      Γ ⋅ Re ⊫ t.fst ∈ α

  | wt_snd    : forall (Γ : Γ) (Re : ℜ) (t : Λ) (α β : Τ),

                    Γ ⋅ Re ⊫ t ∈ (α × β) -> 
                (*---------------------------- WT-Snd *)
                      Γ ⋅ Re ⊫ t.snd ∈ β

  | wt_fix    : forall (Γ : Γ) (Re : ℜ) (t : Λ) (τ : Τ),

                    Γ ⋅ Re ⊫ t ∈ (τ → τ) ->
                (*---------------------------- WT-Fix *)
                      Γ ⋅ Re ⊫ Fix t ∈ τ

  | wt_arr    : forall (Γ : Γ) (Re : ℜ) (t : Λ) (α β : Τ),

                        Γ ⋅ Re ⊫ t ∈ (α → β) -> 
                (*-------------------------------------- WT-Arr *)
                    Γ ⋅ Re ⊫ arr(t) ∈ (α ⟿ β ∣ ∅)%rs

  | wt_first  : forall (Γ : Γ) (Re : ℜ) (R : resources) (t : Λ) (α β τ : Τ),

                    Γ ⋅ Re ⊫ t ∈ (α ⟿ β ∣ R) -> (Re⁺ ⊩ τ)%ty ->
                (*------------------------------------------------ WT-First *)
                  Γ ⋅ Re ⊫ first(τ:t) ∈ ((α × τ) ⟿ (β × τ) ∣ R)

  | wt_comp   : forall (Γ : Γ) (Re : ℜ) (R R1 R2 : resources) (t1 t2 : Λ) (α β τ : Τ),

                  Γ ⋅ Re ⊫ t1 ∈ (α ⟿ τ ∣ R1) -> (R = (R1 ∪ R2))%rs -> 
                  Γ ⋅ Re ⊫ t2 ∈ (τ ⟿ β ∣ R2) -> (∅ = (R1 ∩ R2))%rs -> 
                (*----------------------------------------------------- WT-Comp *)
                      Γ ⋅ Re ⊫ (t1 >>> t2) ∈ (α ⟿ β ∣ R)

  | wt_rsf    : forall (Γ : Γ) (Re : ℜ) (r : resource) (τin τout : Τ),
                        Re ⌊r⌋ = Some (τin,τout) ->
                (*------------------------------------------ WT-Rsf *)
                  Γ ⋅ Re ⊫ rsf[r] ∈ (τin ⟿ τout ∣ \{{r}})

  | wt_wh     : forall (Γ : Γ) (Re : ℜ) (R R' : resources) (i t : Λ) (α β τ : Τ),
                    let k := Re⁺ in
                    Γ ⋅ Re ⊫ i ∈ τ ->
                    (R = R' \ \{{ k; (S k) }})%rs -> 
                    (k ⊩ α)%ty -> (k ⊩ β)%ty ->
                    Γ ⋅ (⌈(S k) ⤆ (τ,<[𝟙]>)⌉ (⌈k ⤆ (<[𝟙]>,τ)⌉ Re)) ⊫ t ∈ (α ⟿ β ∣ R') ->
                (*-------------------------------------------------------------------- WT-Wh *)
                                  Γ ⋅ Re ⊫ wormhole(i;t) ∈ (α ⟿ β ∣ R)
where "G '⋅' R '⊫' t '∈' T" := (well_typed G R t T).

End definition.

Notation "G '⋅' R '⊫' t '∈' T" := (well_typed G R t T) (at level 40, t custom wh, T custom wh).

Hint Constructors well_typed : core.

(** *** Some facts *)

#[export] Instance well_typed_rc :
  Proper (VContext.eq ==> RContext.eq ==> Term.eq ==> Typ.eq ==> iff) well_typed.
Proof.
  do 6 red; unfold Term.eq,Typ.eq. 
  intros Γ Γ' HGeq Re Re1 HReq t t' HTmeq α β HTyeq; subst; split.
  - intro wt; revert Γ' Re1 HReq HGeq.
    induction wt; intros Γ' Re1 HReq HGeq; auto.
    -- rewrite HGeq in *. 
       apply (wt_var Γ' _ _ _ H).
    -- rewrite HReq in *. constructor; auto.
       apply IHwt; auto. now rewrite HGeq.
    -- apply wt_app with (α := α); auto.
    -- apply wt_fst with (β := β); auto.
    -- apply wt_snd with (α := α); auto.
    -- rewrite HReq in *; constructor; auto.
    -- apply wt_comp with (R1 := R1) (R2 := R2) (τ := τ); auto.
    -- rewrite HReq in *;
       apply (wt_rsf _ _ _ _ _ H).
    -- unfold k in *; clear k; rewrite HReq in H0,H1,H.
       apply wt_wh with (R' := R') (τ := τ); auto.
       apply IHwt2; auto; now rewrite HReq.
  - intro wt; revert Γ Re HReq HGeq.
    induction wt; intros Γ Re1 HReq HGeq; auto.
    -- rewrite <- HGeq in *. 
       apply (wt_var Γ _ _ _ H).
    -- rewrite <- HReq in *. constructor; auto.
       apply IHwt; auto. now rewrite HGeq.
    -- apply wt_app with (α := α); auto.
    -- apply wt_fst with (β := β); auto.
    -- apply wt_snd with (α := α); auto.
    -- rewrite <- HReq in *; constructor; auto.
    -- apply wt_comp with (R1 := R1) (R2 := R2) (τ := τ); auto.
    -- rewrite <- HReq in *;
       apply (wt_rsf _ _ _ _ _ H).
    -- unfold k in *; clear k; rewrite <- HReq in H0,H1,H.
       apply wt_wh with (R' := R') (τ := τ); auto.
       apply IHwt2; auto; now rewrite HReq.
Qed.

Fact free_in_context : forall x t τ Γ Re,
  isFV(x,t) -> Γ ⋅ Re ⊫ t ∈ τ -> (x ∈ Γ)%vc.
Proof with eauto.
  intros x t τ Γ Re Hafi Htyp; induction Htyp; inversion Hafi; subst; eauto.
  - exists τ; now apply VContext.find_2.
  - apply IHHtyp in H5. rewrite VContext.add_in_iff in H5; 
    destruct H5; subst; auto. contradiction.
  - inversion H1.
Qed.

Open Scope term_scope.

(** *** Proof of determinism 

  If a term is well typed according to the same contexts with two types τ and τ';
  then τ and τ' are equivalent.    
*)
Lemma typing_deterministic : forall t Γ Re τ τ',
  Γ ⋅ Re ⊫ t ∈ τ  ->  Γ ⋅ Re ⊫ t ∈ τ' -> 
(*------------------------------------------*)
                 (τ = τ')%ty.
Proof.
  intro t; induction t; intros Γ Re τ1 τ1' Hwt Hwt'; inversion Hwt; inversion Hwt'; subst. 
  - rewrite H2 in *; inversion H7; subst; reflexivity.
  - apply IHt1 with (τ := <[α → τ1]>) in H10; auto.
    inversion H10; subst; reflexivity.
  - inversion H3.
  - inversion H9.
  - apply IHt2 with (τ := <[τ1 → τ1]>) in H10; auto.
    inversion H10; subst; reflexivity.
  - apply IHt with (τ := β) in H13; auto.
    inversion H13; subst; reflexivity.
  - apply IHt1 with (τ := α) in H10; auto.
    apply IHt2 with (τ := β) in H12; auto. now rewrite H10,H12.
  - apply IHt with (τ := <[τ1 × β]>) in H7; auto.
    inversion H7; subst; reflexivity.
  - apply IHt with (τ := <[α × τ1]>) in H7; auto.
    inversion H7; subst; reflexivity.
  - apply IHt with (τ := <[α → β]>) in H7; auto.
    inversion H7; subst; reflexivity.
  - apply IHt with (τ := <[α ⟿ β ∣ R]>) in H10; auto.
    inversion H10; subst; reflexivity.
  - apply IHt1 with (τ := <[α ⟿ τ ∣ R1]>) in H10; auto.
    apply IHt2 with (τ := <[τ ⟿ β ∣ R2]>) in H14; auto.
    inversion H10; inversion H14; subst.
    apply Resources.eq_leibniz in H2,H11; now subst.
  - rewrite H2 in H7; inversion H7; now subst.
  - apply IHt1 with (τ := τ) in H11; auto. unfold Typ.eq in *; subst.
    apply IHt2 with (τ := <[α ⟿ β ∣ R']>) in H18; auto.
    inversion H18; subst. unfold k,k0 in *; apply Resources.eq_leibniz in H2,H12; now subst.
  - reflexivity.
Qed.

(** *** Proof that the used resources set is in the resource context

  If a well typed value is reactive and, consequently, has a set of used resources R;
  then all resources identifiers contained in R are also in Re.
*)
Lemma typing_Re_R : forall t Γ Re α β R,
       value(t) -> Γ ⋅ Re ⊫ t ∈ (α ⟿ β ∣ R) -> 
(*---------------------------------------------------*)
    (forall (r : resource), (r ∈ R)%rs -> (r ∈ Re)%rc).
Proof.
  intro t; induction t; intros Γ Re τ1 τ1' R Hvt Hwt r1 HIn; inversion Hvt; subst; 
  inversion Hwt; subst.
  - inversion HIn.
  - eapply IHt; eauto.
  - rewrite H9 in HIn; rewrite Resources.St.union_spec in HIn.
    destruct HIn; eauto.
  - rewrite Resources.St.singleton_spec in HIn; subst; apply RContext.in_find; intro.
    rewrite H3 in H; inversion H.
  - rewrite H9 in HIn; rewrite Resources.St.diff_spec in HIn; destruct HIn.
    eapply IHt2 in H12; eauto. repeat rewrite Resources.St.add_notin_spec in *;
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
   (* (1) *) (Re⁺ ⊩ Γ)%vc -> 
   (* (2) *) (Re⁺ ⊩ Re)%rc -> (* (3) *) Γ ⋅ Re ⊫ t ∈ τ ->
(*-------------------------------------------------------*)
      (* (4) *) Re⁺ ⊩ t /\ (* (5) *) (Re⁺ ⊩ τ)%ty.
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
    apply Resources.eq_leibniz in H2; subst. rewrite Resources.valid_union_iff; split; auto.
  (* rsf *)
  - apply RContext.valid_find_spec with (lb := Re⁺) in H2 as []; auto.
    destruct H0; simpl in *. split; constructor; auto. now apply Resources.valid_singleton_iff.
  (* wormhole *)
  - apply IHt1 in H1; auto; destruct H1; apply IHt2 in H8; eauto.
    -- unfold k in *; clear k; destruct H8; inversion H4; subst.
      rewrite RContext.new_key_wh_spec in *; split; 
      repeat constructor; eauto. apply Resources.eq_leibniz in H2; subst. now apply Resources.valid_wh_spec.
    -- apply VContext.valid_weakening with (k := Re⁺); auto. unfold k in *; rewrite RContext.new_key_wh_spec in *; lia.
    -- unfold k in *; rewrite RContext.new_key_wh_spec. rewrite RContext.valid_add_notin_spec.
      + repeat split.
        ++ unfold Resource.valid; lia.
        ++ simpl; apply Typ.valid_weakening with (k := Re⁺); auto.
        ++ simpl; constructor.
        ++ rewrite RContext.valid_add_notin_spec; repeat split; simpl.
            * unfold Resource.valid; lia.
            * constructor.
            * apply Typ.valid_weakening with (k := Re⁺); auto.
            * apply RContext.valid_weakening with (k := Re⁺); auto.
            * apply RContext.Ext.new_key_notin_spec; lia.
      + apply RContext.Ext.new_key_notin_spec.
        rewrite RContext.Ext.new_key_add_ge_spec; auto.
        apply RContext.Ext.new_key_notin_spec; lia. 
  (* unit *)
  - repeat constructor.
Qed.

(** *** Proof of variable context weakening *)

Theorem weakening_Γ : forall t Γ Γ' Re τ,
    (Γ ⊆ Γ')%vc -> Γ ⋅ Re ⊫ t ∈ τ -> 
(*---------------------------------*)
         Γ' ⋅ Re ⊫ t ∈ τ .
Proof.
  intros t Γ Γ' Re τ HSub wtt. generalize dependent Γ'.
  dependent induction wtt; intros Γ' HSub; try (econstructor; now eauto).
  - constructor. eapply VContext.Submap_find_spec; eauto.
  - econstructor; eauto; eapply IHwtt. now apply VContext.Submap_add_spec.
Qed.

Open Scope typ_scope.

(** *** General proof of resource context weakening *)
Theorem weakening_ℜ_gen : forall (Γ : Γ) (Re Re1 : ℜ) (t : Λ) (τ : Τ) (k k' : nat),
    (* (1) *) k <= Re⁺ -> (* (2) *) k' <= Re1⁺ -> (* (3) *) k <= k' -> 
      (* (4) *) Re⁺ <= Re1⁺ -> (* (5) *) k' - k = Re1⁺ - Re⁺ ->

      (* (6) *) (([⧐ k – (k' - k)] Re) ⊆ Re1)%rc -> Γ ⋅ Re ⊫ t ∈ τ -> 
(*---------------------------------------------------------------------------------*)
    ([⧐ k – (k' - k)] Γ)%vc ⋅ Re1 ⊫ {Term.shift k (k' - k) t} ∈ [⧐ k – {k' - k}] τ.
Proof.
  simpl; intros Γ Re Re1 t τ k k' Hle Hle' Hle'' Hlen Heq Hsub wt.
  revert Re1 k k' Hle' Hsub Hle  Hle'' Heq Hlen.
  dependent induction wt; intros Re1 n m Hle' Hsub Hle  Hle'' Heq Hlen; simpl; 
  try (econstructor; now eauto); eauto.
  (* variable *)
  - constructor; now apply VContext.shift_find_iff.
  (* abstraction *) 
  - constructor.
    -- rewrite <- VContext.shift_add_spec. apply IHwt; auto.
    -- apply Typ.shift_preserves_valid_gen with (Re⁺); auto.
  (* first *)
  - econstructor; eauto. apply Typ.shift_preserves_valid_gen with (Re⁺); auto.
  (* comp *)
  - econstructor; eauto.
    -- apply Resources.eq_leibniz in H; subst.
      now rewrite Resources.shift_union_spec.
    -- rewrite <- Resources.shift_inter_spec. apply Resources.eq_leibniz in H0; rewrite <- H0.
      rewrite Resources.shift_empty_spec; reflexivity.
  (* rsf *)
  - rewrite Resources.shift_singleton_spec; constructor.
    apply RContext.Submap_find_spec with (m :=  ([⧐ n – m - n] Re)); auto.
    apply RContext.shift_find_iff with (lb := n) (k := m - n) in H; 
    unfold Typ.PairTyp.shift in *; simpl in *; assumption.
  (* wormhole *)
  - 
    eapply wt_wh with (τ := <[[⧐ n – {m - n}] τ]>) (R' := ([⧐ n – m - n] R')%rs); eauto.
    -- apply Resources.eq_leibniz in H; subst; unfold k.
      rewrite Resources.shift_diff_spec. repeat rewrite Resources.shift_add_notin_spec.
      + unfold Resource.shift. rewrite <- Nat.leb_le in Hle; rewrite Hle.
        replace (n <=? S (Re⁺)) with true.
        ++ rewrite Resources.shift_empty_spec. rewrite Heq; simpl.
            replace (Re⁺ + (Re1⁺ - Re⁺)) with (Re1⁺); try reflexivity.
            apply RContext.Ext.new_key_Submap_spec in Hsub; lia.
        ++ symmetry; rewrite Nat.leb_le in *; lia.
      + intro; inversion H.
      + rewrite Resources.St.add_notin_spec; split; auto. intro; inversion H.
    -- apply Typ.shift_preserves_valid_gen with (Re⁺); auto.
    -- apply Typ.shift_preserves_valid_gen with (Re⁺); auto.
    -- apply IHwt2; unfold k in *; try (rewrite RContext.new_key_wh_spec in *);
        try lia.
      + repeat rewrite RContext.shift_add_notin_spec.
        ++ unfold PairTyp.shift; simpl; unfold Resource.shift.
           replace (n <=? S (Re⁺)) with true; replace (n <=? Re⁺) with true;
           try (symmetry; rewrite Nat.leb_le; lia).
           replace (Re⁺ + (m - n)) with (Re1⁺) by lia.
           replace (S (Re ⁺) + (m - n)) with (S (Re1⁺)) by lia.
           repeat apply RContext.Submap_add_spec. assumption.
        ++ apply RContext.Ext.new_key_notin_spec; lia.
        ++ apply RContext.Ext.new_key_notin_spec.
           rewrite RContext.Ext.new_key_add_ge_spec; auto.
           apply RContext.Ext.new_key_notin_spec; lia.
      + rewrite RContext.new_key_wh_spec; lia.
      + rewrite RContext.new_key_wh_spec; lia.
Qed. 

(** *** Proof of resource context weakening *)
Corollary weakening_ℜ_1 : forall Γ (Re Re1 : ℜ) t (τ : Τ),
                (Re⁺ ⊩ Re)%rc -> (Re ⊆ Re1)%rc -> Γ ⋅ Re ⊫ t ∈ τ -> 
(*---------------------------------------------------------------------------------*)
  ([⧐ Re⁺ – (Re1⁺ - Re⁺)] Γ)%vc ⋅ Re1 ⊫ 
              {Term.shift (Re⁺) (Re1⁺ - Re⁺) t} ∈ ([⧐ {Re⁺} – {Re1⁺ - Re⁺}] τ)%ty.
Proof. 
  simpl; intros; apply weakening_ℜ_gen with (Re := Re); auto;
  try (apply RContext.Ext.new_key_Submap_spec in H0; assumption).
  assert (([⧐ Re⁺ – Re1⁺ - Re⁺] Re = Re)%rc)
  by now apply RContext.shift_valid_refl.
  now rewrite H2.
Qed.

(** *** Weakening corollaries *)

Corollary weakening_Γ_empty : forall Γ Re t τ,
  (∅)%vc ⋅ Re ⊫ t ∈ τ -> Γ ⋅ Re ⊫ t ∈ τ.
Proof. 
  intros Γ Re t τ; eapply weakening_Γ. 
  apply VContext.Submap_empty_bot. 
Qed.

Corollary weakening_ℜ : forall (Γ : Γ) (Re Re1 : ℜ) t (τ : Τ),
          (Re⁺ ⊩ Γ)%vc -> (Re⁺ ⊩ Re)%rc -> 
          (Re ⊆ Re1)%rc -> Γ ⋅ Re ⊫ t ∈ τ -> 
(*----------------------------------------------------------*)
     Γ ⋅ Re1 ⊫ {Term.shift (Re⁺) (Re1⁺ - Re⁺) t} ∈ τ.
Proof. 
  simpl; intros. apply well_typed_implies_valid in H2 as H2'; try assumption.
  destruct H2'. 
  rewrite <- VContext.shift_valid_refl with (lb := Re⁺) (t := Γ0) 
                                            (k := Re1⁺ - Re⁺); try assumption.
  rewrite <- Typ.shift_valid_refl with (lb := Re⁺) (τ := τ) 
                                        (k := Re1⁺ - Re⁺); try assumption.
  apply weakening_ℜ_1 with (Re := Re); auto.
Qed.

Corollary weakening_ℜ_bis : forall Γ (Re Re1 : ℜ) k k' t (τ : Τ),
      (Re⁺ ⊩ Γ)%vc -> (Re⁺ ⊩ Re)%rc -> 
    k = Re⁺ -> k' = Re1⁺ - Re⁺ ->
    (Re ⊆ Re1)%rc -> Γ ⋅ Re ⊫ t ∈ τ -> 
(*--------------------------------------*) 
     Γ ⋅ Re1 ⊫ {Term.shift k k' t} ∈ τ.
Proof. intros; subst. now apply weakening_ℜ. Qed.