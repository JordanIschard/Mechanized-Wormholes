From Coq Require Import Lia Arith.PeanoNat Classes.Morphisms.
From Mecha Require Import Typ Resource Term Var VContext RContext Resources.
Import ResourceNotations TypNotations TermNotations RContextNotations 
       VContextNotations VarNotations ResourcesNotations SetNotations.


(** * Semantics - Type System 

  Wormhole's type system, denoted Γ ⋅ ℜ ⊢ t ∈ α, ensures that [t] is typed by [α] under two contexts [Γ] and [ℜ]. The former is the usual variable context, defined in [VContext.v], and the latter is a resource context, defined in [RContext.v]. This file contains the [well_typed] property definition and its weakening proofs.
*)


Open Scope rcontext_scope. 

Module RC := RContext.
Module VC := VContext.

(** ** Definition - Type System *)

Reserved Notation "G '⋅' R '⊢' t '∈' T" (at level 40, t custom wh, T custom wh).

Inductive well_typed : Γ -> ℜ -> Λ -> Τ -> Prop :=
  | wt_var (Γ : Γ) (Re : ℜ) (x : variable) (τ : Τ) :

            (Γ ⌊x⌋)%vc = Some τ -> 
    (* -------------------------------- WT-Var *)
         Γ ⋅ Re ⊢ {Term.tm_var x} ∈ τ

  | wt_abs (Γ : Γ) (Re : ℜ) (x : variable) (t : Λ) (α β : Τ) :

         (⌈x ⤆ α⌉ Γ)%vc ⋅ Re ⊢ t ∈ β -> (Re⁺ ⊩ α)%ty ->
    (* --------------------------------------------------- WT-Abs *)
                  Γ ⋅ Re ⊢ (\x :α, t) ∈ (α → β)

  | wt_app  (Γ : Γ) (Re : ℜ) (t1 t2 : Λ) (α β : Τ) :

         Γ ⋅ Re ⊢ t1 ∈ (α → β) -> Γ ⋅ Re ⊢ t2 ∈ α -> 
    (* ------------------------------------------------ WT-App *)
                      Γ ⋅ Re ⊢ t1 t2 ∈ β

  | wt_unit (Γ : Γ) (Re : ℜ) :

    (* --------------------- WT-Unit *)
         Γ ⋅ Re ⊢ unit ∈ 𝟙       

  | wt_pair (Γ : Γ) (Re : ℜ) (t1 t2 : Λ) (α β : Τ) :

         Γ ⋅ Re ⊢ t1 ∈ α -> Γ ⋅ Re ⊢ t2 ∈ β -> 
    (* ------------------------------------------ WT-Pair *)
            Γ ⋅ Re ⊢ ⟨t1, t2⟩ ∈ (α × β)

  | wt_fst (Γ : Γ) (Re : ℜ) (t : Λ) (α β : Τ) :

         Γ ⋅ Re ⊢ t ∈ (α × β) -> 
    (* --------------------------- WT-Fst *)
          Γ ⋅ Re ⊢ (fst.t) ∈ α

  | wt_snd (Γ : Γ) (Re : ℜ) (t : Λ) (α β : Τ) :

        Γ ⋅ Re ⊢ t ∈ (α × β) -> 
    (* --------------------------- WT-Snd *)
          Γ ⋅ Re ⊢ (snd.t) ∈ β

  | wt_fix (Γ : Γ) (Re : ℜ) (t : Λ) (τ : Τ) :

         Γ ⋅ Re ⊢ t ∈ (τ → τ) ->
    (* --------------------------- WT-Fix *)
           Γ ⋅ Re ⊢ Fix t ∈ τ

  | wt_arr (Γ : Γ) (Re : ℜ) (t : Λ) (α β : Τ) :

             Γ ⋅ Re ⊢ t ∈ (α → β) -> 
    (* ------------------------------------- WT-Arr *)
         Γ ⋅ Re ⊢ arr(t) ∈ (α ⟿ β ∣ ∅)%s

  | wt_first (Γ : Γ) (Re : ℜ) (R : resources) (t : Λ) (α β τ : Τ) :

         Γ ⋅ Re ⊢ t ∈ (α ⟿ β ∣ R) -> (Re⁺ ⊩ τ)%ty ->
    (* ------------------------------------------------ WT-First *)
         Γ ⋅ Re ⊢ first(τ:t) ∈ ((α × τ) ⟿ (β × τ) ∣ R)

  | wt_comp (Γ : Γ) (Re : ℜ) (R R1 R2 : resources) (t1 t2 : Λ) (α β τ : Τ) :

         Γ ⋅ Re ⊢ t1 ∈ (α ⟿ τ ∣ R1) -> (R = (R1 ∪ R2))%s -> 
         Γ ⋅ Re ⊢ t2 ∈ (τ ⟿ β ∣ R2) -> (∅ = (R1 ∩ R2))%s -> 
    (* -------------------------------------------------------- WT-Comp *)
              Γ ⋅ Re ⊢ (t1 >>> t2) ∈ (α ⟿ β ∣ R)

  | wt_rsf (Γ : Γ) (Re : ℜ) (r : resource) (τin τout : Τ) :

              Re ⌊r⌋ = Some (τin,τout) ->
    (* -------------------------------------------- WT-Rsf *)
         Γ ⋅ Re ⊢ rsf[r] ∈ (τin ⟿ τout ∣ \{{r}})

  | wt_wh (Γ : Γ) (Re : ℜ) (R R' : resources) (t1 t2 : Λ) (α β τ : Τ) :

         (R = R' \ \{{ Re⁺; (S (Re⁺)) }})%s -> (Re⁺ ⊩ α)%ty -> (Re⁺ ⊩ β)%ty ->

         Γ ⋅ Re ⊢ t1 ∈ τ ->
         Γ ⋅ (⌈(S (Re⁺)) ⤆ (τ,<[𝟙]>)⌉ (⌈Re⁺ ⤆ (<[𝟙]>,τ)⌉ Re)) ⊢ t2 ∈ (α ⟿ β ∣ R') ->
    (* -------------------------------------------------------------------------------- WT-Wh *)
                          Γ ⋅ Re ⊢ wormhole(t1;t2) ∈ (α ⟿ β ∣ R)

where "G '⋅' R '⊢' t '∈' T" := (well_typed G R t T).

Hint Constructors well_typed : core.

(** ---- *)

(** ** Property - Type System *)

Open Scope term_scope.

#[export] Instance well_typed_iff : 
  Proper (VC.eq ==> RC.eq ==> Term.eq ==> Typ.eq ==> iff) well_typed.
Proof.
  intros Γ Γ' HGeq Re Re1 HReq t' t HTmeq α β HTyeq.
  unfold Term.eq,Typ.eq in *; subst; split.
  - intro wt; revert Γ' HGeq Re1 HReq; induction wt; intros; eauto.
    -- constructor; now rewrite <- HGeq.
    -- constructor; try (now rewrite <- HReq). 
       apply IHwt; auto; now rewrite HGeq.
    -- constructor; auto; try (now rewrite <- HReq). 
    -- constructor; auto; now rewrite <- HReq.
    -- apply wt_wh with (R' := R') (τ := τ); auto;
       try (apply IHwt2; auto); now rewrite <- HReq.
  - intro wt; revert Γ HGeq Re HReq; induction wt; intros; eauto.
    -- constructor; now rewrite HGeq.
    -- constructor; try (now rewrite HReq). 
       apply IHwt; auto; now rewrite <- HGeq.
    -- constructor; auto; now rewrite HReq.
    -- constructor; auto; now rewrite HReq.
    -- apply wt_wh with (R' := R') (τ := τ); auto;
       try (apply IHwt2; auto); now rewrite HReq.
Qed.

Lemma wt_deterministic (Γ : Γ) (Re : ℜ) (t : Λ) (α β : Τ) :
  Γ ⋅ Re ⊢ t ∈ α -> Γ ⋅ Re ⊢ t ∈ β -> α = β.
Proof.
  revert Γ Re α β; induction t;
  intros G Re α β Hwt Hwt'; 
  inversion Hwt; subst; inversion Hwt'; subst; auto.
  - rewrite H2 in H3; inversion H3; auto.
  - f_equal; auto.
    apply IHt with (α :=β0) in H7; auto.
  - apply IHt2 with (α := α0) in H7; auto; subst.
    apply IHt1 with (α := <[α1 → α]>) in H4; auto.
    now inversion H4; subst.
  - f_equal; 
    try (now apply (IHt1 G Re); auto);
    try (now apply (IHt2 G Re); auto).
  - apply (IHt G Re <[α → α]>) in H3; auto.
    inversion H3; now subst.
  - apply (IHt G Re <[α × β0]>) in H3; auto.
    now inversion H3.
  - apply (IHt G Re <[α0 × α]>) in H3; auto.
    now inversion H3.
  - apply (IHt G Re <[α0 → β0]>) in H3; auto.
    inversion H3; f_equal; auto.
  - apply (IHt G Re <[α0 ⟿ β0 ∣ R]>) in H4; auto.
    inversion H4; f_equal; auto.
  - rewrite H2 in H3; inversion H3; f_equal; auto.
  - apply (IHt1 G Re <[α0 ⟿ τ ∣ R1]>) in H3; auto.
    inversion H3; subst; clear H3.
    apply (IHt2 G Re <[τ0 ⟿ β0 ∣ R2]>) in H9; auto.
    inversion H9; subst; clear H9.
    apply Resources.eq_leibniz in H2,H4; subst; auto.
  - apply (IHt1 G Re τ) in H11; auto; subst.
    apply (IHt2 G _ <[α0 ⟿ β0 ∣ R']>) in H13; auto.
    inversion H13; subst; clear H13.
    apply Resources.eq_leibniz in H1,H4; subst; auto.
Qed.

(** *** Used resource names come from the resource context

  Suppose a value [t] (1), well typed by [(α ⟿ β ∣ R)] under contexts [Γ] and [Re] (2). Resource names in the set of used resources [R] have to be in Re, i.e. We can use only resource names known.
*)
Theorem typing_Re_R (Γ : Γ) (Re : ℜ) (t : Λ) (α β : Τ) (R : resources) :

       (* (1) *) value(t) -> (* (2) *) Γ ⋅ Re ⊢ t ∈ (α ⟿ β ∣ R) -> 
  (* ---------------------------------------------------------------- *)
           (forall (r : resource), (r ∈ R)%s -> (r ∈ Re)%rc).
Proof.
  revert Γ Re α β R; induction t; intros Γ Re α β R Hvt Hwt r1 HIn; 
  inversion Hvt; subst; inversion Hwt; subst.
  (* arr *)
  - inversion HIn.
  (* first *)
  - apply (IHt Γ _ α0 β0 R); assumption.
  (* rsf *)
  - rewrite Resources.St.singleton_spec in HIn; subst.
    exists (α,β); now apply RC.find_2.
  (* comp *)
  - rewrite H9 in HIn. 
    apply Resources.St.union_spec in HIn as [HIn | HIn]; eauto.
  (* wormhole *)
  - rewrite H8 in HIn. 
    apply Resources.St.diff_spec in HIn as [HIn HnIn].
    eapply IHt2 in H12; eauto. 
    (repeat rewrite Resources.St.add_notin_spec in HnIn); destruct HnIn as [Hneq [Hneq' _]].
    (repeat rewrite RC.add_in_iff in H12). 
    destruct H12 as [Heq | [Heq | HIn']]; subst; try contradiction; assumption. 
Qed.

(** *** Well typed implies well formedness 

  Suppose a term [t], well typed by [τ] under contexts [Γ] and [Re] (3), knowing that both contexts are well formed under [Re⁺] (1,2). We can prove that [t] and [τ] are also well formed under [Re⁺] (4,5).
*)
Theorem well_typed_implies_Wf (Γ : Γ) (Re : ℜ) (t : Λ) (τ : Τ) :

       (* (1) *) (Re⁺ ⊩ Γ)%vc ->  (* (2) *) (Re⁺ ⊩ Re)%rc -> (* (3) *) Γ ⋅ Re ⊢ t ∈ τ ->
  (* -------------------------------------------------------------------------------------- *)
                      (* (4) *) Re⁺ ⊩ t /\ (* (5) *) (Re⁺ ⊩ τ)%ty.
Proof.
  revert Γ Re τ; induction t; simpl; intros Γ Re ty HvΓ HvRe Hwt; inversion Hwt; subst;
  try (apply IHt in H2 as [Hvt Hvf]; auto; inversion Hvf; subst; now repeat constructor).
  (* unit *)
  - repeat constructor.
  (* variable *)
  - split; try constructor. 
    now apply (VC.Wf_find (Re⁺)) in H2.
  (* abstraction *)
  - apply (IHt (⌈x ⤆ τ⌉ Γ)%vc _ β) in HvRe; auto. 
    -- destruct HvRe; split; auto; constructor; assumption.
    -- now apply VContext.Wf_add.
  (* application *)
  - apply IHt1 in H3 as [Hvt1 Hvf]; eauto.
    apply IHt2 in H5 as [Hvt2 _]; eauto.
    inversion Hvf; subst.
    split; auto; constructor; auto.
  (* pair *) 
  - apply IHt1 in H3 as [Hvt1 Hvα]; apply IHt2 in H5 as [Hvt2 Hvβ]; auto; 
    now repeat constructor.
  (* first *)
  - apply IHt in H3 as [Hvt Hvf]; auto; inversion Hvf; subst.
    repeat constructor; auto.
  (* rsf *)
  - apply RC.Wf_find with (lb := Re⁺) in H2 as [Hvr Hvf]; auto.
    inversion Hvf; simpl in *; repeat constructor; auto.
    now apply Resources.Wf_singleton_iff.
  (* comp *)
  - apply IHt1 in H1 as [Hvt1 Hvα]; apply IHt2 in H5 as [Hvt2 Hvβ]; auto.
    inversion Hvα; inversion Hvβ; subst; repeat constructor; auto.
    rewrite H2; rewrite Resources.Wf_union_iff; now split.
  (* wormhole *)
  - apply IHt1 in H6 as [Hvt1 Hvτ]; auto.
    apply IHt2 in H8 as [Hvt2 Hvf]; rewrite RC.new_key_wh in *.
    -- inversion Hvf; subst; repeat constructor; auto. 
       rewrite H1; now apply Resources.Wf_wh.
    -- apply VC.Wf_weakening with (k := Re⁺); auto.
    -- apply RC.Wf_wh; auto; now repeat constructor; simpl.
Qed.

(** *** Variable context weakening 

  Suppose a term [t], well typed by [τ] under contexts [Γ] and [Re] (2) and another variable context named [Γ'] such as [Γ] is included in [Γ'] (1). We can state that [t] is also well typed by swap [Γ] with [Γ'].
*)
Theorem weakening_Γ (Γ Γ' : Γ) (Re : ℜ) (t : Λ) (τ : Τ) :

       (* (1) *) (Γ ⊆ Γ')%vc -> (* (2) *) Γ ⋅ Re ⊢ t ∈ τ -> 
  (* -------------------------------------------------------- *)
                       Γ' ⋅ Re ⊢ t ∈ τ .
Proof.
  intros Hsub wt; revert Γ' Hsub; induction wt; intros; auto;
  try (econstructor; now eauto).
  - constructor; now apply (VC.Submap_find _ _ Γ0).
  - apply wt_abs; auto; apply IHwt. 
    now apply VC.Submap_add.
Qed.

Open Scope typ_scope.

(** *** Resource context weakening 

  Suppose a term [t], well typed by [τ] under contexts [Γ] and [Re] (5) and another resource context named [Re1] such as ([[⧐ k – (k' - k)] Re]) is included in [Re1] (4). [k] and [k'] are levels such as they satisfy hypothesis (1),(2) and (3). We prove that [t] is also well typed by swap [Re] with [Re1] modulo [shift] applications.
  
*)
Theorem weakening_ℜ_gen (k k' : lvl) (Γ : Γ) (Re Re1 : ℜ) (t : Λ) (τ : Τ) :

        (* (1) *) k <= Re⁺ ->  (* (2) *) k <= k' -> (* (3) *) k' - k = Re1⁺ - Re⁺ ->
         (* (4) *) (([⧐ k – (k' - k)] Re) ⊆ Re1)%rc -> (* (5) *) Γ ⋅ Re ⊢ t ∈ τ -> 
  (* ------------------------------------------------------------------------------------ *)
       ([⧐ k – (k' - k)] Γ)%vc ⋅ Re1 ⊢ {Term.shift k (k' - k) t} ∈ [⧐ k – {k' - k}] τ.
Proof.
  intros Hle Hle' Heq Hsub wt; revert Re1 k k' Hle Hle' Hsub Heq.
  induction wt; intros Re1 n m Hle Hle' Hsub Heq; simpl; auto.
  (* variable *)
  - constructor; now apply VC.shift_find_iff.
  (* abstraction *)
  - constructor.
    -- rewrite <- VC.shift_add; now apply IHwt.
    -- assert (Re⁺ <= Re1⁺).
       { 
         apply RC.Ext.new_key_Submap in Hsub. 
         now rewrite <- RC.shift_new_key_le in Hsub.
       }
       apply (Typ.shift_preserves_wf_gen (Re⁺)); auto; lia. 
  (* application *)
  - apply wt_app with (α := <[[⧐n – {m - n}] α]>); auto.
  (* fst *)
  - simpl in *; apply wt_fst with (β := <[[⧐ n – {m - n}] β]>); auto.
  (* snd *)
  - simpl in *; apply wt_snd with (α := <[[⧐ n – {m - n}] α]>); auto.
  (* first *)
  - econstructor; eauto. 
    assert (Re⁺ <= Re1⁺).
    { 
      apply RC.Ext.new_key_Submap in Hsub. 
      now rewrite <- RC.shift_new_key_le in Hsub.
    }
    apply Typ.shift_preserves_wf_gen with (Re⁺); auto; lia.
  (* comp *)
  - econstructor; eauto.
    -- rewrite <- Resources.shift_union.
       now rewrite H.
    -- rewrite <- Resources.shift_inter; rewrite <- H0. 
       now rewrite Resources.shift_empty.
  (* rsf *)
  - rewrite Resources.shift_singleton; constructor.
    apply RC.Submap_find with (m :=  ([⧐ n – m - n] Re)); auto.
    apply RC.shift_find_iff with (lb := n) (k := m - n) in H; auto.
  (* wormhole *)
  - assert (Hle1 : Re⁺ <= Re1⁺). 
    { 
      apply RC.Ext.new_key_Submap in Hsub. 
      now rewrite <- RC.shift_new_key_le in Hsub.
    }
    eapply wt_wh with (τ := <[[⧐ n – {m - n}] τ]>) (R' := ([⧐ n – m - n] R')%rs); auto.
    -- rewrite H; rewrite Resources.shift_diff.
       repeat rewrite Resources.shift_add_notin.
       + unfold Resource.shift. 
         rewrite <- Nat.leb_le in Hle; rewrite Hle.
         replace (n <=? S (Re⁺)) with true.
         ++ rewrite Resources.shift_empty. 
            rewrite Heq; simpl.
            now replace (Re⁺ + (Re1⁺ - Re⁺)) with (Re1⁺) by lia.
        ++ symmetry; rewrite Nat.leb_le in *; lia.
      + intro HIn; inversion HIn.
      + rewrite Resources.St.add_notin_spec; split; auto. 
        intro HIn; inversion HIn.
    -- apply Typ.shift_preserves_wf_gen with (Re⁺); auto; lia.
    -- apply Typ.shift_preserves_wf_gen with (Re⁺); auto; lia.
    -- apply IHwt2; rewrite RC.new_key_wh in *; try lia. 
       + repeat rewrite RC.shift_add_notin.
         ++ unfold PairTyp.shift; simpl; unfold Resource.shift.
           replace (n <=? S (Re⁺)) with true; replace (n <=? Re⁺) with true;
           try (symmetry; rewrite Nat.leb_le; lia).
           replace (Re⁺ + (m - n)) with (Re1⁺) by lia.
           replace (S (Re ⁺) + (m - n)) with (S (Re1⁺)) by lia.
           now repeat apply RC.Submap_add.
        ++ apply RC.Ext.new_key_notin; lia.
        ++ apply RC.Ext.new_key_notin.
           rewrite RC.Ext.new_key_add_max; lia.
      + rewrite RC.new_key_wh; lia.
Qed.

(** *** Weakening corollaries *)

Corollary weakening_Γ_empty (Γ : Γ) (Re : ℜ) (t : Λ) (τ : Τ) :

       (∅)%vc ⋅ Re ⊢ t ∈ τ -> 
  (* -------------------------- *)
          Γ ⋅ Re ⊢ t ∈ τ.
Proof. apply weakening_Γ; apply VContext.Submap_empty_bot. Qed.

Corollary weakening_ℜ_1 (Γ : Γ) (Re Re1 : ℜ) (t : Λ) (τ : Τ) :

                (Re⁺ ⊩ Re)%rc -> (Re ⊆ Re1)%rc -> Γ ⋅ Re ⊢ t ∈ τ -> 
(* ---------------------------------------------------------------------------------- *)
     ([⧐ Re⁺ – (Re1⁺ - Re⁺)] Γ)%vc ⋅ Re1 ⊢ 
               {Term.shift (Re⁺) (Re1⁺ - Re⁺) t} ∈ ([⧐ {Re⁺} – {Re1⁺ - Re⁺}] τ)%ty.
Proof. 
  intros HvRe Hsub Hwt; apply weakening_ℜ_gen with (Re := Re); auto.
  - now apply RC.Ext.new_key_Submap.
  - rewrite RC.shift_wf_refl; auto.
Qed.

Corollary weakening_ℜ (Γ : Γ) (Re Re1 : ℜ) (t : Λ) (τ : Τ) :

       (Re⁺ ⊩ Γ)%vc -> (Re⁺ ⊩ Re)%rc -> (Re ⊆ Re1)%rc -> Γ ⋅ Re ⊢ t ∈ τ -> 
  (* ----------------------------------------------------------------------- *)
              Γ ⋅ Re1 ⊢ {Term.shift (Re⁺) (Re1⁺ - Re⁺) t} ∈ τ.
Proof.
  intros HvΓ HvRe Hsub Hwt.
  apply (weakening_ℜ_1 _ _ Re1) in Hwt as Hwt'; auto.
  rewrite VC.shift_wf_refl in Hwt'; auto.
  apply well_typed_implies_Wf in Hwt as [_ Hvτ]; auto.
  now rewrite Typ.shift_wf_refl in Hwt'. 
Qed.

Corollary weakening_ℜ_2 (k k' : lvl) (Γ : Γ) (Re Re1 : ℜ) (t : Λ) (τ : Τ) :

      (Re⁺ ⊩ Γ)%vc -> (Re⁺ ⊩ Re)%rc -> k = Re⁺ -> k' = Re1⁺ - Re⁺ ->
                (Re ⊆ Re1)%rc -> Γ ⋅ Re ⊢ t ∈ τ -> 
  (* ------------------------------------------------------------------ *) 
                Γ ⋅ Re1 ⊢ {Term.shift k k' t} ∈ τ.
Proof. intros; subst; now apply weakening_ℜ. Qed.

Corollary weakening_ℜ_wh (Γ : Γ) (Re : ℜ) (t : Λ) (α β τ : Τ) :

                (Re⁺ ⊩ Γ)%vc -> (Re⁺ ⊩ Re)%rc -> Γ ⋅ Re ⊢ t ∈ τ -> 
  (* ------------------------------------------------------------------------------- *)
       Γ ⋅ (⌈S (Re⁺) ⤆ (β, α)⌉ (⌈Re⁺ ⤆ (α, β)⌉ Re)) ⊢ {Term.shift (Re⁺) 2 t} ∈ τ.
Proof.
  intros HvΓ HvRe Hwt.
  apply (weakening_ℜ_2 _ _ _ Re); auto.
  - rewrite RC.new_key_wh; lia.
  - apply RC.Submap_wh.
Qed.