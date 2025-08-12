From Coq Require Import Lia Arith.PeanoNat Classes.Morphisms.
From Mecha Require Import Typ Resource Term Var VContext RContext 
                          SyntaxNotation EnvNotation.


(** * Semantics - Type System 

  Wormhole's type system, denoted Γ ⋅ ℜ ⊢ t ∈ A, ensures that [t] is typed by [A] under two contexts [Γ] and [ℜ]. The former is a variable context, defined in [VContext.v], and the latter is a resource context, defined in [RContext.v]. This file contains the [well_typed] property definition and its weakening proofs.
*)


Open Scope rcontext_scope.

(** ** Definition - Type System *)

Reserved Notation "G '⋅' R '⊢' t '∈' T" (at level 40, t custom wh, T custom wh).

Inductive well_typed : Γ -> ℜ -> Λ -> Τ -> Prop :=
  | wt_var (Γ : Γ) (Re : ℜ) (x : variable) (A : Τ) :

            (Γ ⌊x⌋)%vc = Some A -> 
    (* -------------------------------- WT-Var *)
         Γ ⋅ Re ⊢ {Term.tm_var x} ∈ A

  | wt_abs (Γ : Γ) (Re : ℜ) (x : variable) (t : Λ) (A B : Τ) :

         (⌈x ⤆ A⌉ Γ)%vc ⋅ Re ⊢ t ∈ B -> (Re⁺ ⊩ A)%ty ->
    (* --------------------------------------------------- WT-Abs *)
                  Γ ⋅ Re ⊢ (\x :A, t) ∈ (A → B)

  | wt_app  (Γ : Γ) (Re : ℜ) (t1 t2 : Λ) (A B : Τ) :

         Γ ⋅ Re ⊢ t1 ∈ (A → B) -> Γ ⋅ Re ⊢ t2 ∈ A -> 
    (* ------------------------------------------------ WT-App *)
                      Γ ⋅ Re ⊢ t1 t2 ∈ B

  | wt_unit (Γ : Γ) (Re : ℜ) :

    (* --------------------- WT-Unit *)
         Γ ⋅ Re ⊢ unit ∈ 𝟙       

  | wt_pair (Γ : Γ) (Re : ℜ) (t1 t2 : Λ) (A B : Τ) :

         Γ ⋅ Re ⊢ t1 ∈ A -> Γ ⋅ Re ⊢ t2 ∈ B -> 
    (* ------------------------------------------ WT-Pair *)
            Γ ⋅ Re ⊢ ⟨t1, t2⟩ ∈ (A × B)

  | wt_fst (Γ : Γ) (Re : ℜ) (t : Λ) (A B : Τ) :

         Γ ⋅ Re ⊢ t ∈ (A × B) -> 
    (* --------------------------- WT-Fst *)
          Γ ⋅ Re ⊢ (fst.t) ∈ A

  | wt_snd (Γ : Γ) (Re : ℜ) (t : Λ) (A B : Τ) :

        Γ ⋅ Re ⊢ t ∈ (A × B) -> 
    (* --------------------------- WT-Snd *)
          Γ ⋅ Re ⊢ (snd.t) ∈ B

  | wt_fix (Γ : Γ) (Re : ℜ) (t : Λ) (C : Τ) :

         Γ ⋅ Re ⊢ t ∈ (C → C) ->
    (* --------------------------- WT-Fix *)
           Γ ⋅ Re ⊢ Fix t ∈ C

  | wt_arr (Γ : Γ) (Re : ℜ) (t : Λ) (A B : Τ) :

             Γ ⋅ Re ⊢ t ∈ (A → B) -> 
    (* ------------------------------------- WT-Arr *)
         Γ ⋅ Re ⊢ arr(t) ∈ (A ⟿ B ∣ ∅)%s

  | wt_first (Γ : Γ) (Re : ℜ) (R : resources) (t : Λ) (A B C : Τ) :

         Γ ⋅ Re ⊢ t ∈ (A ⟿ B ∣ R) -> (Re⁺ ⊩ C)%ty ->
    (* ------------------------------------------------ WT-First *)
         Γ ⋅ Re ⊢ first(C:t) ∈ ((A × C) ⟿ (B × C) ∣ R)

  | wt_comp (Γ : Γ) (Re : ℜ) (R R1 R2 : resources) (t1 t2 : Λ) (A B C : Τ) :

         Γ ⋅ Re ⊢ t1 ∈ (A ⟿ C ∣ R1) -> (R = (R1 ∪ R2))%s -> 
         Γ ⋅ Re ⊢ t2 ∈ (C ⟿ B ∣ R2) -> (∅ = (R1 ∩ R2))%s -> 
    (* -------------------------------------------------------- WT-Comp *)
              Γ ⋅ Re ⊢ (t1 >>> t2) ∈ (A ⟿ B ∣ R)

  | wt_rsf (Γ : Γ) (Re : ℜ) (r : resource) (τin τout : Τ) :

              Re ⌊r⌋ = Some (τin,τout) ->
    (* -------------------------------------------- WT-Rsf *)
         Γ ⋅ Re ⊢ rsf[r] ∈ (τin ⟿ τout ∣ \{{r}})

  | wt_wh (Γ : Γ) (Re : ℜ) (R R' : resources) (t1 t2 : Λ) (A B C : Τ) :

         (R = R' \ \{{ Re⁺; (S (Re⁺)) }})%s -> (Re⁺ ⊩ A)%ty -> (Re⁺ ⊩ B)%ty ->

         Γ ⋅ Re ⊢ t1 ∈ C ->
         Γ ⋅ (⌈(S (Re⁺)) ⤆ (C,<[𝟙]>)⌉ (⌈Re⁺ ⤆ (<[𝟙]>,C)⌉ Re)) ⊢ t2 ∈ (A ⟿ B ∣ R') ->
    (* -------------------------------------------------------------------------------- WT-Wh *)
                          Γ ⋅ Re ⊢ wormhole(t1;t2) ∈ (A ⟿ B ∣ R)

where "G '⋅' R '⊢' t '∈' T" := (well_typed G R t T).

Hint Constructors well_typed : core.

(** ---- *)

(** ** Property - Type System *)

Open Scope term_scope.

#[export] Instance well_typed_iff : 
  Proper (VC.eq ==> RC.eq ==> Term.eq ==> Typ.eq ==> iff) well_typed.
Proof.
  intros Γ Γ' HGeq Re Re1 HReq t' t HTmeq A B HTyeq.
  unfold Term.eq,Typ.eq in *; subst; split.
  - intro wt; revert Γ' HGeq Re1 HReq; induction wt; intros;
    try (econstructor; now auto); auto.
    -- constructor; now rewrite <- HGeq.
    -- constructor; try (now rewrite <- HReq). 
       apply IHwt; auto; now rewrite HGeq.
    -- constructor; auto; try (now rewrite <- HReq).
    -- constructor; auto; now rewrite <- HReq.
    -- apply wt_wh with (R' := R') (C := C); auto;
       try (apply IHwt2; auto); now rewrite <- HReq.
  - intro wt; revert Γ HGeq Re HReq; induction wt; intros;
    try (econstructor; now auto); auto.
    -- constructor; now rewrite HGeq.
    -- constructor; try (now rewrite HReq). 
       apply IHwt; auto; now rewrite <- HGeq.
    -- constructor; auto; now rewrite HReq.
    -- constructor; auto; now rewrite HReq.
    -- apply wt_wh with (R' := R') (C := C); auto;
       try (apply IHwt2; auto); now rewrite HReq.
Qed.

(** *** Determinism of [well_typed] property 

  For the same variable context [Γ], resource context [ℜ] and term [t], if [A] and [B] type [t] under [Γ] and [ℜ] then [A] is equal to [B].
*)
Lemma wt_deterministic (Γ : Γ) (Re : ℜ) (t : Λ) (A B : Τ) :
  Γ ⋅ Re ⊢ t ∈ A -> Γ ⋅ Re ⊢ t ∈ B -> A = B.
Proof.
  revert Γ Re A B; induction t;
  intros G Re A' B' Hwt Hwt'; 
  inversion Hwt; subst; inversion Hwt'; subst; auto.
  - rewrite H2 in H3; inversion H3; auto.
  - f_equal; auto.
    apply IHt with (A := B) in H7; auto.
  - apply IHt2 with (A := A) in H7; auto; subst.
    apply IHt1 with (A := <[A0 → A']>) in H4; auto.
    now inversion H4; subst.
  - f_equal; 
    try (now apply (IHt1 G Re); auto);
    try (now apply (IHt2 G Re); auto).
  - apply (IHt G Re <[A' → A']>) in H3; auto.
    inversion H3; now subst.
  - apply (IHt G Re <[A' × B]>) in H3; auto.
    now inversion H3.
  - apply (IHt G Re <[A × A']>) in H3; auto.
    now inversion H3.
  - apply (IHt G Re <[A → B]>) in H3; auto.
    inversion H3; f_equal; auto.
  - apply (IHt G Re <[A0 ⟿ B ∣ R]>) in H4; auto.
    inversion H4; f_equal; auto.
  - rewrite H2 in H3; inversion H3; f_equal; auto.
  - apply (IHt1 G Re <[A ⟿ C ∣ R1]>) in H3; auto.
    inversion H3; subst; clear H3.
    apply (IHt2 G Re <[C0 ⟿ B ∣ R2]>) in H9; auto.
    inversion H9; subst; clear H9.
    apply RS.eq_leibniz in H2,H4; subst; auto.
  - apply (IHt1 G Re C) in H11; auto; subst.
    apply (IHt2 G _ <[A ⟿ B ∣ R']>) in H13; auto.
    inversion H13; subst; clear H13.
    apply RS.eq_leibniz in H1,H4; subst; auto.
Qed.

(** *** Used resource names come from the resource context

  Suppose a value [t] (1), well typed by [(A ⟿ B ∣ R)] under contexts [Γ] and [Re] (2). Resource names in the set of used resources [R] have to be in Re, i.e. We can use only resource names known.
*)
Theorem typing_Re_R (Γ : Γ) (Re : ℜ) (t : Λ) (A B : Τ) (R : resources) :

       (* (1) *) value(t) -> (* (2) *) Γ ⋅ Re ⊢ t ∈ (A ⟿ B ∣ R) -> 
  (* ---------------------------------------------------------------- *)
           (forall (r : resource), (r ∈ R)%s -> (r ∈ Re)%rc).
Proof.
  revert Γ Re A B R; induction t; intros Γ Re A' B' R Hvt Hwt r1 HIn; 
  inversion Hvt; subst; inversion Hwt; subst.
  (* arr *)
  - inversion HIn.
  (* first *)
  - apply (IHt Γ _ A0 B R); assumption.
  (* rsf *)
  - rewrite RS.St.singleton_spec in HIn; subst.
    exists (A',B'); now apply RC.find_2.
  (* comp *)
  - rewrite H9 in HIn. 
    apply RS.St.union_spec in HIn as [HIn | HIn]; eauto.
  (* wormhole *)
  - rewrite H8 in HIn. 
    apply RS.St.diff_spec in HIn as [HIn HnIn].
    eapply IHt2 in H12; eauto. 
    (repeat rewrite RS.St.add_notin_spec in HnIn); destruct HnIn as [Hneq [Hneq' _]].
    (repeat rewrite RC.add_in_iff in H12). 
    destruct H12 as [Heq | [Heq | HIn']]; subst; try contradiction; assumption. 
Qed.

(** *** Well typed implies well formedness 

  Suppose a term [t], well typed by [C] under contexts [Γ] and [Re] (3), knowing that both contexts are well formed under [Re⁺] (1,2). We can prove that [t] and [C] are also well formed under [Re⁺] (4,5).
*)
Theorem well_typed_implies_Wf (Γ : Γ) (Re : ℜ) (t : Λ) (C : Τ) :

       (* (1) *) (Re⁺ ⊩ Γ)%vc ->  (* (2) *) (Re⁺ ⊩ Re)%rc -> (* (3) *) Γ ⋅ Re ⊢ t ∈ C ->
  (* -------------------------------------------------------------------------------------- *)
                      (* (4) *) Re⁺ ⊩ t /\ (* (5) *) (Re⁺ ⊩ C)%ty.
Proof.
  revert Γ Re C; induction t; simpl; intros Γ Re ty HvΓ HvRe Hwt; inversion Hwt; subst;
  try (apply IHt in H2 as [Hvt Hvf]; auto; inversion Hvf; subst; now repeat constructor).
  (* unit *)
  - repeat constructor.
  (* variable *)
  - split; try constructor. 
    now apply (VC.Wf_find (Re⁺)) in H2.
  (* abstraction *)
  - apply (IHt (⌈x ⤆ A⌉ Γ)%vc _ B) in HvRe; auto. 
    -- destruct HvRe; split; auto; constructor; assumption.
    -- now apply VContext.Wf_add.
  (* application *)
  - apply IHt1 in H3 as [Hvt1 Hvf]; eauto.
    apply IHt2 in H5 as [Hvt2 _]; eauto.
    inversion Hvf; subst.
    split; auto; constructor; auto.
  (* pair *) 
  - apply IHt1 in H3 as [Hvt1 HvA]; apply IHt2 in H5 as [Hvt2 HvB]; auto; 
    now repeat constructor.
  (* first *)
  - apply IHt in H3 as [Hvt Hvf]; auto; inversion Hvf; subst.
    repeat constructor; auto.
  (* rsf *)
  - apply RC.Wf_find with (lb := Re⁺) in H2 as [Hvr Hvf]; auto.
    inversion Hvf; simpl in *; repeat constructor; auto.
    now apply RS.Wf_singleton_iff.
  (* comp *)
  - apply IHt1 in H1 as [Hvt1 HvA]; apply IHt2 in H5 as [Hvt2 HvB]; auto.
    inversion HvA; inversion HvB; subst; repeat constructor; auto.
    rewrite H2; rewrite RS.Wf_union_iff; now split.
  (* wormhole *)
  - apply IHt1 in H6 as [Hvt1 Hvτ]; auto.
    apply IHt2 in H8 as [Hvt2 Hvf]; rewrite RC.new_key_wh in *.
    -- inversion Hvf; subst; repeat constructor; auto. 
       rewrite H1; now apply RS.Wf_wh.
    -- apply VC.Wf_weakening with (k := Re⁺); auto.
    -- apply RC.Wf_wh; auto; now repeat constructor; simpl.
Qed.

(** *** Variable context weakening 

  Suppose a term [t], well typed by [C] under contexts [Γ] and [Re] (2) and another variable context named [Γ'] such as [Γ] is included in [Γ'] (1). We can state that [t] is also well typed by swap [Γ] with [Γ'].
*)
Theorem weakening_Γ (Γ Γ' : Γ) (Re : ℜ) (t : Λ) (C : Τ) :

       (* (1) *) (Γ ⊆ Γ')%vc -> (* (2) *) Γ ⋅ Re ⊢ t ∈ C -> 
  (* -------------------------------------------------------- *)
                       Γ' ⋅ Re ⊢ t ∈ C .
Proof.
  intros Hsub wt; revert Γ' Hsub; induction wt; intros; auto;
  try (econstructor; now auto).
  - constructor; now apply (VC.Submap_find _ _ Γ).
  - apply wt_abs; auto; apply IHwt. 
    now apply VC.Submap_add.
Qed.

Open Scope typ_scope.

(** *** Resource context weakening 

  Suppose a term [t], well typed by [C] under contexts [Γ] and [Re] (5) and another resource context named [Re1] such as ([[⧐ k – (k' - k)] Re]) is included in [Re1] (4). [k] and [k'] are levels such as they satisfy hypothesis (1),(2) and (3). We prove that [t] is also well typed by swap [Re] with [Re1] modulo [shift] applications.
  
*)
Theorem weakening_ℜ_gen (k k' : lvl) (Γ : Γ) (Re Re1 : ℜ) (t : Λ) (C : Τ) :

        (* (1) *) k <= Re⁺ ->  (* (2) *) k <= k' -> (* (3) *) k' - k = Re1⁺ - Re⁺ ->
         (* (4) *) (([⧐ k – (k' - k)] Re) ⊆ Re1)%rc -> (* (5) *) Γ ⋅ Re ⊢ t ∈ C -> 
  (* ------------------------------------------------------------------------------------ *)
       ([⧐ k – (k' - k)] Γ)%vc ⋅ Re1 ⊢ {Term.shift k (k' - k) t} ∈ [⧐ k – {k' - k}] C.
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
  - apply wt_app with (A := <[[⧐n – {m - n}] A]>); auto.
  (* fst *)
  - simpl in *; apply wt_fst with (B := <[[⧐ n – {m - n}] B]>); auto.
  (* snd *)
  - simpl in *; apply wt_snd with (A := <[[⧐ n – {m - n}] A]>); auto.
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
    -- rewrite <- RS.shift_union.
       now rewrite H.
    -- rewrite <- RS.shift_inter; rewrite <- H0. 
       now rewrite RS.shift_empty.
  (* rsf *)
  - rewrite RS.shift_singleton; constructor.
    apply RC.Submap_find with (m :=  ([⧐ n – m - n] Re)); auto.
    apply RC.shift_find_iff with (lb := n) (k := m - n) in H; auto.
  (* wormhole *)
  - assert (Hle1 : Re⁺ <= Re1⁺). 
    { 
      apply RC.Ext.new_key_Submap in Hsub. 
      now rewrite <- RC.shift_new_key_le in Hsub.
    }
    eapply wt_wh with (C := <[[⧐ n – {m - n}] C]>) (R' := ([⧐ n – m - n] R')%rs); auto.
    -- rewrite H; rewrite RS.shift_diff.
       repeat rewrite RS.shift_add_notin.
       + unfold Resource.shift. 
         rewrite <- Nat.leb_le in Hle; rewrite Hle.
         replace (n <=? S (Re⁺)) with true.
         ++ rewrite RS.shift_empty. 
            rewrite Heq; simpl.
            now replace (Re⁺ + (Re1⁺ - Re⁺)) with (Re1⁺) by lia.
        ++ symmetry; rewrite Nat.leb_le in *; lia.
      + intro HIn; inversion HIn.
      + rewrite RS.St.add_notin_spec; split; auto. 
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

Corollary weakening_Γ_empty (Γ : Γ) (Re : ℜ) (t : Λ) (C : Τ) :

       (∅)%vc ⋅ Re ⊢ t ∈ C -> 
  (* -------------------------- *)
          Γ ⋅ Re ⊢ t ∈ C.
Proof. apply weakening_Γ; apply VContext.Submap_empty_bot. Qed.

Corollary weakening_ℜ_1 (Γ : Γ) (Re Re1 : ℜ) (t : Λ) (C : Τ) :

                (Re⁺ ⊩ Re)%rc -> (Re ⊆ Re1)%rc -> Γ ⋅ Re ⊢ t ∈ C -> 
(* ---------------------------------------------------------------------------------- *)
     ([⧐ Re⁺ – (Re1⁺ - Re⁺)] Γ)%vc ⋅ Re1 ⊢ 
               {Term.shift (Re⁺) (Re1⁺ - Re⁺) t} ∈ ([⧐ {Re⁺} – {Re1⁺ - Re⁺}] C)%ty.
Proof. 
  intros HvRe Hsub Hwt; apply weakening_ℜ_gen with (Re := Re); auto.
  - now apply RC.Ext.new_key_Submap.
  - rewrite RC.shift_wf_refl; auto.
Qed.

Corollary weakening_ℜ (Γ : Γ) (Re Re1 : ℜ) (t : Λ) (C : Τ) :

       (Re⁺ ⊩ Γ)%vc -> (Re⁺ ⊩ Re)%rc -> (Re ⊆ Re1)%rc -> Γ ⋅ Re ⊢ t ∈ C -> 
  (* ----------------------------------------------------------------------- *)
              Γ ⋅ Re1 ⊢ {Term.shift (Re⁺) (Re1⁺ - Re⁺) t} ∈ C.
Proof.
  intros HvΓ HvRe Hsub Hwt.
  apply (weakening_ℜ_1 _ _ Re1) in Hwt as Hwt'; auto.
  rewrite VC.shift_wf_refl in Hwt'; auto.
  apply well_typed_implies_Wf in Hwt as [_ Hvτ]; auto.
  now rewrite Typ.shift_wf_refl in Hwt'. 
Qed.

Corollary weakening_ℜ_2 (k k' : lvl) (Γ : Γ) (Re Re1 : ℜ) (t : Λ) (C : Τ) :

      (Re⁺ ⊩ Γ)%vc -> (Re⁺ ⊩ Re)%rc -> k = Re⁺ -> k' = Re1⁺ - Re⁺ ->
                (Re ⊆ Re1)%rc -> Γ ⋅ Re ⊢ t ∈ C -> 
  (* ------------------------------------------------------------------ *) 
                Γ ⋅ Re1 ⊢ {Term.shift k k' t} ∈ C.
Proof. intros; subst; now apply weakening_ℜ. Qed.

Corollary weakening_ℜ_wh (Γ : Γ) (Re : ℜ) (t : Λ) (A B C : Τ) :

                (Re⁺ ⊩ Γ)%vc -> (Re⁺ ⊩ Re)%rc -> Γ ⋅ Re ⊢ t ∈ C -> 
  (* ------------------------------------------------------------------------------- *)
       Γ ⋅ (⌈S (Re⁺) ⤆ (B, A)⌉ (⌈Re⁺ ⤆ (A, B)⌉ Re)) ⊢ {Term.shift (Re⁺) 2 t} ∈ C.
Proof.
  intros HvΓ HvRe Hwt.
  apply (weakening_ℜ_2 _ _ _ Re); auto.
  rewrite RC.new_key_wh; lia.
Qed.

Hint Resolve weakening_Γ_empty weakening_ℜ_wh : core.