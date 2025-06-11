From Coq Require Import Lia Arith.PeanoNat Classes.Morphisms List.
From DeBrLevel Require Import ListLevel LevelInterface.
From Mecha Require Import Typ Resource Term Var VContext Resources.
Import ResourceNotations TypNotations TermNotations ListNotations
       VContextNotations VarNotations ResourcesNotations SetNotations.


(** * Semantics - Type System 

  Wormhole's type system, denoted Γ ⋅ RC.t ⊢ t ∈ α, ensures that [t] is typed by [α] under two contexts [Γ] and [RC.t]. The former is the usual variable context, defined in [VContext.v], and the latter is a resource context, defined in [RContext.v]. This file contains the [well_typed] property definition and its weakening proofs.
*)



Module RC <: IsLvlETWL.
  Include IsLvlListETWL PairTyp.

  Definition threshold (l :t) := List.length l.

  Definition find (n : nat) (l : t) := List.nth_error l n.

  Definition add v (l : t) := l ++ [v].

  Definition multi_add vl (l : t) :=
    List.fold_right (fun v acc => add v acc) l vl.

  Definition key_in n (l : t) := n < (threshold l).

  Lemma find_some_in n v l :
    find n l = Some v -> key_in n l.
  Proof.
    revert n.
    induction l; intros n Hfi.
    - unfold key_in, find in *; simpl in *.
      destruct n; simpl in *; inversion Hfi.
    - destruct n; simpl in *.
      -- unfold key_in; simpl; lia.
      -- unfold key_in; simpl.
         apply IHl in Hfi; unfold key_in in *; lia.
  Qed.

  Lemma find_some_In n v l :
    find n l = Some v -> In v l.
  Proof.
    revert n.
    induction l; intros n Hfi.
    - unfold key_in, find in *; simpl in *.
      destruct n; simpl in *; inversion Hfi.
    - destruct n; simpl in *.
      -- inversion Hfi; auto.
      -- apply IHl in Hfi; auto.
  Qed.

  Lemma key_in_add n v l :
    key_in n (add v l) -> n = threshold l \/ key_in n l.
  Proof.
    unfold key_in, threshold, add.
    rewrite List.length_app; simpl in *.
    lia.
  Qed.

  Lemma threshold_add v l : threshold (add v l) = S (threshold l).
  Proof.
    unfold threshold, add.
    rewrite List.length_app; simpl in *.
    lia.
  Qed.

  Lemma Wf_add n v l :
    Wf n (add v l) -> PairTyp.Wf n v /\ Wf n l.
  Proof.
    intro Hwf; split.
    - apply Hwf; unfold add.
      apply in_or_app; right; simpl; auto.
    - intros x HIn; apply Hwf.
      unfold add.
      apply in_or_app; left; simpl; auto.
  Qed.

  Lemma Wf_add' n v l :
    PairTyp.Wf n v /\ Wf n l -> Wf n (add v l).
  Proof.
    intros [Hwfv Hwf] x HIn.
    unfold add in *.
    apply in_app_or in HIn as [].
    - now apply Hwf.
    - simpl in *; destruct H; try contradiction; subst; auto.
  Qed.

  Lemma Wf_add_iff n v l :
    Wf n (add v l) <-> PairTyp.Wf n v /\ Wf n l.
  Proof.
    split.
    - apply Wf_add.
    - apply Wf_add'.
  Qed.

  Lemma find_Wf n v l : 
    Wf (threshold l) l ->
    find n l = Some v -> Resource.Wf (threshold l) n /\ PairTyp.Wf (threshold l) v.
  Proof.
    unfold Wf.
    intros Hwf Hfi.
    apply find_some_in in Hfi as Hin.
    apply find_some_In in Hfi as HIn.
    apply Hwf in HIn; split; auto.
  Qed.

  Lemma Wf_wh v v' (l : t) :
    Wf (threshold l) l -> (threshold l ⊩ v)%pty -> (threshold l ⊩ v')%pty -> 
    Wf (S (S (threshold l))) (add v (add v' l)).
  Proof.
    intros Hvm Hvv Hvv'.
    repeat rewrite Wf_add_iff.
    split.
    - apply PairTyp.Wf_weakening with (n := threshold l); auto.
    - split.
      -- apply PairTyp.Wf_weakening with (n := threshold l); auto.
      -- apply Wf_weakening with (k := threshold l); auto.
  Qed.
          
End RC.

Module VC := VContext.

(** ** Definition - Type System *)

Reserved Notation "G '⋅' R '⊢' t '∈' T" (at level 40, t custom wh, T custom wh).

Inductive well_typed : Γ -> RC.t -> Λ -> Τ -> Prop :=
  | wt_var (Γ : Γ) (Re : RC.t) (x : variable) (τ : Τ) :

            (Γ ⌊x⌋)%vc = Some τ -> 
    (* -------------------------------- WT-Var *)
         Γ ⋅ Re ⊢ {Term.tm_var x} ∈ τ

  | wt_abs (Γ : Γ) (Re : RC.t) (x : variable) (t : Λ) (α β : Τ) :

         (⌈x ⤆ α⌉ Γ)%vc ⋅ Re ⊢ t ∈ β -> 
         ((RC.threshold Re) ⊩ α)%ty ->
    (* --------------------------------------------------- WT-Abs *)
                  Γ ⋅ Re ⊢ (\x, t) ∈ (α → β)

  | wt_app  (Γ : Γ) (Re : RC.t) (t1 t2 : Λ) (α β : Τ) :

         Γ ⋅ Re ⊢ t1 ∈ (α → β) -> Γ ⋅ Re ⊢ t2 ∈ α -> 
    (* ------------------------------------------------ WT-App *)
                      Γ ⋅ Re ⊢ t1 t2 ∈ β

  | wt_unit (Γ : Γ) (Re : RC.t) :

    (* --------------------- WT-Unit *)
         Γ ⋅ Re ⊢ unit ∈ 𝟙       

  | wt_pair (Γ : Γ) (Re : RC.t) (t1 t2 : Λ) (α β : Τ) :

         Γ ⋅ Re ⊢ t1 ∈ α -> Γ ⋅ Re ⊢ t2 ∈ β -> 
    (* ------------------------------------------ WT-Pair *)
            Γ ⋅ Re ⊢ ⟨t1, t2⟩ ∈ (α × β)

  | wt_fst (Γ : Γ) (Re : RC.t) (t : Λ) (α β : Τ) :

         Γ ⋅ Re ⊢ t ∈ (α × β) -> 
    (* --------------------------- WT-Fst *)
          Γ ⋅ Re ⊢ (fst.t) ∈ α

  | wt_snd (Γ : Γ) (Re : RC.t) (t : Λ) (α β : Τ) :

        Γ ⋅ Re ⊢ t ∈ (α × β) -> 
    (* --------------------------- WT-Snd *)
          Γ ⋅ Re ⊢ (snd.t) ∈ β

  | wt_fix (Γ : Γ) (Re : RC.t) (t : Λ) (τ : Τ) :

         Γ ⋅ Re ⊢ t ∈ (τ → τ) ->
    (* --------------------------- WT-Fix *)
           Γ ⋅ Re ⊢ Fix t ∈ τ

  | wt_arr (Γ : Γ) (Re : RC.t) (t : Λ) (α β : Τ) :

             Γ ⋅ Re ⊢ t ∈ (α → β) -> 
    (* ------------------------------------- WT-Arr *)
         Γ ⋅ Re ⊢ arr(t) ∈ (α ⟿ β ∣ ∅)%s

  | wt_first (Γ : Γ) (Re : RC.t) (R : resources) (t : Λ) (α β τ : Τ) :

         Γ ⋅ Re ⊢ t ∈ (α ⟿ β ∣ R) -> 
         ((RC.threshold Re) ⊩ τ)%ty ->
    (* ------------------------------------------------ WT-First *)
         Γ ⋅ Re ⊢ first(t) ∈ ((α × τ) ⟿ (β × τ) ∣ R)

  | wt_comp (Γ : Γ) (Re : RC.t) (R R1 R2 : resources) (t1 t2 : Λ) (α β τ : Τ) :

         Γ ⋅ Re ⊢ t1 ∈ (α ⟿ τ ∣ R1) -> (R = (R1 ∪ R2))%s -> 
         Γ ⋅ Re ⊢ t2 ∈ (τ ⟿ β ∣ R2) -> (∅ = (R1 ∩ R2))%s -> 
    (* -------------------------------------------------------- WT-Comp *)
              Γ ⋅ Re ⊢ (t1 >>> t2) ∈ (α ⟿ β ∣ R)

  | wt_rsf (Γ : Γ) (Re : RC.t) (r : resource) (τin τout : Τ) :

              RC.find r Re = Some (τin,τout) ->
    (* -------------------------------------------- WT-Rsf *)
         Γ ⋅ Re ⊢ rsf[r] ∈ (τin ⟿ τout ∣ \{{r}})

  | wt_wh (Γ : Γ) (Re : RC.t) (R R' : resources) (t1 t2 : Λ) (α β τ : Τ) :

         (R = R' \ \{{ (RC.threshold Re); (S ((RC.threshold Re))) }})%s -> ((RC.threshold Re) ⊩ α)%ty -> ((RC.threshold Re) ⊩ β)%ty ->

         Γ ⋅ Re ⊢ t1 ∈ τ ->
         Γ ⋅ (RC.add (τ,<[𝟙]>) (RC.add (<[𝟙]>,τ) Re)) ⊢ t2 ∈ (α ⟿ β ∣ R') ->
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
  unfold Term.eq,Typ.eq,RC.eq in *; subst; split.
  - intro wt; revert Γ' HGeq; induction wt; intros; eauto.
    -- constructor; now rewrite <- HGeq.
    -- constructor; auto.
       apply IHwt; auto; now rewrite HGeq.
  - intro wt; revert Γ HGeq; induction wt; intros; eauto.
    -- constructor; now rewrite HGeq.
    -- constructor; auto.
       apply IHwt; auto; now rewrite <- HGeq.
Qed.

(** *** Used resource names come from the resource context

  Suppose a value [t] (1), well typed by [(α ⟿ β ∣ R)] under contexts [Γ] and [Re] (2). Resource names in the set of used resources [R] have to be in Re, i.e. We can use only resource names known.
*)
Theorem typing_Re_R (Γ : Γ) (Re : RC.t) (t : Λ) (α β : Τ) (R : resources) :

       (* (1) *) value(t) -> (* (2) *) Γ ⋅ Re ⊢ t ∈ (α ⟿ β ∣ R) -> 
  (* ---------------------------------------------------------------- *)
           (forall (r : resource), (r ∈ R)%s -> (RC.key_in r Re)).
Proof.
  revert Γ Re α β R; induction t; intros Γ Re α β R Hvt Hwt r1 HIn; 
  inversion Hvt; subst; inversion Hwt; subst.
  (* arr *)
  - inversion HIn.
  (* first *)
  - apply (IHt Γ _ α0 β0 R); assumption.
  (* rsf *)
  - rewrite Resources.St.singleton_spec in HIn; subst.
    apply RC.find_some_in in H3; auto.
  (* comp *)
  - rewrite H9 in HIn. 
    apply Resources.St.union_spec in HIn as [HIn | HIn]; eauto.
  (* wormhole *)
  - rewrite H8 in HIn. 
    apply Resources.St.diff_spec in HIn as [HIn HnIn].
    eapply IHt2 in H12; eauto. 
    (repeat rewrite Resources.St.add_notin_spec in HnIn); destruct HnIn as [Hneq [Hneq' _]].
    apply RC.key_in_add in H12 as [].
    -- rewrite RC.threshold_add in H; subst; contradiction.
    -- apply RC.key_in_add in H as []; auto.
       subst; contradiction.
Qed.

(** *** Well typed implies well formedness 

  Suppose a term [t], well typed by [τ] under contexts [Γ] and [Re] (3), knowing that both contexts are well formed under [(RC.threshold Re)] (1,2). We can prove that [t] and [τ] are also well formed under [(RC.threshold Re)] (4,5).
*)
Theorem well_typed_implies_Wf (Γ : Γ) (Re : RC.t) (t : Λ) (τ : Τ) :

       (* (1) *) ((RC.threshold Re) ⊩ Γ)%vc ->  (* (2) *) (RC.Wf (RC.threshold Re) Re) -> (* (3) *) Γ ⋅ Re ⊢ t ∈ τ ->
  (* -------------------------------------------------------------------------------------- *)
                      (* (4) *) (RC.threshold Re) ⊩ t /\ (* (5) *) ((RC.threshold Re) ⊩ τ)%ty.
Proof.
  revert Γ Re τ; induction t; simpl; intros Γ Re τ HvΓ HvRe Hwt; inversion Hwt; subst;
  try (apply IHt in H2 as [Hvt Hvf]; auto; inversion Hvf; subst; now repeat constructor).
  (* unit *)
  - repeat constructor.
  (* variable *)
  - split; try constructor. 
    now apply (VC.Wf_find ((RC.threshold Re))) in H2.
  (* abstraction *)
  - apply (IHt (⌈x ⤆ α⌉ Γ)%vc _ β) in HvRe as [Hvt Hvf]; auto.
    -- split; auto; constructor; assumption.
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
  - apply IHt in H0 as [Hvt Hvf]; auto; inversion Hvf; subst.
    repeat constructor; auto.
  (* rsf *)
  - apply RC.find_Wf in H2 as [Hvr Hvf]; auto.
    inversion Hvf; simpl in *; repeat constructor; auto.
    now apply Resources.Wf_singleton_iff.
  (* comp *)
  - apply IHt1 in H1 as [Hvt1 Hvα]; apply IHt2 in H5 as [Hvt2 Hvβ]; auto.
    inversion Hvα; inversion Hvβ; subst; repeat constructor; auto.
    rewrite H2; rewrite Resources.Wf_union_iff; now split.
  (* wormhole *)
  - apply IHt1 in H6 as [Hvt1 Hvτ]; auto.
    apply IHt2 in H8 as [Hvt2 Hvf]; repeat (rewrite RC.threshold_add in *).
    -- inversion Hvf; subst. 
       split; constructor; auto.
       apply Resources.eq_leibniz in H1; subst.
       now apply Resources.Wf_wh.
    -- apply VC.Wf_weakening with (k := (RC.threshold Re)); auto.
    -- apply RC.Wf_wh; auto; now repeat constructor; simpl.
Qed.

(** *** Variable context weakening 

  Suppose a term [t], well typed by [τ] under contexts [Γ] and [Re] (2) and another variable context named [Γ'] such as [Γ] is included in [Γ'] (1). We can state that [t] is also well typed by swap [Γ] with [Γ'].
*)
Theorem weakening_Γ (Γ Γ' : Γ) (Re : RC.t) (t : Λ) (τ : Τ) :

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
Theorem weakening_RC_gen (k k' : lvl) (Γ : Γ) vl (Rc : RC.t) (t : Λ) (τ : Τ) :

        (* (1) *) k <= (RC.threshold Rc) ->  
        (* (2) *) k <= k' -> 
        (* (3) *) k' - k = (RC.threshold (RC.multi_add vl Rc)) - (RC.threshold Rc) ->
        (* (5) *) Γ ⋅ Rc ⊢ t ∈ τ -> 
  (* ------------------------------------------------------------------------------------ *)
       ([⧐ k – (k' - k)] Γ)%vc ⋅ 
       (RC.multi_add vl Rc) ⊢ 
      {Term.shift k (k' - k) t} ∈ [⧐ k – {k' - k}] τ.
Proof.
  intros Hle Hle' Heq Hsub wt; revert Re1 k k' Hle Hle' Hsub Heq.
  induction wt; intros Re1 n m Hle Hle' Hsub Heq; simpl; auto.
  (* variable *)
  - constructor; now apply VC.shift_find_iff.
  (* abstraction *)
  - constructor.
    -- rewrite <- VC.shift_add; now apply IHwt.
    -- assert ((RC.threshold Rc) <= Re1⁺).
       { 
         apply RC.Ext.new_key_Submap in Hsub. 
         now rewrite <- RC.shift_new_key_le in Hsub.
       }
       apply (Typ.shift_preserves_wf_gen ((RC.threshold Re))); auto; lia. 
  (* application *)
  - apply wt_app with (α := <[[⧐n – {m - n}] α]>); auto.
  (* fst *)
  - simpl in *; apply wt_fst with (β := <[[⧐ n – {m - n}] β]>); auto.
  (* snd *)
  - simpl in *; apply wt_snd with (α := <[[⧐ n – {m - n}] α]>); auto.
  (* first *)
  - econstructor; eauto. 
    assert ((RC.threshold Re) <= Re1⁺).
    { 
      apply RC.Ext.new_key_Submap in Hsub. 
      now rewrite <- RC.shift_new_key_le in Hsub.
    }
    apply Typ.shift_preserves_wf_gen with ((RC.threshold Re)); auto; lia.
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
  - assert (Hle1 : (RC.threshold Re) <= Re1⁺). 
    { 
      apply RC.Ext.new_key_Submap in Hsub. 
      now rewrite <- RC.shift_new_key_le in Hsub.
    }
    eapply wt_wh with (τ := <[[⧐ n – {m - n}] τ]>) (R' := ([⧐ n – m - n] R')%rs); auto.
    -- rewrite H; rewrite Resources.shift_diff.
       repeat rewrite Resources.shift_add_notin.
       + unfold Resource.shift. 
         rewrite <- Nat.leb_le in Hle; rewrite Hle.
         replace (n <=? S ((RC.threshold Re))) with true.
         ++ rewrite Resources.shift_empty. 
            rewrite Heq; simpl.
            now replace ((RC.threshold Re) + (Re1⁺ - (RC.threshold Re))) with (Re1⁺) by lia.
        ++ symmetry; rewrite Nat.leb_le in *; lia.
      + intro HIn; inversion HIn.
      + rewrite Resources.St.add_notin_spec; split; auto. 
        intro HIn; inversion HIn.
    -- apply Typ.shift_preserves_wf_gen with ((RC.threshold Re)); auto; lia.
    -- apply Typ.shift_preserves_wf_gen with ((RC.threshold Re)); auto; lia.
    -- apply IHwt2; rewrite RC.new_key_wh in *; try lia. 
       + repeat rewrite RC.shift_add_notin.
         ++ unfold PairTyp.shift; simpl; unfold Resource.shift.
           replace (n <=? S ((RC.threshold Re))) with true; replace (n <=? (RC.threshold Re)) with true;
           try (symmetry; rewrite Nat.leb_le; lia).
           replace ((RC.threshold Re) + (m - n)) with (Re1⁺) by lia.
           replace (S (Re ⁺) + (m - n)) with (S (Re1⁺)) by lia.
           now repeat apply RC.Submap_add.
        ++ apply RC.Ext.new_key_notin; lia.
        ++ apply RC.Ext.new_key_notin.
           rewrite RC.Ext.new_key_add_max; lia.
      + rewrite RC.new_key_wh; lia.
Qed.

(** *** Weakening corollaries *)

Corollary weakening_Γ_empty (Γ : Γ) (Re : RC.t) (t : Λ) (τ : Τ) :

       (∅)%vc ⋅ Re ⊢ t ∈ τ -> 
  (* -------------------------- *)
          Γ ⋅ Re ⊢ t ∈ τ.
Proof. apply weakening_Γ; apply VContext.Submap_empty_bot. Qed.

Corollary weakening_RC_1 (Γ : Γ) (Re Re1 : RC.t) (t : Λ) (τ : Τ) :

                ((RC.threshold Re) ⊩ Re)%rc -> (Re ⊆ Re1)%rc -> Γ ⋅ Re ⊢ t ∈ τ -> 
(* ---------------------------------------------------------------------------------- *)
     ([⧐ (RC.threshold Re) – (Re1⁺ - (RC.threshold Re))] Γ)%vc ⋅ Re1 ⊢ 
               {Term.shift ((RC.threshold Re)) (Re1⁺ - (RC.threshold Re)) t} ∈ ([⧐ {(RC.threshold Re)} – {Re1⁺ - (RC.threshold Re)}] τ)%ty.
Proof. 
  intros HvRe Hsub Hwt; apply weakening_RC.t_gen with (Re := Re); auto.
  - now apply RC.Ext.new_key_Submap.
  - rewrite RC.shift_wf_refl; auto.
Qed.

Corollary weakening_RC (Γ : Γ) (Re Re1 : RC.t) (t : Λ) (τ : Τ) :

       ((RC.threshold Re) ⊩ Γ)%vc -> ((RC.threshold Re) ⊩ Re)%rc -> (Re ⊆ Re1)%rc -> Γ ⋅ Re ⊢ t ∈ τ -> 
  (* ----------------------------------------------------------------------- *)
              Γ ⋅ Re1 ⊢ {Term.shift ((RC.threshold Re)) (Re1⁺ - (RC.threshold Re)) t} ∈ τ.
Proof.
  intros HvΓ HvRe Hsub Hwt.
  apply (weakening_RC.t_1 _ _ Re1) in Hwt as Hwt'; auto.
  rewrite VC.shift_wf_refl in Hwt'; auto.
  apply well_typed_implies_Wf in Hwt as [_ Hvτ]; auto.
  now rewrite Typ.shift_wf_refl in Hwt'. 
Qed.

Corollary weakening_RC.t_2 (k k' : lvl) (Γ : Γ) (Re Re1 : RC.t) (t : Λ) (τ : Τ) :

      ((RC.threshold Re) ⊩ Γ)%vc -> ((RC.threshold Re) ⊩ Re)%rc -> k = (RC.threshold Re) -> k' = Re1⁺ - (RC.threshold Re) ->
                (Re ⊆ Re1)%rc -> Γ ⋅ Re ⊢ t ∈ τ -> 
  (* ------------------------------------------------------------------ *) 
                Γ ⋅ Re1 ⊢ {Term.shift k k' t} ∈ τ.
Proof. intros; subst; now apply weakening_RC.t. Qed.

Corollary weakening_RC.t_wh (Γ : Γ) (Re : RC.t) (t : Λ) (α β τ : Τ) :

                ((RC.threshold Re) ⊩ Γ)%vc -> ((RC.threshold Re) ⊩ Re)%rc -> Γ ⋅ Re ⊢ t ∈ τ -> 
  (* ------------------------------------------------------------------------------- *)
       Γ ⋅ (⌈S ((RC.threshold Re)) ⤆ (β, α)⌉ (⌈(RC.threshold Re) ⤆ (α, β)⌉ Re)) ⊢ {Term.shift ((RC.threshold Re)) 2 t} ∈ τ.
Proof.
  intros HvΓ HvRe Hwt.
  apply (weakening_RC.t_2 _ _ _ Re); auto.
  - rewrite RC.new_key_wh; lia.
  - apply RC.Submap_wh.
Qed.


(* Theorem weakening_RC.t_gen' (k k' : lvl) (Γ : Γ) (Re Re1 : RC.t) (t : Λ) (τ : Τ) :

        (* (1) *) k <= (RC.threshold Re) ->  (* (2) *) k <= k' -> (* (3) *) k' - k = Re1⁺ - (RC.threshold Re) ->
         (* (4) *) (([⧐ k – (k' - k)] Re) ⊆ Re1)%rc -> (* (5) *)
          ([⧐ k – (k' - k)] Γ)%vc ⋅ Re1 ⊢ {Term.shift k (k' - k) t} ∈ [⧐ k – {k' - k}] τ -> 
  (* ------------------------------------------------------------------------------------ *)
        Γ ⋅ Re ⊢ t ∈ τ .
Proof.
  revert k k' Γ Re Re1 τ; induction t;
  intros k k' Γ Re Re1 τ Hle Hle' Heq Hsub Hwt.
  - simpl in *; inversion Hwt; subst.
    destruct τ; inversion H1.
    constructor.
  - simpl in *; inversion Hwt; subst.
    apply VC.shift_find_iff in H2.
    constructor; auto.
  - simpl in *; inversion Hwt; subst.
    destruct τ; inversion H3; subst.
    constructor.
    -- eapply IHt; eauto.
       rewrite VC.shift_add; auto.
    -- admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - simpl in *; inversion Hwt; subst.
    destruct τ; inversion H2; subst; clear H2.
      *)