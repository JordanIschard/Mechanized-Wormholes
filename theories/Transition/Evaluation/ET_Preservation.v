From Coq Require Import Lia Program.
From Mecha Require Import Typ Resource Term Var VContext RContext Typing ET_Definition.
Import ResourceNotations TermNotations TypNotations VContextNotations RContextNotations.

(** * Transition - Evaluation - Preservation *)

(** *** General proof of preservation of typing through the substitution

  **** Hypothesis

  Knowing the context is valid regards of its own new key (1),
  the term t is well typed according to a certain context Re (2), 
  the substitute is well typed according to a certain context Re1 (3) and
  Re is a submap of Re1 (4);

  **** Result

  We can state that the term t where x is replaced with v is well typed
  according to Re (modulo a shift). 
*)
Theorem subst_preserves_typing_gen : forall Γ Re Re1 t v τ τ' x,
  (* (1) *) Re1⁺ᵣᵪ ⊩ᵣᵪ Re1 -> 
  (* (2) *) ⌈x ⤆ τ'⌉ᵥᵪ Γ ⋅ Re ⊫ t ∈ τ -> 
  (* (3) *) ∅ᵥᵪ ⋅ Re1 ⊫ v ∈ τ' ->
  (* (4) *) Re1 ⊆ᵣᵪ Re ->

  Γ ⋅ Re ⊫ ([x := v ~  {Re1⁺ᵣᵪ} ≤ {Re⁺ᵣᵪ - Re1⁺ᵣᵪ}] t) ∈ τ.
Proof.
  intros Γ Re Re1 t; revert Γ Re Re1; induction t;
  intros Γ Re Re1 v' α β x HvRₑ wt Hwv Hsub; inversion wt; subst;
  try (econstructor; now eauto).
  - simpl; destruct (Var.eqb_spec x v); subst.
    -- rewrite VContext.add_eq_o in H2; inversion H2; subst; clear H2; auto.
       apply weakening_Γ_empty. apply weakening_ℜ; auto.
       apply VContext.valid_empty_spec. 
    -- constructor; rewrite VContext.add_neq_o in H2; assumption.
  - simpl; destruct (Var.eqb_spec x v); subst.
    -- constructor; auto. now rewrite VContext.add_shadow in H5.
    -- constructor; auto. rewrite VContext.add_add_2 in H5; auto.
       eapply IHt; eauto.
  - econstructor; eauto; fold subst.
    eapply IHt2 in Hwv; eauto.
    -- replace (S (S (Re⁺ᵣᵪ - Re1⁺ᵣᵪ))) with ((S (S (Re⁺ᵣᵪ))) - Re1⁺ᵣᵪ).
      + erewrite <- RContext.new_key_wh_spec; eauto.
      + apply RContext.Ext.new_key_Submap_spec in Hsub; lia.
    -- now apply RContext.Ext.new_key_Submap_spec_1.
Qed.

(** *** Proof of preservation of typing through the substitution

  **** Hypothesis

  Knowing the context is valid regards of its own new key (1),
  the term t is well typed according to a certain context Re (2) and
  the substitute is well typed according to a certain context Re (3);

  **** Result

  We can state that the term t where x is replaced with v is well typed
  according to Re (modulo a shift). 
*)
Corollary subst_preserves_typing : forall Γ Re t v τ τ' x,
  (* (1) *) Re⁺ᵣᵪ ⊩ᵣᵪ Re -> 
  (* (2) *) ⌈x ⤆ τ'⌉ᵥᵪ Γ ⋅ Re ⊫ t ∈ τ -> 
  (* (3) *) ∅ᵥᵪ ⋅ Re ⊫ v ∈ τ' -> 

  Γ ⋅ Re ⊫ ([x := v ~  {Re⁺ᵣᵪ}] t) ∈ τ.
Proof.
  intros; replace 0 with (Re⁺ᵣᵪ - Re⁺ᵣᵪ) by lia. 
  apply subst_preserves_typing_gen with (τ' := τ'); try assumption.
  apply RContext.Submap_refl.
Qed.

(** ** Proof of preservation of typing through the evaluation transition

  **** Hypothesis

  Knowing the context is valid regards of its own new key (1),
  the term t is well typed according to a certain context Re (2), 
  there is a certain t' that is the result of t after one step of transition (3);

  **** Result

  We can state that the term t' is well typed. 
*)
Theorem evaluate_preserves_typing : forall Re t t' τ,
  (* (1) *) Re⁺ᵣᵪ ⊩ᵣᵪ Re ->
  (* (2) *) ∅ᵥᵪ ⋅ Re ⊫ t ∈ τ -> 
  (* (3) *) Re⁺ᵣᵪ ⊨ t ⟼ t' -> 

  ∅ᵥᵪ ⋅ Re ⊫ t' ∈ τ.
Proof. 
  intros Re t t' τ HvRe Hwt; generalize dependent t'; dependent induction Hwt; intros t' HeTt;
  inversion HeTt; subst; try (econstructor; now eauto); eauto.
  - inversion Hwt1; subst. eapply subst_preserves_typing; eauto.
  - inversion Hwt2; subst; inversion Hwt1.
  - inversion Hwt; subst; auto.
  - inversion Hwt; subst; auto.
  - inversion Hwt; subst. eapply subst_preserves_typing; eauto. constructor; eauto.
  - econstructor; eauto. apply IHHwt2; auto.
    -- rewrite RContext.new_key_wh_spec; apply RContext.valid_wh_spec; auto;
        unfold Typ.PairTyp.valid; simpl; split; try (constructor);
        apply well_typed_implies_valid in Hwt1 as [_ Hvτ]; auto; apply VContext.valid_empty_spec.
    -- now rewrite RContext.new_key_wh_spec.
Qed.

(** ** Proof of preservation of typing through multiple evaluation transitions

  **** Hypothesis

  Knowing the context is valid regards of its own new key (1),
  the term t is well typed according to a certain context Re (2), 
  there is a certain t' that is the result of t after zero or k steps of transition (3);

  **** Result

  We can state that the term t' is well typed. 
*)
Theorem multi_preserves_typing : forall Re t t' τ,
  (* (1) *) Re⁺ᵣᵪ ⊩ᵣᵪ Re ->
  (* (2) *) ∅ᵥᵪ ⋅ Re ⊫ t ∈ τ -> 
  (* (3) *) Re⁺ᵣᵪ ⊨ t ⟼⋆ t' -> 
  
  ∅ᵥᵪ ⋅ Re ⊫ t' ∈ τ.
Proof.
  intros Re t t' τ HvRe Hwt HmeT; dependent induction HmeT; subst; try assumption.
  apply IHHmeT; auto. eapply (evaluate_preserves_typing Re x y τ HvRe Hwt H).
Qed.