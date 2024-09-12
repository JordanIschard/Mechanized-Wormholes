From Coq Require Import Lia Program.
From Mecha Require Import Typ Resource Term Var VContext RContext Typing ET_Definition.
Import VarNotations ResourceNotations TermNotations 
       TypNotations VContextNotations RContextNotations.

Open Scope term_scope.
Open Scope rcontext_scope.

(** * Transition - Evaluation - Preservation *)

Hint Resolve VContext.valid_empty_spec : core.

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
Theorem subst_preserves_typing_gen (Γ : Γ) (Re Re1 : ℜ) (t v : Λ) (τ τ' : Τ) (x : variable) :

    (* (1) *) (Re1⁺ ⊩ Re1)%rc -> (* (2) *) (⌈x ⤆ τ'⌉ Γ)%vc ⋅ Re ⊫ t ∈ τ -> 
    (* (3) *) (∅)%vc ⋅ Re1 ⊫ v ∈ τ' -> (* (4) *) Re1 ⊆ Re ->
(*-----------------------------------------------------------------------------*)
            Γ ⋅ Re ⊫ ([x := v ~  {Re1⁺} – {Re⁺ - Re1⁺}] t) ∈ τ.
Proof.
  revert Γ Re Re1 v τ τ' x. 
  induction t; intros Γ Re Re1 v' α β x HvRₑ wt Hwv Hsub; 
  inversion wt; subst; simpl; try (econstructor; now eauto).
  (* variable *)
  -
    (* clean *) rename H2 into HfΓ. (* clean *)

    destruct (Var.eqb_spec x v); subst.
    -- rewrite VContext.add_eq_o in HfΓ; auto. 
       inversion HfΓ; subst; clear HfΓ.
       apply weakening_Γ_empty.
       apply weakening_ℜ; auto.
    -- rewrite VContext.add_neq_o in HfΓ; auto. 
  (* abstraction *)
  - destruct (Var.eqb_spec x v); subst; constructor; auto.
    -- now rewrite VContext.add_shadow in H5.
    -- rewrite VContext.add_add_2 in H5; auto.
       apply (IHt _ _ _ _ _ β x HvRₑ H5 Hwv Hsub).
  (* wormhole *)
  - unfold k in *. 
    apply (wt_wh _ _ _ R' _ _ _ _ τ); auto.
    -- apply (IHt1 _ _ _ _ _ β _ HvRₑ H1 Hwv Hsub).
    -- apply RContext.Ext.new_key_Submap_spec in Hsub as Hle.
       replace (S (S (Re⁺ - Re1⁺))) with ((S (S (Re⁺))) - Re1⁺) by lia.
       eapply IHt2 in Hwv; eauto.
       + erewrite <- RContext.new_key_wh_spec; eauto.
       + now apply RContext.Ext.new_key_Submap_add_spec.
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

    (* (1) *) (Re⁺ ⊩ Re)%rc -> 
    (* (2) *) (⌈x ⤆ τ'⌉ Γ)%vc ⋅ Re ⊫ t ∈ τ -> (* (3) *) (∅)%vc ⋅ Re ⊫ v ∈ τ' -> 
(*-----------------------------------------------------------------------------------*)
                    Γ ⋅ Re ⊫ ([x := v ~  {Re⁺}] t) ∈ τ.
Proof.
  intros; replace 0 with (Re⁺ - Re⁺) by lia. 
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

    (* (1) *) (Re⁺ ⊩ Re)%rc -> 
    (* (2) *) (∅)%vc ⋅ Re ⊫ t ∈ τ -> (* (3) *) Re⁺ ⊨ t ⟼ t' -> 
(*-----------------------------------------------------------------*)
                    (∅)%vc ⋅ Re ⊫ t' ∈ τ.
Proof. 
  intros Re t t' τ HvRe Hwt; generalize dependent t'; dependent induction Hwt; intros t' HeTt;
  inversion HeTt; subst; try (econstructor; now eauto); eauto.
  - inversion Hwt1; subst. eapply subst_preserves_typing; eauto.
  - inversion Hwt2; subst; inversion Hwt1.
  - inversion Hwt; subst; auto.
  - inversion Hwt; subst; auto.
  - inversion Hwt; subst. 
    apply (subst_preserves_typing _ _ _ _ _ τ _ HvRe H3).
    now constructor.
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

    (* (1) *) (Re⁺ ⊩ Re)%rc ->
    (* (2) *) (∅)%vc ⋅ Re ⊫ t ∈ τ -> (* (3) *) Re⁺ ⊨ t ⟼⋆ t' -> 
(*-----------------------------------------------------------------*)
                        (∅)%vc ⋅ Re ⊫ t' ∈ τ.
Proof.
  intros Re t t' τ HvRe Hwt HmeT; dependent induction HmeT; subst; try assumption.
  apply IHHmeT; auto. 
  apply (evaluate_preserves_typing Re x y τ HvRe Hwt H).
Qed.