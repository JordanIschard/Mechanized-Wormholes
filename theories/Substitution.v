From Coq Require Import Lia Arith.PeanoNat Lists.List Program.
Require Import Term Typ Var Typing Context.

(** * Substitution *)

(** *** Definition *)

Reserved Notation "'[' x ':=' v ']' t" (in custom arrow at level 66, 
                                                                  right associativity).

Fixpoint subst (x : Var.t) (v t : Λ) : Λ :=
  match t with
    | Term.tm_var y => if (x =? y)%v then v else t 
    | <[t1 t2]> => <[([x := v]t1) ([x := v]t2)]>
    | <[\y:τ,t0]> => if (x =? y)%v then t else <[\y:τ,[x := v]t0]>

    | <[⟨t1,t2⟩]> => <[⟨([x := v]t1),([x := v]t2)⟩]>
    | <[t0.fst]> => <[([x := v]t0).fst]>
    | <[t0.snd]> => <[([x := v]t0).snd]>

    | <[arr(t0)]> => <[arr([x := v]t0)]>
    | <[first(τ:t0)]> => <[first(τ:[x := v]t0)]>
    | <[t1 >>> t2]> => <[([x := v]t1) >>> ([x := v]t2)]>

    | _ => t
  end
  where "'[' x ':=' v ']' t" := (subst x v t) (in custom arrow)
.

(** *** Substitution regards of variables *)

Lemma subst_afi_refl : forall t x,
  ~ isFV(x,t) -> forall v, <[ [x:= v] t ]> = t.
Proof with eauto.
  intros t; induction t; unfold not; intros x afi v1; try (now simpl);
  try (simpl; f_equal; now eauto).
  - simpl. destruct (Var.eqb_spec x v); subst; auto; exfalso; apply afi; constructor.
  - simpl; destruct (Var.eqb_spec x v); subst; auto.
    f_equal; apply IHt; unfold not; intros; apply afi; now constructor.
Qed.

Lemma subst_closed_refl : forall t,
  clₜₘ(t) -> forall x t', <[ [x := t'] t ]> = t.
Proof. intros. apply subst_afi_refl. apply H. Qed.

Lemma closed_subst_not_afi : forall t x v,
  clₜₘ(v) ->  ~ isFV(x,<[ [x := v] t ]>).
Proof.
  unfold Term.closed, not; intro t; induction t; intros x v1 Hcl HFV; simpl;
  try (inversion HFV; subst; now eauto); simpl in *;
  try (destruct (Var.eqb_spec x v); subst; eauto).
  - inversion HFV; auto.
  - inversion HFV; subst; eauto.
  - inversion HFV; subst; eauto.
Qed.

Lemma subst_shadow : forall t' x t v,
  clₜₘ(v) -> <[[x := t] ([ x := v] t')]> = <[ [x := v] t' ]>.
Proof. intros; eapply subst_afi_refl; apply closed_subst_not_afi; assumption. Qed.

Lemma subst_permute : forall t x x1 v v1,
  x <> x1 -> clₜₘ(v) -> clₜₘ(v1) ->
  <[[x1 := v1] ([ x := v] t)]> = <[[x := v] ([ x1 := v1] t)]>.
Proof.
  intro t; induction t; intros; simpl; try (now reflexivity); try (f_equal; now auto).
  - (* var *)
    destruct (Var.eqb_spec x v); destruct (Var.eqb_spec x1 v); subst; simpl.
    -- now contradiction H.
    -- rewrite Var.eqb_refl; rewrite subst_closed_refl; auto.
    -- rewrite Var.eqb_refl; rewrite subst_closed_refl; auto.
    -- rewrite <- Var.eqb_neq in *; rewrite n; now rewrite n0.
  - destruct (Var.eqb_spec x v); destruct (Var.eqb_spec x1 v); subst; simpl.
    -- now contradiction H.
    -- rewrite Var.eqb_refl; rewrite <- Var.eqb_neq in n; now rewrite n.
    -- rewrite Var.eqb_refl; rewrite <- Var.eqb_neq in n; now rewrite n.
    -- rewrite <- Var.eqb_neq in n,n0; rewrite n,n0; f_equal; now apply IHt.
Qed.

(** *** Proof of preservation of typing through the substitution

  **** Hypothesis

  Knowing that the term t is well typed according to a certain context Γ (1), 
  the substitute is well typed according to Γ (2)

  **** Result

  We can state that the term t where x is replaced with v is well typed
  according to Γ. 
*)
Theorem subst_preserves_typing : forall Γ t v τ τ' x,
  (* (1) *) ⌈x ⤆ τ'⌉ᵧ Γ ⊫ t ∈ τ -> 
  (* (2) *) ∅ᵧ ⊫ v ∈ τ' ->

  Γ ⊫ ([x := v] t) ∈ τ.
Proof.
  intros Γ t v τ τ' x wt. revert v. dependent induction wt; intros v; auto;
  try (econstructor; now eauto).
  - simpl; destruct (Var.eqb_spec x x0); subst.
    -- rewrite Context.OP.P.add_eq_o in H; inversion H; subst; clear H; auto.
       apply weakening_Γ_empty.
    -- constructor; rewrite Context.OP.P.add_neq_o in H; assumption.
  - simpl; destruct (Var.eqb_spec x x0); subst.
    -- constructor; auto. now rewrite Context.add_shadow in wt.
    -- constructor; auto. apply Context.OP.P.add_add_2 in n.
Qed.
(** *** General proof of preservation of typing through the substitution

  **** Hypothesis

  Knowing the context is valid regards of its own new key (1),
  the term t is well typed according to a certain context Re (2), 
  the substitute is well typed according to a certain context Re' (3) and
  Re is a submap of Re' (4);

  **** Result

  We can state that the term t where x is replaced with v is well typed
  according to Re (modulo a shift). 
*)
Theorem subst_preserves_typing_gen : forall Γ Re Re' t v τ τ' x,
  (* (1) *) newᵣᵪ( Re') ⊩ᵣᵪ Re' -> 
  (* (2) *) ⌈x ⤆ τ'⌉ᵥᵪ Γ ⋅ Re ⊫ t ∈ τ -> 
  (* (3) *) ∅ᵥᵪ ⋅ Re' ⊫ v ∈ τ' ->
  (* (4) *) Re' ⊆ᵣᵪ Re ->

  Γ ⋅ Re ⊫ ([x := v ~  {newᵣᵪ(Re')} ≤ {newᵣᵪ(Re) - newᵣᵪ(Re')}] t) ∈ τ.
Proof.
  intros Γ Re Re' t; revert Γ Re Re'; induction t;
  intros Γ Re Re' v' α β x HvRₑ wt Hwv Hsub; inversion wt; subst;
  try (econstructor; now eauto).
  - simpl; destruct (Var.eqb_spec x v); subst.
    -- rewrite VContext.add_eq_o in H2; inversion H2; subst; clear H2; auto.
       apply weakening_Γ_empty. apply weakening_ℜ_1; auto.
       apply VContext.valid_empty_spec. 
    -- constructor; rewrite VContext.add_neq_o in H2; assumption.
  - simpl; destruct (Var.eqb_spec x v); subst.
    -- constructor; auto. now rewrite VContext.add_shadow in H5.
    -- constructor; auto. rewrite VContext.add_add_2 in H5; auto.
       eapply IHt; eauto.
  - econstructor; eauto; fold subst.
    eapply IHt2 in Hwv; eauto.
    -- replace (S (S (newᵣᵪ( Re) - newᵣᵪ( Re')))) with ((S (S (newᵣᵪ( Re)))) - newᵣᵪ( Re')).
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
  (* (1) *) newᵣᵪ( Re) ⊩ᵣᵪ Re -> 
  (* (2) *) ⌈x ⤆ τ'⌉ᵥᵪ Γ ⋅ Re ⊫ t ∈ τ -> 
  (* (3) *) ∅ᵥᵪ ⋅ Re ⊫ v ∈ τ' -> 

  Γ ⋅ Re ⊫ ([x := v ~  {newᵣᵪ(Re)} ≤ 0] t) ∈ τ.
Proof.
  intros; replace 0 with (newᵣᵪ(Re) - newᵣᵪ(Re)) by lia. 
  apply subst_preserves_typing_gen with (τ' := τ'); try assumption.
  apply RContext.Submap_refl.
Qed.