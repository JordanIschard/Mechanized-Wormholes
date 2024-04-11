From Coq Require Import Lia Arith.PeanoNat Lists.List Program.
Require Import Resource Resources Term Var Typing VContext RContext Typ.

(** * Substitution *)

(** *** Definition *)

Reserved Notation "'[' x ':=' v ']' t" (in custom rsf at level 66, 
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
  where "'[' x ':=' v ']' t" := (subst x v t) (in custom rsf)
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
  - inversion HFV; subst; contradiction.
  - inversion HFV; subst. auto.
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

(** *** General proof of preservation of typing through the substitution *)
Theorem subst_preserves_typing : forall Γ Re Re' t v τ τ' x,
  ⌈x ⤆ τ'⌉ᵥᵪ Γ ⋅ Re ⊫ t ∈ τ -> 
  ∅ᵥᵪ ⋅ Re' ⊫ v ∈ τ' ->
  Re' ⊆ᵣᵪ Re ->

  Γ ⋅ Re ⊫ [x := v] t ∈ τ.
Proof.
  intros Γ Re Re' t; revert Γ Re Re'; induction t;
  intros Γ Re Re' v' α β x wt Hwv Hsub; inversion wt; subst;
  try (econstructor; now eauto).
  - simpl; destruct (Var.eqb_spec x v); subst.
    -- rewrite VContext.OP.P.add_eq_o in H2; inversion H2; subst; clear H2; auto.
       apply weakening_Γ_empty. apply weakening_ℜ with (Re := Re'); auto.
    -- constructor; rewrite VContext.OP.P.add_neq_o in H2; assumption.
  - simpl; destruct (Var.eqb_spec x v); subst.
    -- constructor; auto. now rewrite VContext.add_shadow in H5.
    -- constructor; auto. rewrite VContext.OP.P.add_add_2 in H5; auto.
       eapply IHt; eauto.
Qed.