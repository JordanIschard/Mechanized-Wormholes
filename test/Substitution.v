From Coq Require Import Lia Arith.PeanoNat Lists.List Program.
From Mecha Require Import Resource Resources Term Var Typing VContext RContext Typ.

(** * Substitution *)

(** *** Definition *)

Reserved Notation "'[' x ':=' v '~' lb '≤' k ']' t" (in custom wormholes at level 66, 
                                                                  right associativity).

(** **** Substitution function 

  The substitution function works as well as the classic one with extra information.
  Indeed, when we go through the term searching compatible variables, we can go through
  a [wormhole] term. However the wormhole term does not have the same level inside. In fact
  it has the level outside increment by 2. Then we add extra information:
  - the current level of the substitute [lb] and
  - the shift between the level of the substitute [v] and the current term.

  Thus, when we find a compatible variable we substitute it by the term [v] after
  having perfomed a shift.

*)
Fixpoint subst (lb : nat) (k : nat) (x : Var.t) (v t : Λ) : Λ :=
  match t with
    | Term.tm_var y => if (x =? y)%v then <[[⧐ₜₘ lb ≤ k] v]> else t 
    | <[t1 t2]> => <[([x := v ~ lb ≤ k]t1) ([x := v ~ lb ≤ k]t2)]>
    | <[\y:τ,t0]> => if (x =? y)%v then t else <[\y:τ,[x := v ~ lb ≤ k]t0]>

    | <[⟨t1,t2⟩]> => <[⟨([x := v ~ lb ≤ k]t1),([x := v ~ lb ≤ k]t2)⟩]>
    | <[t0.fst]> => <[([x := v ~ lb ≤ k]t0).fst]>
    | <[t0.snd]> => <[([x := v ~ lb ≤ k]t0).snd]>

    | <[arr(t0)]> => <[arr([x := v ~ lb ≤ k]t0)]>
    | <[first(τ:t0)]> => <[first(τ:[x := v ~ lb ≤ k]t0)]>
    | <[t1 >>> t2]> => <[([x := v ~ lb ≤ k]t1) >>> ([x := v ~ lb ≤ k]t2)]>

    | <[wormhole(t1;t2)]> => <[wormhole([x := v ~ lb ≤ k] t1;[x := v ~ lb ≤ {S (S k)}] t2)]>

    | _ => t
  end
  where "'[' x ':=' v '~' lb '≤' k ']' t" := (subst lb k x v t) (in custom wormholes)
.

Notation "'[' x ':=' v '~' lb ']' t" := (subst lb 0 x v t) (in custom wormholes at level 66, 
                                                                  right associativity).

(** **** Example

  Suppose the following Womhole's terms:
<<
(1) wormhole[rr,rw](i'; rsf[rr] >>> x)
(2) wormhole[rr1,rw1](i; rsf[rr1])
>>

  Translated in the De Bruijn level representation we have:
<<
(1) wormhole(i'; rsf[0] >>> x)
(2) wormhole(i; rsf[0])
>>

  If we substitute x by (2) in (1) with the classic substitution we have the following result:
<<
  [x := (2)] wormhole(i'; rsf[0] >>> x)
= wormhole([x := (2)] i'; [x := (2)] (rsf[0] >>> x))
= wormhole([x := (2)] i'; [x := (2)] rsf[0] >>> [x := (2)] x)
= wormhole([x := (2)] i'; rsf[0] >>> wormhole(i; rsf[0]))
>>

  If we do the opposite translation we expect:
<<
wormhole[rr,rw](i'; rsf[rr] >>> wormhole[rr1,rw1](i; rsf[rr1]))
>>

  but found:
<<
wormhole[rr,rw](i'; rsf[rr] >>> wormhole[rr1,rw1](i; rsf[rr]))
>>

  With our substitution the result is the expected one, as we can see below.

<<
  [x := (1) ~ 0 ≤ 0] wormhole(i'; rsf[0] >>> x)
= wormhole([x := (1) ~ 0 ≤ 0] i'; [x := (1) ~ 0 ≤ 2] (rsf[0] >>> x))
= wormhole([x := (1) ~ 0 ≤ 0] i'; [x := (1) ~ 0 ≤ 2] rsf[0] >>> [x := (1) ~ 0 ≤ 2] x)
= wormhole([x := (1) ~ 0 ≤ 0] i'; rsf[0] >>> [>> 0 ≤ 2] wormhole(i; rsf[0]))
= wormhole([x := (1) ~ 0 ≤ 0] i'; rsf[0] >>> wormhole([>> 0 ≤ 2] i; [>> 0 ≤ 2] rsf[0]))
= wormhole([x := (1) ~ 0 ≤ 0] i'; rsf[0] >>> wormhole([>> 0 ≤ 2] i; rsf[2]))
>>
*)

(** *** Substitution regards of variables *)

Lemma subst_afi_refl : forall t x lb k,
  ~ isFV(x,t) -> forall v, <[ [x:= v ~ lb ≤ k] t ]> = t.
Proof with eauto.
  intros t; induction t; unfold not; intros x lb k afi v1; try (now simpl);
  try (simpl; f_equal; now eauto).
  - simpl. destruct (Var.eqb_spec x v); subst; auto; exfalso; apply afi; constructor.
  - simpl; destruct (Var.eqb_spec x v); subst; auto.
    f_equal; apply IHt; unfold not; intros; apply afi; now constructor.
Qed.

Lemma subst_closed_refl : forall t lb k,
  clₜₘ(t) -> forall x t', <[ [x := t' ~ lb ≤ k] t ]> = t.
Proof. intros. apply subst_afi_refl. apply H. Qed.

Lemma subst_refl : forall v (x : variable) lb, <[[x := v ~ lb ≤ 0] x]> = v.
Proof. intros v x lb; simpl; rewrite Var.eqb_refl; now apply Term.shift_refl. Qed.

Lemma closed_subst_not_afi : forall t x v lb k,
  clₜₘ(v) ->  ~ isFV(x,<[ [x := v ~ lb ≤ k] t ]>).
Proof.
  unfold Term.closed, not; intro t; induction t; intros x v1 lb k Hcl HFV; simpl;
  try (inversion HFV; subst; now eauto); simpl in *;
  try (destruct (Var.eqb_spec x v); subst; eauto).
  - apply (Hcl v). rewrite Term.shift_afi_iff; eauto.
  - inversion HFV; auto.
  - inversion HFV; subst; eauto.
  - inversion HFV; subst; eauto.
Qed.

Lemma subst_shadow : forall t' x t v lb k,
  clₜₘ(v) -> <[[x := t ~ lb ≤ k] ([ x := v ~ lb ≤ k] t')]> = <[ [x := v ~ lb ≤ k] t' ]>.
Proof. intros; eapply subst_afi_refl; apply closed_subst_not_afi; assumption. Qed.

Lemma subst_permute : forall t x x1 v v1 lb k,
  x <> x1 -> clₜₘ(v) -> clₜₘ(v1) ->
  <[[x1 := v1 ~ lb ≤ k] ([ x := v ~ lb ≤ k] t)]> = <[[x := v ~ lb ≤ k] ([ x1 := v1 ~ lb ≤ k] t)]>.
Proof.
  intro t; induction t; intros; simpl; try (now reflexivity); try (f_equal; now auto).
  - (* var *)
    destruct (Var.eqb_spec x v); destruct (Var.eqb_spec x1 v); subst; simpl.
    -- now contradiction H.
    -- rewrite Var.eqb_refl; rewrite subst_closed_refl; auto; now rewrite <- Term.shift_closed_iff.
    -- rewrite Var.eqb_refl; rewrite subst_closed_refl; auto; now rewrite <- Term.shift_closed_iff.
    -- rewrite <- Var.eqb_neq in *; rewrite n; now rewrite n0.
  - destruct (Var.eqb_spec x v); destruct (Var.eqb_spec x1 v); subst; simpl.
    -- now contradiction H.
    -- rewrite Var.eqb_refl; rewrite <- Var.eqb_neq in n; now rewrite n.
    -- rewrite Var.eqb_refl; rewrite <- Var.eqb_neq in n; now rewrite n.
    -- rewrite <- Var.eqb_neq in n,n0; rewrite n,n0; f_equal; now apply IHt.
Qed.

(** *** Substitution modulo shift function *)

Lemma subst_shift_spec : forall lb k k' t x v,
  <[[⧐ₜₘ lb ≤ k] ([x := v ~ lb ≤ k'] t)]> = 
  <[[x := ([⧐ₜₘ lb ≤ k] v) ~ lb ≤ k'] ([⧐ₜₘ lb ≤ k] t)]>.
Proof.
  intros lb k k' t; revert lb k k'; induction t; intros lb k k' x v1; simpl;
  f_equal; eauto.
  - destruct (Var.eqb_spec x v); subst.
    -- apply Term.shift_permute.
    -- now simpl.
  - destruct (Var.eqb x v); simpl; try reflexivity; f_equal; auto.
Qed.

Lemma subst_shift_spec_1 : forall lb k k' t x v,
  <[[⧐ₜₘ lb ≤ k] ([x := v ~ lb ≤ k'] t)]> = 
  <[[x := ([⧐ₜₘ lb ≤ k] v) ~ {lb + k} ≤ k'] ([⧐ₜₘ lb ≤ k] t)]>.
Proof.
  intros lb k k' t; revert lb k k'; induction t; intros lb k k' x v1; simpl;
  f_equal; eauto.
  - destruct (Var.eqb_spec x v); subst.
    -- apply Term.shift_permute_1.
    -- now simpl.
  - destruct (Var.eqb x v); simpl; try reflexivity; f_equal; auto.
Qed.

Lemma subst_shift_spec_2 : forall lb lb' k k' t x v,
  lb <= lb' ->
  <[[⧐ₜₘ lb ≤ k] ([x := v ~ lb' ≤ k'] t)]> = 
  <[[x := ([⧐ₜₘ lb ≤ k] v) ~ {lb' + k} ≤ k'] ([⧐ₜₘ lb ≤ k] t)]>.
Proof.
  intros lb lb' k k' t; revert lb lb' k k'; induction t; intros lb lb' k k' x v1 Hle; simpl;
  f_equal; eauto.
  - destruct (Var.eqb_spec x v); simpl; try reflexivity.
    now apply Term.shift_permute_2.
  - destruct (Var.eqb_spec x v); simpl; f_equal; auto.
Qed.

(** *** Valid through substitution *)

Lemma subst_preserves_valid : forall k k' v x t,
  k >= k' -> k ⊩ₜₘ t -> k' ⊩ₜₘ v -> k ⊩ₜₘ <[[x := v ~ k' ≤ {k - k'}] t]>.
Proof.
  intros k k' v x t; revert k k'; induction t; intros k k' Hle Hvt Hvv; auto;
  try (unfold Term.valid in *; inversion Hvt; subst; constructor; now eauto).
  - simpl; destruct (Var.eqb_spec x v0); subst; auto.
    replace (k ⊩ₜₘ <[ [⧐ₜₘ k' ≤ {k - k'}] v ]>) 
    with ((k' + (k - k')) ⊩ₜₘ <[ [⧐ₜₘ k' ≤ {k - k'}] v ]>).
    -- now apply Term.shift_preserves_valid.
    -- f_equal; lia.
  - unfold Term.valid in *; inversion Hvt; subst; simpl. 
    destruct (Var.eqb_spec x v0); subst; auto; constructor; auto.
  - unfold Term.valid in *; inversion Hvt; subst; simpl; constructor;
    auto. replace (S (S (k - k'))) with ((S (S k)) - k'); try lia. apply IHt2; auto.
Qed.

Lemma subst_preserves_valid_4 : forall k x v t,
  k ⊩ₜₘ t ->  k ⊩ₜₘ v -> k ⊩ₜₘ <[[x := v ~ k] t]>.
Proof.
  intros k x v t Hvt; replace 0 with (k - k) by lia; apply subst_preserves_valid;
  try assumption; lia.
Qed.

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
    -- replace (S (S (newᵣᵪ( Re) - Re1⁺ᵣᵪ))) with ((S (S (newᵣᵪ( Re)))) - Re1⁺ᵣᵪ).
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

  Γ ⋅ Re ⊫ ([x := v ~  {Re⁺ᵣᵪ}] t) ∈ τ.
Proof.
  intros; replace 0 with (Re⁺ᵣᵪ - Re⁺ᵣᵪ) by lia. 
  apply subst_preserves_typing_gen with (τ' := τ'); try assumption.
  apply RContext.Submap_refl.
Qed.