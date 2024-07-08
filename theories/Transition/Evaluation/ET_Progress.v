From Coq Require Import Lia.
From Mecha Require Import Typ Resource Term Var VContext RContext Typing ET_Definition.
Import ResourceNotations TypNotations TermNotations VContextNotations RContextNotations.

Open Scope term_scope.
Open Scope rcontext_scope.

(** * Transition - Evaluation - Progress *)

(** ** Proof of progress of the evaluation transtion

  If the term is well typed then 
  - either we have a value (1) or 
  - we can evaluate at least one time the term (2).

*)
Theorem progress_of_evaluate : forall t Re τ,
                      (∅)%vc ⋅ Re ⊫ t ∈ τ -> 
(*-------------------------------------------------------------------*)
     (* (1) *) value(t) \/ (* (2) *) exists t', Re⁺ ⊨ t ⟼ t'.
Proof.
  intro t; induction t; intros Re τ' Hwt; inversion Hwt; subst; 
  try (now left); try (apply IHt1 in H3 as H3'; apply IHt2 in H5 as H5').
  - destruct H3',H5'; right. 
    -- inversion H; subst; inversion H3; subst. exists <[[x:= t2 ~ {Re⁺} – 0] t]>.
      now constructor.
    -- destruct H0; exists <[t1 x]>; now constructor.
    -- destruct H; exists <[x t2]>; now constructor.
    -- destruct H; exists <[x t2]>; now constructor.
  - right; apply IHt2 in H4 as H4'; destruct H4'.
    -- destruct t2; inversion H4; subst; inversion H; subst.
        exists <[[v := Fix (\ v : τ', t2) ~ {Re⁺} – 0] t2]>; constructor.
    -- destruct H; exists <[Fix x]>; constructor; auto.
  - destruct H3',H5'; auto.
    -- right; destruct H0; exists <[⟨t1,x⟩]>; now constructor.
    -- right; destruct H; exists <[⟨x,t2⟩]>; now constructor.
    -- right; destruct H; exists <[⟨x,t2⟩]>; now constructor.
  - apply IHt in H2 as H2'; destruct H2'; right.
    -- inversion H; subst; inversion H2; subst; exists v1; now constructor. 
    -- destruct H; exists (Term.tm_fst x); now constructor.
  - apply IHt in H2 as H2'; destruct H2'; right.
    -- inversion H; subst; inversion H2; subst; exists v2; now constructor. 
    -- destruct H; exists (Term.tm_snd x); now constructor.
  - apply IHt in H2 as H2'; destruct H2' as [Hvt | [t' HeT']]; 
    try (left; now constructor); right; exists <[arr(t')]>; now constructor.
  - apply IHt in H3 as H3'; destruct H3' as [Hvt | [t' HeT']]; 
    try (left; now constructor); right; exists <[first(τ:t')]>; now constructor.
  - apply IHt1 in H1 as H1'; apply IHt2 in H5 as H5';
    destruct H1' as [Hvt1 | [t1' HeT1']]; destruct H5' as [Hvt2 | [t2' HeT2']];
    try (left; now constructor); right.
    -- exists <[t1 >>> t2']>; now constructor.
    -- exists <[t1' >>> t2]>; now constructor.
    -- exists <[t1' >>> t2]>; now constructor.
  - apply IHt1 in H1 as H1'; apply IHt2 in H8 as H8';
    destruct H1' as [Hvt1 | [t1' HeT1']]; destruct H8' as [Hvt2 | [t2' HeT2']];
    try (left; now constructor); right.
    -- exists <[wormhole(t1;t2')]>; constructor; auto.
        unfold k in HeT2'; rewrite RContext.new_key_wh_spec in HeT2'; auto.
    -- exists <[wormhole(t1';t2)]>; now constructor.
    -- exists <[wormhole(t1';t2)]>; now constructor.
Qed.