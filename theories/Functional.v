From Coq Require Import Program Lia Relations.Relation_Definitions Classes.RelationClasses 
                        Classical_Prop Classical_Pred_Type Bool.Bool Classes.Morphisms.
Require Import Typ Term Var Substitution Evaluation Typing Context.

(** * Transition - Functional

Wormholes's semantics are divided in three sub semantics:
- evaluation transition
- functional transition <--
- temporal transition

*)

Module C := Context.

(** *** Definition *)

Reserved Notation "⪡ st ; t ⪢ ⭆ ⪡ st1 ; t1 ⪢" (at level 57, st custom arrow,
                                                              st1 custom arrow,
                                                              t custom arrow, 
                                                              t1 custom arrow, 
                                                                no associativity).

Inductive functional : Λ -> Λ -> Λ -> Λ -> Prop :=

  | fT_eT    :  forall (st st' t t' t'' : Λ),

        ⊨ t ⟼ t' -> ⪡ st ; t' ⪢ ⭆ ⪡ st' ; t'' ⪢ -> 
    (*---------------------------------------------------*)
             ⪡ st ; t ⪢ ⭆ ⪡ st' ; t'' ⪢

  | fT_arr   :  forall (st t : Λ), 

                value(<[arr(t)]>) ->
    (*-------------------------------------------*)
        ⪡ st ; arr(t) ⪢ ⭆ ⪡ (t st) ; arr(t) ⪢ 

  | fT_first :  forall (st v1 v1' v2 t t' : Λ) (τ : Τ),

                    value(<[first(τ:t)]>) ->
        ⊨ st ⟼⋆ ⟨v1,v2⟩ -> ⪡ v1 ; t ⪢ ⭆ ⪡ v1' ; t' ⪢ ->
    (*-------------------------------------------------------*)
        ⪡ st ; first(τ:t) ⪢ ⭆ ⪡ ⟨v1', v2⟩ ; first(τ:t') ⪢

  | fT_comp  :  forall (st st' st'' t1 t1' t2 t2' : Λ),

                            value(<[t1 >>> t2]>) -> 
        ⪡ st ; t1 ⪢ ⭆ ⪡ st' ; t1' ⪢ -> ⪡ st' ; t2 ⪢ ⭆ ⪡ st'' ; t2' ⪢ ->
    (*----------------------------------------------------------------------*)
                ⪡ st ; (t1 >>> t2) ⪢ ⭆ ⪡ st'' ; (t1' >>> t2') ⪢

where "⪡ st ; t ⪢ ⭆ ⪡ st1 ; t1 ⪢" := (functional st t st1 t1)
.

(** ** Preservation *)


(**
  *** General proof of preservation of typing through functional transition

*)
Theorem functional_preserves_typing : 
  forall (sv sv' sf sf' : Λ) (α β : Τ),

    (* (1) *) ∅ᵧ ⊫ sf ∈ (α ⟿ β) ->
    (* (2) *) ∅ᵧ ⊫ sv ∈ α -> 
    (* (3) *) ⪡ sv ; sf ⪢ ⭆ ⪡ sv' ; sf' ⪢ -> 


    ∅ᵧ ⊫ sv' ∈ β /\ ∅ᵧ ⊫ sf' ∈ (α ⟿ β).
Proof.
  intros sv sv' sf sf' α β Hwsf Hwsv fT; revert α β Hwsf Hwsv;
  induction fT; intros α β Hwsf Hwsv.
  (* fT_eT *)
  - 
    (* clean *)
    move α before t''; move β before α; move fT after IHfT; 
    rename fT into HfT; rename H into HeT; move HeT after HfT.
    (* clean *)

    apply evaluate_preserves_typing with (t' := t') in Hwsf as Hwsf'; auto.
  (* fT_arr *)
  - 
    (* clean *)
    inversion Hwsf; subst; rename H3 into Hwt; clear Hwsf H; move Hwt after Hwsv.
    (* clean *)

    split. 
    -- now apply wt_app with (τ2 := α).
    -- now constructor.
  (* fT_first *)
  -
    (* clean *)
    clear H; inversion Hwsf; subst. move τ1 before τ; move τ2 before τ1;
    clear Hwsf; rename H2 into Hwt; move Hwt after Hwsv; rename H0 into HmeT; 
    rename fT into HfT; move HfT after IHfT; move HmeT after HfT.
    (* clean *)

    apply multi_preserves_typing with (t' := <[⟨v1,v2⟩]>) in Hwsv; auto.

    (* clean *)
    inversion Hwsv; subst; rename H3 into Hwv1; rename H5 into Hwv2; 
    move Hwv1 before Hwt; move Hwv2 before Hwv1; clear Hwsv.
    (* clean *)

    apply IHfT with (β := τ2) in Hwv1 as IH; auto.

    clear IHfT; destruct IH as [Hwv1' Hwt'].

    (* clean *)
    move Hwv1' before Hwv1; clear Hwv1; move Hwt' before Hwt; clear Hwt.
    (* clean *)

    split.
    -- now constructor.
    -- now constructor.
  (* fT_comp *)
  -
    (* clean *)
    clear H; inversion Hwsf; subst; clear Hwsf;
    move α before t2'; move β before α; move α before β; rename fT1 into HfT1;
    move HfT1 after IHfT2; rename fT2 into HfT2; move HfT2 after HfT1;
    rename H3 into Hwt1; rename H5 into Hwt2; move τ before β.
    (* clean *)

    apply IHfT1 with (β := τ) in Hwsv as IH1; auto.
    clear IHfT1; destruct IH1 as [Hwsv' Hwt1'].

    (* clean *)
    move Hwsv' before Hwsv; move Hwt1' before Hwt1.
    (* clean *)

    apply IHfT2 with (β := β) in Hwsv' as IH2; auto.
    destruct IH2 as [Hwsv'' Hwt2'].

    (* clean *)
    move Hwsv'' before Hwsv'; move Hwt2' before Hwt2; clear IHfT2.
    (* clean *)

    split; auto; now apply wt_comp with τ.
Qed.

(** ** Progress *)

Definition all_arrow_halting := forall t α β,
  ∅ᵧ ⊫ arr(t) ∈ (α ⟿ β) -> forall v, ∅ᵧ ⊫ v ∈ α -> halts <[t v]>.

  
Theorem progress_of_functional_value : forall (sv sf : Λ) (α β : Τ),
    value(sf) ->
    ∅ᵧ ⊫ sf ∈ (α ⟿ β) -> 
    ∅ᵧ ⊫ sv ∈ α ->

    halts sv ->
    all_arrow_halting ->

    exists (sv' sf' : Λ), 
      ⪡ sv ; sf ⪢ ⭆ ⪡ sv' ; sf' ⪢ /\
      halts sv' /\
      halts sf'.
Proof.
  intros sv sf; revert sv; induction sf; intros sv α β Hvsf Hwsf Hwsv Hlt Hlta;
  inversion Hwsf; subst; inversion Hvsf; subst.
  (* wt_arr *)
  - exists <[sf sv]>; exists <[arr(sf)]>; split.
    -- now constructor.
    -- split.
       + unfold all_arrow_halting in Hlta. eapply Hlta; eauto.
       + exists <[arr(sf)]>; split; auto.
  (* wt_first *)
  - destruct Hlt as [sv' [HmeT Hvsv']].
    apply multi_preserves_typing with (t' := sv') in Hwsv as Hwsv'; auto.
    destruct sv'; subst; inversion Hvsv'; subst; inversion Hwsv'; subst.

    apply (IHsf sv'1 τ1 τ2) in H1; auto.
    -- destruct H1 as [sv' [sf'  [fT [Hlt' Hlt'']]]].
       exists <[⟨sv',sv'2⟩]>; exists <[first(τ:sf')]>; repeat split.
       + eapply fT_first; eauto.
       + apply halts_pair; split; auto. exists sv'2. split; auto.
       + destruct Hlt'' as [sf'' [HmeT' Hvsf'']]. exists <[ first(τ : sf'') ]>; split.
         ++ now apply multi_first.
         ++ now constructor.
    -- exists sv'1; split; auto.
  (* wt_comp *)
  - inversion Hvsf; subst. eapply IHsf1 in Hwsv as IH; eauto. 
    destruct IH as [sv' [sf1' [HfT1 [Hlt' Hlt'']]]].
    eapply functional_preserves_typing in HfT1 as IH; eauto.
    destruct IH as [Hwsv' Hwsf1'].
    eapply IHsf2 in Hwsv' as IH; eauto. 
    destruct IH as [sv'' [sf2' [HfT2 [Hlt0' Hlt0'']]]].
    exists sv''; exists <[sf1' >>> sf2']>; split.
    -- eapply fT_comp; eauto.
    -- split; auto. rewrite halts_comp; split; auto.
Qed.

Theorem progress_of_functional : 
  forall (sv sf : Λ) (α β : Τ),
    ∅ᵧ ⊫ sf ∈ (α ⟿ β) -> 
    ∅ᵧ ⊫ sv ∈ α ->

    halts sf ->
    halts sv ->
    all_arrow_halting ->

    exists (sv' sf' : Λ), 
      ⪡ sv ; sf ⪢ ⭆ ⪡ sv' ; sf' ⪢ /\
      halts sv' /\
      halts sf'.
Proof. 
  intros sv sf α β Hwsf Hwsv Hltsf; revert sv α β Hwsf Hwsv; destruct Hltsf as [sf' [HmeT Hvsf]].
  apply multi_indexed in HmeT as [k HieT]; revert sf sf' HieT Hvsf; induction k;
  intros sf sf' HieT Hvsf' sv α β Hwsf Hwsv Hltsv Hlta.
  (* sf is a value *)
  - inversion HieT; subst; clear HieT.
    eapply progress_of_functional_value; eauto.
  (* sf can be reduced at least one time *)
  - inversion HieT; subst.

    (* clean *)
    clear HieT; rename y into sf1; rename H0 into HeT; rename H1 into HieT;
    move sf before k; move sf' before sf; move sf1 before sf';
    move sv before sf1; move α before sv; move β before α.
    (* clean *)

    apply evaluate_preserves_typing with (t' := sf1) in Hwsf as Hwsf1; auto.
    eapply IHk in HieT as IH; eauto.
    destruct IH as [sv' [sf1' [HfT Hltsv']]];
       exists sv'; exists sf1'; split; auto;  eapply fT_eT; eauto.
Qed.