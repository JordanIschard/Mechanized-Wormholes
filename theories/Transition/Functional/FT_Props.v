From Coq Require Import Program Lia Relations.Relation_Definitions Classes.RelationClasses PeanoNat
                        Classical_Prop Classical_Pred_Type Bool.Bool Classes.Morphisms.
From Mecha Require Import Resource Resources Term Typ Var ReadStock Typing VContext RContext 
                          ET_Definition Cell REnvironment Stock FT_Definition ET_Props.
Import ResourceNotations TermNotations TypNotations CellNotations
       VContextNotations RContextNotations REnvironmentNotations
       ReadStockNotations ResourcesNotations StockNotations SetNotations.

Module RC := RContext.
Module RE := REnvironment.
Module SK := Stock.

Open Scope renvironment_scope.

(** * Transition - Functional - Properties *)

(** ** Lift of multiple evaluation transitions *)

Lemma fT_MeT_sf (V V1 : 𝐕) (W : 𝐖) (st st' t t' t'' : Λ) :

       V⁺ ⊨ t ⟼⋆ t' -> ⪡ V ; st ; t' ⪢ ⭆ ⪡ V1 ; st' ; t'' ; W ⪢ -> 
    (*-------------------------------------------------------------------*)
                ⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st' ; t'' ; W ⪢.
Proof.
  intro HmeT. apply multi_indexed in HmeT as [k HieT].
  revert V V1 st st' t t' t'' HieT; induction k; intros; inversion HieT; subst; auto.
  apply fT_eT_sf with (t' := y); auto. apply IHk with (t' := t'); auto.
Qed.

Lemma fT_MeT_sv (V V1 : 𝐕) (W : 𝐖) (st st' st'' t t' : Λ) :

       V⁺ ⊨ st ⟼⋆ st' -> ⪡ V ; st' ; t ⪢ ⭆ ⪡ V1 ; st'' ; t' ; W ⪢ -> 
    (*--------------------------------------------------------------------*)
                ⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st'' ; t' ; W ⪢.
Proof.
  intro HmeT. apply multi_indexed in HmeT as [k HieT].
  revert V V1 st st' st'' t t' HieT; induction k; intros; inversion HieT; subst; auto.
  apply fT_eT_sv with (st' := y); auto. apply IHk with (st' := st'); auto.
Qed.

(** ** Property about domain equality *)

Fact fT_eqDom_Empty (Re : ℜ) (V : 𝐕):
 (forall r, (r ∈ Re)%rc <-> r ∈ V) -> (isEmpty(Re))%rc <-> isEmpty(V).
Proof.
  intro HeqDom. split; intros HEmp.
  - intro r. 
    assert (r ∉ Re)%rc.
    { intro. destruct H. now apply (HEmp r x). }
    intro v. intro Hc.
    apply H. rewrite HeqDom. now exists v.
  - intro r.
    assert (r ∉ V).
    { intro. destruct H. now apply (HEmp r x). }
    rewrite <- HeqDom in H.
    intro v. intro Hc.
    apply H. now exists v.
Qed.
  
Fact fT_eqDom_is_empty (Re : ℜ) (V : 𝐕):
  (forall r, (r ∈ Re)%rc <-> r ∈ V) -> RC.Raw.is_empty Re = RE.Raw.is_empty V.
Proof.
  intro HeqDom.
  destruct (RC.Raw.is_empty Re) eqn:HisEmp;
  destruct (RE.Raw.is_empty V) eqn:HisEmp';
  try reflexivity.
  - exfalso.  
    apply RC.OP.P.is_empty_2 in HisEmp.
    rewrite fT_eqDom_Empty in HisEmp; eauto.
    apply RE.OP.P.is_empty_1 in HisEmp.
    rewrite HisEmp' in *. inversion HisEmp.
  - exfalso.  
    apply RE.OP.P.is_empty_2 in HisEmp'.
    rewrite <- fT_eqDom_Empty in HisEmp'; eauto.
    apply RC.OP.P.is_empty_1 in HisEmp'.
    rewrite HisEmp in *. inversion HisEmp'.
Qed.

Fact fT_eqDom_find (Re : ℜ) (V : 𝐕):
  (forall r, (r ∈ Re)%rc <-> r ∈ V) -> 
  forall r τ τ', 
    Re⌊r⌋%rc = Some (τ, τ') -> exists v, (V⌊r⌋ = Some v)%type.
Proof. 
  intros HeqDom r τ τ' HfRe.
  assert (r ∈ Re)%rc.
  { exists (τ,τ'). now apply RC.OP.P.find_2. }
  rewrite HeqDom in *. destruct H.
  exists x. now apply RE.OP.P.find_1.
Qed.

Fact fT_eqDom_max (Re : ℜ) (V : 𝐕):
  (forall r, (r ∈ Re)%rc <-> r ∈ V) -> max(Re)%rc = max(V).
Proof.
  revert V.
  induction Re using RC.OP.P.map_induction; intros V HeqDom.
  - rewrite RC.Ext.max_key_Empty_spec; auto.
    rewrite (fT_eqDom_Empty Re V HeqDom) in H.
    rewrite RE.Ext.max_key_Empty_spec; auto.
  - assert (HAddV: exists v, Add x v (RE.Raw.remove x V) V). 
    {
      assert (x ∈ V). { 
        rewrite <- HeqDom. unfold RC.OP.P.Add in *; rewrite H0.
        rewrite RC.OP.P.add_in_iff; auto. 
      }
      destruct H1 as [v HM].
      exists v. unfold RE.OP.P.Add.
      rewrite RE.OP.P.add_remove_1.
      symmetry. rewrite RE.OP.P.add_id.
      now apply RE.OP.P.find_1.
    }
    destruct HAddV as [v HAddV]. remember (RE.Raw.remove x V) as V0.
    assert (HeqDom': forall r : RContext.Raw.key, (r ∈ Re1)%rc <-> r ∈ V0).
    { 
      intro r; split; intro HIn.
      - assert (r ∈ Re2)%rc. 
        { unfold RC.OP.P.Add in *; rewrite H0. rewrite RC.OP.P.add_in_iff; auto. }
        rewrite HeqDom in H1.
        unfold RE.OP.P.Add in *; rewrite HAddV in *.
        rewrite RE.OP.P.add_in_iff in H1; destruct H1; subst; auto.
        contradiction.
      - assert (r ∈ V). 
        { unfold RE.OP.P.Add in *; rewrite HAddV. rewrite RE.OP.P.add_in_iff; auto. }
        rewrite <- HeqDom in H1.
        unfold RC.OP.P.Add in *. rewrite H0 in *.
        rewrite RC.OP.P.add_in_iff in H1; destruct H1; subst; auto.
        rewrite RE.OP.P.remove_in_iff in HIn; destruct HIn; contradiction.
    }
    apply IHRe1 in HeqDom' as Hmax.
    unfold RC.OP.P.Add in *. rewrite H0. 
    unfold RE.OP.P.Add in *. rewrite HAddV.
    destruct (Resource.ltb_spec0 x (max(Re1))%rc).
    -- rewrite RC.Ext.max_key_add_lt_spec; auto.
       rewrite RE.Ext.max_key_add_lt_spec; auto.
       + subst. intro Hc. 
        rewrite RE.OP.P.remove_in_iff in Hc. 
        destruct Hc; contradiction.
       + now rewrite Hmax in *.
    -- rewrite RC.Ext.max_key_add_ge_spec; auto; try lia.
       rewrite Hmax in n.
       rewrite RE.Ext.max_key_add_ge_spec; auto; try lia.
       subst. intro Hc. 
       rewrite RE.OP.P.remove_in_iff in Hc. 
       destruct Hc; contradiction.
Qed.

Fact fT_eqDom_new (Re : ℜ) (V : 𝐕):
  (forall r, (r ∈ Re)%rc <-> r ∈ V) -> Re⁺%rc = V⁺.
Proof.
  intro HeqDom. unfold RC.Ext.new_key,RE.Ext.new_key.
  apply fT_eqDom_is_empty in HeqDom as HisEmp.
  destruct (RC.Raw.is_empty Re) eqn:HEmp.
  - now rewrite <- HisEmp.
  - rewrite <- HisEmp; f_equal; now apply fT_eqDom_max.
Qed.


(** *** Property about wf_env_fT *)

(** **** Projection *)

Fact wf_env_fT_in (Re : ℜ) (V : 𝐕):
  Wfᵣₜ(Re,V) -> forall r, (r ∈ Re)%rc <-> r ∈ V.
Proof. now intros [HeqDom _]. Qed.

Fact wf_env_fT_valid (Re : ℜ) (V : 𝐕):
  Wfᵣₜ(Re,V) -> (Re⁺ ⊩ Re)%rc /\ V⁺ ⊩ V.
Proof. intros [_ [HvRe [HvV _]]]; now split. Qed.

Fact wf_env_fT_well_typed (Re : ℜ) (V : 𝐕):
  Wfᵣₜ(Re,V) -> 
  forall (r : resource) (v : 𝑣) (τ τ' : Τ),
  Re⌊r⌋%rc = Some (τ,τ') ->  V⌊r⌋ = Some v  -> 
  match v with
    | (⩽ v' … ⩾) => ∅%vc ⋅ Re ⊫ v' ∈ τ'
    | (⩽ … v' ⩾) => ∅%vc ⋅ Re ⊫ v' ∈ τ
  end.
Proof. intros [_ [_ [_ Hwt]]] r v τ τ' HfRe HfV. apply (Hwt r); assumption. Qed.

(** **** Corollary *)

Corollary wf_env_fT_Empty (Re : ℜ) (V : 𝐕):
  Wfᵣₜ(Re,V) -> isEmpty(Re)%rc <-> isEmpty(V).
Proof. intros [HeqDom _]. now apply fT_eqDom_Empty. Qed.

Corollary wf_env_fT_is_empty (Re : ℜ) (V : 𝐕):
  Wfᵣₜ(Re,V) -> RC.Raw.is_empty Re = RE.Raw.is_empty V.
Proof. intros [HeqDom _]. now apply fT_eqDom_is_empty. Qed.

Corollary wf_env_fT_find (Re : ℜ) (V : 𝐕):
  Wfᵣₜ(Re,V) -> forall r τ τ', 
  Re⌊r⌋%rc = Some(τ, τ') -> exists v, (V⌊r⌋ = Some v)%type.
Proof. 
  intros [HeqDom _] r τ τ' HfRe.
  now apply (fT_eqDom_find Re _ HeqDom r τ τ').
Qed.

Corollary wf_env_fT_max (Re : ℜ) (V : 𝐕):
  Wfᵣₜ(Re,V) -> max(Re)%rc = max(V).
Proof. intros [HeqDom _]. now apply fT_eqDom_max. Qed.

Corollary wf_env_fT_new (Re : ℜ) (V : 𝐕):
  Wfᵣₜ(Re,V) -> Re⁺%rc = V⁺.
Proof. intros [HeqDom _]. now apply fT_eqDom_new. Qed.

(** **** Equality *)

#[export] 
Instance wfFT_eq : Proper (RC.eq ==> RE.eq ==> iff) (wf_env_fT).
Proof.
  repeat red; split; intros [HeqDom [Hvx [Hvx0 Hwt]]].
  - split.
    -- split; intros.
       + rewrite <- H0. rewrite <- HeqDom. now rewrite H.
       + rewrite <- H. rewrite HeqDom. now rewrite H0.
    -- repeat split.
       + now rewrite <- H.
       + now rewrite <- H0.
       + intros. rewrite <- H in *. rewrite <- H0 in *.
         apply (Hwt r τ τ' v) in H2; auto.
         destruct v; now rewrite <- H.
  - split.
    -- split; intros.
       + rewrite H0. rewrite <- HeqDom. now rewrite <- H.
       + rewrite H. rewrite HeqDom. now rewrite <- H0.
    -- repeat split.
       + now rewrite H.
       + now rewrite H0.
       + intros. rewrite H in *. rewrite H0 in *.
         apply (Hwt r τ τ' v) in H2; auto.
         destruct v; now rewrite H.
Qed.

(** **** Wh *)

Lemma wfFT_env_wh (Re : ℜ) (V : 𝐕) (τ : Τ) (i : Λ) :
  (Re⁺%rc ⊩ τ)%ty -> (Re⁺%rc ⊩ i)%tm -> ∅%vc ⋅ Re ⊫ i ∈ τ ->
  Wfᵣₜ(Re,V) ->
  Wfᵣₜ((RC.Raw.add (S (Re⁺)%rc) (τ,<[𝟙]>) (RC.Raw.add (Re⁺)%rc (<[𝟙]>,τ) Re)),
       (RE.Raw.add (S  (V⁺)) (Cell.inp <[unit]>) 
             (RE.Raw.add (V⁺) (Cell.shift (V⁺) 2 (Cell.inp i)) ([⧐ (V⁺) – 2] V)))).
Proof.
  intros Hvτ Hvi Hwti Hwf. 
  apply (wf_env_fT_new Re V) in Hwf as Hnew.
  apply (wf_env_fT_valid Re V) in Hwf as Hv.
  destruct Hv as [HvRe HvV].
  repeat split.
  
  - intro HIn. 
    repeat rewrite RE.OP.P.add_in_iff.  
    repeat apply RC.OP.P.add_in_iff in HIn as [Heq' | HIn]; subst; auto.
    repeat right. 
    rewrite (wf_env_fT_in Re V) in HIn; auto.
    apply RE.valid_in_spec with (lb := V⁺) in HIn as Hvr; auto.
    rewrite <- (Resource.shift_valid_refl (V⁺) 2 r); auto.
    now apply RE.shift_in_iff.
  - intro HIn. 
    repeat rewrite RC.OP.P.add_in_iff.
    repeat apply RE.OP.P.add_in_iff in HIn as [Heq' | HIn]; subst; auto.
    repeat right.
    apply RE.shift_in_e_spec in HIn as Hr'.
    destruct Hr' as [r' Heq']; subst.
    apply RE.shift_in_iff in HIn.
    apply RE.valid_in_spec with (lb := V⁺) in HIn as Hvr; auto.
    rewrite (Resource.shift_valid_refl (V⁺) 2 r'); auto.
    now apply (wf_env_fT_in Re V).
  - rewrite RC.new_key_wh_spec; 
    apply RC.valid_wh_spec; auto; split; simpl; auto;
    try now constructor.
  - rewrite RE.new_key_wh_spec.
    apply RE.valid_wh_spec_1; auto; try now constructor.
    unfold Cell.valid; simpl. now rewrite <- Hnew.
  - intros r τ1 τ1' v HfRe HfV.
    destruct (Resource.eq_dec r (S (Re⁺)%rc)); subst.
    -- rewrite RE.add_eq_o in HfV; auto.
       rewrite RC.add_eq_o in HfRe; auto.
       inversion HfRe; inversion HfV; subst; clear HfV HfRe.
       constructor.
    -- destruct (Resource.eq_dec r (Re⁺)%rc); subst.
       + rewrite RE.add_neq_o in HfV; try lia.
         rewrite RE.add_eq_o in HfV; auto.
         rewrite RC.add_neq_o in HfRe; try lia.
         rewrite RC.add_eq_o in HfRe; auto.
         inversion HfRe; inversion HfV; subst; clear HfV HfRe.
         apply (weakening_ℜ_bis _ Re); auto.
         ++ apply VContext.valid_empty_spec.
         ++  rewrite RC.new_key_wh_spec; lia.
         ++ apply RC.Ext.Submap_add_spec_1.
            * apply RC.Ext.new_key_notin_spec.
              rewrite RC.Ext.new_key_add_ge_spec; auto.
              apply RC.Ext.new_key_notin_spec; lia.
            * apply RC.Ext.Submap_add_spec_1.
              ** apply RC.Ext.new_key_notin_spec; lia.
              ** reflexivity.
       + rewrite RE.add_neq_o in HfV; try lia.
         rewrite RE.add_neq_o in HfV; try lia.
         rewrite RC.add_neq_o in HfRe; try lia.
         rewrite RC.add_neq_o in HfRe; try lia.
         apply RE.shift_find_e_spec_1 in HfV as Hr'.
         destruct Hr' as [[r' Heqr'] [v' Heqv']]; subst.
         apply Cell.eq_leibniz in Heqv'.
         rewrite Heqv' in *; clear Heqv'.
         apply RE.shift_find_iff in HfV.
         apply RE.valid_find_spec with (lb := V⁺) in HfV as Hvr'; auto.
         destruct Hvr' as [Hvr' _].
         rewrite Resource.shift_valid_refl in HfRe; auto.
         apply (wf_env_fT_well_typed Re V Hwf r' v') in HfRe as Hwv'; auto.
         destruct v'; auto; simpl.
         ++ apply (weakening_ℜ_bis _ Re); auto.
            * apply VContext.valid_empty_spec.
            * rewrite RC.new_key_wh_spec; lia.
            * apply RC.Ext.Submap_add_spec_1.
              ** apply RC.Ext.new_key_notin_spec.
                 rewrite RC.Ext.new_key_add_ge_spec; auto.
                 apply RC.Ext.new_key_notin_spec; lia.
              ** apply RC.Ext.Submap_add_spec_1.
                 { apply RC.Ext.new_key_notin_spec; lia. }
                 { reflexivity. }
         ++ apply (weakening_ℜ_bis _ Re); auto.
            * apply VContext.valid_empty_spec.
            * rewrite RC.new_key_wh_spec; lia.
            * apply RC.Ext.Submap_add_spec_1.
              ** apply RC.Ext.new_key_notin_spec.
                rewrite RC.Ext.new_key_add_ge_spec; auto.
                apply RC.Ext.new_key_notin_spec; lia.
              ** apply RC.Ext.Submap_add_spec_1.
                { apply RC.Ext.new_key_notin_spec; lia. }
                { reflexivity. }
Qed.