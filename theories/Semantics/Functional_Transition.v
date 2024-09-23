From Coq Require Import Lia Morphisms Lists.List.
From Mecha Require Import Resource Resources Term Typ Cell VContext RContext  
                          Type_System Evaluation_Transition  REnvironment ReaderStock Stock.
Import ResourceNotations TermNotations TypNotations CellNotations ListNotations
       VContextNotations RContextNotations REnvironmentNotations
       ReaderStockNotations ResourcesNotations SetNotations StockNotations.

(** * Semantics - Functional

  Wormholes’s dynamic semantics is split in three sets of transition rules: the evaluation transition, defined in [Evaluation_Transition.v], which extends standard β-reduction; the functional transition which performs the logical instant, and the temporal transition, defined in [Temporal_Transition.v], which corresponds to the reactivity of the program: it initializes the resources values, performs the instant via the functional transition and updates the system. In this file, we focus on the functional transition.
*)


(** ** Definition - Functional *)

Open Scope renvironment_scope.

(** *** Domain equality 

  We define the domain equality as follows: for all key [k], [k] is in the resource context if and only if [k] is in the resource environment. This property is already define in [MMaps], however we need it for maps with different data and the one in [MMaps] library does not match.
*)
Definition eqDom (Re : ℜ) (V : 𝐕) := forall (r : resource), (r ∈ Re)%rc <-> r ∈ V.

(** *** Well-formed environment-context 

  For subsequent proofs we define a well-formed property between the resource context ([Re]) and the resource environment ([V]). They need four property: (1) their domain matches; (2,3) they are both well-formed under their new key; (4) and all pair (types, cell) admit the well-typed property under the empty variable context and the resource context [Re].
*)
Definition well_formed_ec (Re : ℜ) (V : 𝐕) :=
  (* (1) *) eqDom Re V /\ 
  (* (2) *) (Re⁺ ⊩ Re)%rc /\  (* (3) *) V⁺ ⊩ V /\
  (* (4) *) (forall (r : resource) (α β : Τ) (v : 𝑣),
                Re⌊r⌋%rc = Some (α,β) -> V⌊r⌋ = Some v -> 
                match v with
                  | (⩽ v' … ⩾) => (∅)%vc ⋅ Re ⊢ v' ∈ β
                  | (⩽ … v' ⩾) => (∅)%vc ⋅ Re ⊢ v' ∈ α
                end).

Notation "'WF(' Re , V )" := (well_formed_ec Re V) (at level 50).

(** *** Functional transition 

  The functional transition is a big-step semantics that performs an instant. It takes an input environment [V], a signal input sample [st] and a signal function [t] and produces an updated environment [V1], an output term [st1], an updated signal function [t1] and a stock [W]. There are numerous shifts done during the functional transition. We suppose input components as well-formed under [V⁺] and we want output components well-formed under [V1⁺]. Consequently, all shifts aims to keep consistent this statement.
*)

Reserved Notation "⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st1 ; t1 ; W ⪢" 
  (at level 57, V constr, V1 constr, st custom wh, st1 custom wh,t custom wh, t1 custom wh, no associativity).

Inductive functional : 𝐕 -> Λ -> Λ -> 𝐕 -> Λ -> Λ -> 𝐖 -> Prop :=

  | fT_eT_sf (st st' t t' t'' : Λ) (V V1 : 𝐕) (W : 𝐖) :

       V⁺ ⊨ t ⟼ t' -> ⪡ V ; st ; t' ⪢ ⭆ ⪡ V1 ; st' ; t'' ; W ⪢ -> 
  (* ----------------------------------------------------------------- *)
             ⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st' ; t'' ; W ⪢

  | fT_eT_sv (st st' st'' t t' : Λ) (V V1 : 𝐕) (W : 𝐖) :

       V⁺ ⊨ st ⟼ st' -> ⪡ V ; st' ; t ⪢ ⭆ ⪡ V1 ; st'' ; t' ; W ⪢ -> 
  (* ------------------------------------------------------------------- *)
              ⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st'' ; t' ; W ⪢

  | fT_arr  (st t : Λ) (V : 𝐕) :

  (* ----------------------------------------------------------- *)
       ⪡ V ; st ; arr(t) ⪢ ⭆ ⪡ V ; (t st) ; arr(t) ; (∅)%sk ⪢ 

  | fT_first (v1 v1' v2 t t' : Λ) (α : Τ) (V V1 : 𝐕) (W : 𝐖) :

                        ⪡ V ; v1 ; t ⪢ ⭆ ⪡ V1 ; v1' ; t' ; W ⪢ ->
  (* ------------------------------------------------------------------------------------------ *)
       ⪡ V ; ⟨v1,v2⟩ ; first(t) ⪢ ⭆ ⪡ V1 ; ⟨v1',[⧐ {V⁺} – {V1⁺ - V⁺}] v2⟩ ; first(t') ; W ⪢

  | fT_comp (st st' st'' t1 t1' t2 t2' : Λ) (V V1 V2 : 𝐕) (W W': 𝐖) :

                          ⪡ V ; st ; t1 ⪢ ⭆ ⪡ V1 ; st' ; t1' ; W ⪢ ->
            ⪡ V1 ; st' ; ([⧐ {V⁺} – {V1⁺ - V⁺}] t2) ⪢ ⭆ ⪡ V2 ; st'' ; t2' ; W' ⪢ ->
  (* ------------------------------------------------------------------------------------------ *)
       ⪡ V ; st ; (t1 >>> t2) ⪢ 
       ⭆ ⪡ V2 ; st'' ; (([⧐ {V1⁺} – {V2⁺ - V1⁺}] t1') >>> t2') ; 
                                                       (([⧐ V1⁺ – (V2⁺ - V1⁺)] W) ∪ W')%sk ⪢

  | fT_rsf (r : resource) (st v : Λ) (V : 𝐕) :

                               V⌊r⌋ = Some (⩽ v … ⩾) -> 
  (* ------------------------------------------------------------------------ *)
       ⪡ V ; st ; rsf[r] ⪢ ⭆ ⪡ ⌈ r ⤆ ⩽ … st ⩾ ⌉ V ; v ; rsf[r] ; (∅)%sk ⪢

  | fT_wh (st st' i t t' : Λ) (V V1 : 𝐕) (W : 𝐖) :
                
       ⪡ (⌈S (V⁺) ⤆ ⩽ <[unit]> … ⩾⌉ (⌈V⁺ ⤆ ([⧐ V⁺ – 2] ⩽ i … ⩾)%cl⌉ ([⧐ V⁺ – 2] V))) ; 
                                    (<[[⧐ {V⁺} – 2] st]>) ; t ⪢ ⭆ ⪡ V1 ; st' ; t' ; W ⪢ ->
  (* ------------------------------------------------------------------------------------------ *)
       ⪡ V ; st ; wormhole(i;t) ⪢  
       ⭆ ⪡ V1 ; st' ; t' ; (⌈V⁺ ~ S (V⁺) ⤆ <[[⧐ {V⁺} – {V1⁺ - V⁺}] i]>⌉ W)%sk ⪢

where "⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st1 ; t1 ; W ⪢" := (functional V st t V1 st1 t1 W).

(** ---- *)

(** ** Property - Functional *)

Module RE := REnvironment.
Module RC := RContext.
Module RS := Resources.St.

(** *** Lift of multi-evaluation transitions *)

Lemma fT_MeT_sf (V V1 : 𝐕) (W : 𝐖) (st st' t t' t'' : Λ) :

       V⁺ ⊨ t ⟼⋆ t' -> ⪡ V ; st ; t' ⪢ ⭆ ⪡ V1 ; st' ; t'' ; W ⪢ -> 
  (* ------------------------------------------------------------------ *)
                ⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st' ; t'' ; W ⪢.
Proof.
  intro HmeT; revert V1 W st st' t''; induction HmeT; auto.
  intros V1 W st st' t'' HfT.
  apply fT_eT_sf with (t' := y); auto.
Qed.

Lemma fT_MeT_sv (V V1 : 𝐕) (W : 𝐖) (st st' st'' t t' : Λ) :

       V⁺ ⊨ st ⟼⋆ st' -> ⪡ V ; st' ; t ⪢ ⭆ ⪡ V1 ; st'' ; t' ; W ⪢ -> 
  (* -------------------------------------------------------------------- *)
                ⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st'' ; t' ; W ⪢.
Proof.
  intro HmeT; revert V1 W t t' st''; induction HmeT; auto.
  intros V1 W t t' st'' HfT.
  apply fT_eT_sv with (st' := y); auto.
Qed.



(** *** [eqDom] property *)

#[export] Instance eqDom_eq : Proper (RC.eq ==> RE.eq ==> iff) eqDom.
Proof.
  intros Re Re1 HeqRe V V1 HeqV; unfold eqDom; split; intros.
  - rewrite <- HeqRe; rewrite <- HeqV; auto.
  - rewrite HeqRe; rewrite HeqV; auto.
Qed.

Fact fT_eqDom_In (r : resource) (Re : ℜ) (V : 𝐕):
  eqDom Re V -> (r ∈ Re)%rc <-> r ∈ V.
Proof. unfold eqDom; intro HeqDom; auto. Qed.

Fact fT_eqDom_MapsTo (r : resource) (α β : Τ) (Re : ℜ) (V : 𝐕) :
  eqDom Re V -> RC.Raw.MapsTo r (α,β) Re -> exists (v : 𝑣), RE.Raw.MapsTo r v V.
Proof. 
  intros HeqDom HM.
  assert (HIn : r ∈ V).
  { 
    rewrite <- (fT_eqDom_In _ Re); auto.
    now exists (α,β). 
  }
  destruct HIn as [v HM']; now exists v.
Qed.

Fact fT_eqDom_Empty (Re : ℜ) (V : 𝐕):
 eqDom Re V -> (isEmpty(Re))%rc <-> isEmpty(V).
Proof.
  intro HeqDom; split; intros HEmp r v HM.
  - assert (HnIn : (r ∉ Re)%rc).
    { intros [v' HM']; now apply (HEmp r v'). }
    apply HnIn. 
    rewrite (fT_eqDom_In _ _ V); auto. 
    now exists v.
  - assert (HnIn : (r ∉ V)).
    { intros [v' HM']; now apply (HEmp r v'). }
    apply HnIn. 
    rewrite <- (fT_eqDom_In _ Re V); auto. 
    now exists v.
Qed.
  
Fact fT_eqDom_is_empty (Re : ℜ) (V : 𝐕):
  eqDom Re V -> RC.Raw.is_empty Re = RE.Raw.is_empty V.
Proof.
  intro HeqDom.
  destruct (RC.Raw.is_empty Re) eqn:HisEmp;
  destruct (RE.Raw.is_empty V) eqn:HisEmp'; auto; exfalso.
  - apply RC.is_empty_2 in HisEmp.
    rewrite (fT_eqDom_Empty _ V) in HisEmp; auto.
    apply RE.is_empty_1 in HisEmp.
    rewrite HisEmp' in *; inversion HisEmp.
  - exfalso.  
    apply RE.is_empty_2 in HisEmp'.
    rewrite <- fT_eqDom_Empty in HisEmp'; eauto.
    apply RC.is_empty_1 in HisEmp'.
    rewrite HisEmp in *. inversion HisEmp'.
Qed.

Fact fT_eqDom_find (Re : ℜ) (V : 𝐕):
  eqDom Re V -> 
  forall (r : resource) (α β : Τ), Re⌊r⌋%rc = Some (α, β) -> exists v, (V⌊r⌋ = Some v)%type.
Proof. 
  intros HeqDom r α β HfRe.
  apply RC.find_2 in HfRe.
  apply fT_eqDom_MapsTo with (V := V) in HfRe as [v HM]; auto.
  now exists v; apply RE.find_1.
Qed.

Fact fT_eqDom_max (Re : ℜ) (V : 𝐕):
  eqDom Re V -> max(Re)%rc = max(V).
Proof.
  revert V; induction Re using RC.map_induction; intros V HeqDom.
  - rewrite RC.Ext.max_key_Empty_spec; auto.
    rewrite (fT_eqDom_Empty Re V HeqDom) in H.
    rewrite RE.Ext.max_key_Empty_spec; auto.
  - assert (HAddV: exists v, Add x v (RE.Raw.remove x V) V). 
    {
      assert (HIn : x ∈ V). 
      { 
        unfold eqDom in *; rewrite <- HeqDom. 
        unfold RC.Add in *; rewrite H0.
        rewrite RC.add_in_iff; auto. 
      }
      destruct HIn as [v HM].
      exists v; unfold RE.Add.
      rewrite RE.add_remove_1.
      symmetry. rewrite RE.add_id.
      now apply RE.find_1.
    }
    destruct HAddV as [v HAddV]. 
    remember (RE.Raw.remove x V) as V0.
    assert (HeqDom': forall r : RContext.Raw.key, (r ∈ Re1)%rc <-> r ∈ V0).
    { 
      intro r; split; intro HIn.
      - assert (r ∈ Re2)%rc. 
        { unfold RC.Add in *; rewrite H0. rewrite RC.add_in_iff; auto. }
        unfold eqDom in *; rewrite HeqDom in H1.
        unfold RE.Add in *; rewrite HAddV in *.
        rewrite RE.add_in_iff in H1; destruct H1; subst; auto.
        contradiction.
      - assert (r ∈ V). 
        { unfold RE.Add in *; rewrite HAddV. rewrite RE.add_in_iff; auto. }
        unfold eqDom in *; rewrite <- HeqDom in H1.
        unfold RC.Add in *. rewrite H0 in *.
        rewrite RC.add_in_iff in H1; destruct H1; subst; auto.
        rewrite RE.remove_in_iff in HIn; destruct HIn; contradiction.
    }
    apply IHRe1 in HeqDom' as Hmax.
    unfold RC.Add in *. rewrite H0. 
    unfold RE.Add in *. rewrite HAddV.
    destruct (Resource.ltb_spec0 x (max(Re1))%rc).
    -- rewrite RC.Ext.max_key_add_lt_spec; auto.
       rewrite RE.Ext.max_key_add_lt_spec; auto.
       + subst. intro Hc. 
        rewrite RE.remove_in_iff in Hc. 
        destruct Hc; contradiction.
       + now rewrite Hmax in *.
    -- rewrite RC.Ext.max_key_add_ge_spec; auto; try lia.
       rewrite Hmax in n.
       rewrite RE.Ext.max_key_add_ge_spec; auto; try lia.
       subst. intro Hc. 
       rewrite RE.remove_in_iff in Hc. 
       destruct Hc; contradiction.
Qed.

Fact fT_eqDom_new (Re : ℜ) (V : 𝐕):
  eqDom Re V -> Re⁺%rc = V⁺.
Proof.
  unfold RC.Ext.new_key,RE.Ext.new_key; intro HeqDom.
  apply fT_eqDom_is_empty in HeqDom as HisEmp.
  destruct (RC.Raw.is_empty Re) eqn:HEmp.
  - now rewrite <- HisEmp.
  - rewrite <- HisEmp; f_equal; now apply fT_eqDom_max.
Qed.

(** *** [well_formed_ec] property *)


(** **** Projection *)

Fact WF_ec_In (Re : ℜ) (V : 𝐕):
  WF(Re,V) -> forall r, (r ∈ Re)%rc <-> r ∈ V.
Proof. now intros [HeqDom _]. Qed.

Fact WF_ec_valid (Re : ℜ) (V : 𝐕):
  WF(Re,V) -> (Re⁺ ⊩ Re)%rc /\ V⁺ ⊩ V.
Proof. intros [_ [HvRe [HvV _]]]; now split. Qed.

Fact WF_ec_well_typed (Re : ℜ) (V : 𝐕):
  WF(Re,V) -> 
  forall (r : resource) (α β : Τ) (v : 𝑣),
    Re⌊r⌋%rc = Some (α,β) ->  V⌊r⌋ = Some v  -> 
    match v with
      | (⩽ v' … ⩾) => ∅%vc ⋅ Re ⊢ v' ∈ β
      | (⩽ … v' ⩾) => ∅%vc ⋅ Re ⊢ v' ∈ α
    end.
Proof. 
  intros [_ [_ [_ Hwt]]] r v α β HfRe HfV. 
  now apply (Hwt r). 
Qed.

(** **** Corollary *)

Corollary WF_ec_Empty (Re : ℜ) (V : 𝐕):
  WF(Re,V) -> isEmpty(Re)%rc <-> isEmpty(V).
Proof. intros [HeqDom _]; now apply fT_eqDom_Empty. Qed.

Corollary WF_ec_is_empty (Re : ℜ) (V : 𝐕):
  WF(Re,V) -> RC.Raw.is_empty Re = RE.Raw.is_empty V.
Proof. intros [HeqDom _]; now apply fT_eqDom_is_empty. Qed.

Corollary WF_ec_find (Re : ℜ) (V : 𝐕):
  WF(Re,V) -> forall r α β, 
  Re⌊r⌋%rc = Some(α, β) -> exists v, (V⌊r⌋ = Some v)%type.
Proof. 
  intros [HeqDom _] r α β HfRe.
  now apply (fT_eqDom_find Re _ HeqDom r α β).
Qed.

Corollary WF_ec_max (Re : ℜ) (V : 𝐕):
  WF(Re,V) -> max(Re)%rc = max(V).
Proof. intros [HeqDom _]; now apply fT_eqDom_max. Qed.

Corollary WF_ec_new (Re : ℜ) (V : 𝐕):
  WF(Re,V) -> Re⁺%rc = V⁺.
Proof. intros [HeqDom _]; now apply fT_eqDom_new. Qed.

(** **** Wormholes specification *)

Lemma WF_ec_wh (Re : ℜ) (V : 𝐕) (α : Τ) (i : Λ) :
  (Re⁺%rc ⊩ α)%ty -> (Re⁺%rc ⊩ i)%tm -> ∅%vc ⋅ Re ⊢ i ∈ α ->
  WF(Re,V) ->
  WF((RC.Raw.add (S (Re⁺)%rc) (α,<[𝟙]>) (RC.Raw.add (Re⁺)%rc (<[𝟙]>,α) Re)),
       (RE.Raw.add (S  (V⁺)) (Cell.inp <[unit]>) 
             (RE.Raw.add (V⁺) (Cell.shift (V⁺) 2 (Cell.inp i)) ([⧐ (V⁺) – 2] V)))).
Proof.
  intros Hvτ Hvi Hwti Hwf. 
  apply (WF_ec_new Re V) in Hwf as Hnew.
  apply (WF_ec_valid Re V) in Hwf as Hv.
  destruct Hv as [HvRe HvV].
  repeat split.
  - intro HIn. 
    repeat rewrite RE.add_in_iff.  
    repeat apply RC.add_in_iff in HIn as [Heq' | HIn]; subst; auto.
    repeat right.
    rewrite (WF_ec_In Re V) in HIn; auto.
    apply RE.valid_in_spec with (lb := V⁺) in HIn as Hvr; auto.
    rewrite <- (Resource.shift_valid_refl (V⁺) 2 r); auto.
    now apply RE.shift_in_iff.
  - intro HIn. 
    repeat rewrite RC.add_in_iff.
    repeat apply RE.add_in_iff in HIn as [Heq' | HIn]; subst; auto.
    repeat right.
    apply RE.shift_in_e_spec in HIn as Hr'.
    destruct Hr' as [r' Heq']; subst.
    apply RE.shift_in_iff in HIn.
    apply RE.valid_in_spec with (lb := V⁺) in HIn as Hvr; auto.
    rewrite (Resource.shift_valid_refl (V⁺) 2 r'); auto.
    now apply (WF_ec_In Re V).
  - apply RC.valid_wh_full_spec; auto; 
    split; unfold Cell.valid; simpl; auto; constructor.
  - apply RE.valid_wh_full_spec; auto; 
    unfold Cell.valid; simpl; try constructor.
    now rewrite <- Hnew.
  - intros r τ β v HfRe HfV.
    destruct (Resource.eq_dec r (S (Re⁺)%rc)); subst.
    -- rewrite RE.add_eq_o in HfV; auto.
       rewrite RC.add_eq_o in HfRe; auto.
       inversion HfRe; inversion HfV; subst; clear HfV HfRe.
       constructor.
    -- destruct (Resource.eq_dec r (Re⁺)%rc) as [| Hneq]; subst.
       + rewrite RE.add_neq_o in HfV; try lia.
         rewrite RE.add_eq_o in HfV; auto.
         rewrite RC.add_neq_o in HfRe; try lia.
         rewrite RC.add_eq_o in HfRe; auto.
         inversion HfRe; inversion HfV; subst; clear HfV HfRe.
         apply (weakening_ℜ_2 _ _ _ Re); auto.
         ++ rewrite RC.new_key_wh_spec; lia.
         ++ apply RC.Submap_wh_spec.
       + do 2 rewrite RE.add_neq_o in HfV; try lia.
         do 2 rewrite RC.add_neq_o in HfRe; try lia.
         apply RE.shift_find_e_spec_1 in HfV as Hr'.
         destruct Hr' as [[r' Heqr'] [v' Heqv']]; subst.
         apply RE.shift_find_iff in HfV.
         apply RE.valid_find_spec with (lb := V⁺) in HfV as Hvr'; auto.
         destruct Hvr' as [Hvr' _].
         rewrite Resource.shift_valid_refl in HfRe; auto.
         apply (WF_ec_well_typed Re V Hwf r' _ _ v') in HfRe as Hwv'; auto.
         destruct v' as [v' | v']; auto; simpl; 
         rewrite <- Hnew; now apply weakening_ℜ_wh.
Qed.

(** ---- *)

(** ** Preservation - Functional *)
Section preservation.


Hint Resolve VContext.valid_empty_spec Stock.valid_empty_spec Resources.valid_empty_spec : core.

(** *** Preservation of well-formedness through the functional transition 

  Suppose a functional transition (1), if input components ([V], [st] and [sf]) are well-formed under [V⁺] (2,3,4), then output components ([V1], [st'], [sf'] and [W]) are well-formed under [V1⁺] (5). In addition, we can state that [V⁺] is lower or equal to [V1⁺] (6).
*)
Lemma functional_preserves_valid (V V1 : 𝐕) (W : 𝐖) (st st' sf sf' : Λ) :

               (* (1) *) ⪡ V ; st ; sf ⪢ ⭆ ⪡ V1 ; st' ; sf' ; W ⪢ ->
        (* (2) *) V⁺ ⊩ V -> (* (3) *) (V⁺ ⊩ st)%tm -> (* (4) *) (V⁺ ⊩ sf)%tm ->
  (* ------------------------------------------------------------------------------ *)
       (* (5) *) V1⁺ ⊩ V1 /\ (V1⁺ ⊩ st')%tm /\ (V1⁺ ⊩ sf')%tm /\ (V1⁺ ⊩ W)%sk /\ 
                                (* (6) *) V⁺ <= V1⁺.
Proof.
  intro fT; induction fT; intros HvV Hvst Hvt.
  (* fT_eT_sf *)
  - destruct IHfT as [HvV1 [Hvst' [Hvt'' [HvW Hlt]]]]; auto.
    now apply evaluate_preserves_valid_term with (t := t).
  (* fT_eT_sv *)
  - destruct IHfT as [HvV1 [Hvst' [Hvt'' [HvW Hlt]]]]; auto.
    now apply evaluate_preserves_valid_term with (t := st).
  (* fT_arr *)
  - repeat split; auto. 
    constructor; inversion Hvt; now subst.
  (* fT_first *)
  - inversion Hvst; inversion Hvt; subst; fold Term.valid in *; clear Hvst Hvt. 
    destruct IHfT as [HvV1 [Hvst' [Hvt'' [HvW Hlt]]]]; auto.
    repeat split; auto; try (now destruct HvW); constructor; auto.
    now apply Term.shift_preserves_valid_2.
  (* fT_comp *)
  - inversion Hvt; subst; 
    destruct IHfT1 as [HvV1 [Hvst' [Hvt1' [HvW1 Hlt1]]]]; auto;
    destruct IHfT2 as [HvV2 [Hvst'' [Hvt2' [HvW2 Hlt2]]]]; auto; fold Term.valid in *.
    -- now apply Term.shift_preserves_valid_2.
    -- do 3 (split; auto).
       + constructor; auto.
         now apply Term.shift_preserves_valid_2.
       + split; try lia. 
         apply Stock.valid_union_spec; split; auto.
         now apply Stock.shift_preserves_valid_2.
  (* fT_rsf *)
  - assert (r ∈ V).
    { rewrite RE.in_find; rewrite H; intro c; now inversion c. }
    rewrite RE.Ext.new_key_add_in_spec; auto; try lia; repeat split; auto.
    -- now apply RE.valid_update_spec.
    -- now apply RE.valid_find_spec with (lb := V⁺) in H as [_ H].
  (* fT_wh *)
  - rewrite RE.new_key_wh_spec in *. 
    inversion Hvt; subst; clear Hvt.
    destruct IHfT as [HvV1 [Hvst' [Hvt'' [HvW Hlt]]]]; auto; fold Term.valid in *. 
    + apply RE.valid_wh_spec; auto; constructor.
    + replace (S (S (V⁺))) with ((V⁺) + 2) by lia.
      now apply Term.shift_preserves_valid_1.
    + do 3 (split; auto); split; try lia.
      apply Stock.valid_add_spec; eauto.
      ++ unfold Resource.valid; lia.
      ++ apply Term.shift_preserves_valid_2; auto; lia.
Qed.

(** *** Preservation of environment's keys through the functional transition 
 
  Suppose a functional transition (1), we state that all keys in [V] are in [V1], i.e. we do not forget keys during the transition.
*)
Lemma functional_preserves_keys (V V1 : 𝐕) (W : 𝐖) (sv sv' sf sf' : Λ) :
  
       (* (1) *) ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ ->
  (* ---------------------------------------------------------- *)
             (forall (r : resource), r ∈ V -> r ∈ V1).
Proof.
  intro fT; induction fT; intros (* HvV Hvsv Hvsf *) r' HInV; auto.
  (* fT_rsf *)
  - destruct (Resource.eq_dec r r'); subst; apply RE.add_in_iff; auto.
  (* fT_wh *)
  - apply IHfT.
    do 2 rewrite RE.add_in_iff.
    do 2 right.
    now rewrite RE.shift_in_new_key.
Qed.

(** *** Consistency between V and W 

  Suppose a functional transition (1), we prove that all local resource names stored in [W] during the functional transition are new regards of the input resource environment [V] and are in the output resource environment [V1].
*)
Lemma consistency_V_W (V V1 : 𝐕) (W : 𝐖) (sv sv' sf sf' : Λ) :

       (* (1) *) ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ ->
  (* ----------------------------------------------------------- *)
       (forall (r : resource), (r ∈ W)%sk -> r ∉ V /\ r ∈ V1).
Proof.
  intro fT; induction fT; auto.
  (* fT_arr *)
  - intros r HIn; apply Stock.empty_in_spec in HIn; contradiction.
  (* fT_comp *)
  - intros r HIn.
    apply Stock.union_spec in HIn as [HIn | HIn].
    -- apply Stock.shift_in_e_spec in HIn as H.
       destruct H as [r' Heq]; subst.
       rewrite <- Stock.shift_in_iff in HIn.
       apply IHfT1 in HIn as [HnInV HInV1].
       apply RE.Ext.new_key_in_spec in HInV1 as Hlt.
       rewrite (Resource.shift_valid_refl (V1⁺) (V2⁺ - V1⁺) r'); auto.
       split; auto.
       eapply functional_preserves_keys; eauto.
    -- apply IHfT2 in HIn as [HnInV1 HnInv2]; auto.
       split; auto; intro HIn.
       eapply functional_preserves_keys in HIn; eauto.
  (* fT_rsf *)
  - intros r' HIn; apply Stock.empty_in_spec in HIn; contradiction.
  (* fT_wh *)
  - intros rf HIn.
    apply Stock.add_spec in HIn as [Heq | [Heq | HIn]]; subst; split;
    try (apply RE.Ext.new_key_notin_spec; lia).
    -- eapply functional_preserves_keys; eauto; try rewrite RE.new_key_wh_spec; auto.
       repeat rewrite RE.add_in_iff; auto.
    -- eapply functional_preserves_keys; eauto; try rewrite RE.new_key_wh_spec; auto.
       repeat rewrite RE.add_in_iff; auto.
    -- eapply IHfT in HIn as [HnIn HIn]; eauto.
       intro c; apply HnIn; repeat rewrite RE.add_in_iff; repeat right.
       now rewrite RE.shift_in_new_key.
    -- eapply IHfT in HIn as [HnIn HIn]; eauto. 
Qed.

(** *** Well-formed stock

  Suppose a functional transition (1), we prove that a stock cannot contains the same key in its both components, i.e. the set of resource names which represent reading interactions does not overlap with the set of resource names which represent writing interactions.
*)
Lemma W_well_formed (V V1 : 𝐕) (W : 𝐖) (st st' sf sf' : Λ) :
 
            (* (1) *) ⪡ V ; st ; sf ⪢ ⭆ ⪡ V1 ; st' ; sf' ; W ⪢ ->
  (* -------------------------------------------------------------------  *)
       (forall r, (r ∈ W)%sk -> ((r ∈ (fst W))%rk /\ r ∉ (snd W))%s \/ 
                                ((r ∉ (fst W))%rk /\ r ∈ (snd W)))%s.
Proof.
  intro fT; induction fT; auto; intros r' HIn; 
  try (apply Stock.empty_in_spec in HIn; contradiction). 
  
  - move r' before W'.

    apply Stock.union_spec in HIn as [HInW | HInW'].
    -- destruct W as [Rw Ww];
       destruct HInW as [HInRw | HInWw]; simpl in *.
       + left; split; try now rewrite ReaderStock.extend_in_iff; left.
         intro HIn. apply RS.union_spec in HIn as [HInWw | HInWw].
         ++ apply ReaderStock.shift_in_e_spec in HInRw as H.
            destruct H as [r1 Heq]; subst.
            rewrite <- ReaderStock.shift_in_iff in HInRw.
            rewrite <- Resources.shift_in_iff in HInWw.
            assert (HInW : (r1 ∈ (Rw, Ww))%sk) by (red; auto).
            apply IHfT1 in HInW as [[] | []]; auto.
         ++ destruct W' as [Rw' Ww']; simpl in *. 
            apply ReaderStock.shift_in_e_spec in HInRw as H.
            destruct H as [r1 Heq]; subst.
            rewrite <- ReaderStock.shift_in_iff in HInRw.
            assert (HInW : (r1 ∈ (Rw, Ww))%sk) by (red; auto).
            eapply consistency_V_W in fT1 as H; eauto.
            destruct H as [HnInV HInV1].
            apply RE.Ext.new_key_in_spec in HInV1 as Hlt.
            rewrite (Resource.shift_valid_refl (V1⁺) (V2⁺ - V1⁺) r1) in HInWw; auto.
            apply IHfT1 in HInW as [[_ HnInWw] | []]; auto.
            assert (HInW : (r1 ∈ (Rw', Ww'))%sk) by (red; auto).
            apply IHfT2 in HInW as [[] | [HnInRw' _]]; auto.
            eapply consistency_V_W with (r := r1) in fT2 as [HnInV1 HInV2]; eauto.
            red; auto.
       + right; split; try (rewrite RS.union_spec; now left).
         intro HIn; apply ReaderStock.extend_in_iff in HIn as [HInRw | HInRw].
         ++ apply ReaderStock.shift_in_e_spec in HInRw as H.
            destruct H as [r1 Heq]; subst.
            rewrite <- ReaderStock.shift_in_iff in HInRw.
            rewrite <- Resources.shift_in_iff in HInWw.
            assert (HInW : (r1 ∈ (Rw, Ww))%sk) by (red; auto).
            apply IHfT1 in HInW as [[] | []]; auto.
         ++ destruct W' as [Rw' Ww']; simpl in *. 
            apply Resources.shift_in_e_spec in HInWw as [r1 [Heq HInWw]]; subst.
            rewrite <- Resources.shift_in_iff in HInWw.
            assert (HInW : (r1 ∈ (Rw, Ww))%sk) by (red; auto).
            eapply consistency_V_W in fT1 as H; eauto.
            destruct H as [HnInV HInV1].
            apply RE.Ext.new_key_in_spec in HInV1 as Hlt.
            rewrite (Resource.shift_valid_refl (V1⁺) (V2⁺ - V1⁺) r1) in HInRw; auto.
            apply IHfT1 in HInW as [[_ HnInWw] | []]; auto.
            assert (HInW : (r1 ∈ (Rw', Ww'))%sk) by (red; auto).
            apply IHfT2 in HInW as [[] | [HnInRw' _]]; auto.
            eapply consistency_V_W with (r := r1) in fT2 as [HnInV1 HInV2]; eauto.
            red; auto.
    -- destruct HInW' as [HInRw' | HInWw']; 
       destruct W as [Rw Ww]; simpl in *. 
       + left; split; try (rewrite ReaderStock.extend_in_iff; now right).
         intro HIn; apply RS.union_spec in HIn as [HInWw | HInWw].
         ++ apply Resources.shift_in_e_spec in HInWw as [r1 [Heq HInWw]]; subst.
            rewrite <- Resources.shift_in_iff in HInWw.
            assert (HInW : (r1 ∈ (Rw, Ww))%sk) by (red; auto).
            eapply consistency_V_W in fT1 as H; eauto.
            destruct H as [HnInV HInV1].
            apply RE.Ext.new_key_in_spec in HInV1 as Hlt.
            rewrite (Resource.shift_valid_refl (V1⁺) (V2⁺ - V1⁺) r1) in HInRw'; auto.
            destruct W' as [Rw' Ww']; simpl in *. 
            apply IHfT1 in HInW as [[] | [HnInRw _]]; auto.
            assert (HInW : (r1 ∈ (Rw', Ww'))%sk) by (red; auto).
            apply IHfT2 in HInW as [[_ HnInWw'] | []]; auto.
            eapply consistency_V_W with (r := r1) in fT2 as [HnInV1 HInV2]; eauto.
            red; auto.
         ++ destruct W' as [Rw' Ww']; simpl in *.  
            assert (HInW : (r' ∈ (Rw', Ww'))%sk) by (red; auto).
            apply IHfT2 in HInW as [[_ HnInWw'] | []]; auto.
       + right; split; try (rewrite RS.union_spec; now right).
         destruct W' as [Rw' Ww']; simpl in *.
         intro HIn; apply ReaderStock.extend_in_iff in HIn as [HInRw | HInRw'].
         ++ apply ReaderStock.shift_in_e_spec in HInRw as H; subst.
            destruct H as [r1 Heq]; subst.
            rewrite <- ReaderStock.shift_in_iff in HInRw.
            assert (HInW : (r1 ∈ (Rw, Ww))%sk) by (red; auto).
            eapply consistency_V_W in fT1 as H; eauto.
            destruct H as [HnInV HInV1].
            apply RE.Ext.new_key_in_spec in HInV1 as Hlt.
            rewrite (Resource.shift_valid_refl (V1⁺) (V2⁺ - V1⁺) r1) in HInWw'; auto.
            apply consistency_V_W with (r := r1) in fT2 as [HnInV1 _]; auto; try (red; auto).
         ++ assert (HInW : (r' ∈ (Rw', Ww'))%sk) by (red; auto).
            apply IHfT2 with (r := r') in HInW  as [[] | []]; auto; try (red; auto).
  (* fT_wh *)
  - destruct W as [Rw Ww]; simpl in HIn; simpl; destruct HIn as [HInRw | HInWw].
    -- left; split; auto.
       rewrite RS.add_spec; intros [| HIn]; subst.
       + apply ReaderStock.add_in_iff in HInRw as [| HInRw]; try lia.
         apply consistency_V_W with (r := (S (V⁺))) in fT as [HnIn _]; try (red;auto).
         apply HnIn; repeat rewrite RE.add_in_iff; now left.
       + apply ReaderStock.add_in_iff in HInRw as [| HInRw]; try lia; subst.
         ++ apply consistency_V_W with (r := V⁺) in fT as [HnIn _]; try (red; auto).
            apply HnIn. repeat rewrite RE.add_in_iff; right; now left.
         ++ simpl in *. 
            assert (HInW : (r' ∈ (Rw, Ww))%sk) by (red; auto).
            apply IHfT with (r := r') in HInW as [[] | []]; auto.
    -- right; split; auto. 
       apply RS.add_spec in HInWw as [Heq | HInWw]; subst.
       + intro HInRw; apply ReaderStock.add_in_iff in HInRw as [| HInRw]; try lia.
         apply consistency_V_W with (r := S (V⁺)) in fT as [HnIn _]; try (red; auto).
         apply HnIn. repeat rewrite RE.add_in_iff; now left.
       + intro HInRw; apply ReaderStock.add_in_iff in HInRw as [| HInRw]; subst.
         ++ apply consistency_V_W with (r := V⁺) in fT as [HnIn _]; try (red; auto).
            apply HnIn. repeat rewrite RE.add_in_iff; right; now left.
         ++ simpl in *. 
            assert (HInW : (r' ∈ (Rw, Ww))%sk) by (red; auto).
            apply IHfT with (r := r') in HInW as [[] | []]; auto.
Qed.

Hypothesis all_arrow_halting : forall Re t α β,
  ∅%vc ⋅ Re ⊢ arr(t) ∈ (α ⟿ β ∣ ∅%s) -> forall v, ∅%vc ⋅ Re ⊢ v ∈ α -> halts (Re⁺)%rc <[t v]>.

(** *** Typing preservation through functional transition

  Suppose well-typed expression [sv], [sf], that halt, under [Re] (1,2,4,5). In addition, suppose that [V] halts (3) and is well-formed regards of [Re] (7). If there is a transition (6), then we can prove the following properties:
  - each data mapped with a resource name present in [R] has to be unused in [V] (8);
  - each data mapped with a resource name not present in [R'] but present in [V] 
    has to be unchanged in [V1] (9);
  - we can found a context [Re1] and a resource set [R'] such as :
    - the resource context [Re] is a subset of [Re1] (10);
    - the resources set [R] is a subset of [R'] (11);
    - [Re1] and [V1] are well-formed (12); 
    - all term stored in [W] are well typed regards of the new context [Re1] (13);
    - all new resources names in [R'] are stored in [W] and is not in [V] (14); 
    - each data mapped with a resource name present in [R'] has to be used in [V1] (15);
    - the output term [sv'] is well typed under [Re1] (16);
    - the term [sf'] is well typed under [Re1] (17);
    - terms [sf'] and [sv'] halts (18,19);
    - each term in [V1] halts (20).
*)
Theorem functional_preserves_typing_gen (Re : ℜ) (V V1 : 𝐕) (W : 𝐖) (sv sv' sf sf' : Λ) 
                                                                      (α β : Τ) (R : resources) :

                 (* (1) *) halts (Re⁺)%rc sf -> (* (2) *) halts (Re⁺)%rc sv -> 
                                (* (3) *) RE.halts (Re⁺)%rc V -> 

           (* (4) *) ∅%vc ⋅ Re ⊢ sf ∈ (α ⟿ β ∣ R) -> (* (5) *) ∅%vc ⋅ Re ⊢ sv ∈ α -> 
          (* (6) *) ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ -> (* (7) *) WF(Re,V) ->
  (* ------------------------------------------------------------------------------------------- *)
       (* (8) *)(forall (r : resource), (r ∈ R)%s -> RE.unused r V) /\
       (* (9) *)(forall (r : resource), (r ∉ R)%s /\ (r ∈ V) -> 
                                                ([⧐ (V⁺) – ((V1⁺) - (V⁺))] V) ⌊r⌋ = V1 ⌊r⌋) /\

       exists (Re1 : ℜ) (R' : resources), 

          (* (10) *) (Re ⊆ Re1)%rc /\ (* (11) *) (R ⊆ R')%s /\
          (* (12) *) WF(Re1,V1) /\
          (* (13) *) (forall (r : resource) (v : Λ) (α β : Τ), 
                                    W⌊r⌋%sk = Some v -> Re1⌊r⌋%rc = Some (β,α) -> 
                                                                        ∅%vc ⋅ Re1 ⊢ v ∈ α) /\
          (* (14) *) (forall (r : resource), (r ∈ (R' \ R))%s -> (r ∈ W)%sk /\ (r ∉ V)) /\
          (* (15) *) (forall (r : resource), (r ∈ R')%s -> RE.used r V1) /\
    
          (* (16) *) ∅%vc ⋅ Re1 ⊢ sv' ∈ β /\ (* (17) *) ∅%vc ⋅ Re1 ⊢ sf' ∈ (α ⟿ β ∣ R') /\
    
          (* (18) *) halts (Re1⁺)%rc sf' /\ (* (19) *) halts (Re1⁺)%rc sv' /\ 
          (* (20) *) RE.halts (Re1⁺)%rc V1 /\ (* (21) *) Stock.halts (Re1⁺)%rc W.
Proof.
  intros Hlsf Hlsv HltV Hwsf Hwsv fT; revert Re R α β Hlsf Hlsv HltV Hwsf Hwsv.
  induction fT; intros Re R γ β Hlsf Hlsv HlV Hwsf Hwsv Hwf;

  apply WF_ec_valid in Hwf as HvRe; destruct HvRe as [HvRe HvV];
  apply WF_ec_new in Hwf as Hnew;
  
  move HvRe before Hwf; move HvV before HvRe; move Hnew before Hwf.
  (* fT_eT_sf *)
  - 
    (* clean *)
    move Re before W; move R before Re; move γ before R; move β before γ; move fT after IHfT;
    rename fT into HfT; rename H into HeT; move HeT after HfT; clear all_arrow_halting.
    (* clean *)

    rewrite <- Hnew in HeT.
    apply evaluate_preserves_typing with (t' := t') in Hwsf as Hwsf'; auto.
    
    (* clean *)
    clear Hwsf HvRe; move Hwsf' after Hwsv.
    (* clean *)

    apply IHfT; auto.
    now rewrite <- evaluate_preserves_halting with (t := t).
  (* fT_eT_sv *)
  - 
    (* clean *)
    move Re before W; move R before Re; move γ before R; move β before γ; move fT after IHfT;
    rename fT into HfT; rename H into HeT; move HeT after HfT.
    (* clean *)

    rewrite <- Hnew in HeT. 
    apply evaluate_preserves_typing with (t' := st') in Hwsv as Hwsv'; auto. 
    
    (* clean *)
    clear HvRe; move Hwsv' after Hwsv.
    (* clean *)

    apply IHfT; auto. 
    now rewrite <- evaluate_preserves_halting with (t := st).
  (* fT_arr *)
  - 
    (* clean *)
    inversion Hwsf; subst; rename H3 into Hwt; clear Hwsf; move Hwt after Hwsv.
    (* clean *)

    repeat split.
    -- intros r HIn; inversion HIn.
    -- intros r [HnIn HIn]; replace (V⁺ - V⁺) with 0 by lia.
        now rewrite RE.shift_zero_refl.
    -- exists Re; exists ∅%s. repeat (split; try now auto).
        + apply wt_app with (α := γ); assumption.
        + eapply all_arrow_halting with (β := β); eauto. 
  (* fT_first *)
  -
    (* clean *)
    inversion Hwsf; subst; move Re before W; move R before Re. move α0 before α;
    move β0 before α0; clear Hwsf; rename H4 into Hwt; rename H6 into Hvτ;
    move Hwt after Hwsv; move Hvτ before Hwsv. rename fT into HfT;  move HfT after IHfT;
    inversion Hwsv; subst; rename H4 into Hwv1; rename H6 into Hwv2; move Hwv1 before Hwt;
    move Hwv2 before Hwv1; clear Hwsv; move HvRe after Hvτ; move HvV after HvRe.
    rename α0 into γ; rename β0 into β.
    (* clean *)

    rewrite halts_first in Hlsf; apply halts_pair in Hlsv as [Hlv1 Hlv2].
    apply IHfT with (R := R) (β := β) in Hwv1 as IH; auto; clear IHfT.

    
    destruct IH as [Hunsd [Hlcl [Re' [R' [HSubRe [HSubR [Hwf' 
                          [HwtW [HInW [Husd [Hwv1' [Hwt' [Hlt' [Hlv1' [HlV1 HlW]]]]]]]]]]]]]]].

    (* clean *)
    move Re' before Re; move R' before R; move Hwv1' before Hwv1; clear Hwv1;
    move Hwt' before Hwt; clear Hwt; move Hwf' before Hwf; move Hunsd before Husd.
    move Hlt' before Hlsf; move Hlv1' before Hlv1; move HlV1 before HlV; 
    move Hlcl after HSubR; move HlW before HlV1.
    (* clean *)

    apply WF_ec_new in Hwf' as Hnew'; move Hnew' before Hnew.

    repeat (split; try now auto).
    exists Re'; exists R'; repeat (split; try now auto).
    -- constructor; auto; rewrite <- Hnew, <- Hnew'.
       apply weakening_ℜ; auto.
    -- apply wt_first; auto.
       apply Typ.valid_weakening with (k := (Re⁺)%rc); auto.
       now apply RC.Ext.new_key_Submap_spec in HSubRe.
    -- now apply halts_first.
    -- apply halts_pair; split; auto. 
       rewrite <- Hnew, <- Hnew'.
       apply halts_weakening; auto. 
       now apply RC.Ext.new_key_Submap_spec in HSubRe.

  (* fT_comp *)
  -
    (* clean *)
    inversion Hwsf; subst; apply Resources.eq_leibniz in H7; subst;
    clear Hwsf; move Re before W'; move R1 before Re; move R2 before R1; 
    move γ before R2; move β before γ; move γ before β; rename fT1 into HfT1;
    move HfT1 after IHfT2; rename fT2 into HfT2; move HfT2 after HfT1.
    rename H6 into Hwt1; rename H8 into Hwt2; rename H9 into HEmp.
    move Hwt1 after Hwsv; move Hwt2 before Hwt1.
    (* clean *)

    apply halts_comp in Hlsf as [Hlt1 Hlt2].
    apply IHfT1 with (R := R1) (β := τ) in Hwsv as IH1; auto;
    try (intros; apply Hunsd; rewrite RS.union_spec; now left).
    clear IHfT1; 
    destruct IH1 as [Hunsd1 [Hlcl1 [Re' [R1' [HSubRe [HSubR1 [Hwf' 
                    [HwtW [HInW [Husd1 [Hwsv' [Hwt1' [Hlt1' [Hlst' [HlV1 HlW1]]]]]]]]]]]]]]].

    (* clean *)
    move Re' before Re; move R1' before R1; move Hwsv' before Hwsv;
    move Hwt1' before Hwt1; move Hunsd1 after HInW; move Hwf' before Hwf;
    move Hlt1' before Hlt1; move Hlst' before Hlsv; move HlV1 before HlV.
    move HlW1 before HlV1.
    (* clean *)

    apply WF_ec_new in Hwf' as Hnew'; move Hnew' before Hnew.
    apply IHfT2 with (R := R2) (β := β) in Hwsv' as IH2; auto.

    -- destruct IH2 as [Hunsd2 [Hlcl2 [Re'' [R2' [HSubRe' [HSubR2 
                       [Hwf'' [HwtW' [HInW'  [Husd2 [Hwsv'' [Hwt2' [Hlt2' 
                       [Hlst'' [HlV2 HlW2]]]]]]]]]]]]]]].

       (* clean *)
       move Re'' before Re'; move R2' before R2; move Hwsv'' before Hwsv';
       move Hwt2' before Hwt2; move Hunsd2 before Hunsd1; move Hwf'' before Hwf';
       clear IHfT2; move HSubRe' before HSubRe; move HSubR2 before HSubR1; move HInW' before HInW;
       move Husd2 before Husd1; move Hlcl2 before Hlcl1; move Hlt2' before Hlt2; 
       move Hlst'' before Hlst'; move HlV2 before HlV1; move HlW2 before HlW1.
       (* clean *)

       apply WF_ec_new in Hwf'' as Hnew''; move Hnew'' before Hnew'.
       assert (HEmp' : (∅ = R1' ∩ R2')%s).
      {
        symmetry; apply RS.empty_is_empty_1; unfold RS.Empty.
        intros r' HIn; apply RS.inter_spec in HIn as [HIn1 HIn2].
        destruct (RS.In_dec r' R1) as [HInR1 | HnInR1]; 
        destruct (RS.In_dec r' R2) as [HInR2 | HnInR2].
        - symmetry in HEmp; apply RS.empty_is_empty_2 in HEmp.
          apply (HEmp r'). apply RS.inter_spec; split; auto.
        - destruct (HInW' r') as [_ HnInV1]; try (rewrite RS.diff_spec; split; auto).
          assert (HInV1 : r' ∈ V).
          { 
            apply Hunsd1 in HInR1.
            apply RE.unused_find_e_spec in HInR1 as [v Hfi]. 
            exists (⩽ v … ⩾); now apply RE.find_2. 
          }
          apply (functional_preserves_keys V V1 W st st' t1 t1') in HInV1; auto.
            
        - assert (HInV1 : r' ∈ V).
          { 
            rewrite <- (WF_ec_In Re V Hwf r'). 
            destruct Hlt2 as [v2 [HmeT Hvv2]]. 
            apply multi_preserves_typing with (t' := v2) in Hwt2; auto.
            eapply typing_Re_R; eauto.
          }

          revert HInV1; apply HInW; rewrite RS.diff_spec; split; assumption.

        - destruct (HInW r') as [HInW1 HnInV]; try (rewrite RS.diff_spec; now split).
          destruct (HInW' r') as [_ HnInV1]; try (rewrite RS.diff_spec; now split).

          apply consistency_V_W with (r := r') in HfT1 as [_ Hc]; auto.
        }

        move HEmp' before HEmp. repeat split.
        + intros r HIn; apply RS.union_spec in HIn as [HInR1 | HInR2]; auto.
          destruct Hlt2 as [v2 [HmeT Hvv2]]; 
          apply multi_preserves_typing with (t' := v2) in Hwt2; auto.
          eapply typing_Re_R in HInR2 as HInRe; eauto.
          rewrite (WF_ec_In Re V Hwf r) in HInRe; destruct HInRe as [v HfV];
          apply RE.find_1 in HfV; destruct v.
          ++ apply (RE.unused_find_spec _ λ _ HfV).
          ++ apply Hunsd2 in HInR2 as HunsdV1. 
             apply RE.shift_find_iff with (lb := V⁺) (k := V1⁺ - V⁺) in HfV as HfV'.
             rewrite Resource.shift_valid_refl in HfV'.
             * rewrite Hlcl1 in HfV'.
               ** unfold RE.unused in HunsdV1. 
                  rewrite HfV' in HunsdV1; simpl in *; contradiction.
               ** split.
                  {
                    intro. symmetry in HEmp; apply RS.empty_is_empty_2 in HEmp; 
                    apply (HEmp r); rewrite RS.inter_spec; now split.
                  }
                  { exists (⩽ … λ ⩾); now apply RE.find_2.  }
             * apply RE.valid_in_spec with (m := V); auto. 
               exists (⩽ … λ ⩾); now apply RE.find_2.
        + intros r [HnInR HInV]. 
          apply RS.union_notin_spec in HnInR as [HnInR1 HnInR2].
          apply functional_preserves_keys with (r := r) in HfT1 as HInV1; auto;
          try (now rewrite <- Hnew).
          apply RE.Ext.new_key_in_spec in HInV as Hvr. 
          apply RE.Ext.new_key_in_spec in HInV1 as Hvr1. 
          rewrite <- (RE.shift_unfold_1 _ (V1⁺)).
          ++ rewrite <- Hlcl2; try (now split).
             apply RE.shift_find_valid_spec; auto.
             rewrite <- (Resource.shift_valid_refl (V⁺) (V1⁺ - V⁺) r); auto.
             now rewrite <- RE.shift_in_iff.
          ++ rewrite <- Hnew, <- Hnew'.
             now apply RC.Ext.new_key_Submap_spec.
          ++ rewrite <- Hnew', <- Hnew''. 
             now apply RC.Ext.new_key_Submap_spec.
        + exists Re''; exists (R1' ∪ R2')%rs; 
          repeat (split; try now auto; try (now transitivity Re')).
          ++ intros r HIn. 
             rewrite RS.union_spec in *; destruct HIn as [HIn | HIn]; auto.
          ++ intros r v α τ1 Hfi HfiRe.

            (* clean *)
            move r before α; move τ1 before α; move β before α; move v before t2'.
            (* clean *)
            
            apply Stock.union_find_spec in Hfi; destruct Hfi.
            * apply ReaderStock.shift_find_e_spec_1 in H as HI.
              destruct HI as [[r' Heq] [v' Heqv]]; subst.
              rewrite <- Hnew''; rewrite <- Hnew'; apply weakening_ℜ; auto.
              ** apply (WF_ec_valid Re' V1 Hwf').
              ** apply ReaderStock.shift_find_iff in H. 
                 apply (HwtW _ _ α τ1) in H; auto.
                 assert (r' ∈ W)%sk. 
                 { unfold Stock.In; left. exists v'; now apply ReaderStock.find_2. }

                 apply consistency_V_W with (r := r') in HfT1 as [_ HInV1]; auto.
                 apply (WF_ec_In Re' V1 Hwf' r') in HInV1 as HInRe'.
                 apply RE.Ext.new_key_in_spec in HInV1 as Hvr'. 
                 rewrite Resource.shift_valid_refl in HfiRe; auto.
                 destruct HInRe' as [v HfRe']; apply RC.find_1 in HfRe'.
                 apply RC.Submap_find_spec with (m' := Re'') in HfRe' as HfRe''; auto.
                 rewrite HfRe'' in HfiRe; inversion HfiRe; now subst.
            * apply (HwtW' r _ _ τ1); auto.
          ++ apply RS.diff_spec in H as [HIn HnIn]. 
             apply RS.union_notin_spec in HnIn as [HnInR1 HnInR2].
             apply RS.union_spec in HIn as [HInR1' | HInR2'].
             * destruct (HInW r) as [HInW1 HnInV]; try (apply RS.diff_spec; split; auto).
               apply Stock.union_spec; left.
               apply consistency_V_W with (r := r) in HfT1 as [_ HInV1]; auto.
              apply RE.Ext.new_key_in_spec in HInV1 as Hvr'. 
               rewrite <- (Resource.shift_valid_refl (V1⁺) (V2⁺ - V1⁺) r); auto.
               now apply Stock.shift_in_iff.
             * destruct (HInW' r) as [HInW1 HnInV]; try (apply RS.diff_spec; split; auto).
               apply Stock.union_spec; now right.
          ++ apply RS.diff_spec in H as [HIn HnIn]. 
             apply RS.union_notin_spec in HnIn as [HnInR1 HnInR2].
             apply RS.union_spec in HIn as [HInR1' | HInR2'].
             * destruct (HInW r) as [HInW1 HnInV]; 
               try (apply RS.diff_spec; split; auto); assumption.
             * intro HInV. apply functional_preserves_keys with (r := r) in HfT1; auto;
               try (now rewrite <- Hnew). revert HfT1.
               apply (HInW' r); apply RS.diff_spec; split; assumption.
          ++ intros r HIn; apply RS.union_spec in HIn as [HInR1' | HInR2']; auto.
             apply Husd1 in HInR1' as HI.
             apply RE.used_find_e_spec in HI as [v HfV1].

             assert (HI : (r ∉ R2')%s /\ r ∈ V1). 
             { 
              split. 
              - intro. symmetry in HEmp'; apply RS.empty_is_empty_2 in HEmp'; 
                apply (HEmp' r); rewrite RS.inter_spec; split; auto.
              - apply RE.in_find. intro c; rewrite HfV1 in c; inversion c.
             }
             destruct HI as [HnInR2' HInV1].
             apply RE.Ext.new_key_in_spec in HInV1 as Hvr'. 
             apply (RE.shift_find_iff (V1⁺) (V2⁺ - V1⁺)) in HfV1 as HfshV1.
             simpl in *. rewrite Resource.shift_valid_refl in HfshV1; auto.
             rewrite Hlcl2 in HfshV1; auto.
             now apply RE.used_find_spec in HfshV1.
          ++ rewrite <- Hnew', <- Hnew''. 
             apply wt_comp with (R1 := R1') (R2 := R2') (τ := τ); auto; try reflexivity.
             apply weakening_ℜ; auto. apply (WF_ec_valid Re' V1 Hwf').
          ++ rewrite <- Hnew', <- Hnew''. 
             apply halts_comp; split; auto.
             apply halts_weakening; auto. 
             now apply RC.Ext.new_key_Submap_spec.
          ++ apply Stock.halts_union_spec; split; auto.
             rewrite <- (WF_ec_new Re'' V2); auto.
             rewrite <- (WF_ec_new Re' V1); auto.
             apply Stock.halts_weakening; auto.
             now apply RC.Ext.new_key_Submap_spec.
    -- rewrite <- Hnew, <- Hnew'; apply halts_weakening; auto.
       apply RC.Ext.new_key_Submap_spec in HSubRe; assumption.
    -- rewrite <- Hnew, <- Hnew'; apply weakening_ℜ; auto.
  (* fT_rsf *)
  -
    (* clean *)
    inversion Hwsf; subst. clear Hwsf; move Re before V; rename H into HfV; 
    rename H4 into HfRe; move HfV after HfRe. 
    (* clean *)

    repeat split.
    -- intros r' HIn; rewrite RS.singleton_spec in HIn; subst.
       now apply RE.unused_find_spec in HfV.
    -- intros r' [HnIn HIn]; apply RS.singleton_notin_spec in HnIn.
        rewrite RE.add_neq_o; auto. 
        rewrite RE.Ext.new_key_add_in_spec.
        + replace (V⁺ - V⁺) with 0 by lia; now rewrite RE.shift_zero_refl.
        + exists (⩽ v … ⩾); now apply RE.find_2.
    -- exists Re; exists \{{r}}; split; try reflexivity; auto; 
       repeat (split; try now auto).
       + intros. rewrite (WF_ec_In Re V) in H; auto.
         rewrite RE.add_in_iff; now right.
       + intros HIn. apply RE.add_in_iff in HIn as [Heq | HIn]; subst.
         ++ exists (γ,β); now apply RC.find_2.
         ++ now rewrite (WF_ec_In Re V).
       + apply RE.valid_find_spec with (lb := V⁺) in HfV as Hv; auto.
         destruct Hv as [Hvr Hvv].
         rewrite RE.Ext.new_key_add_in_spec.
         ++ apply RE.valid_add_spec; repeat split; auto.
            unfold Cell.valid; simpl. 
            rewrite <- (WF_ec_new Re V); auto.
            apply well_typed_implies_valid in Hwsv as [Hwst _]; auto.
         ++ exists (⩽ v … ⩾); now apply RE.find_2.
       + intros r1 α τ v1 HfRe1 HfV1.
         destruct (Resource.eq_dec r r1); subst.
         ++ rewrite RE.add_eq_o in *; auto. 
            inversion HfV1; subst; clear HfV1.
            rewrite HfRe in HfRe1; inversion HfRe1; now subst.
         ++ rewrite RE.add_neq_o in HfV1; auto.
            now apply (WF_ec_well_typed Re V Hwf r1).
       + rename H into HIn; apply RS.diff_spec in HIn as [HIn HnIn]; contradiction.
       + rename H into HIn; apply RS.diff_spec in HIn as [HIn HnIn]; contradiction.
       + intros r' HIn; apply RS.singleton_spec in HIn; subst; unfold RE.used.
         rewrite RE.add_eq_o; simpl; auto.
       + apply WF_ec_well_typed with (V := V) (v := ⩽ v … ⩾) in HfRe; try assumption.
       + unfold RE.halts in *; apply HlV in HfV; now simpl in *.
       + apply RE.halts_add_spec; split; simpl; auto.
  (* fT_wh *)
  -
    (* clean *)
    inversion Hwsf; subst; move Re before W; move R before Re; move R' before R.
    move τ before R'; move γ before τ; move β before γ; rename H6 into Heq; rename H7 into Hvγ; 
    rename H8 into Hvβ; rename H9 into Hwi; rename H10 into Hwt;
    move Hwt after Hwsv; move Hwi after Hwt.
    (* clean *)

    apply halts_wh in Hlsf as [Hli Hlt].
    apply weakening_ℜ_wh with (α := τ) (β := <[𝟙]>) in Hwsv as Hwsv'; auto.

    apply IHfT in Hwt as IH; clear IHfT.
    -- destruct IH as [Hunsd [Hlcl [Re1 [R1 [HSubRe1 [HSubR [Hwf' 
                      [HwtW [HInW  [Husd [Hwst' [Hwt' [Hlt' [Hlst' [HlV1 HlW]]]]]]]]]]]]]]].
       repeat split.

       + intros r HIn; rewrite Heq in HIn. 
         apply RS.diff_spec in HIn as [HInR' HnIn].
         repeat rewrite RS.add_notin_spec in HnIn; destruct HnIn as [Hneq [Hneq' _]].
         apply Hunsd in HInR' as HI; rewrite Hnew in Hneq, Hneq'.
         do 2 rewrite <- RE.unused_add_neq_spec in HI; auto.
         now rewrite RE.unused_shift_valid_spec in HI. 
       + intros r [HInR HInV]. 
         rewrite RE.new_key_wh_spec in *; rewrite <- Hlcl.
         ++ symmetry. do 2 rewrite RE.shift_add_spec; simpl.
            do 2 (try rewrite RE.add_neq_o).
            * replace (S (S (V⁺))) with ((V⁺) + 2) by lia. 
              rewrite <- RE.shift_unfold.
              replace (2 + (V1⁺ - (V⁺ + 2))) with (V1⁺ - V⁺); auto.
              apply functional_preserves_valid in fT; 
              try (rewrite RE.new_key_wh_spec in * ); try lia.
              ** apply RE.valid_wh_spec; auto; try constructor.
                 red; simpl.
                 apply well_typed_implies_valid in Hwi as [Hwi _]; auto.
                 now rewrite <- Hnew.
              ** replace (S (S (V ⁺))) with ((V⁺) + 2) by lia.
                 apply Term.shift_preserves_valid_1. 
                 rewrite <- Hnew.
                 apply well_typed_implies_valid in Hwsv as [Hvst _]; auto.
              ** apply well_typed_implies_valid in Hwi as [Hwi Hvτ]; auto. 
                 apply well_typed_implies_valid in Hwt as [Hwt _]; auto;
                 try now rewrite RC.new_key_wh_spec in Hwt; rewrite <- Hnew.
                 apply RC.valid_wh_full_spec; auto; split; simpl; try constructor; auto.
            * apply RE.Ext.new_key_in_spec in HInV. 
              unfold Resource.shift.
              destruct (Resource.leb_spec (S (S (V⁺))) (V⁺)); try lia.
            * apply RE.Ext.new_key_in_spec in HInV. 
              unfold Resource.shift.
              destruct (Resource.leb_spec (S (S (V⁺))) (S (V⁺))); try lia.
         ++ split.
            * rewrite Heq in HInR; 
              apply RS.diff_notin_spec in HInR as [HnIn | HIn]; auto.
              rewrite <- (WF_ec_In Re V) in HInV; auto.
              apply RC.Ext.new_key_in_spec in HInV. 
              do 2 rewrite RS.add_spec in HIn.
              destruct HIn as [Heq' | [Heq'| HIn]]; subst; try lia.
              inversion HIn.
            * repeat (rewrite RE.add_in_iff; right).
              now rewrite RE.valid_in_iff. 
       + exists Re1; exists R1; split.
         ++ now apply RC.Submap_wh_spec_1 in HSubRe1.
         ++ repeat (split; try now auto).
            * rewrite Heq; intro r. intros HIn.
              apply RS.diff_spec in HIn as [HIn _]. now apply HSubR.   
            * intros r v τ1 α HfW HfRe1.
              destruct W as [rW wW]; unfold Stock.find,Stock.add in *; simpl in *.
              rewrite ReaderStock.add_o in HfW; auto. 
              destruct (Resource.eq_dec (V⁺) r); subst.
              ** inversion HfW; subst; clear HfW. rewrite <- Hnew.
                 apply WF_ec_new in Hwf' as Hnew'; rewrite <- Hnew'.
                 apply weakening_ℜ; auto.
                 { now apply RC.Submap_wh_spec_1 in HSubRe1. }
                 {
                  apply (RC.Ext.Submap_find_spec _ _ (Re⁺)%rc (<[𝟙]>,τ)) in HSubRe1 as HfRe.
                  - rewrite Hnew in HfRe; rewrite HfRe1 in HfRe; inversion HfRe; now subst.
                  - rewrite RC.add_neq_o; try lia; rewrite RC.add_eq_o; auto.
                 }
              ** apply (HwtW r _ τ1 α); auto.
            * apply RS.diff_spec in H as [HInR1 HnInR]. 
              rewrite Heq in HnInR.
              apply RS.diff_notin_spec in HnInR as [HnInR' | HIn].
              ** destruct (HInW r); try (now apply RS.diff_spec).
                 apply Stock.add_spec; right; right; assumption.
              ** rewrite <- Hnew.
                 repeat rewrite RS.add_spec in HIn. 
                 destruct HIn as [Heq' | [Heq' | HIn]]; try (now inversion HIn); subst;
                 unfold Stock.In; simpl.
                 { left; apply ReaderStock.add_in_iff; now left. }
                 { right; apply RS.add_spec; now left. }
            * apply RS.diff_spec in H as [HInR1 HnInR]. rewrite Heq in HnInR.
              apply RS.diff_notin_spec in HnInR as [HnInR' | HIn].
              ** destruct (HInW r) as [_ HInsV]; try (apply RS.diff_spec; now split).
                 intro HInV; apply HInsV. repeat (rewrite RE.add_in_iff; right).
                 now rewrite RE.shift_in_new_key.
              ** rewrite Hnew in HIn. repeat rewrite RS.add_spec in HIn;
                 destruct HIn as [Heq' | [Heq' | HIn]]; try (inversion HIn); subst;
                 apply RE.Ext.new_key_notin_spec; auto.
            * apply Stock.halts_add_spec; split; auto.
              rewrite <- (WF_ec_new Re V); auto.
              rewrite <- (WF_ec_new Re1 V1); auto.
              apply halts_weakening; auto.
              apply RC.Ext.new_key_Submap_spec.
              now apply RC.Submap_wh_spec_1 in HSubRe1.
    -- now rewrite RC.new_key_wh_spec.
    -- rewrite RC.new_key_wh_spec; replace (S (S (Re⁺)%rc)) with ((Re⁺)%rc + 2) by lia.
       rewrite <- Hnew. 
       now apply halts_weakening_1.
    -- rewrite RC.new_key_wh_spec. 
       apply RE.halts_add_spec; split.
       + simpl; exists <[unit]>; split; auto; reflexivity.
       + apply RE.halts_add_spec; split.
         ++ replace (S (S (Re⁺)%rc)) with ((Re⁺)%rc + 2) by lia.
            rewrite <- Hnew. 
            apply halts_weakening_1; auto.
         ++ rewrite <- Hnew. 
            replace (S (S (Re⁺)%rc)) with ((Re⁺)%rc + 2) by lia.
            apply RE.halts_weakening_1; auto.
    -- rewrite <- Hnew. 
       apply weakening_ℜ_wh; auto.
    -- apply well_typed_implies_valid in Hwi as HI; auto.
       destruct HI as [Hvi Hvτ]; auto. 
       apply WF_ec_wh; auto.
Qed.

End preservation.

(** ---- *)

(** ** Progress - Functional *)
Section progress.

Hint Resolve VContext.valid_empty_spec Stock.valid_empty_spec Resources.valid_empty_spec : core.

Hypothesis all_arrow_halting : forall Re t α β,
  ∅%vc ⋅ Re ⊢ arr(t) ∈ (α ⟿ β ∣ ∅%s) -> forall v, ∅%vc ⋅ Re ⊢ v ∈ α -> halts (Re⁺)%rc <[t v]>.


Theorem progress_of_functional_value_gen (Re : ℜ) (m n : list nat) (V : 𝐕) (tv sf : Λ) (α β : Τ) (R : resources) :
  (* (1) *) value(sf) -> (* (2) *) halts (Re⁺)%rc tv -> (* (3) *) RE.halts (Re⁺)%rc V -> 

  (* (4) *) ∅%vc ⋅ Re ⊢ [⧐⧐ m – n] sf ∈ (α ⟿ β ∣ R) ->
  (* (5) *) ∅%vc ⋅ Re ⊢ tv ∈ α ->
  (* (6) *) WF(Re,V) ->
  (* (7) *)(forall (r : resource), (r ∈ R)%s -> RE.unused r V) ->

  exists (V1 : 𝐕) (tv' sf' : Λ) (W : 𝐖),
    ⪡ V ; tv ; [⧐⧐ m – n] sf ⪢ ⭆ ⪡ V1 ; tv' ; sf' ; W ⪢.
Proof.
  revert Re m n V tv α β R; induction sf;
  intros Re m n V tv τ1 τ1' R Hvalsf Hltv HlV Hwsf Hwtv Hwf Hunsd;
  inversion Hvalsf; subst.

  - rewrite Term.multi_shift_unit in *; inversion Hwsf.  
  - rewrite Term.multi_shift_abs in *. inversion Hwsf; subst.
  - rewrite Term.multi_shift_pair in *. inversion Hwsf; subst.
 
  - rewrite Term.multi_shift_arr in *. inversion Hwsf; subst.
    exists V; exists <[([⧐⧐ m – n] sf) tv]>; 
    exists <[arr([⧐⧐ m – n] sf)]>; exists (∅%sk).
    simpl. now constructor.
 
  - rewrite Term.multi_shift_first in *. inversion Hwsf; subst.
    destruct Hltv as [tv' [HmeT Hvtv']].
    apply multi_preserves_typing with (t' := tv') in Hwtv as Hwtv'; auto.
    -- inversion Hvtv'; subst; inversion Hwtv'; subst.
      apply (IHsf Re m n V v1 _ β R) in H9 as HfT; auto.
      + destruct HfT as [V1 [v1' [sf1 [W fT]]]].
        exists V1; exists <[⟨v1',[⧐ {V⁺} – {V1⁺ - V⁺}] v2⟩]>; 
        exists (Term.tm_first sf1); exists W.
        apply fT_MeT_sv with (st' := <[ ⟨ v1, v2 ⟩ ]>).
        ++ rewrite <- (WF_ec_new Re V); auto.
        ++ simpl. now constructor.
      + inversion Hvtv'; subst; exists v1; split; now auto.
    -- eapply WF_ec_valid; eauto.
  
  - rewrite Term.multi_shift_rsf in *; inversion Hwsf; subst.
    assert (RE.unused ([⧐⧐m – n] r)%r V).
    -- apply Hunsd. 
       now apply RS.singleton_spec.
    -- apply RE.unused_find_e_spec in H as [v Hfi].
  
       exists (⌈([⧐⧐ m – n] r)%r ⤆ ⩽ … tv ⩾ ⌉ V); exists v; 
       exists <[rsf[([⧐⧐ m – n] r)%r]]>; exists ∅%sk.
       now constructor.

  - rewrite Term.multi_shift_comp in *. inversion Hwsf; subst.
    apply (IHsf1 Re m n V tv τ1 τ R1) in Hwtv as HfT; auto.
    -- clear IHsf1; destruct HfT as [V1 [tv' [sf1' [W1 fT1]]]].
       apply functional_preserves_typing_gen
       with (Re := Re) (α := τ1) (β := τ) (R := R1) in fT1 as Hfpt; auto.
       + destruct Hfpt as 
         [Hunsd1 [HeqVV1 [Re1 [R1' [Hsub1 [HsubR1 [Hwf1 
        [HW1 [HW1' [Husd1 [Hwtv' [Hwsf1' [Hlsf1' [Hltv' [HlV1 HlW]]]]]]]]]]]]]]].
         apply weakening_ℜ with (Re1 := Re1) in H10 as Hwsf2bis; 
         auto; try (eapply (WF_ec_valid Re V); now auto).
         rewrite <- Term.multi_shift_cons in Hwsf2bis.

         apply (IHsf2 Re1 (Re⁺ :: m)%rc ((Re1⁺ - Re⁺) :: n)%rc V1 tv' τ τ1' R2) in Hwtv' as HfT; auto.
         ++ destruct HfT as [V2 [tv'' [sf2' [W2 fT2]]]].
            exists V2; exists tv'';
            exists <[([⧐ {V1⁺} – {V2⁺ - V1⁺}] sf1') >>> sf2']>;
            exists (([⧐ V1⁺ – (V2⁺ - V1⁺)] W1) ∪ W2)%sk.
            eapply fT_comp; eauto.
            rewrite <- (WF_ec_new Re1 V1); auto.
            rewrite <- (WF_ec_new Re V); auto.
         ++ intros.
            clear all_arrow_halting IHsf2.
            apply typing_Re_R with (r := r) in H10 as HInRe1; auto.
            * rewrite (WF_ec_In Re V) in HInRe1; auto.
              assert (r ∉ ∅)%s. { intro c. inversion c. }
              assert (r ∉ R1)%s. 
              { intro HInR1. apply H0. rewrite H11. rewrite RS.inter_spec; now split. }
              assert (RE.unused r V).
              { 
                apply Hunsd. 
                rewrite H9. 
                now rewrite RS.union_spec; right.
              }
              apply RE.unused_find_e_spec in H4 as [v Hfi].
              rewrite (RE.shift_find_iff (V⁺) (V1⁺ - V⁺)) in Hfi.
              apply RE.Ext.new_key_in_spec in HInRe1 as Hlt.
              rewrite Resource.shift_valid_refl in Hfi; auto.
              rewrite HeqVV1 in Hfi; auto. 
              apply RE.valid_in_spec with (lb := V⁺) in HInRe1 as HvV.
              ** now apply RE.unused_find_spec in Hfi.
              ** eapply (WF_ec_valid Re V); auto.
            * now apply Term.multi_shift_value_iff.
       + exists <[[⧐⧐ m – n] sf1]>; split; auto.
         ++ reflexivity.
         ++ now apply Term.multi_shift_value_iff.
    -- intros. apply Hunsd. rewrite H9.
       rewrite RS.union_spec; now left.

  - clear IHsf1. rewrite Term.multi_shift_wh in *; inversion Hwsf; subst.
    apply WF_ec_valid in Hwf as H; destruct H as [HvRe HvV].
    apply weakening_ℜ_wh with (β := τ) (α := <[ 𝟙 ]>) in Hwtv; auto.
    apply (IHsf2 _ m n
                  (⌈S (V⁺) ⤆ ⩽<[unit]> … ⩾⌉ (⌈V⁺ ⤆ ([⧐ V⁺ – 2] ⩽ ([⧐⧐ m – n] sf1) … ⩾)%cl⌉ 
                    ([⧐ V⁺ – 2] V)))
    ) with (β := τ1') (R := R') in Hwtv as HfT; auto. 
    -- destruct HfT as [V1 [tv' [sf' [W fT]]]]; clear IHsf2.
       exists V1; exists tv'; exists sf'; 
       exists (⌈V⁺ ~ S (V⁺) ⤆ <[[⧐ {V⁺} – {V1⁺ - V⁺}] ([⧐⧐ m – n] sf1)]>⌉ W)%sk.
       apply fT_wh. 
       rewrite (WF_ec_new Re V) in fT; auto.
    -- rewrite RC.new_key_wh_spec.
       replace (S (S (Re⁺)%rc)) with ((Re⁺)%rc + 2) by lia.
       now apply halts_weakening_1.
    -- rewrite RC.new_key_wh_spec.
       apply RE.halts_add_spec; split; simpl.
       + exists <[unit]>; split; now auto.
       + apply RE.halts_add_spec; split; simpl.
         ++ exists <[ [⧐ {V⁺} – 2] [⧐⧐ m – n] sf1 ]>; split; auto.
            * reflexivity.
            * apply Term.shift_value_iff.
              now apply Term.multi_shift_value_iff.
         ++ replace (S (S (Re⁺)%rc)) with ((Re⁺)%rc + 2) by lia.
            rewrite (WF_ec_new Re V) in *; auto.
            now apply RE.halts_weakening_1.
    -- apply well_typed_implies_valid in H11 as Hv; auto.
       destruct Hv; apply WF_ec_wh; auto. 
    -- intros r HIn.
       destruct (Resource.eq_dec r (S (V⁺))) as [| Hneq]; subst.
       + apply RE.unused_add_eq_spec; auto; now simpl.
       + apply RE.unused_add_neq_spec; auto.
         destruct (Resource.eq_dec r (V⁺)) as [| Hneq']; subst.
         ++ apply RE.unused_add_eq_spec; auto; now simpl.
         ++ apply RE.unused_add_neq_spec; auto.
            rewrite RE.unused_shift_valid_spec; auto.
            apply Hunsd; rewrite H8.
            apply RS.diff_spec; split; auto.
            rewrite (WF_ec_new Re V); auto.
            do 2 (apply RS.add_notin_spec; split; auto).
            intro c; inversion c.
Qed.

Theorem progress_of_functional_value (Re : ℜ) (V : 𝐕) (tv sf : Λ) (α β : Τ) (R : resources) :
  (* (1) *) value(sf) -> (* (2) *) halts (Re⁺)%rc tv -> (* (3) *) RE.halts (Re⁺)%rc V -> 

  (* (4) *) ∅%vc ⋅ Re ⊢ sf ∈ (α ⟿ β ∣ R) ->
  (* (5) *) ∅%vc ⋅ Re ⊢ tv ∈ α ->
  (* (6) *) WF(Re,V) ->
  (* (7) *)(forall (r : resource), (r ∈ R)%s -> RE.unused r V) ->

  exists (V1 : 𝐕) (tv' sf' : Λ) (W : 𝐖),
    ⪡ V ; tv ; sf ⪢ ⭆ ⪡ V1 ; tv' ; sf' ; W ⪢.
Proof.
  intros. rewrite <- (Term.multi_shift_nil sf) in H2.
  eapply progress_of_functional_value_gen in H3; eauto.
  destruct H3 as [V1 [tv' [sf' [W fT]]]].
  rewrite (Term.multi_shift_nil sf) in *.
  now exists V1; exists tv'; exists sf'; exists W.
Qed.

Theorem progress_of_functional(Re : ℜ) (V : 𝐕) (tv t : Λ) (τ τ' : Τ) (R : resources) :

  (* (1) *) halts (Re⁺)%rc  t -> (* (2) *) halts (Re⁺)%rc tv -> (* (3) *) RE.halts (Re⁺)%rc V ->

  (* (4) *) ∅%vc ⋅ Re ⊢ t ∈ (τ ⟿ τ' ∣ R) -> (* (5) *) ∅%vc ⋅ Re ⊢ tv ∈ τ ->

  (* (6) *) WF(Re,V) -> (* (7) *) (forall (r : resource), (r ∈ R)%s -> RE.unused r V) ->

  (*-------------------------------------------------------------------------------------------------*)
    (exists (V1 : 𝐕) (tv' t' : Λ) (W : 𝐖), 
        (*  (8) *) ⪡ V ; tv ; t ⪢ ⭆ ⪡ V1 ; tv' ; t' ; W ⪢ /\
        (*  (9) *) halts (V1⁺) t' /\ (* (10) *) halts (V1⁺) tv'/\ (* (11) *) RE.halts (V1⁺) V1).
Proof. 
  intros Hlt; destruct Hlt as [t' [HmeT Hvt']]; revert V tv τ τ' R.
  induction HmeT; intros V tv τ τ' R Hltv HltV Hwt Hwtv Hwf Hunsd.
  (* sf is a value *)
  - apply (progress_of_functional_value _ _ tv x τ τ' R) in Hwf as HfT; try assumption.
    destruct HfT as [V1 [tv' [t'' [W fT]]]].
    eapply functional_preserves_typing_gen in fT as HfT; eauto.
    -- destruct HfT as [_ [_ [Re1 [R' [_ [_ [Hwf1 [_ [_ [_ [_ 
                       [_ [Ht'' [Hltv' [HlV' HlW]]]]]]]]]]]]]]].
       rewrite (WF_ec_new Re1 V1) in *; auto.  
       exists V1; exists tv'; exists t''; exists W; repeat split; auto.
    -- exists x; split; now auto.
  (* sf can be reduced at least one time *)
  - apply WF_ec_valid in Hwf as Hv; destruct Hv as [HvRe HvV].
    apply evaluate_preserves_typing with (t' := y) in Hwt as Hwt1; auto.
    eapply IHHmeT in Hvt' as IH; eauto.
    destruct IH as [V1 [tv' [t1' [W [HfT [Hlt1' [Hltv' HltV']]]]]]].
    exists V1; exists tv'; exists t1'; exists W; split; auto; eapply fT_eT_sf; eauto.
    now rewrite <- (WF_ec_new Re V).
Qed.

End progress.