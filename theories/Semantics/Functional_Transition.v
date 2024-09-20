From Coq Require Import Lia Morphisms.
From Mecha Require Import Resource Resources Term Typ Cell VContext RContext  
                          Type_System Evaluation_Transition  REnvironment ReaderStock Stock.
Import ResourceNotations TermNotations TypNotations CellNotations
       VContextNotations RContextNotations REnvironmentNotations
       ReaderStockNotations ResourcesNotations SetNotations StockNotations.

(** * Semantics - Functional

  Wormholes’s dynamic semantics is split in three sets of transition rules: the evaluation transition, defined in [Evaluation_Transition.v], which extends standard β-reduction; the functional transition which performs the logical instant, and the temporal transition, defined in [Temporal_Transition.v], which corresponds to the reactivity of the program: it initializes the resources values, performs the instant via the functional transition and updates the system. In this file, we focus on the functional transition.
*)


(** ** Definition - Functional *)

Open Scope renvironment_scope.

(** *** Well-formed environment-context 

*)

Definition eqDom (Re : ℜ) (V : 𝐕) := forall (r : resource), (r ∈ Re)%rc <-> r ∈ V.

Definition well_formed_ec (Re : ℜ) (V : 𝐕) :=
  eqDom Re V /\ 
  (Re⁺ ⊩ Re)%rc /\ V⁺ ⊩ V /\
  (forall (r : resource) (α β : Τ) (v : 𝑣), Re⌊r⌋%rc = Some (α,β) -> V⌊r⌋ = Some v -> 
   match v with
     | (⩽ v' … ⩾) => (∅)%vc ⋅ Re ⊢ v' ∈ β
     | (⩽ … v' ⩾) => (∅)%vc ⋅ Re ⊢ v' ∈ α
   end).

Notation "'WF(' Re , V )" := (well_formed_ec Re V) (at level 50).

(** *** Functional transition *)

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

(** *** Proof of preservation of validity through the functional transition 

  The concept of validity have to be consistent after a functional transition because typing, evaluation transition are based on.

  **** Hypothesis

  If there is a functional transition (1) with the environment (2), the stream term (3) and the signal function (4) valid according to the new key of the environment;

  **** Result

  All output element of the functional transition (V1,st',...) are valid according to the new key of the output environment (5) and the new key of the output environment is greater or equal to the new key of the input environment (6).
*)
Lemma functional_preserves_valid (V V1 : 𝐕) (W : 𝐖) (st st' sf sf' : Λ) :
  (* (1) *) ⪡ V ; st ; sf ⪢ ⭆ ⪡ V1 ; st' ; sf' ; W ⪢ ->
  (* (2) *) V⁺ ⊩ V -> 
  (* (3) *) (V⁺ ⊩ st)%tm -> 
  (* (4) *) (V⁺ ⊩ sf)%tm ->

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

(** *** Proof of preservation of keys in the environment 

  Keeping consistent the typing through the functional transition is 
  needed for the resources environment. Thus, knowing that we cannot loose 
  keys is required.
*)
Lemma functional_preserves_keys (V V1 : 𝐕) (W : 𝐖) (sv sv' sf sf' : Λ) :
  ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ ->
  V⁺ ⊩ V -> 
  (V⁺ ⊩ sv)%tm -> 
  (V⁺ ⊩ sf)%tm ->

  (forall (r : resource), r ∈ V -> r ∈ V1).
Proof.
  intro fT; induction fT; intros HvV Hvsv Hvsf r' HInV; auto.
  (* fT_eT_sf *)
  - apply IHfT in HInV; auto. 
    now apply evaluate_preserves_valid_term with t.
  (* fT_eT_sf *)
  - apply IHfT in HInV; auto. 
    now apply evaluate_preserves_valid_term with st.
  (* fT_first *) 
  - inversion Hvsf; inversion Hvsv; subst; apply IHfT in HInV; auto; fold Term.valid in *.
  (* fT_comp *)
  - inversion Hvsf; subst; fold Term.valid in *. 
    apply IHfT1 in HInV; auto.
    apply functional_preserves_valid in fT1 as HD; auto; 
    destruct HD as [HvV1 [Hvst' [Hvt1' [HvW Hle]]]].
    apply IHfT2; auto. 
    now apply Term.shift_preserves_valid_2.
  (* fT_rsf *)
  - destruct (Resource.eq_dec r r'); subst; apply RE.add_in_iff; auto.
  (* fT_wh *)
  - rewrite RE.new_key_wh_spec in *.
    inversion Hvsf; subst; destruct IHfT with (r := r'); auto.
    -- apply RE.valid_wh_spec; auto; constructor.
    -- replace (S (S (V⁺))) with ((V⁺) + 2) by lia.
       now apply Term.shift_preserves_valid_1.
    -- do 2 (rewrite RE.add_in_iff; right).
       rewrite RE.valid_in_iff; auto.
    -- now exists x.
Qed.

(** *** Proof of consistency between V and W 

  W stocks all virtual resources created during the functional transition. Those virtual
  resources are also added in the resource environment V1 and cannot be found in the environment V.
*)
Lemma consistency_V_W (V V1 : 𝐕) (W : 𝐖) (sv sv' sf sf' : Λ) :
  ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ ->
  V⁺ ⊩ V -> 
  (V⁺ ⊩ sv)%tm -> 
  (V⁺ ⊩ sf)%tm ->

  (forall (r : resource), (r ∈ W)%sk -> r ∉ V /\ r ∈ V1).
Proof.
  intro fT; induction fT; intros HvV Hvsv Hvsf; auto.
  (* fT_eT_sf *)
  - apply IHfT; auto. 
    now apply evaluate_preserves_valid_term with (t := t).
  (* fT_eT_sv *)
  - apply IHfT; auto. 
    now apply evaluate_preserves_valid_term with (t := st).
  (* fT_arr *)
  - intros r HIn; apply Stock.empty_in_spec in HIn; contradiction.
  (* fT_first *)
  - intros r HIn; inversion Hvsv; inversion Hvsf; subst; apply IHfT; auto.
  (* fT_comp *)
  - inversion Hvsf; subst; intros r HIn.
    apply functional_preserves_valid in fT1 as HD; auto; 
    destruct HD as [HvV1 [Hvst' [Hvt1' [HvW Hle]]]].
    apply Stock.union_spec in HIn as [HIn | HIn].
    -- rewrite Stock.valid_in_iff in HIn; auto.
       apply IHfT1 in HIn as [HnInV HInV1]; auto.
       split; auto.
       eapply functional_preserves_keys in HInV1; eauto.
       now apply Term.shift_preserves_valid_2.
    -- apply IHfT2 in HIn; auto.
       + destruct HIn; split; auto. 
         intro HIn; eapply functional_preserves_keys in H2; eauto.
       + now apply Term.shift_preserves_valid_2.
  (* fT_rsf *)
  - intros r' HIn; apply Stock.empty_in_spec in HIn; contradiction.
  (* fT_wh *)
  - inversion Hvsf; subst; clear Hvsf; fold Term.valid in *.
    rewrite RE.new_key_wh_spec in *. intros rf HIn.
    apply Stock.add_spec in HIn as [Heq | [Heq | HIn]]; subst; split;
    try (apply RE.Ext.new_key_notin_spec; lia).
    -- eapply functional_preserves_keys; eauto; try rewrite RE.new_key_wh_spec; auto.
       + apply RE.valid_wh_spec; auto; constructor.
       + replace (S (S (V⁺))) with ((V⁺) + 2) by lia; 
         now apply Term.shift_preserves_valid_1.
       + repeat rewrite RE.add_in_iff; auto.
    -- eapply functional_preserves_keys; eauto; try rewrite RE.new_key_wh_spec; auto.
       + apply RE.valid_wh_spec; auto; constructor.
       + replace (S (S (V⁺))) with ((V⁺) + 2) by lia; 
         now apply Term.shift_preserves_valid_1.
       + repeat rewrite RE.add_in_iff; auto.
    -- eapply IHfT in HIn as [HnIn HIn]; eauto.
       + intro c; apply HnIn; repeat rewrite RE.add_in_iff; repeat right.
         apply RE.valid_in_iff; auto.
       + apply RE.valid_wh_spec; auto; constructor.
       + replace (S (S (V⁺))) with ((V⁺) + 2) by lia; 
         now apply Term.shift_preserves_valid_1.
    -- eapply IHfT in HIn as [HnIn HIn]; eauto. 
       + apply RE.valid_wh_spec; auto; constructor.
       + replace (S (S (V⁺))) with ((V⁺) + 2) by lia; 
         now apply Term.shift_preserves_valid_1.
Qed.

(** *** Proof of inner constraint of W 

  W stocks reading virtual resource names and writing virtual resource names. It is relevant
  to state that the intersection of set of reading and writing resource names is empty.
*)
Lemma W_well_formed (V V1 : 𝐕) (W : 𝐖) (st st' sf sf' : Λ) :
  ⪡ V ; st ; sf ⪢ ⭆ ⪡ V1 ; st' ; sf' ; W ⪢ ->
  V⁺ ⊩ V -> 
  (V⁺ ⊩ st)%tm -> 
  (V⁺ ⊩ sf)%tm ->

  (forall r, (r ∈ W)%sk -> ((r ∈ (fst W))%rk /\ r ∉ (snd W))%s \/ ((r ∉ (fst W))%rk /\ r ∈ (snd W)))%s.
Proof.
  intro fT; induction fT; intros HvV Hvst Hvsf; auto; intros r' HIn; 
  try (apply Stock.empty_in_spec in HIn; contradiction).
  (* fT_eT_sf *)
  - apply IHfT; auto. 
    now apply evaluate_preserves_valid_term with t.
  (* fT_eT_sv *)
  - apply IHfT; auto. 
    now apply evaluate_preserves_valid_term with st.
  (* fT_firts *)
  - inversion Hvst; inversion Hvsf; subst; apply IHfT; auto.
  (* fT_comp *)
  - inversion Hvsf; subst; clear Hvsf; fold Term.valid in *.

    move r' before W'; rename H2 into Hvt1; rename H3 into Hvt2;
    move Hvt1 after HIn; move Hvt2 before Hvt1.

    apply functional_preserves_valid in fT1 as Hv; auto.
    destruct Hv as [HvV1 [Hvst' [Hvt1' [HvW Hle]]]].

    move Hvst' before Hvst; move HvV1 before HvV; 
    move Hvt1' before Hvt1; move HvW before HvV1;
    move Hle before HvV1.

    destruct W as [Rw Ww]; destruct W' as [Rw' Ww']. 
    apply Stock.union_spec in HIn as [HInW | HInW'];
    destruct HvW as [HvRw HvWw]; simpl in *.
    -- destruct HInW as [HInRw | HInWw]; simpl in *.
       + left; split; try now rewrite ReaderStock.extend_in_iff; left.
         intro HIn. apply RS.union_spec in HIn as [HInWw | HInWw].
         ++ rewrite Resources.valid_in_iff in HInWw; auto.
            rewrite ReaderStock.valid_in_iff in HInRw; auto.
            assert (HInW : (r' ∈ (Rw, Ww))%sk) by (red; auto).
            apply IHfT1 in HInW as [[] | []]; auto.
         ++ rewrite ReaderStock.valid_in_iff in HInRw; auto.
            assert (HInW : (r' ∈ (Rw, Ww))%sk) by (red; auto).
            apply IHfT1 in HInW as [[_ HnInWw] | []]; auto.
            assert (HInW : (r' ∈ (Rw', Ww'))%sk) by (red; auto).
            apply IHfT2 in HInW as [[] | [HnInRw' _]]; auto.
            * apply consistency_V_W with (r := r') in fT1 as [_ HInV1]; 
              auto; try (red; now auto).
              apply consistency_V_W with (r := r') in fT2 as [HnInV1 _]; 
              auto; try (red; now auto). 
              now apply Term.shift_preserves_valid_2.
            * now apply Term.shift_preserves_valid_2.
       + right; split; try (rewrite RS.union_spec; now left).
         intro HIn. apply ReaderStock.extend_in_iff in HIn as [HInRw | HInRw].
         ++ rewrite Resources.valid_in_iff in HInWw; auto.
            rewrite ReaderStock.valid_in_iff in HInRw; auto.
            assert (HInW : (r' ∈ (Rw, Ww))%sk) by (red; auto).
            apply IHfT1 in HInW as [[] | []]; auto.
         ++ rewrite Resources.valid_in_iff in HInWw; auto.
            assert (HInW : (r' ∈ (Rw, Ww))%sk) by (red; auto).
            apply IHfT1 in HInW as [[] | [HnInRw _]]; auto.
            assert (HInW : (r' ∈ (Rw', Ww'))%sk) by (red; auto).
            apply IHfT2 in HInW as [[_ HnInWw'] | []]; auto.
            * apply consistency_V_W with (r := r') in fT1 as [_ HInV1]; 
              auto; try (red; now auto).
              apply consistency_V_W with (r := r') in fT2 as [HnInV1 _]; 
              auto; try (red; now auto). 
              now apply Term.shift_preserves_valid_2.
            * now apply Term.shift_preserves_valid_2.
    -- destruct HInW' as [HInRw' | HInWw']; simpl in *. 
       + left; split; try (rewrite ReaderStock.extend_in_iff; now right).
         intro HIn; apply RS.union_spec in HIn as [HInWw | HInWw].
         ++ rewrite Resources.valid_in_iff in HInWw; auto.
            assert (HInW : (r' ∈ (Rw, Ww))%sk) by (red; auto).
            apply IHfT1 in HInW as [[] | [HnInRw _]]; auto.
            assert (HInW : (r' ∈ (Rw', Ww'))%sk) by (red; auto).
            apply IHfT2 in HInW as [[_ HnInWw'] | []]; auto.
             * apply consistency_V_W with (r := r') in fT1 as [_ HInV1]; 
              auto; try (red; now auto).
              apply consistency_V_W with (r := r') in fT2 as [HnInV1 _]; 
              auto; try (red; now auto). 
              now apply Term.shift_preserves_valid_2.
            * now apply Term.shift_preserves_valid_2.
         ++ assert (HInW : (r' ∈ (Rw', Ww'))%sk) by (red; auto).
            apply IHfT2 in HInW as [[_ HnInWw'] | []]; auto.
            now apply Term.shift_preserves_valid_2.
       + right; split; try (rewrite RS.union_spec; now right).
         intro HIn; apply ReaderStock.extend_in_iff in HIn as [HInRw | HInRw'].
         ++ rewrite ReaderStock.valid_in_iff in HInRw; auto.
            apply consistency_V_W with (r := r') in fT1 as [_ HInV1]; auto; try (red; auto).
            apply consistency_V_W with (r := r') in fT2 as [HnInV1 _]; auto; try (red; auto).
            apply Term.shift_preserves_valid_2; auto.
         ++ apply IHfT2 with (r := r') in HvV1 as [[_ HnI] | [Hc _]]; auto; try (red; auto).
            apply Term.shift_preserves_valid_2; auto.
  (* fT_wh *)
  - inversion Hvsf; subst; fold Term.valid in *; unfold Stock.add, Stock.In in *.
    rewrite RE.new_key_wh_spec in *.
    clear Hvsf; destruct W as [Rw Ww]; simpl in HIn; simpl; destruct HIn as [HInRw | HInWw].
    -- left; split; auto.
       rewrite RS.add_spec; intros [| HIn]; subst.
       + apply ReaderStock.add_in_iff in HInRw as [| HInRw]; try lia.
         apply consistency_V_W with (r := (S (V⁺))) in fT as [HnIn _].
         ++ apply HnIn; repeat rewrite RE.add_in_iff; now left.
         ++ apply RE.valid_wh_full_spec; auto; constructor.
         ++ rewrite RE.new_key_wh_spec. 
            replace (S (S (V⁺))) with ((V⁺) + 2) by lia.
            now apply Term.shift_preserves_valid_1.
         ++ now rewrite RE.new_key_wh_spec. 
         ++ unfold Stock.In; simpl; auto.
       + apply ReaderStock.add_in_iff in HInRw as [| HInRw]; try lia; subst.
         ++ apply consistency_V_W with (r := V⁺) in fT as [HnIn _]; 
            try (rewrite RE.new_key_wh_spec); auto.
            * apply HnIn. repeat rewrite RE.add_in_iff; right; now left.
            * apply RE.valid_wh_spec; auto; constructor.
            * replace (S (S (V⁺))) with ((V⁺) + 2) by lia.
              now apply Term.shift_preserves_valid_1.
            * unfold Stock.In; simpl; auto.
         ++ apply IHfT with (r := r') in H3 as [[_ HnInWw] | [HnInRw _]]; auto.
            * apply RE.valid_wh_spec; auto; constructor.
            * replace (S (S (V⁺))) with ((V⁺) + 2) by lia.
              now apply Term.shift_preserves_valid_1.
    -- right; split; auto. 
       apply RS.add_spec in HInWw as [Heq | HInWw]; subst.
       + intro HInRw; apply ReaderStock.add_in_iff in HInRw as [| HInRw]; try lia.
         apply consistency_V_W with (r := S (V⁺)) in fT as [HnIn _]; 
         try (rewrite RE.new_key_wh_spec); auto.
         ++ apply HnIn. repeat rewrite RE.add_in_iff; now left.
         ++ apply RE.valid_wh_spec; auto; constructor.
         ++ replace (S (S (V⁺))) with ((V⁺) + 2) by lia.
              now apply Term.shift_preserves_valid_1.
         ++ unfold Stock.In; simpl; auto.
       + intro HInRw; apply ReaderStock.add_in_iff in HInRw as [| HInRw]; subst.
         ++ apply consistency_V_W with (r := V⁺) in fT as [HnIn _]; 
            try (rewrite RE.new_key_wh_spec); auto.
            * apply HnIn. repeat rewrite RE.add_in_iff; right; now left.
            * apply RE.valid_wh_spec; auto; constructor.
            * replace (S (S (V⁺))) with ((V⁺) + 2) by lia.
              now apply Term.shift_preserves_valid_1.
            * unfold Stock.In; simpl; auto.
         ++ apply IHfT with (r := r') in H3 as [[_ HnInWw] | [HnInRw _]]; auto.
            * apply RE.valid_wh_spec; auto; constructor.
            * replace (S (S (V⁺))) with ((V⁺) + 2) by lia.
              now apply Term.shift_preserves_valid_1.
Qed.

Hypothesis all_arrow_halting : forall Re t α β,
  ∅%vc ⋅ Re ⊢ arr(t) ∈ (α ⟿ β ∣ ∅%s) -> forall v, ∅%vc ⋅ Re ⊢ v ∈ α -> halts (Re⁺)%rc <[t v]>.

(**
  *** General proof of preservation of typing through functional transition

  **** Hypothesis

  Suppose terms [sf],[sv] are well typed (4,5) and halts (1,2), a functional transition (6) using 
  [sf] and [sv] respectively as a signal function and a stream value, and [V] the input resource 
  environment such as each value in its halts (3) and it is well formed (7) regarding the resource
  context [Re] that is used for typing [sf] and [sv].

  **** Results

  We can state that:
  - each value mapped with a resource name present in [R] has to be unused in [V] (8);
  - each value mapped with a resource name not present in [R'] but present in [V] 
    has to be unchanged in [V1] (9);
  - we can found a context [Re1] and a resource set [R'] such as :
    - the old context is a subset of the new one (10);
    - the old resources set is a subset of the new one (11);
    - [V1] is well formed regarding [Re1] (12); 
    - all initial value stocked in [W] are well typed regards of the new context [Re1] (13);
    - all new resources founded in [R'] are stored in [W] and is not in [R] (14); 
    - each value mapped with a resource name present in [R'] has to be used in [V1] (15);
    - the output stream term [sv'] is well typed (16);
    - the term [sf'] is well typed (17);
    - terms [sf'] and [sv'] halts (18,19);
    - each value in [V1] halts (20).
*)
Theorem functional_preserves_typing_gen (Re : ℜ) (V V1 : 𝐕) (W : 𝐖) (sv sv' sf sf' : Λ) 
                                                                      (α β : Τ) (R : resources) :

  (* (1) *) halts (Re⁺)%rc sf -> (* (2) *) halts (Re⁺)%rc sv -> (* (3) *) RE.halts (Re⁺)%rc V -> 

  (* (4) *) ∅%vc ⋅ Re ⊢ sf ∈ (α ⟿ β ∣ R) ->
  (* (5) *) ∅%vc ⋅ Re ⊢ sv ∈ α -> 
  (* (6) *) ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ -> 
  (* (7) *) WF(Re,V) ->


  (* (8) *)(forall (r : resource), (r ∈ R)%s -> RE.unused r V) /\
  (* (9) *)(forall (r : resource), (r ∉ R)%s /\ (r ∈ V) -> 
              ([⧐ (V⁺) – ((V1⁺) - (V⁺))] V) ⌊r⌋ = V1 ⌊r⌋) /\

  exists (Re1 : ℜ) (R' : resources), 
    (* (10) *) (Re ⊆ Re1)%rc     /\ 
    (* (11) *) (R ⊆ R')%s    /\
    (* (12) *) WF(Re1,V1) /\
    (* (13) *) (forall (r : resource) (v : Λ) (α β : Τ), 
                  W⌊r⌋%sk = Some v -> Re1⌊r⌋%rc = Some (β,α) -> ∅%vc ⋅ Re1 ⊢ v ∈ α) /\
    (* (14) *) (forall (r : resource), (r ∈ (R' \ R))%s -> (r ∈ W)%sk /\ (r ∉ V)) /\
    (* (15) *) (forall (r : resource), (r ∈ R')%s -> RE.used r V1) /\
    (* (16) *) ∅%vc ⋅ Re1 ⊢ sv' ∈ β /\
    (* (17) *) ∅%vc ⋅ Re1 ⊢ sf' ∈ (α ⟿ β ∣ R') /\
    
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

       apply well_typed_implies_valid in Hwt1 as Hvt1; auto; destruct Hvt1 as [Hvt1 _].
       apply well_typed_implies_valid in Hwsv as Hvst; auto; destruct Hvst as [Hvst _].
       apply WF_ec_new in Hwf'' as Hnew''; move Hnew'' before Hnew'.
       apply functional_preserves_valid in HfT1 as HI; auto; (try now rewrite <- Hnew).
       destruct HI as [HvV1 [Hvst' [Hvt1' [HvW Hle]]]].

       (* clean *)
       move HvV1 before HvV; move Hvt1 before HvV1; move Hvt1' before Hvt1; 
       move Hvst before Hvt1'; move Hvst' before Hvst; move HvW before HvV1;
       move Hle before HvV1.
       (* clean *)

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
          rewrite Hnew in Hvt1,Hvst. 
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

          -- rewrite <- Hnew. 
             apply (well_typed_implies_valid (∅%vc) Re st γ); auto. 
          -- rewrite <- Hnew. 
             apply (well_typed_implies_valid (∅%vc) Re t1 <[γ ⟿ τ ∣ R1]>); auto. 
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
          rewrite <- (RE.shift_unfold_1 _ (V1⁺)).
          ++ rewrite (RE.shift_find_spec_3 _ _ r ([⧐ V⁺ – V1⁺ - V⁺] V) V1); auto.
             * rewrite Hnew in *. 
               now apply (RE.valid_in_spec _ _ V1).
             * now apply RE.valid_in_iff.
          ++ rewrite <- Hnew, <- Hnew'; now apply RC.Ext.new_key_Submap_spec.
          ++ rewrite <- Hnew', <- Hnew''; now apply RC.Ext.new_key_Submap_spec.
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

                 apply consistency_V_W with (r := r') in HfT1 as [_ HInV1]; 
                 auto; try (now rewrite <- Hnew).
                 apply (WF_ec_In Re' V1 Hwf' r') in HInV1 as HInRe'. 
                 apply RE.valid_in_spec with (lb := V1⁺) in HInV1; auto.
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
               apply consistency_V_W with (r := r) in HfT1 as [_ HInV1]; auto;
               try (now rewrite <- Hnew).
               apply RE.valid_in_spec with (lb := V1⁺) in HInV1; auto.
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
             apply (RE.valid_in_spec _ r V1) in HvV1; auto.
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
    inversion Hwsf; subst. clear Hwsf; move Re before V; rename H into HfV; rename H4 into HfRe;
    move HfV after HfRe. 
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
            * apply RE.new_key_in_spec in HInV. 
              unfold Resource.shift.
              destruct (Resource.leb_spec (S (S (V⁺))) (V⁺)); try lia.
            * apply RE.new_key_in_spec in HInV. 
              unfold Resource.shift.
              destruct (Resource.leb_spec (S (S (V⁺))) (S (V⁺))); try lia.
         ++ split.
            * rewrite Heq in HInR; 
              apply RS.diff_notin_spec in HInR as [HnIn | HIn]; auto.
              rewrite <- (WF_ec_In Re V) in HInV; auto.
              apply RC.new_key_in_spec in HInV. 
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
                 apply RE.valid_in_spec with (lb := V⁺) in HInV as Hvr; auto.
                 rewrite (RE.shift_in_iff (V⁺) 2) in HInV. 
                 now rewrite Resource.shift_valid_refl in HInV.
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