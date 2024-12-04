From Coq Require Import Lia Morphisms Lists.List.
From Mecha Require Import Resource Resources Term Typ Cell VContext RContext  
                          Type_System Evaluation_Transition  REnvironment SREnvironment Stock.
Import ResourceNotations TermNotations TypNotations CellNotations ListNotations
       VContextNotations RContextNotations REnvironmentNotations
       SREnvironmentNotations ResourcesNotations SetNotations StockNotations.

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

  For subsequent proofs we define a well-formed property between the resource context ([Re]) and the resource environment ([V]). They need four property: (1) their domain matches; (2,3) they are both well-formed under their new key; (4) and each pair (types, cell) is well-typed under the empty variable context and the resource context [Re].
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


Definition fT_inputs_halts (Rc: ℜ) (V: 𝐕) (t1 t2: Λ) :=
  REnvironment.halts (Rc⁺)%rc V /\ halts (Rc⁺)%rc t1 /\ halts (Rc⁺)%rc t2.

Definition fT_outputs_halts (Rc: ℜ) (V: 𝐕) (W: 𝐖) (t1 t2: Λ) :=
  REnvironment.halts (Rc⁺)%rc V /\ Stock.halts (Rc⁺)%rc W /\ halts (Rc⁺)%rc t1 /\ halts (Rc⁺)%rc t2.

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
                                                       (([⧐ (V1⁺)%re – (V2⁺ - V1⁺)%re] W) ∪ W')%sk ⪢

  | fT_rsf (r : resource) (st v : Λ) (V : 𝐕) :

                               V⌊r⌋ = Some (⩽ v … ⩾) -> 
  (* ------------------------------------------------------------------------ *)
       ⪡ V ; st ; rsf[r] ⪢ ⭆ ⪡ ⌈ r ⤆ ⩽ … st ⩾ ⌉ V ; v ; rsf[r] ; (∅)%sk ⪢

  | fT_wh (st st' i t t' : Λ) (V V1 : 𝐕) (W : 𝐖) :
                
       ⪡ (⌈S (V⁺) ⤆ ⩽ <[unit]> … ⩾⌉ (⌈V⁺ ⤆ ([⧐ V⁺ – 2] ⩽ i … ⩾)%cl⌉ ([⧐ V⁺ – 2] V))) ; 
                                    (<[[⧐ {V⁺} – 2] st]>) ; t ⪢ ⭆ ⪡ V1 ; st' ; t' ; W ⪢ ->
  (* ------------------------------------------------------------------------------------------ *)
       ⪡ V ; st ; wormhole(i;t) ⪢  
       ⭆ ⪡ V1 ; st' ; t' ; (⌈(V⁺)%re ~ S (V⁺)%re ⤆ <[[⧐ {(V⁺)%re} – {(V1⁺ - V⁺)%re}] i]>⌉ W)%sk ⪢

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

(** *** [eqDom] properties *)

#[export] Instance eqDom_iff : Proper (RC.eq ==> RE.eq ==> iff) eqDom.
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
  - rewrite RC.Ext.max_key_Empty; auto.
    rewrite (fT_eqDom_Empty Re V HeqDom) in H.
    rewrite RE.Ext.max_key_Empty; auto.
  - assert (HIn : x ∈ V). 
    { 
      unfold eqDom in *; rewrite <- HeqDom. 
      unfold RC.Add in *; rewrite H0.
      rewrite RC.add_in_iff; auto. 
    }
    assert (HIn': x ∈ V) by auto.
    destruct HIn as [v Hfi].
    apply RE.find_1 in Hfi.
    apply RE.add_id in Hfi as Heq; rewrite <- Heq.
    rewrite <- RE.add_remove_1.
    unfold RC.Add in H0; rewrite H0 in *; clear H0 Heq.
    rewrite RC.Ext.max_key_add_max.
    rewrite RE.Ext.max_key_add_max.

    assert (HeqDom': eqDom Re1 (RE.Raw.remove x V)%re).
    {
     intro r; split; intro HIn.
     - destruct (Resource.eq_dec r x); subst; auto.
       -- contradiction.
       -- rewrite RE.remove_in_iff; split; auto.
          apply HeqDom.
          rewrite RC.add_in_iff; auto.
     - apply RE.remove_in_iff in HIn as [Hneq HIn].
       apply HeqDom in HIn.
       apply RC.add_in_iff in HIn as [| HIn]; subst; auto.
       contradiction.
    }
    rewrite <- IHRe1; auto.
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

(** *** [well_formed_ec] properties *)


Fact WF_ec_In (Re : ℜ) (V : 𝐕):
  WF(Re,V) -> forall r, (r ∈ Re)%rc <-> r ∈ V.
Proof. now intros [HeqDom _]. Qed.

Fact WF_ec_Wf (Re : ℜ) (V : 𝐕):
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

#[export] Instance WF_ec_iff : Proper (RC.eq ==> RE.eq ==> iff) well_formed_ec.
Proof.
  intros Re Re1 HeqRe V V1 HeqV; unfold well_formed_ec. 
  split; intros [HeqDom [HvRe [HvV Hwt]]].
  - rewrite <- HeqRe, <- HeqV; repeat (split; auto).
    intros r α β v Hfi Hfi'; destruct v;
    rewrite <- HeqRe, <- HeqV in *;
    eapply Hwt in Hfi'; eauto.
  - rewrite HeqRe, HeqV; repeat (split; auto).
    intros r α β v Hfi Hfi'; destruct v;
    rewrite HeqRe, HeqV in *;
    eapply Hwt in Hfi'; eauto.
Qed.

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


Lemma WF_ec_wh (Re : ℜ) (V : 𝐕) (α : Τ) (i : Λ) :
  (Re⁺%rc ⊩ α)%ty -> (Re⁺%rc ⊩ i)%tm -> ∅%vc ⋅ Re ⊢ i ∈ α ->
  WF(Re,V) ->
  WF((RC.Raw.add (S (Re⁺)%rc) (α,<[𝟙]>) (RC.Raw.add (Re⁺)%rc (<[𝟙]>,α) Re)),
       (RE.Raw.add (S  (V⁺)) (Cell.inp <[unit]>) 
             (RE.Raw.add (V⁺) (Cell.shift (V⁺) 2 (Cell.inp i)) ([⧐ (V⁺) – 2] V)))).
Proof.
  intros Hvτ Hvi Hwti Hwf. 
  apply (WF_ec_new Re V) in Hwf as Hnew.
  apply (WF_ec_Wf Re V) in Hwf as Hv.
  destruct Hv as [HvRe HvV].
  repeat split.
  - intro HIn. 
    repeat rewrite RE.add_in_iff.  
    repeat apply RC.add_in_iff in HIn as [Heq' | HIn]; subst; auto.
    repeat right.
    rewrite (WF_ec_In Re V) in HIn; auto.
    apply RE.Wf_in with (lb := V⁺) in HIn as Hvr; auto.
    rewrite <- (Resource.shift_wf_refl (V⁺) 2 r); auto.
    now apply RE.shift_in_iff.
  - intro HIn. 
    repeat rewrite RC.add_in_iff.
    repeat apply RE.add_in_iff in HIn as [Heq' | HIn]; subst; auto.
    repeat right.
    apply RE.shift_in_e in HIn as Hr'.
    destruct Hr' as [r' Heq']; subst.
    apply RE.shift_in_iff in HIn.
    apply RE.Wf_in with (lb := V⁺) in HIn as Hvr; auto.
    rewrite (Resource.shift_wf_refl (V⁺) 2 r'); auto.
    now apply (WF_ec_In Re V).
  - apply RC.Wf_wh_full; auto; 
    split; unfold Cell.Wf; simpl; auto; constructor.
  - apply RE.Wf_wh_full; auto; 
    unfold Cell.Wf; simpl; try constructor.
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
         ++ rewrite RC.new_key_wh; lia.
         ++ apply RC.Submap_wh.
       + do 2 rewrite RE.add_neq_o in HfV; try lia.
         do 2 rewrite RC.add_neq_o in HfRe; try lia.
         apply RE.shift_find_e_1 in HfV as Hr'.
         destruct Hr' as [[r' Heqr'] [v' Heqv']]; subst.
         apply RE.shift_find_iff in HfV.
         apply RE.Wf_find with (lb := V⁺) in HfV as Hvr'; auto.
         destruct Hvr' as [Hvr' _].
         rewrite Resource.shift_wf_refl in HfRe; auto.
         apply (WF_ec_well_typed Re V Hwf r' _ _ v') in HfRe as Hwv'; auto.
         destruct v' as [v' | v']; auto; simpl; 
         rewrite <- Hnew; now apply weakening_ℜ_wh.
Qed.

Lemma WF_ec_rsf (Rc: ℜ) (V : 𝐕) (r: resource) (α β: Τ) (i v : Λ) :
  ∅%vc ⋅ Rc ⊢ i ∈ α -> (Rc ⌊ r ⌋)%rc = Some (α, β) -> V⌊r⌋ = Some (⩽ v … ⩾) ->
  WF(Rc,V) -> WF(Rc,⌈r ⤆ ⩽ … i ⩾⌉ V).
Proof.
  intros Hwti HfiRc HfiV [HeqDom [HwfRc [HwfV Hwt]]].
  split.
  - intro r'; split; intro HIn.
    -- apply HeqDom in HIn.
       rewrite RE.add_in_iff; auto.
    -- apply HeqDom.
       apply RE.add_in_iff in HIn as [|]; subst; auto.
       exists (⩽ v … ⩾).
       now apply RE.find_2.
  - do 2 (split; auto).
    -- assert (HIn: r ∈ V).
       { exists (⩽ v … ⩾); now apply RE.find_2. }
       apply RE.Ext.new_key_in in HIn as Hlt.
       rewrite RE.Ext.new_key_add_max.
       apply RE.Wf_update. auto.
       + destruct (Resource.eq_dec (S r) (V⁺)).
         ++ rewrite e.
            rewrite Resource.max_l; auto.
         ++ rewrite Resource.max_r; auto.
       + unfold Cell.Wf.
         destruct (Resource.eq_dec (S r) (V⁺)).
         ++ rewrite e; simpl.
            rewrite Resource.max_l; auto.
            rewrite <- (fT_eqDom_new Rc V); auto.
            apply well_typed_implies_Wf in Hwti as []; auto.
         ++ rewrite Resource.max_r; auto; simpl.
            rewrite <- (fT_eqDom_new Rc V); auto.
            apply well_typed_implies_Wf in Hwti as []; auto.
    -- intros r' ty ty' v' HfiRc' HfiV'.
       destruct (Resource.eq_dec r r') as [| Hneq]; subst.
       + rewrite RE.add_eq_o in HfiV'; auto.
         inversion HfiV'; subst; clear HfiV'.
         rewrite HfiRc in HfiRc'.
         inversion HfiRc'; now subst.
       + rewrite RE.add_neq_o in HfiV'; auto.
         apply (Hwt _ ty ty' _ HfiRc') in HfiV'; auto.
Qed.

(** *** [fT_inputs_halts] properties *)

Lemma fT_inputs_halts_Λ_2 (Rc: ℜ) (V: 𝐕) (t1 t2 t2': Λ) :
  fT_inputs_halts Rc V t1 t2 -> (Rc ⁺)%rc ⊨ t2 ⟼ t2' -> fT_inputs_halts Rc V t1 t2'.
Proof.
  intros [HltV [Hlt1 Hlt2]] HeT; do 2 (split; auto).
  apply evaluate_preserves_halting in HeT.
  now rewrite <- HeT.
Qed.

Lemma fT_inputs_halts_Λ_1 (Rc: ℜ) (V: 𝐕) (t1 t1' t2: Λ) :
  fT_inputs_halts Rc V t1 t2 -> (Rc ⁺)%rc ⊨ t1 ⟼ t1' -> fT_inputs_halts Rc V t1' t2.
Proof.
  intros [HltV [Hlt1 Hlt2]] HeT; do 2 (split; auto).
  apply evaluate_preserves_halting in HeT.
  now rewrite <- HeT.
Qed.

Lemma fT_inputs_halts_first (Rc: ℜ) (V: 𝐕) (t1 t2 t3: Λ) :
  fT_inputs_halts Rc V <[⟨t1, t2⟩]> <[first(t3)]> -> fT_inputs_halts Rc V t1 t3.
Proof.
  intros [HltV [Hltpair Hltfirst]]. 
  do 2 (split; auto).
  - now apply halts_pair in Hltpair as [].
  - now apply halts_first.
Qed.

Lemma fT_inputs_halts_comp_l (Rc: ℜ) (V: 𝐕) (t1 t2 t3: Λ) :
  fT_inputs_halts Rc V t1 <[t2 >>> t3]> -> fT_inputs_halts Rc V t1 t2.
Proof.
  intros [HltV [Hltpair Hltfirst]]. 
  do 2 (split; auto).
  now apply halts_comp in Hltfirst as [].
Qed.

Lemma fT_inputs_halts_comp_r (Rc Rc': ℜ) (V V': 𝐕) (W: 𝐖) (t1 t1' t2 t2' t3: Λ) :
  (Rc ⊆ Rc')%rc -> 
  fT_inputs_halts Rc V t1 <[t2 >>> t3]> -> 
  fT_outputs_halts Rc' V' W t1' t2' -> 
  fT_inputs_halts Rc' V' t1'  <[ [⧐{(Rc⁺)%rc} – {(Rc'⁺)%rc - (Rc⁺)%rc}] t3]>.
Proof.
  intros Hsub [HltV [Hltpair Hltcomp]] [HltV' [HltW [Hlt1' Hlt2']]]. 
  do 2 (split; auto).
  apply halts_comp in Hltcomp as [].
  apply halts_weakening; auto.
  now apply RC.Ext.new_key_Submap.
Qed.

Lemma fT_inputs_halts_wh  (Rc: ℜ) (V: 𝐕) (τ: Τ) (t1 t2 t3: Λ) :
  (Rc⁺)%rc = V⁺ ->
  fT_inputs_halts Rc V t1 <[wormhole(t2;t3)]> ->
  fT_inputs_halts (⌈S (Rc⁺) ⤆ (τ, <[𝟙]>)⌉ (⌈Rc⁺ ⤆ (<[𝟙]>, τ)⌉ Rc))%rc
                  (⌈S (V⁺) ⤆ ⩽ unit … ⩾⌉ (⌈V⁺ ⤆ ([⧐V ⁺ – 2] ⩽ t2 … ⩾)%cl⌉ 
                  ([⧐ V⁺ – 2] V))) <[[⧐ {V⁺} – 2] t1]> t3.
Proof.
  intros Heq [HltV [Hlt1 Hltwh]].
  apply halts_wh in Hltwh as [Hlt2 Hlt3].
  repeat split; auto.
  - rewrite RC.new_key_wh.
    rewrite Heq.
    apply RE.halts_add; split. 
    -- exists <[unit]>; simpl; split; auto; reflexivity.
    -- apply RE.halts_add; split.
       + replace (S (S (V⁺))) with (V⁺ + 2) by lia.
         rewrite <- Heq.
         apply halts_weakening_1; auto.
       + rewrite <- Heq. 
         replace (S (S (Rc⁺)%rc)) with ((Rc⁺)%rc + 2) by lia.
         apply RE.halts_weakening_1; auto.
  - rewrite RC.new_key_wh.
    rewrite <- Heq. 
    replace (S (S (Rc⁺)%rc)) with ((Rc⁺)%rc + 2) by lia.
    apply halts_weakening_1; auto.
  - now rewrite RC.new_key_wh.
Qed.    

(** *** [fT_outputs_halts] properties *)

Lemma fT_outputs_halts_Λ_2 (Rc: ℜ) (V: 𝐕) (W: 𝐖) (t1 t2 t2': Λ) :
  fT_outputs_halts Rc V W t1 t2' -> (Rc ⁺)%rc ⊨ t2 ⟼ t2' -> fT_outputs_halts Rc V W t1 t2.
Proof.
  intros [HltV [HltW [Hlt1 Hlt2]]] HeT; do 3 (split; auto).
  apply evaluate_preserves_halting in HeT.
  now rewrite HeT.
Qed.

Lemma fT_outputs_halts_arr (Rc: ℜ) (V: 𝐕) (t1 t2: Λ) :
  fT_inputs_halts Rc V t1 <[arr(t2)]> -> 
  halts (Rc⁺)%rc <[t2 t1]> -> fT_outputs_halts Rc V (∅)%sk <[t2 t1]> <[arr(t2)]>.
Proof.
  intros [HltV [Hlt1 Hltarr]] Hltapp.
  repeat split; auto.
  apply Stock.halts_Empty.
  apply Stock.Empty_empty.
Qed.

Lemma fT_outputs_halts_first (Rc Rc': ℜ) (V V': 𝐕) (W: 𝐖) (t1 t1' t2 t3 t3': Λ) :
  (Rc ⊆ Rc')%rc -> 
  fT_inputs_halts Rc V <[⟨t1, t2⟩]> <[first(t3)]> ->
  fT_outputs_halts Rc' V' W t1' t3' ->
  fT_outputs_halts Rc' V' W <[⟨t1', [⧐{(Rc⁺)%rc} – {(Rc'⁺)%rc - (Rc⁺)%rc}] t2⟩]> <[first(t3')]>.
Proof.
  intros Hsub [_ [Hltpair Hltfirst]] [HltV [HltW [Hlt1' Hlt3']]].
  repeat split; auto.
  - apply halts_pair in Hltpair as [_ Hlt2]. 
    apply halts_pair; split; auto.
    apply halts_weakening; auto.
    now apply RC.Ext.new_key_Submap.
  - now apply halts_first.
Qed.

Lemma fT_outputs_halts_comp (Rc Rc': ℜ) (V V': 𝐕) (W W': 𝐖) (t1 t1' t2 t3: Λ) :
  (Rc ⊆ Rc')%rc -> 
  fT_outputs_halts Rc V W t1 t2 ->
  fT_outputs_halts Rc' V' W' t1' t3 ->
  fT_outputs_halts Rc' V' (([⧐ (Rc⁺)%rc – (Rc'⁺)%rc - (Rc⁺)%rc] W) ∪ W')%sk 
                   t1' <[([⧐{(Rc⁺)%rc} – {(Rc'⁺)%rc - (Rc⁺)%rc}] t2) >>> t3]> .
Proof.
  intros Hsub [HltV [HltW [Hlt1 Hlt2]]] [HltV' [HltW' [Hlt1' Hlt3]]].
  repeat split; auto.
  - apply Stock.halts_union; split; auto.
    apply Stock.halts_weakening; auto.
    now apply RC.Ext.new_key_Submap.
  - apply halts_comp; split; auto.
    apply halts_weakening; auto.
    now apply RC.Ext.new_key_Submap.
Qed.

Lemma fT_outputs_halts_rsf (r: resource) (Rc : ℜ) (V: 𝐕) (t1 t2: Λ) :
  fT_inputs_halts Rc V t1 <[rsf[r]]> -> V⌊r⌋ = Some (⩽ t2 … ⩾) -> 
  fT_outputs_halts Rc (⌈r ⤆ ⩽ … t1 ⩾⌉ V) ∅%sk t2 <[rsf[r]]>.
Proof.
  intros [HltV [Hlt1 _]] HfiV.
  repeat split.
  - apply RE.halts_add; split; auto.
  - apply Stock.halts_Empty.
    apply Stock.Empty_empty.
  - apply HltV in HfiV; auto.
  - exists <[rsf[r]]>; split; auto; reflexivity.
Qed.

Lemma fT_outputs_halts_wh (Rc Rc': ℜ) (V V': 𝐕) (W W': 𝐖) (t1 t2 t3: Λ) :
  (Rc ⊆ Rc')%rc -> 
  (Rc⁺)%rc = V⁺ ->
  (Rc'⁺)%rc = V'⁺ ->
  halts (Rc⁺)%rc t3 ->
  fT_outputs_halts Rc' V' W t1 t2 ->
  fT_outputs_halts Rc' V' 
                   (⌈(V⁺)%re ~ S (V⁺)%re ⤆ <[[⧐ {V⁺%re} – {(V'⁺)%re - (V⁺)%re}] t3]>⌉ W)%sk t1 t2.
Proof.
  intros Hsub Heq Heq' Hlt [HltV [HltW [Hlt1 Hlt2]]].
  repeat split; auto.
  apply Stock.halts_add; split; auto.
  rewrite Heq, Heq' in *.
  apply halts_weakening; auto.
  rewrite <- Heq.
  rewrite <- Heq'.
  apply RC.Ext.new_key_Submap; auto.
Qed.

(** ---- *)

(** ** Preservation - Functional *)
Section preservation.


Hint Resolve VContext.Wf_empty Stock.Wf_empty Resources.Wf_empty : core.

(** *** Preservation of well-formedness through the functional transition 

  Suppose a functional transition (1), if input components ([V], [st] and [sf]) are well-formed under [V⁺] (2,3,4), then output components ([V1], [st'], [sf'] and [W]) are well-formed under [V1⁺] (5). In addition, we can state that [V⁺] is lower or equal to [V1⁺] (6).
*)
Lemma functional_preserves_Wf (V V1 : 𝐕) (W : 𝐖) (st st' sf sf' : Λ) :

               (* (1) *) ⪡ V ; st ; sf ⪢ ⭆ ⪡ V1 ; st' ; sf' ; W ⪢ ->
        (* (2) *) V⁺ ⊩ V -> (* (3) *) (V⁺ ⊩ st)%tm -> (* (4) *) (V⁺ ⊩ sf)%tm ->
  (* ------------------------------------------------------------------------------ *)
       (* (5) *) V1⁺ ⊩ V1 /\ (V1⁺ ⊩ st')%tm /\ (V1⁺ ⊩ sf')%tm /\ ((V1⁺)%re ⊩ W)%sk /\ 
                                (* (6) *) V⁺ <= V1⁺.
Proof.
  intro fT; induction fT; intros HvV Hvst Hvt.
  (* fT_eT_sf *)
  - destruct IHfT as [HvV1 [Hvst' [Hvt'' [HvW Hlt]]]]; auto.
    now apply evaluate_preserves_wf_term with (t := t).
  (* fT_eT_sv *)
  - destruct IHfT as [HvV1 [Hvst' [Hvt'' [HvW Hlt]]]]; auto.
    now apply evaluate_preserves_wf_term with (t := st).
  (* fT_arr *)
  - repeat split; auto. 
    constructor; inversion Hvt; now subst.
  (* fT_first *)
  - inversion Hvst; inversion Hvt; subst; fold Term.Wf in *; clear Hvst Hvt. 
    destruct IHfT as [HvV1 [Hvst' [Hvt'' [HvW Hlt]]]]; auto.
    repeat split; auto; try (now destruct HvW); constructor; auto.
    now apply Term.shift_preserves_wf_2.
  (* fT_comp *)
  - inversion Hvt; subst; 
    destruct IHfT1 as [HvV1 [Hvst' [Hvt1' [HvW1 Hlt1]]]]; auto;
    destruct IHfT2 as [HvV2 [Hvst'' [Hvt2' [HvW2 Hlt2]]]]; auto; fold Term.Wf in *.
    -- now apply Term.shift_preserves_wf_2.
    -- do 3 (split; auto).
       + constructor; auto.
         now apply Term.shift_preserves_wf_2.
       + split; try lia. 
         apply Stock.Wf_union; split; auto.
         now apply Stock.shift_preserves_wf_2.
  (* fT_rsf *)
  - assert (r ∈ V).
    { rewrite RE.in_find; rewrite H; intro c; now inversion c. }
    rewrite RE.Ext.new_key_add_in; auto; try lia; repeat split; auto.
    -- now apply RE.Wf_update.
    -- now apply RE.Wf_find with (lb := V⁺) in H as [_ H].
  (* fT_wh *)
  - rewrite RE.new_key_wh in *. 
    inversion Hvt; subst; clear Hvt.
    destruct IHfT as [HvV1 [Hvst' [Hvt'' [HvW Hlt]]]]; auto; fold Term.Wf in *. 
    + apply RE.Wf_wh; auto; constructor.
    + replace (S (S (V⁺))) with ((V⁺) + 2) by lia.
      now apply Term.shift_preserves_wf_1.
    + do 3 (split; auto); split; try lia.
      apply Stock.Wf_add; eauto.
      ++ unfold Resource.Wf; lia.
      ++ apply Term.shift_preserves_wf_2; auto; lia.
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
  - intros r HIn; apply Stock.empty_in in HIn; contradiction.
  (* fT_comp *)
  - intros r HIn.
    apply Stock.union_in_iff in HIn as [HIn | HIn].
    -- apply Stock.shift_in_e in HIn as H.
       destruct H as [r' Heq]; subst.
       rewrite <- Stock.shift_in_iff in HIn.
       apply IHfT1 in HIn as [HnInV HInV1].
       apply RE.Ext.new_key_in in HInV1 as Hlt.
       rewrite (Resource.shift_wf_refl (V1⁺) (V2⁺ - V1⁺) r'); auto.
       split; auto.
       eapply functional_preserves_keys; eauto.
    -- apply IHfT2 in HIn as [HnInV1 HnInv2]; auto.
       split; auto; intro HIn.
       eapply functional_preserves_keys in HIn; eauto.
  (* fT_rsf *)
  - intros r' HIn; apply Stock.empty_in in HIn; contradiction.
  (* fT_wh *)
  - intros rf HIn.
    apply Stock.add_in_iff in HIn as [Heq | [Heq | HIn]]; subst; split;
    try (apply RE.Ext.new_key_notin; lia).
    -- eapply functional_preserves_keys; eauto; try rewrite RE.new_key_wh; auto.
       repeat rewrite RE.add_in_iff; auto.
    -- eapply functional_preserves_keys; eauto; try rewrite RE.new_key_wh; auto.
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
       (forall r, (r ∈ W)%sk -> ((r ∈ (fst W))%sr /\ r ∉ (snd W))%s \/ 
                                ((r ∉ (fst W))%sr /\ r ∈ (snd W)))%s.
Proof.
  intro fT; induction fT; auto; intros r' HIn; 
  try (apply Stock.empty_in in HIn; contradiction). 
  
  - move r' before W'.

    apply Stock.union_in_iff in HIn as [HInW | HInW'].
    -- destruct W as [Rw Ww];
       destruct HInW as [HInRw | HInWw]; simpl in *.
       + left; split; try now rewrite SREnvironment.extend_in_iff; left.
         intro HIn. apply RS.union_spec in HIn as [HInWw | HInWw].
         ++ apply SREnvironment.shift_in_e in HInRw as H.
            destruct H as [r1 Heq]; subst.
            rewrite <- SREnvironment.shift_in_iff in HInRw.
            rewrite <- Resources.shift_in_iff in HInWw.
            assert (HInW : (r1 ∈ (Rw, Ww))%sk) by (red; auto).
            apply IHfT1 in HInW as [[] | []]; auto.
         ++ destruct W' as [Rw' Ww']; simpl in *. 
            apply SREnvironment.shift_in_e in HInRw as H.
            destruct H as [r1 Heq]; subst.
            rewrite <- SREnvironment.shift_in_iff in HInRw.
            assert (HInW : (r1 ∈ (Rw, Ww))%sk) by (red; auto).
            eapply consistency_V_W in fT1 as H; eauto.
            destruct H as [HnInV HInV1].
            apply RE.Ext.new_key_in in HInV1 as Hlt.
            rewrite (Resource.shift_wf_refl (V1⁺) (V2⁺ - V1⁺) r1) in HInWw; auto.
            apply IHfT1 in HInW as [[_ HnInWw] | []]; auto.
            assert (HInW : (r1 ∈ (Rw', Ww'))%sk) by (red; auto).
            apply IHfT2 in HInW as [[] | [HnInRw' _]]; auto.
            eapply consistency_V_W with (r := r1) in fT2 as [HnInV1 HInV2]; eauto.
            red; auto.
       + right; split; try (rewrite RS.union_spec; now left).
         intro HIn; apply SREnvironment.extend_in_iff in HIn as [HInRw | HInRw].
         ++ apply SREnvironment.shift_in_e in HInRw as H.
            destruct H as [r1 Heq]; subst.
            rewrite <- SREnvironment.shift_in_iff in HInRw.
            rewrite <- Resources.shift_in_iff in HInWw.
            assert (HInW : (r1 ∈ (Rw, Ww))%sk) by (red; auto).
            apply IHfT1 in HInW as [[] | []]; auto.
         ++ destruct W' as [Rw' Ww']; simpl in *. 
            apply Resources.shift_in_e in HInWw as [r1 [Heq HInWw]]; subst.
            rewrite <- Resources.shift_in_iff in HInWw.
            assert (HInW : (r1 ∈ (Rw, Ww))%sk) by (red; auto).
            eapply consistency_V_W in fT1 as H; eauto.
            destruct H as [HnInV HInV1].
            apply RE.Ext.new_key_in in HInV1 as Hlt.
            rewrite (Resource.shift_wf_refl (V1⁺) (V2⁺ - V1⁺) r1) in HInRw; auto.
            apply IHfT1 in HInW as [[_ HnInWw] | []]; auto.
            assert (HInW : (r1 ∈ (Rw', Ww'))%sk) by (red; auto).
            apply IHfT2 in HInW as [[] | [HnInRw' _]]; auto.
            eapply consistency_V_W with (r := r1) in fT2 as [HnInV1 HInV2]; eauto.
            red; auto.
    -- destruct HInW' as [HInRw' | HInWw']; 
       destruct W as [Rw Ww]; simpl in *. 
       + left; split; try (rewrite SREnvironment.extend_in_iff; now right).
         intro HIn; apply RS.union_spec in HIn as [HInWw | HInWw].
         ++ apply Resources.shift_in_e in HInWw as [r1 [Heq HInWw]]; subst.
            rewrite <- Resources.shift_in_iff in HInWw.
            assert (HInW : (r1 ∈ (Rw, Ww))%sk) by (red; auto).
            eapply consistency_V_W in fT1 as H; eauto.
            destruct H as [HnInV HInV1].
            apply RE.Ext.new_key_in in HInV1 as Hlt.
            rewrite (Resource.shift_wf_refl (V1⁺) (V2⁺ - V1⁺) r1) in HInRw'; auto.
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
         intro HIn; apply SREnvironment.extend_in_iff in HIn as [HInRw | HInRw'].
         ++ apply SREnvironment.shift_in_e in HInRw as H; subst.
            destruct H as [r1 Heq]; subst.
            rewrite <- SREnvironment.shift_in_iff in HInRw.
            assert (HInW : (r1 ∈ (Rw, Ww))%sk) by (red; auto).
            eapply consistency_V_W in fT1 as H; eauto.
            destruct H as [HnInV HInV1].
            apply RE.Ext.new_key_in in HInV1 as Hlt.
            rewrite (Resource.shift_wf_refl (V1⁺) (V2⁺ - V1⁺) r1) in HInWw'; auto.
            apply consistency_V_W with (r := r1) in fT2 as [HnInV1 _]; auto; try (red; auto).
         ++ assert (HInW : (r' ∈ (Rw', Ww'))%sk) by (red; auto).
            apply IHfT2 with (r := r') in HInW  as [[] | []]; auto; try (red; auto).
  (* fT_wh *)
  - destruct W as [Rw Ww]; simpl in HIn; simpl; destruct HIn as [HInRw | HInWw].
    -- left; split; auto.
       rewrite RS.add_spec; intros [| HIn]; subst.
       + apply SREnvironment.add_in_iff in HInRw as [| HInRw]; try lia.
         apply consistency_V_W with (r := (S (V⁺))) in fT as [HnIn _]; try (red;auto).
         apply HnIn; repeat rewrite RE.add_in_iff; now left.
       + apply SREnvironment.add_in_iff in HInRw as [| HInRw]; try lia; subst.
         ++ apply consistency_V_W with (r := V⁺) in fT as [HnIn _]; try (red; auto).
            apply HnIn. repeat rewrite RE.add_in_iff; right; now left.
         ++ simpl in *. 
            assert (HInW : (r' ∈ (Rw, Ww))%sk) by (red; auto).
            apply IHfT with (r := r') in HInW as [[] | []]; auto.
    -- right; split; auto. 
       apply RS.add_spec in HInWw as [Heq | HInWw]; subst.
       + intro HInRw; apply SREnvironment.add_in_iff in HInRw as [| HInRw]; try lia.
         apply consistency_V_W with (r := S (V⁺)) in fT as [HnIn _]; try (red; auto).
         apply HnIn. repeat rewrite RE.add_in_iff; now left.
       + intro HInRw; apply SREnvironment.add_in_iff in HInRw as [| HInRw]; subst.
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
  
  
  Theorem functional_preserves_typing_gen (Rc : ℜ) (V V1 : 𝐕) (W : 𝐖) (st st' t t' : Λ) 
                                                                      (α β : Τ) (R : resources) :

                fT_inputs_halts Rc V st t ->

           (* (4) *) ∅%vc ⋅ Rc ⊢ t ∈ (α ⟿ β ∣ R) -> (* (5) *) ∅%vc ⋅ Rc ⊢ st ∈ α -> 
          (* (6) *) ⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st' ; t' ; W ⪢ -> (* (7) *) WF(Rc,V) ->
  (* ------------------------------------------------------------------------------------------- *)
       
       
       (* (8) *)(forall (r : resource), (r ∈ R)%s -> RE.unused r V) /\
       (* (9) *)(forall (r : resource), (r ∉ R)%s /\ (r ∈ V) -> 
                                                ([⧐ (V⁺) – ((V1⁺) - (V⁺))] V) ⌊r⌋ = V1 ⌊r⌋) /\

       exists (Rc1 : ℜ) (R' : resources),

          (* inputs included in outputs *)
          (Rc ⊆ Rc1)%rc /\ 
          (R ⊆ R')%s /\

          (* outputs halts *)
          fT_outputs_halts Rc1 V1 W st' t' /\

          (* typing preserved *)
          ∅%vc ⋅ Rc1 ⊢ st' ∈ β /\ ∅%vc ⋅ Rc1 ⊢ t' ∈ (α ⟿ β ∣ R') /\

          (* properties about resource context and environment preserved *)
          WF(Rc1,V1) /\

          (* properties of [W] *)
          ((Rc1⁺)%rc ⊩ W)%sk /\
          (~ Stock.Empty W -> (Rc1⁺)%rc = (W⁺)%sk) /\
          (forall (r : resource), (r ∈ (RC.diff Rc1 Rc))%rc <-> (r ∈ W)%sk) /\
          (forall (r : resource) (v : Λ) (α β : Τ), 
                    W⌊r⌋%sk = Some v -> Rc1⌊r⌋%rc = Some (β,α) -> ∅%vc ⋅ Rc1 ⊢ v ∈ α) /\

          (* properties of [R'] *)
          (* (14) *) (forall (r : resource), (r ∈ (R' \ R))%s -> (r ∈ W)%sk /\ (r ∉ V)) /\
          (* (15) *) (forall (r : resource), (r ∈ R')%s -> RE.used r V1).
Proof.
  intros Hltinp Hwt Hwtst fT; revert Rc R α β Hltinp Hwt Hwtst.
  induction fT; intros Rc R γ β Hltinp Hwt Hwst HWF;
  
  apply WF_ec_Wf in HWF as HvRc; destruct HvRc as [HvRc HvV];
  apply WF_ec_new in HWF as Hnew;
  
  move HvRc before HWF; move HvV before HvRc; move Hnew before HWF.
  (* fT_eT_sf *)
  - 
    (* clean *)
    move Rc before W; move R before Rc; move γ before R; move β before γ; move fT after IHfT;
    rename fT into HfT; rename H into HeT; move HeT after HfT; clear all_arrow_halting.
    (* clean *)

    rewrite <- Hnew in HeT.
    apply evaluate_preserves_typing with (t' := t') in Hwt as Hwt'; auto.
    apply fT_inputs_halts_Λ_2 with (t2' := t') in Hltinp; auto.
    
  (* fT_eT_sv *)
  - 
    (* clean *)
    move Rc before W; move R before Rc; move γ before R; move β before γ; move fT after IHfT;
    rename fT into HfT; rename H into HeT; move HeT after HfT.
    (* clean *)

    rewrite <- Hnew in HeT. 
    apply evaluate_preserves_typing with (t' := st') in Hwst as Hwst'; auto. 
    
    (* clean *)
    clear HvRc; move Hwst' after Hwst.
    (* clean *)

    apply IHfT; auto.
    apply fT_inputs_halts_Λ_1 with (t1 := st); auto.

  (* fT_arr *)
  - 
    (* clean *)
    inversion Hwt; subst; rename H3 into Hwt'; clear Hwt; move Hwt' after Hwst.
    (* clean *)

    split.
    (** [arr] does not need unused resources at start because it can used them. *)
    { intros r Hc; inversion Hc. }
    split.
    (** All resources in [V] cannot be used by [arr], consequently their values are unchanged. *)
    { 
      intros r [HnIn HIn]. 
      replace (V⁺ - V⁺) with 0 by lia.
      now rewrite RE.shift_zero_refl.
    }

    exists Rc, ∅%s. 
    do 3 (split; try reflexivity).
    (** Outputs of the functional transition halt thanks to the hypothesis [all_arrow_halting]. *)
    {
      apply fT_outputs_halts_arr; auto.
      apply (all_arrow_halting _ _ γ β); auto.
    }
    split.
    (** The output value is well-typed. *)
    { apply (wt_app _ _ _ _ γ); auto. }
    do 4 (split; auto).
    (** [W] is empty then we cannot deduce anything. *)
    { 
      intro HIn.
      contradict HIn.
      apply Stock.Empty_empty.
    }
    split.
    (** [W] is empty then there is no additional resources in [Rc]. *)
    {
      intro r; split; intro HIn.
      - apply RC.diff_in_iff in HIn as []; contradiction.
      - exfalso; revert HIn.
        apply Stock.Empty_notin_1.
        apply Stock.Empty_empty.
    }
    split.
    (** [W] is empty then we cannot deduce anything. *)
    { intros r v ty ty' Hc; inversion Hc. }
    (** The set of ressource is empty the we cannot deduce anything. *)
    split; intros r Hc; inversion Hc. 
  (* fT_first *)
  -
    (* clean *)
    inversion Hwst; subst; move Rc before W; move R before Rc;
    clear α Hwst; rename α0 into α; rename β0 into γ; rename H3 into Hwv1; rename H5 into Hwv2;
    inversion Hwt; subst; clear Hwt; rename H4 into Hwt; rename H7 into Hvγ; rename β0 into β;
    move α before R; move β before α; move γ before β; move Hvγ before HvRc.
    (* clean *)

    apply (fT_inputs_halts_first _ _ _ v2 _) in Hltinp as Hltinp'.
    apply IHfT with (R := R) (β := β) in Hwv1 as IH; auto; clear IHfT.
    destruct IH as [Hunsd [Hlcl [Rc' [R' [HsubRc [HsubR [Hltout [Hwtv1' [Hwt' 
                   [HWF' [HwfW [HnEmpW [HInRcW [HwtW [HInRW Husd]]]]]]]]]]]]]]].

    apply WF_ec_new in HWF' as Hnew'; auto.

    (* clean *)
    move Rc' before Rc; move R' before R; move Hwtv1' before Hwv1; clear Hwv1;
    move Hwt' before Hwt; clear Hwt; move HWF' before HWF; move HwfW before HvV;
    move HsubRc before γ; move HsubR before γ; move Hltout before Hltinp;
    move Husd before Hunsd; move HInRW before HInRcW; move Hnew' before Hnew.
    (* clean *)

    do 2 (split; auto).
    exists Rc', R'.

    rewrite <- Hnew, <- Hnew'.
    do 2 (split; auto); split.
    (* Outputs of the functional transition halt. *)
    { now apply (fT_outputs_halts_first _ _ V _ _ v1 _ _ t). }
    split.
    (* The output value is well-typed. *)
    {
    constructor; auto.
    now apply weakening_ℜ.
    }
    split.
    (* The output program is well-typed. *)
    {
      constructor; auto.
      apply Typ.Wf_weakening with (k := (Rc⁺)%rc); auto.
      now apply RC.Ext.new_key_Submap.
    }
    do 2 (split; auto).
    
  (* fT_comp *)
  -
    (* clean *)
    inversion Hwt; subst; rename H6 into Hwt1; rename H8 into Hwt2;
    apply Resources.eq_leibniz in H7; subst; clear Hwt; rename H9 into HEmp;
    move Rc before W'; move γ before t2'; move β before γ; move τ before γ;
    move R1 before Rc; move R2 before Rc; move Hwt1 before Hwst; move Hwt2 before Hwt1.
    (* clean *)

    apply (fT_inputs_halts_comp_l) in Hltinp as Hltinp'.
    apply IHfT1 with (R := R1) (β := τ) in Hwst as IH1; auto; clear IHfT1.
    destruct IH1 as [Hunsd1 [Hlcl1 [Rc' [R1' [HsubRc [HsubR1 [Hltout [Hwst' [Hwt1' 
                    [HWF' [HwfW1 [HnEmpW1 [HInRcW1 [HwtW1 [HInRW1 Husd1]]]]]]]]]]]]]]].

    (* clean *)
    move Rc' before Rc; move R1' before R1; move Hwst' before Hwst; move Hwt1' before Hwt1.
    move HsubRc before R1'; move HsubR1 before HsubRc; move HWF' before HWF; 
    move HwfW1 before HvV; move Hltout before Hltinp; move HInRW1 before HInRcW1.
    move Husd1 before Hunsd1.
    (* clean *)


    apply WF_ec_new in HWF' as Hnew'; move Hnew' before Hnew.
    apply (fT_inputs_halts_comp_r Rc _ V _ _ st _ t1 _ t2) in Hltout as Hltinp''; auto.
    apply (weakening_ℜ _ _ Rc') in Hwt2 as Hwt2''; auto.
    rewrite Hnew, Hnew' in Hltinp'', Hwt2''.
    apply IHfT2 with (R := R2) (β := β) in Hwst' as IH2; auto; clear IHfT2.

    destruct IH2 as [Hunsd2 [Hlcl2 [Rc'' [R2' [HsubRc' [HsubR2 [Hltout' [Hwst'' [Hwt2' 
                    [HWF'' [HwfW2 [HnEmpW2 [HInRcW2 [HwtW2 [HInRW2 Husd2]]]]]]]]]]]]]]]. 
                  
    (* clean *)
    move Rc'' before Rc'; move R2' before R2; move Hwst'' before Hwst'; move Hwt2' before Hwt2;
    move HsubRc' before HsubRc; move HsubR2 before HsubR1; move HWF'' before HWF'; 
    move HwfW2 before HwfW1; move Hltout' before Hltout; move HInRW2 before HInRcW2;
    move Husd2 before Husd1; move Hunsd2 before Hunsd1; move Hlcl2 before Hlcl1;
    move Hwt2 before Hwt1; move HwtW2 before HwtW1; move HInRW2 before HInRW1;
    move HInRcW2 before HInRcW1; move HnEmpW2 before HnEmpW1; clear Hwt2'' Hltinp''.
    (* clean *)          

    apply WF_ec_new in HWF'' as Hnew''; move Hnew'' before Hnew'.

    assert (HEmp' : (∅ = R1' ∩ R2')%s).
    {
      symmetry; apply RS.empty_is_empty_1; unfold RS.Empty.
      intros r' HIn; apply RS.inter_spec in HIn as [HIn1 HIn2].

      (** 
      4 cases: 
      - r' ∈ R1 ∧ r' ∈ R2 (contradiction)
      - r' ∈ R1 ∧ r' ∉ R2 
      - r' ∉ R1 ∧ r' ∈ R2 
      - r' ∉ R1 ∧ r' ∉ R2
      *)
      destruct (RS.In_dec r' R1) as [HInR1 | HnInR1]; 
      destruct (RS.In_dec r' R2) as [HInR2 | HnInR2].
      - symmetry in HEmp; apply RS.empty_is_empty_2 in HEmp.
        apply (HEmp r'). apply RS.inter_spec; split; auto.

      - destruct (HInRW2 r') as [_ HnInV1].
        -- rewrite RS.diff_spec; split; auto.
        -- apply Hunsd1 in HInR1 as HInV.
          apply RE.unused_in in HInV.
          apply functional_preserves_keys with (r := r') in fT1 as HInV1; auto.
    
      - destruct (HInRW1 r') as [_ HnInV].
        -- rewrite RS.diff_spec; split; auto.
        -- apply HnInV.
          rewrite <- (WF_ec_In Rc V HWF r').
          destruct Hltinp as [_ [_ Hltcomp]].
          apply halts_comp in Hltcomp as [_ [v2 [HmeT Hv2]]].
          apply multi_preserves_typing with (t' := v2) in Hwt2; auto.
          apply (typing_Re_R (∅)%vc _ v2 τ β R2); auto.

      - destruct (HInRW1 r') as [HInW _].
        -- rewrite RS.diff_spec; split; auto.
        -- apply consistency_V_W with (r := r') in fT1 as [HnInV HInV1]; auto.
          destruct (HInRW2 r') as []; auto.
          rewrite RS.diff_spec; split; auto.
    }

    move HEmp' before HEmp; split.
    (** All resources in [R1 ∪ R2] must be unused in the input resource environment [V]. *)
    {
      intros r HIn.
      apply RS.union_spec in HIn as [HIn | HIn]; auto.

      destruct Hltinp as [_ [_ Hltcomp]].
      apply halts_comp in Hltcomp as [_ [v2 [HmeT Hv2]]].
      apply multi_preserves_typing with (t' := v2) in Hwt2; auto.
      apply (typing_Re_R (∅)%vc Rc v2 τ β R2) in HIn as HInRc; auto.
      apply Hunsd2 in HIn.
      apply RE.unused_find_e in HIn as [v HfiV1].
      rewrite (WF_ec_In Rc V HWF r) in HInRc.
      destruct (RS.In_dec r R1) as [| Hneq]; auto.
      destruct (Hlcl1 r); auto.
      apply RE.shift_find_e_1 in HfiV1 as Heq.
      destruct Heq as [[r'] [v']]. 
      destruct v'; try (simpl in *; now inversion H0).
      subst; rewrite H0 in *; clear H0.
      rewrite <- RE.shift_find_iff in HfiV1.
      apply (RE.unused_find _ λ).
      rewrite Resource.shift_wf_refl; auto.
      apply WF_ec_Wf in HWF as [_ HwfV].
      apply (RE.Wf_find (V⁺)) in HfiV1 as []; auto.
    }
    split.
    (** All unused resources values are unchanged. *)
    {
      intros r [HnInR HInV]. 
      apply RS.union_notin_spec in HnInR as [HnInR1 HnInR2].
      apply functional_preserves_keys with (r := r) in fT1 as HInV1; auto.
      rewrite <- (RE.shift_unfold_1 _ (V1⁺)).
      - rewrite <- (Hlcl2 r); auto.
        apply RE.shift_find_Wf; auto.
        -- now apply RE.Ext.new_key_in.
        -- rewrite <- (Resource.shift_wf_refl (V⁺) (V1⁺ - V⁺) r); auto.
            + now rewrite <- RE.shift_in_iff.
            + now apply RE.Ext.new_key_in.
      - rewrite <- Hnew, <- Hnew'; now apply RC.Ext.new_key_Submap.
      - rewrite <- Hnew', <- Hnew''; now apply RC.Ext.new_key_Submap.
    }

    exists Rc''; exists (R1' ∪ R2')%s.
    split.
    (** By transitivity, [Rc ⊆ Rc' ⊆ Rc''] *)
    { now transitivity Rc'. }
    split.
    (** If [R1 ⊆ R1'] and [R2 ⊆ R2'] then [R1 ∪ R2 ⊆ R1' ∪ R2'] *)
    {
      intros r HIn. 
      rewrite RS.union_spec in *; destruct HIn as [HIn | HIn]; auto.
    }
    rewrite <- Hnew', <- Hnew''.
    split.
    (** Outputs of the functional transition halt. *)
    { now apply (fT_outputs_halts_comp _ _ V1 _ _ _ st'). }
    do 2 (split; auto).
    (** The output program is well-typed. *)
    {
      apply (wt_comp _ _ _ R1' R2' _ _ _ _ τ); auto; try reflexivity.
      apply weakening_ℜ; auto.
      now apply WF_ec_Wf in HWF' as [].            
    }
    do 2 (split; auto).
    (** The stock is well-formed. *)
    {
      apply Stock.Wf_union; split; auto.
      apply Stock.shift_preserves_wf_2; auto.
      now apply RC.Ext.new_key_Submap.
    }
    split.
    {
      intro HEmpW.
      rewrite Stock.Empty_union in HEmpW.
      rewrite Stock.new_key_union.
      rewrite Stock.shift_new_refl; auto.
      - apply Classical_Prop.not_and_or in HEmpW as [HEmpW | HEmpW].
        -- rewrite <- Stock.shift_Empty_iff in HEmpW.
           apply HnEmpW1 in HEmpW.
           destruct (Stock.is_empty W') eqn:Hemp.
           + apply Stock.Empty_is_empty in Hemp.
             rewrite (Stock.new_key_Empty W'); auto.
             rewrite Resource.max_l; try lia.
             assert (Rc'' = Rc')%rc.
             ++ intro x.
                destruct (RC.In_dec Rc'' x) as [HIn' | HnIn'].
                * destruct (RC.In_dec Rc' x) as [HIn | HnIn].
                  ** destruct HIn as [v Hfi]; apply RC.find_1 in Hfi.
                     destruct HIn' as [v' Hfi']; apply RC.find_1 in Hfi'.
                     rewrite Hfi.
                     apply (RC.Ext.Submap_find _ _ _ Rc'') in Hfi; auto.
                  ** assert (x ∈ W')%sk.
                     { 
                      rewrite <- HInRcW2.
                      rewrite RC.diff_in_iff; split; auto.
                     }
                     apply Stock.Empty_notin_1 in H; auto.
                     contradiction.
                * destruct (RC.In_dec Rc' x) as [HIn | HnIn].
                  ** apply (RC.Ext.Submap_in _ _ Rc'') in HIn; auto.
                     contradiction.
                  ** rewrite RC.not_in_find in HnIn', HnIn.
                     now rewrite HnIn', HnIn.
             ++ now rewrite H.
           + apply Stock.not_Empty_is_empty in Hemp.
             apply HnEmpW2 in Hemp.
             rewrite <- HEmpW. 
             rewrite <- Hemp.
             apply RC.Ext.new_key_Submap in HsubRc'; lia.
        -- apply HnEmpW2 in HEmpW as Heq.
           destruct (Stock.is_empty W) eqn:Hemp.
           + apply Stock.Empty_is_empty in Hemp.
             rewrite Stock.new_key_Empty; auto.
           + apply Stock.not_Empty_is_empty in Hemp.
             apply HnEmpW1 in Hemp.
             rewrite <- Heq. 
             rewrite <- Hemp.
             apply RC.Ext.new_key_Submap in HsubRc'; lia.
      - now apply Stock.new_key_Wf.
    } 
    split.
    {
      intro r; split; intro HIn.

      - apply RC.diff_in_iff in HIn as [HIn HnIn].
        rewrite Stock.union_in_iff.
        destruct (RC.In_dec Rc' r).
        -- left.
            rewrite <- (Resource.shift_wf_refl (Rc'⁺)%rc ((Rc''⁺)%rc - (Rc'⁺)%rc) r).
            + rewrite <- Stock.shift_in_iff.
              apply HInRcW1.
              apply RC.diff_in_iff; auto.
            + apply (RC.Wf_in _ _ Rc'); auto.
              now apply WF_ec_Wf in HWF' as [].
        -- right.
            apply HInRcW2.
            apply RC.diff_in_iff; auto.
      - rewrite RC.diff_in_iff.
        apply Stock.union_in_iff in HIn as [HIn | HIn].
        -- rewrite Stock.Wf_in_iff in HIn; auto.
           rewrite <- HInRcW1 in HIn.
           apply RC.diff_in_iff in HIn as [HIn HnIn]. 
           split; auto.
           apply (RC.Ext.Submap_in _ Rc'); auto.

        -- assert (HIn': (r ∈ W')%sk) by assumption.
          
            rewrite <- HInRcW2 in HIn'.
            apply RC.diff_in_iff in HIn' as [HIn' HnIn'].
            split; auto.
            intro Hc.

            apply (RC.Ext.Submap_in _ _ Rc') in Hc; auto.
    }
    split.
    { 
      intros r v ty ty' HfiW HfiRc''.
      apply Stock.find_union in HfiW as [HfiW | HfiW].
      - apply Stock.shift_find_e_1 in HfiW as HI.
        destruct HI as [[r' Heq] [v' Heqv]]; subst.
        apply weakening_ℜ; auto.
        -- apply (WF_ec_Wf Rc' V1 HWF').
        -- apply Stock.shift_find_iff in HfiW.
            apply (HwtW1 r' _ _ ty' HfiW).
            
            assert (HIn: (r' ∈ W)%sk). 
            { unfold Stock.In; left. exists v'; now apply SREnvironment.find_2. }

            apply consistency_V_W with (r := r') in fT1 as [_ HInV1]; auto.
            apply (WF_ec_In Rc' V1 HWF' r') in HInV1 as HInRc'.
            apply RE.Ext.new_key_in in HInV1 as Hvr'. 
            rewrite Resource.shift_wf_refl in HfiRc''.
            + destruct HInRc' as [v HfiRc']; apply RC.find_1 in HfiRc'.
              apply RC.Submap_find with (m' := Rc'') in HfiRc' as HfiRc1; auto.
              rewrite HfiRc'' in HfiRc1; inversion HfiRc1; now subst.
            + now rewrite Hnew'; unfold Resource.Wf.
      - apply (HwtW2 r _ _ ty'); auto. 
    }
    split.
    {
      intros r HIn.
      apply RS.diff_spec in HIn as [HIn HnIn]. 
      apply RS.union_notin_spec in HnIn as [HnInR1 HnInR2].
      apply RS.union_spec in HIn as [HInR1' | HInR2'].
      - destruct (HInRW1 r) as [HInW HnInV]; try (apply RS.diff_spec; split; auto).
        split; auto.
        apply Stock.union_in_iff; left.
        apply consistency_V_W with (r := r) in fT1 as [_ HInV1]; auto.
        apply RE.Ext.new_key_in in HInV1 as Hvr'. 
        rewrite <- (Resource.shift_wf_refl (Rc'⁺)%rc (Rc''⁺ - Rc'⁺)%rc r); auto.
        apply Stock.shift_in_iff; auto.
        now rewrite Hnew'.
      - destruct (HInRW2 r) as [HInW2 HnInV]; try (apply RS.diff_spec; split; auto).
        split; auto.
        -- apply Stock.union_in_iff; now right.
        -- intros HInV; apply HnInV.
            assert (r ∈ V) by auto.
            destruct H as [v HfiV].
            apply RE.find_1 in HfiV.
            rewrite (RE.shift_find_iff (V⁺) ((V1⁺) - (V⁺))) in HfiV.
            rewrite Resource.shift_wf_refl in HfiV; auto.
            + rewrite Hlcl1 in HfiV; auto; simpl in *.
              exists ([⧐V ⁺ – V1 ⁺ - V ⁺] v)%cl.
              now apply RE.find_2.
            + apply (RE.Wf_in _ _ V); auto.
    }
    { 
      intros r HIn.
      apply RS.union_spec in HIn as [HIn | HIn]; auto.
      apply Husd1 in HIn as Husd.
      apply RE.used_in in Husd as HInV1.
      destruct (RS.In_dec r R2) as [HInR2 | HnInR2]; auto.
      apply RE.used_find_e in Husd as [v HfiV1].

      apply WF_ec_Wf in HWF' as [].
      apply (RE.Wf_in (V1⁺)) in HInV1 as Hwfr; auto.

      rewrite (RE.shift_find_iff (V1⁺) ((V2⁺) - (V1⁺))) in HfiV1.
      rewrite Resource.shift_wf_refl in HfiV1; auto.
      rewrite Hlcl2 in HfiV1; auto; simpl in *.
      now apply (RE.used_find _ <[[⧐{V1 ⁺} – {V2 ⁺ - V1 ⁺}] v]>%tm).
    }

  (* fT_rsf *)
  -
    (* clean *)
    inversion Hwt; subst; clear Hwt; move Rc before V; rename H into HfiV. 
    rename H4 into HfiRc; move HfiV after HfiRc. 
    (* clean *)

    split.
    (** [r] must be unused in the input environment. *)
    {
      intros r' HIn.
      apply RS.singleton_spec in HIn; subst.
      now apply (RE.unused_find _ v).
    }
    split.
    (** Despite [r] all resources in [V] have their value unchanged. *)
    {
      intros r' [HnIn HIn].
      apply RS.singleton_notin_spec in HnIn.
      rewrite RE.add_neq_o; auto. 
      rewrite RE.Ext.new_key_add_in; auto.
      - replace (V⁺ - V⁺) with 0 by lia. 
        now rewrite RE.shift_zero_refl.
      - exists (⩽ v … ⩾); now apply RE.find_2.
    }
    exists Rc; exists \{{r}}.
    do 3 (split; try reflexivity; auto).

    (** Outputs halt *)
    { now apply fT_outputs_halts_rsf. }
    split.
    (* The output value is well-typed. *)
    { apply (WF_ec_well_typed _ V HWF _ _ _ (⩽ v … ⩾)) in HfiRc; auto. }
    do 2 (split; auto).
    { now apply (WF_ec_rsf _ _ _ γ β _ v). }
    do 2 (split; auto).
    (** The stock is empty then we cannot deduce anything. *)
    {
     intro Hc; exfalso; apply Hc.
     apply Stock.Empty_empty. 
    }
    split.
    {
      intro r'; split; intro HIn. 
      - apply RC.diff_in_iff in HIn as []; contradiction.
      - exfalso; revert HIn.
        apply Stock.Empty_notin_1.
        apply Stock.Empty_empty.
    }
    split.
    (** The stock is empty then we cannot deduce anything. *)
    { intros r' v' ty ty' Hc; inversion Hc. }
    split.
    {
      intros r' HIn.
      apply RS.diff_spec in HIn as []; contradiction.
    }
    {
      intros r' HIn.
      apply RS.singleton_spec in HIn; subst.
      rewrite <- RE.used_add_eq; constructor.
    }

  (* fT_wh *)
  - 
    (* clean *)
    inversion Hwt; subst; move Rc before W; move R before Rc; move R' before R.
    move τ before R'; move γ before τ; move β before γ; rename H6 into Heq; rename H7 into Hvγ; 
    rename H8 into Hvβ; rename H9 into Hwi; rename H10 into Hwt';
    move Hwt after Hwst; move Hwi after Hwt.
    (* clean *)

    assert (Hltinp': fT_inputs_halts Rc V st <[wormhole(i;t)]>) by auto.
    destruct Hltinp' as [HltV [Hltst Hltwh]].
    apply halts_wh in Hltwh as [Hlti Hlt'].
    apply weakening_ℜ_wh with (α := <[𝟙]>) (β := τ) in Hwst as Hwst'; auto.
    rewrite Hnew in Hwst' at 3.

    apply well_typed_implies_Wf in Hwi as HI; auto.
    destruct HI as [Hwfi Hwfτ].

    apply (WF_ec_wh _ _ τ i) in HWF as HWF1; auto.

    apply (fT_inputs_halts_wh _ _ τ _ _ _ Hnew) in Hltinp as Hltinp'.

    apply IHfT in Hwt' as IH; auto; clear IHfT HWF1 Hltinp'.
    destruct IH as [Hunsd [Hlcl [Rc' [R1 [HsubRc [HsubR [Hltout [Hwst'' [Hwt'' 
                   [HWF' [HwfW1 [HnEmpW1 [HInRcW1 [HwtW1 [HInRW1 Husd1]]]]]]]]]]]]]]].
    
    apply WF_ec_new in HWF' as Hnew'.
       
    split.
    {
      intros r HIn; rewrite Heq in HIn. 
      apply RS.diff_spec in HIn as [HInR' HnIn].
      repeat rewrite RS.add_notin_spec in HnIn; destruct HnIn as [Hneq [Hneq' _]].
      apply Hunsd in HInR' as HI; rewrite Hnew in Hneq, Hneq'.
      do 2 rewrite <- RE.unused_add_neq in HI; auto.
      now rewrite RE.unused_shift_Wf in HI.
    }
    split.
    { 
      intros r [HInR HInV]. 
      rewrite RE.new_key_wh in *; rewrite <- Hlcl.
      - symmetry. do 2 rewrite RE.shift_add; simpl.
        do 2 (try rewrite RE.add_neq_o).
        -- replace (S (S (V⁺))) with ((V⁺) + 2) by lia. 
          rewrite <- RE.shift_unfold.
          replace (2 + (V1⁺ - (V⁺ + 2))) with (V1⁺ - V⁺); auto.
          apply functional_preserves_Wf in fT; 
          try (rewrite RE.new_key_wh in * ); try lia.
          + apply RE.Wf_wh; auto; try constructor.
            red; simpl.
            apply well_typed_implies_Wf in Hwi as [Hwi _]; auto.
            now rewrite <- Hnew.
          + replace (S (S (V ⁺))) with ((V⁺) + 2) by lia.
            apply Term.shift_preserves_wf_1. 
            rewrite <- Hnew.
            apply well_typed_implies_Wf in Hwst as [Hvst _]; auto.
          + apply well_typed_implies_Wf in Hwi as [Hwi Hvτ]; auto. 
            apply well_typed_implies_Wf in Hwt as [Hwt _]; auto.
            inversion Hwt; subst; now rewrite <- Hnew.
        -- apply RE.Ext.new_key_in in HInV. 
          unfold Resource.shift.
          destruct (Resource.leb (S (S (V⁺))) (V⁺)); try lia.
        -- apply RE.Ext.new_key_in in HInV. 
          unfold Resource.shift.
          destruct (Resource.leb (S (S (V⁺))) (S (V⁺))); try lia.
      - split.
        -- rewrite Heq in HInR; 
          apply RS.diff_notin_spec in HInR as [HnIn | HIn]; auto.
          rewrite <- (WF_ec_In Rc V) in HInV; auto.
          apply RC.Ext.new_key_in in HInV. 
          do 2 rewrite RS.add_spec in HIn.
          destruct HIn as [Heq' | [Heq'| HIn]]; subst; try lia.
          inversion HIn.
        -- repeat (rewrite RE.add_in_iff; right).
          now rewrite RE.Wf_in_iff.
    }

    exists Rc'; exists R1; split.

    { now apply RC.Submap_wh_1 in HsubRc. }
    split.
    {
      rewrite Heq; intro r. intros HIn.
      apply RS.diff_spec in HIn as [HIn _]. 
      now apply HsubR.   
    }
    split.
    { 
      apply (fT_outputs_halts_wh Rc); auto.
      now apply RC.Submap_wh_1 in HsubRc.
    }
    do 4 (split; auto).
    {
     rewrite <- Hnew, <- Hnew'.
     apply RC.Ext.new_key_Submap in HsubRc.
     do 2 rewrite RC.Ext.new_key_add_max in HsubRc.
     apply Stock.Wf_add; auto.
     - unfold Resource.Wf; lia.
     - unfold Resource.Wf; lia.
     - apply Term.shift_preserves_wf_2; auto; lia.
    }
    split.
    {
      intro HnEmp.
      rewrite (RC.new_key_diff (⌈S (Rc⁺)%rc ⤆ (τ, <[𝟙]>)⌉ (⌈(Rc⁺)%rc ⤆ (<[𝟙]>, τ)⌉ Rc))%rc); auto.
      do 2 rewrite RC.Ext.new_key_add_max.
      rewrite Stock.new_key_add_max; rewrite <- Hnew.
      replace (Nat.max (S (Rc ⁺)%rc) (Rc ⁺)%rc) with (S (Rc ⁺)%rc) by lia.
      assert ((RC.diff Rc' (⌈S (Rc⁺) ⤆ (τ, <[𝟙]>)⌉ (⌈Rc⁺ ⤆ (<[𝟙]>, τ)⌉ Rc))⁺)%rc = (W ⁺)%sk).
      { admit. }
      rewrite H; lia.
    }
    split.
    {
      intro r; split; intro HIn.
      - rewrite Stock.add_in_iff.
        apply RC.diff_in_iff in HIn as [HIn HnIn].
        destruct (Resource.eq_dec (V⁺) r) as [| Hneq]; subst; auto.
        destruct (Resource.eq_dec (S (V⁺)) r) as [| Hneq']; subst; auto.
        right; right.
        apply HInRcW1.
        rewrite RC.diff_in_iff; split; auto.
        do 2 rewrite RC.add_in_iff.
        intros [| [|]]; subst; auto.
      - rewrite RC.diff_in_iff. 
        apply Stock.add_in_iff in HIn as [| [| HIn]]; subst.
        -- split.
           + rewrite <- Hnew.
             eapply RC.Ext.Submap_in; eauto.
             do 2 rewrite RC.add_in_iff; auto.
           + rewrite <- Hnew.
             apply RC.Ext.new_key_notin; lia.
        -- split.
           + rewrite <- Hnew.
             eapply RC.Ext.Submap_in; eauto.
             do 2 rewrite RC.add_in_iff; auto.
           + rewrite <- Hnew.
             apply RC.Ext.new_key_notin; lia.
        -- rewrite <- HInRcW1 in HIn.
           apply RC.diff_in_iff in HIn as [HIn HnIn].
           split; auto.
           do 2 rewrite RC.add_in_iff in HnIn.
           intro; apply HnIn; auto.
    }
    split.
    {
      intros r v τ1 α HfiW HfRc1.
      destruct (Resource.eq_dec (V⁺) r); subst.
      - rewrite Stock.find_add_eq in HfiW. 
        inversion HfiW; subst; clear HfiW.
        rewrite <- Hnew, <- Hnew'.
        apply weakening_ℜ; auto.
        -- now apply RC.Submap_wh_1 in HsubRc.
        -- apply (RC.Ext.Submap_find (Rc⁺)%rc (<[𝟙]>,τ)) in HsubRc as HfiRc.
           + rewrite Hnew in HfiRc. 
             rewrite HfRc1 in HfiRc.
             inversion HfiRc; now subst.
           + rewrite RC.add_neq_o; try lia; rewrite RC.add_eq_o; auto.
      - rewrite Stock.find_add_neq in HfiW; auto.
        apply (HwtW1 r _ _ α); auto.
    }
    split; auto.
    {
      intros r HIn.
      apply RS.diff_spec in HIn as [HInR1 HnInR]. 
      rewrite Heq in HnInR.
      apply RS.diff_notin_spec in HnInR as [HnInR' | HIn].
      - destruct (HInRW1 r); try (now apply RS.diff_spec).
        split.
        -- apply Stock.add_in_iff; auto.
        -- intro HIn.
           apply H0.
           do 2 rewrite RE.add_in_iff.
           rewrite RE.shift_in_new_key; auto.
      - rewrite <- Hnew.
        repeat rewrite RS.add_spec in HIn. 
        destruct HIn as [Heq' | [Heq' | HIn]]; try inversion HIn; subst.
        -- split.
           + apply Stock.add_in_iff; auto.
           + rewrite Hnew.
             apply RE.Ext.new_key_notin; auto.
        -- split.
           + apply Stock.add_in_iff; auto.
           + rewrite Hnew.
             apply RE.Ext.new_key_notin; auto.
    }
(* Qed. *)
Admitted.

End preservation.

(** ---- *)

(** ** Progress - Functional *)
Section progress.

Hint Resolve VContext.Wf_empty Stock.Wf_empty Resources.Wf_empty : core.

Hypothesis all_arrow_halting : forall Re t α β,
  ∅%vc ⋅ Re ⊢ arr(t) ∈ (α ⟿ β ∣ ∅%s) -> forall v, ∅%vc ⋅ Re ⊢ v ∈ α -> halts (Re⁺)%rc <[t v]>.


Lemma progress_of_functional_value_gen (Re : ℜ) (m n : list lvl) (V : 𝐕) (tv sf : Λ) (α β : Τ) (R : resources) :

       (* (1) *) value(sf) -> (* (2) *) halts (Re⁺)%rc tv -> (* (3) *) RE.halts (Re⁺)%rc V -> 

       (* (4) *) ∅%vc ⋅ Re ⊢ [⧐⧐ m – n] sf ∈ (α ⟿ β ∣ R) -> (* (5) *) ∅%vc ⋅ Re ⊢ tv ∈ α ->

       (* (6) *) WF(Re,V) -> (* (7) *)(forall (r : resource), (r ∈ R)%s -> RE.unused r V) ->
  (* ------------------------------------------------------------------------------------------ *)
       exists (V1 : 𝐕) (tv' sf' : Λ) (W : 𝐖),
                                      ⪡ V ; tv ; [⧐⧐ m – n] sf ⪢ ⭆ ⪡ V1 ; tv' ; sf' ; W ⪢.
Proof.
  (*
  revert Re m n V tv α β R; induction sf;
  intros Re m n V tv τ1 τ1' R Hvalsf Hltv HlV Hwsf Hwtv Hwf Hunsd;
  inversion Hvalsf; subst.

  - rewrite Term.multi_shift_unit in *; inversion Hwsf.  
  - rewrite Term.multi_shift_abs in *. inversion Hwsf; subst.
  - rewrite Term.multi_shift_pair in *. inversion Hwsf; subst.
 
  - rewrite Term.multi_shift_arr in *. inversion Hwsf; subst.
    exists V, <[([⧐⧐ m – n] sf) tv]>, <[arr([⧐⧐ m – n] sf)]>, (∅%sk).
    simpl. now constructor.
 
  - rewrite Term.multi_shift_first in *. inversion Hwsf; subst.
    destruct Hltv as [tv' [HmeT Hvtv']].
    apply multi_preserves_typing with (t' := tv') in Hwtv as Hwtv'; auto.
    -- inversion Hvtv'; subst; inversion Hwtv'; subst.
      apply (IHsf Re m n V v1 _ β R) in H9 as HfT; auto.
      + destruct HfT as [V1 [v1' [sf1 [W fT]]]].
        exists V1, <[⟨v1',[⧐ {V⁺} – {V1⁺ - V⁺}] v2⟩]>, <[first(sf1)]>, W.
        apply fT_MeT_sv with (st' := <[ ⟨ v1, v2 ⟩ ]>).
        ++ rewrite <- (WF_ec_new Re V); auto.
        ++ simpl. now constructor.
      + inversion Hvtv'; subst; exists v1; split; now auto.
    -- eapply WF_ec_Wf; eauto.
  
  - rewrite Term.multi_shift_rsf in *; inversion Hwsf; subst.
    assert (RE.unused ([⧐⧐m – n] r)%r V).
    -- apply Hunsd. 
       now apply RS.singleton_spec.
    -- apply RE.unused_find_e in H as [v Hfi].
  
       exists (⌈([⧐⧐ m – n] r)%r ⤆ ⩽ … tv ⩾ ⌉ V), v. 
       exists <[rsf[([⧐⧐ m – n] r)%r]]>, ∅%sk.
       now constructor.

  - rewrite Term.multi_shift_comp in *. inversion Hwsf; subst.
    apply (IHsf1 Re m n V tv τ1 τ R1) in Hwtv as HfT; auto.
    -- clear IHsf1; destruct HfT as [V1 [tv' [sf1' [W1 fT1]]]].
       apply functional_preserves_typing_gen
       with (Rc := Re) (α := τ1) (β := τ) (R := R1) in fT1 as Hfpt; auto.
       + destruct Hfpt as [Hunsd1 [Hlcl1 [Rc' [R1' [HsubRc [HsubR1 [Hltout [Hwst' [Hwt1' 
                      [HWF' [HwfW1 (*[HnEmpW1*) [HInRcW1 [HwtW1 [HInRW1 Husd1]]]]]]]]]]]]]](*]*).
         apply weakening_ℜ with (Re1 := Rc') in H10 as Hwsf2bis; 
         auto; try (eapply (WF_ec_Wf Re V); now auto).
         rewrite <- Term.multi_shift_cons in Hwsf2bis.

         apply (IHsf2 Rc' (Re⁺ :: m)%rc ((Rc'⁺ - Re⁺) :: n)%rc V1 tv' τ τ1' R2) in Hwst' as HfT; auto.
         ++ destruct HfT as [V2 [tv'' [sf2' [W2 fT2]]]].
            exists V2, tv'', <[([⧐ {V1⁺} – {V2⁺ - V1⁺}] sf1') >>> sf2']>, 
                   (([⧐ (V1⁺)%re – (V2⁺ - V1⁺)%re] W1) ∪ W2)%sk.
            eapply fT_comp; eauto.
            rewrite <- (WF_ec_new Rc' V1); auto.
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
              apply RE.unused_find_e in H4 as [v Hfi].
              rewrite (RE.shift_find_iff (V⁺) (V1⁺ - V⁺)) in Hfi.
              apply RE.Ext.new_key_in in HInRe1 as Hlt.
              rewrite Resource.shift_wf_refl in Hfi; auto.
              rewrite HeqVV1 in Hfi; auto. 
              apply RE.Wf_in with (lb := V⁺) in HInRe1 as HvV.
              ** now apply RE.unused_find in Hfi.
              ** eapply (WF_ec_Wf Re V); auto.
            * now apply Term.multi_shift_value_iff.
       + exists <[[⧐⧐ m – n] sf1]>; split; auto.
         ++ reflexivity.
         ++ now apply Term.multi_shift_value_iff.
    -- intros. apply Hunsd. rewrite H9.
       rewrite RS.union_spec; now left.

  - clear IHsf1. rewrite Term.multi_shift_wh in *; inversion Hwsf; subst.
    apply WF_ec_Wf in Hwf as H; destruct H as [HvRe HvV].
    apply weakening_ℜ_wh with (β := τ) (α := <[ 𝟙 ]>) in Hwtv; auto.
    apply (IHsf2 _ m n
                  (⌈S (V⁺) ⤆ ⩽<[unit]> … ⩾⌉ (⌈V⁺ ⤆ ([⧐ V⁺ – 2] ⩽ ([⧐⧐ m – n] sf1) … ⩾)%cl⌉ 
                    ([⧐ V⁺ – 2] V)))
    ) with (β := τ1') (R := R') in Hwtv as HfT; auto. 
    -- destruct HfT as [V1 [tv' [sf' [W fT]]]]; clear IHsf2.
       exists V1, tv', sf', 
              (⌈(V⁺)%re ~ S (V⁺)%re ⤆ <[[⧐ {(V⁺)%re} – {(V1⁺ - V⁺)%re}] ([⧐⧐ m – n] sf1)]>⌉ W)%sk.
       apply fT_wh. 
       rewrite (WF_ec_new Re V) in fT; auto.
    -- rewrite RC.new_key_wh.
       replace (S (S (Re⁺)%rc)) with ((Re⁺)%rc + 2) by lia.
       now apply halts_weakening_1.
    -- rewrite RC.new_key_wh.
       apply RE.halts_add; split; simpl.
       + exists <[unit]>; split; now auto.
       + apply RE.halts_add; split; simpl.
         ++ exists <[ [⧐ {V⁺} – 2] [⧐⧐ m – n] sf1 ]>; split; auto.
            * reflexivity.
            * apply Term.shift_value_iff.
              now apply Term.multi_shift_value_iff.
         ++ replace (S (S (Re⁺)%rc)) with ((Re⁺)%rc + 2) by lia.
            rewrite (WF_ec_new Re V) in *; auto.
            now apply RE.halts_weakening_1.
    -- apply well_typed_implies_Wf in H11 as Hv; auto.
       destruct Hv; apply WF_ec_wh; auto. 
    -- intros r HIn.
       destruct (Resource.eq_dec r (S (V⁺))) as [| Hneq]; subst.
       + apply RE.unused_add_eq; auto; now simpl.
       + apply RE.unused_add_neq; auto.
         destruct (Resource.eq_dec r (V⁺)) as [| Hneq']; subst.
         ++ apply RE.unused_add_eq; auto; now simpl.
         ++ apply RE.unused_add_neq; auto.
            rewrite RE.unused_shift_Wf; auto.
            apply Hunsd; rewrite H8.
            apply RS.diff_spec; split; auto.
            rewrite (WF_ec_new Re V); auto.
            do 2 (apply RS.add_notin_spec; split; auto).
            intro c; inversion c.
Qed.
*)
Admitted.

(** *** Progress of the functional transition 

  Suppose well-typed expressions [t] and [tv], which halt (1,2), under [Re] (4,5). In addition, suppose that [V] halts (3) and is well-formed regards of [Re] (6). If all resources used by [t] is unused at the beginning (7), then it exists a functional transition (8) where its outputs halt (9,10,11).
*)
Theorem progress_of_functional(Re : ℜ) (V : 𝐕) (tv t : Λ) (α β : Τ) (R : resources) :

                 (* (1) *) halts (Re⁺)%rc t -> (* (2) *) halts (Re⁺)%rc tv -> 
                              (* (3) *) RE.halts (Re⁺)%rc V ->

            (* (4) *) ∅%vc ⋅ Re ⊢ t ∈ (α ⟿ β ∣ R) -> (* (5) *) ∅%vc ⋅ Re ⊢ tv ∈ α ->
       (* (6) *) WF(Re,V) -> (* (7) *) (forall (r : resource), (r ∈ R)%s -> RE.unused r V) ->

  (* ------------------------------------------------------------------------------------------ *)
       (exists (V1 : 𝐕) (tv' t' : Λ) (W : 𝐖), 
       (*  (8) *) ⪡ V ; tv ; t ⪢ ⭆ ⪡ V1 ; tv' ; t' ; W ⪢ /\
       (*  (9) *) halts (V1⁺) t' /\ (* (10) *) halts (V1⁺) tv'/\ (* (11) *) RE.halts (V1⁺) V1).
Proof. 
  (*
  intros Hlt. 
  destruct Hlt as [t' [meT Hvt']]; revert V tv α β R Hvt'.
  induction meT as [t | t t1 t' HeT]; 
  intros V tv α β R Hvt' Hltv HltV Hwt Hwtv Hwf Hunsd.
  (* t is a value *)
  - rewrite <- (Term.multi_shift_nil t) in Hwt.
    apply (progress_of_functional_value_gen _ _ _ V tv t α β R) in Hwt as fT; auto.    
    destruct fT as [V1 [tv' [t' [W fT]]]].
    rewrite Term.multi_shift_nil in *.
    exists V1, tv', t', W; split; auto.
    apply (functional_preserves_typing_gen all_arrow_halting Re _ _ _ _ _ _ _ α β R) in fT; auto.
    -- destruct fT as [_ [_ [Re1 [R' [_ [_ [Hwf1 [_ [_ [_ [_ 
                      [_ [Ht'' [Hltv' [HlV' HlW]]]]]]]]]]]]]]].
       rewrite <- (WF_ec_new Re1 V1); auto.
    -- exists t; split; now auto.
  (* t can be reduced at least one time *)
  - clear meT.
    apply WF_ec_Wf in Hwf as Hv; destruct Hv as [HvRe HvV].
    apply evaluate_preserves_typing with (t' := t1) in Hwt as Hwt1; auto.
    apply (IHmeT V tv α β) in Hwt1 as IH; auto.
    destruct IH as [V1 [tv' [t1' [W [HfT [Hlt1' [Hltv' HltV']]]]]]].
    exists V1, tv', t1', W; split; auto. 
    apply fT_eT_sf with (t' := t1); auto.
    now rewrite <- (WF_ec_new Re V).
Qed.
*)
Admitted.

End progress.

(** ---- *)

(** ** Safey - Functional *)
Section safety.

Hypothesis all_arrow_halting : forall Re t α β,
  ∅%vc ⋅ Re ⊢ arr(t) ∈ (α ⟿ β ∣ ∅%s) -> forall v, ∅%vc ⋅ Re ⊢ v ∈ α -> halts (Re⁺)%rc <[t v]>.

(** *** Resources safety 

  Suppose well-typed expressions [t] and [tv], which halt (1,2), under [Re] (6,7). In addition, [V] halts (3) and is well-formed regards of [Re] (4), and all resources used by [t] is unused at the beginning (5). We can state that:
  - it exists a functional transition (8), i.e. there are no stuck situation and consequently no multiple interations with the same resource;
  - used resources are still in the set at the end (9);
  - all resources not in [R] are unused during the functional transition (10);
  - all resources in [R'\R] are new and stored in [W] (11);
  - all resources in [R] are used during the functional transition (12).
*)
Theorem safety_resources_interaction (Re : ℜ) (V : 𝐕) (t tv : Λ) (α β : Τ) (R : resources) :

                   (* (1) *) halts (Re⁺)%rc t -> (* (2) *) halts (Re⁺)%rc tv -> 
                              (* (3) *) RE.halts (Re⁺)%rc V ->

      (* (4) *) WF(Re,V) -> (* (5) *) (forall (r : resource), (r ∈ R)%s -> RE.unused r V) ->
             (* (6) *) ∅%vc ⋅ Re ⊢ t ∈ (α ⟿ β ∣ R) -> (* (7) *) ∅%vc ⋅ Re ⊢ tv ∈ α -> 
  (* ------------------------------------------------------------------------------------------ *)

       exists (R' : resources) (V1 : 𝐕) (tv' t' : Λ) (W: 𝐖), 
            (*  (8) *) ⪡ V ; tv ; t ⪢ ⭆ ⪡ V1 ; tv' ; t' ; W ⪢ /\

            (*  (9) *) (R ⊆ R')%s    /\
            (* (10) *)(forall (r : resource), (r ∉ R)%s /\ (r ∈ V) -> 
                          ([⧐ (V⁺) – ((V1⁺) - (V⁺))] V) ⌊r⌋ = V1 ⌊r⌋) /\
            (* (11) *) (forall (r : resource), (r ∈ (R' \ R))%s -> (r ∈ W)%sk /\ (r ∉ V)) /\ 
            (* (12) *) (forall (r : resource), (r ∈ R)%s -> RE.used r V1).
Proof.
  (*
  intros Hlt Hltv HltV Hwf Hunsd Hwt Hwtv.
  apply (progress_of_functional all_arrow_halting Re V tv t _ β R) in Hwtv as fT; auto.
  destruct fT as [V1 [tv' [t' [W [HfT [Hlt' [Hltv' HltV1]]]]]]].

  (* clean *)
  move tv before t; move tv' before tv; move t' before t; move V1 before V;
  move HltV1 before HltV; move Hlt' before Hlt; move Hltv' before Hltv; move Hwt before Hwtv;
  move Hunsd after HfT; move Hwf before Hunsd.
  (* clean *)

  apply (functional_preserves_typing_gen all_arrow_halting Re V V1 W _ tv' t t' _ β R) in Hwtv as preserve; auto.
  destruct preserve as [_ [HeqVV1 [_  [R' [_ [Hsub [_ [_ [HW [Husd _]]]]]]]]]].
  exists R', V1, tv', t', W; repeat split; auto; now eapply HW.
Qed.
*)
Admitted.

End safety.