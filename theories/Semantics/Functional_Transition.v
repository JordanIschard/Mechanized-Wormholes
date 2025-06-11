From Coq Require Import Lia Morphisms Lists.List FinFun Program.
From Mecha Require Import Resource Resources Term Typ Cell VContext RContext  
                          Type_System Evaluation_Transition  REnvironment Stock.
Import ResourceNotations TermNotations TypNotations CellNotations ListNotations
       VContextNotations RContextNotations REnvironmentNotations
       ResourcesNotations SetNotations StockNotations.

(** * Semantics - Functional

  Wormholes’s dynamic semantics is split in three sets of transition rules: the evaluation transition, defined in [Evaluation_Transition.v], which extends standard β-reduction; the functional transition which performs the logical instant, and the temporal transition, defined in [Temporal_Transition.v], which corresponds to the reactivity of the program: it initializes the resources values, performs the instant via the functional transition and updates the system. In this file, we focus on the functional transition.
*)


(** ** Definition - Functional *)

Module ST := Stock.

Open Scope renvironment_scope.

(** *** Well-formed environment-context 

  For subsequent proofs we define a well-formed property between the resource context ([Rc]) and the resource environment ([V]). They need four property: (1) their domain matches; (2,3) they are both well-formed under their new key; (4) and each pair (types, cell) is well-typed under the empty variable context and the resource context [Rc].
*)
Definition well_formed_ec (Rc : ℜ) (V : 𝐕) :=
  (* (1) *) REnvironment.eqDom Rc V /\ 
  (* (2) *) (Rc⁺ ⊩ Rc)%rc /\  (* (3) *) V⁺ ⊩ V /\
  (* (4) *) (forall (r : resource) (α β : Τ) (v : 𝑣),
                Rc⌊r⌋%rc = Some (α,β) -> V⌊r⌋ = Some v -> 
                match v with
                  | (⩽ v' … ⩾) => (∅)%vc ⋅ Rc ⊢ v' ∈ β
                  | (⩽ … v' ⩾) => (∅)%vc ⋅ Rc ⊢ v' ∈ α
                end).

Notation "'WF(' Rc , V )" := (well_formed_ec Rc V) (at level 50).


Definition fT_inputs_halts (m: lvl) (V: 𝐕) (t1 t2: Λ) :=
  REnvironment.halts m V /\ halts m t1 /\ halts m t2.

Definition fT_outputs_halts (m: lvl) (V: 𝐕) (W: 𝐖) (t1 t2: Λ) :=
  REnvironment.halts m V /\ ST.halts m W /\ halts m t1 /\ halts m t2.

(** *** Functional transition 

  The functional transition is a big-step semantics that performs an instant. It takes an input environment [V], a signal input sample [st] and a signal function [t] and produces an updated environment [V1], an output term [st1], an updated signal function [t1] and a stock [W]. There are numerous shifts done during the functional transition. We suppose input components as well-formed under [V⁺] and we want output components well-formed under [V1⁺]. Consequently, all shifts aims to keep consistent this statement.
*)

Reserved Notation "⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st1 ; t1 ; W ⪢" 
  (at level 0, V constr, V1 constr, st custom wh, st1 custom wh,t custom wh, t1 custom wh, no associativity).

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
       ⪡ V ; st ; arr(t) ⪢ ⭆ ⪡ V ; (t st) ; arr(t) ; [] ⪢ 

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
                                                       ((ST.shift (V1⁺)%re (V2⁺ - V1⁺) W) ++ W') ⪢

  | fT_rsf (r : resource) (st v : Λ) (V : 𝐕) :

                               V⌊r⌋ = Some (⩽ v … ⩾) -> 
  (* ------------------------------------------------------------------------ *)
       ⪡ V ; st ; rsf[r] ⪢ ⭆ ⪡ ⌈ r ⤆ ⩽ … st ⩾ ⌉ V ; v ; rsf[r] ; [] ⪢

  | fT_wh (st st' i t t' : Λ) (V V1 : 𝐕) (W : 𝐖) :
                
       ⪡ (⌈S (V⁺) ⤆ ⩽ <[unit]> … ⩾⌉ (⌈V⁺ ⤆ ([⧐ V⁺ – 2] ⩽ i … ⩾)%cl⌉ ([⧐ V⁺ – 2] V))) ; 
                                    (<[[⧐ {V⁺} – 2] st]>) ; t ⪢ ⭆ ⪡ V1 ; st' ; t' ; W ⪢ ->
  (* ------------------------------------------------------------------------------------------ *)
       ⪡ V ; st ; wormhole(i;t) ⪢  
       ⭆ ⪡ V1 ; st' ; t' ; ((V⁺)%re,S (V⁺)%re,<[[⧐ {(V⁺)%re} – {(V1⁺ - V⁺)%re}]i]>) :: W ⪢

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

(** *** [well_formed_ec] properties *)


Fact WF_ec_In (Rc : ℜ) (V : 𝐕):
  WF(Rc,V) -> forall r, (r ∈ Rc)%rc <-> r ∈ V.
Proof. now intros [HeqDom _]. Qed.

Fact WF_ec_Wf (Rc : ℜ) (V : 𝐕):
  WF(Rc,V) -> (Rc⁺ ⊩ Rc)%rc /\ V⁺ ⊩ V.
Proof. intros [_ [HvRe [HvV _]]]; now split. Qed.

Fact WF_ec_well_typed (Rc : ℜ) (V : 𝐕):
  WF(Rc,V) -> 
  forall (r : resource) (α β : Τ) (v : 𝑣),
    Rc⌊r⌋%rc = Some (α,β) ->  V⌊r⌋ = Some v  -> 
    match v with
      | (⩽ v' … ⩾) => ∅%vc ⋅ Rc ⊢ v' ∈ β
      | (⩽ … v' ⩾) => ∅%vc ⋅ Rc ⊢ v' ∈ α
    end.
Proof. 
  intros [_ [_ [_ Hwt]]] r v α β HfRe HfV. 
  now apply (Hwt r). 
Qed.

#[export] Instance WF_ec_iff : Proper (RC.eq ==> RE.eq ==> iff) well_formed_ec.
Proof.
  intros Rc Re1 HeqRe V V1 HeqV; unfold well_formed_ec. 
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

Corollary WF_ec_Empty (Rc : ℜ) (V : 𝐕):
  WF(Rc,V) -> isEmpty(Rc)%rc <-> isEmpty(V).
Proof. intros [HeqDom _]; now apply RE.eqDom_Empty. Qed.

Corollary WF_ec_is_empty (Rc : ℜ) (V : 𝐕):
  WF(Rc,V) -> RC.Raw.is_empty Rc = RE.Raw.is_empty V.
Proof. intros [HeqDom _]; now apply RE.eqDom_is_empty. Qed.

Corollary WF_ec_find (Rc : ℜ) (V : 𝐕):
  WF(Rc,V) -> forall r α β, 
  Rc⌊r⌋%rc = Some(α, β) -> exists v, (V⌊r⌋ = Some v)%type.
Proof. 
  intros [HeqDom _] r α β HfRe.
  now apply (RE.eqDom_find Rc _ HeqDom r α β).
Qed.

Corollary WF_ec_max (Rc : ℜ) (V : 𝐕):
  WF(Rc,V) -> max(Rc)%rc = max(V).
Proof. intros [HeqDom _]; now apply RE.eqDom_max. Qed.

Corollary WF_ec_new (Rc : ℜ) (V : 𝐕):
  WF(Rc,V) -> Rc⁺%rc = V⁺.
Proof. intros [HeqDom _]; now apply RE.eqDom_new. Qed.


Lemma WF_ec_wh (Rc : ℜ) (V : 𝐕) (α : Τ) (i : Λ) :
  (Rc⁺%rc ⊩ α)%ty -> (Rc⁺%rc ⊩ i)%tm -> ∅%vc ⋅ Rc ⊢ i ∈ α ->
  WF(Rc,V) ->
  WF((RC.Raw.add (S (Rc⁺)%rc) (α,<[𝟙]>) (RC.Raw.add (Rc⁺)%rc (<[𝟙]>,α) Rc)),
       (RE.Raw.add (S  (V⁺)) (Cell.inp <[unit]>) 
             (RE.Raw.add (V⁺) (Cell.shift (V⁺) 2 (Cell.inp i)) ([⧐ (V⁺) – 2] V)))).
Proof.
  intros Hvτ Hvi Hwti Hwf. 
  apply (WF_ec_new Rc V) in Hwf as Hnew.
  apply (WF_ec_Wf Rc V) in Hwf as Hv.
  destruct Hv as [HvRe HvV].
  repeat split.
  - intro HIn. 
    repeat rewrite RE.add_in_iff.  
    repeat apply RC.add_in_iff in HIn as [Heq' | HIn]; subst; auto.
    repeat right.
    rewrite (WF_ec_In Rc V) in HIn; auto.
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
    now apply (WF_ec_In Rc V).
  - apply RC.Wf_wh_full; auto; 
    split; unfold Cell.Wf; simpl; auto; constructor.
  - apply RE.Wf_wh_full; auto; 
    unfold Cell.Wf; simpl; try constructor.
    now rewrite <- Hnew.
  - intros r τ β v HfRe HfV.
    destruct (Resource.eq_dec r (S (Rc⁺)%rc)); subst.
    -- rewrite RE.add_eq_o in HfV; auto.
       rewrite RC.add_eq_o in HfRe; auto.
       inversion HfRe; inversion HfV; subst; clear HfV HfRe.
       constructor.
    -- destruct (Resource.eq_dec r (Rc⁺)%rc) as [| Hneq]; subst.
       + rewrite RE.add_neq_o in HfV; try lia.
         rewrite RE.add_eq_o in HfV; auto.
         rewrite RC.add_neq_o in HfRe; try lia.
         rewrite RC.add_eq_o in HfRe; auto.
         inversion HfRe; inversion HfV; subst; clear HfV HfRe.
         apply (weakening_ℜ_2 _ _ _ Rc); auto.
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
         apply (WF_ec_well_typed Rc V Hwf r' _ _ v') in HfRe as Hwv'; auto.
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
            rewrite <- (RE.eqDom_new Rc V); auto.
            apply well_typed_implies_Wf in Hwti as []; auto.
         ++ rewrite Resource.max_r; auto; simpl.
            rewrite <- (RE.eqDom_new Rc V); auto.
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

Lemma fT_inputs_halts_eT_r (Rc: ℜ) (V: 𝐕) (t1 t2 t2': Λ) :
  fT_inputs_halts (Rc⁺)%rc V t1 t2 -> (Rc⁺)%rc ⊨ t2 ⟼ t2' -> fT_inputs_halts (Rc⁺)%rc V t1 t2'.
Proof.
  intros [HltV [Hlt1 Hlt2]] HeT; do 2 (split; auto).
  apply evaluate_preserves_halting in HeT.
  now rewrite <- HeT.
Qed.

Lemma fT_inputs_halts_eT_l (Rc: ℜ) (V: 𝐕) (t1 t1' t2: Λ) :
  fT_inputs_halts (Rc⁺)%rc V t1 t2 -> (Rc ⁺)%rc ⊨ t1 ⟼ t1' -> fT_inputs_halts (Rc⁺)%rc V t1' t2.
Proof.
  intros [HltV [Hlt1 Hlt2]] HeT; do 2 (split; auto).
  apply evaluate_preserves_halting in HeT.
  now rewrite <- HeT.
Qed.

Lemma fT_inputs_halts_first (Rc: ℜ) (V: 𝐕) (t1 t2 t3: Λ) :
  fT_inputs_halts (Rc⁺)%rc V <[⟨t1, t2⟩]> <[first(t3)]> -> fT_inputs_halts (Rc⁺)%rc V t1 t3.
Proof.
  intros [HltV [Hltpair Hltfirst]]. 
  do 2 (split; auto).
  - now apply halts_pair in Hltpair as [].
  - now apply halts_first.
Qed.

Lemma fT_inputs_halts_comp_l (Rc: ℜ) (V: 𝐕) (t1 t2 t3: Λ) :
  fT_inputs_halts (Rc⁺)%rc V t1 <[t2 >>> t3]> -> fT_inputs_halts (Rc⁺)%rc V t1 t2.
Proof.
  intros [HltV [Hltpair Hltfirst]]. 
  do 2 (split; auto).
  now apply halts_comp in Hltfirst as [].
Qed.

Lemma fT_inputs_halts_comp_r (Rc Rc': ℜ) (V V': 𝐕) (W: 𝐖) (t1 t1' t2 t2' t3: Λ) :
  (Rc ⊆ Rc')%rc -> 
  fT_inputs_halts (Rc⁺)%rc V t1 <[t2 >>> t3]> -> 
  fT_outputs_halts (Rc'⁺)%rc V' W t1' t2' -> 
  fT_inputs_halts (Rc'⁺)%rc V' t1'  <[ [⧐{(Rc⁺)%rc} – {(Rc'⁺)%rc - (Rc⁺)%rc}] t3]>.
Proof.
  intros Hsub [HltV [Hltpair Hltcomp]] [HltV' [HltW [Hlt1' Hlt2']]]. 
  do 2 (split; auto).
  apply halts_comp in Hltcomp as [].
  apply halts_weakening; auto.
  now apply RC.Ext.new_key_Submap.
Qed.

Lemma fT_inputs_halts_wh  (Rc: ℜ) (V: 𝐕) (τ: Τ) (t1 t2 t3: Λ) :
  (Rc⁺)%rc = V⁺ ->
  fT_inputs_halts (Rc⁺)%rc V t1 <[wormhole(t2;t3)]> ->
  fT_inputs_halts ((⌈S (Rc⁺) ⤆ (τ, <[𝟙]>)⌉ (⌈Rc⁺ ⤆ (<[𝟙]>, τ)⌉ Rc))⁺)%rc
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

Lemma fT_outputs_halts_eT_r (Rc: ℜ) (V: 𝐕) (W: 𝐖) (t1 t2 t2': Λ) :
  fT_outputs_halts (Rc⁺)%rc V W t1 t2' -> (Rc ⁺)%rc ⊨ t2 ⟼ t2' -> fT_outputs_halts (Rc⁺)%rc V W t1 t2.
Proof.
  intros [HltV [HltW [Hlt1 Hlt2]]] HeT; do 3 (split; auto).
  apply evaluate_preserves_halting in HeT.
  now rewrite HeT.
Qed.

Lemma fT_outputs_halts_arr (Rc: ℜ) (V: 𝐕) (t1 t2: Λ) :
  fT_inputs_halts (Rc⁺)%rc V t1 <[arr(t2)]> -> 
  halts (Rc⁺)%rc <[t2 t1]> -> fT_outputs_halts (Rc⁺)%rc V [] <[t2 t1]> <[arr(t2)]>.
Proof.
  intros [HltV [Hlt1 Hltarr]] Hltapp.
  repeat split; auto.
  apply ST.halts_nil.
Qed.

Lemma fT_outputs_halts_first (Rc Rc': ℜ) (V V': 𝐕) (W: 𝐖) (t1 t1' t2 t3 t3': Λ) :
  (Rc ⊆ Rc')%rc -> 
  fT_inputs_halts (Rc⁺)%rc V <[⟨t1, t2⟩]> <[first(t3)]> ->
  fT_outputs_halts (Rc'⁺)%rc V' W t1' t3' ->
  fT_outputs_halts (Rc'⁺)%rc V' W <[⟨t1', [⧐{(Rc⁺)%rc} – {(Rc'⁺)%rc - (Rc⁺)%rc}] t2⟩]> <[first(t3')]>.
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
  fT_outputs_halts (Rc⁺)%rc V W t1 t2 ->
  fT_outputs_halts (Rc'⁺)%rc V' W' t1' t3 ->
  fT_outputs_halts (Rc'⁺)%rc V' ((ST.shift (Rc⁺)%rc ((Rc'⁺)%rc - (Rc⁺)%rc) W) ++ W')
                   t1' <[([⧐{(Rc⁺)%rc} – {(Rc'⁺)%rc - (Rc⁺)%rc}] t2) >>> t3]> .
Proof.
  intros Hsub [HltV [HltW [Hlt1 Hlt2]]] [HltV' [HltW' [Hlt1' Hlt3]]].
  repeat split; auto.
  - apply ST.halts_app; split; auto.
    apply ST.halts_weakening; auto.
    now apply RC.Ext.new_key_Submap.
  - apply halts_comp; split; auto.
    apply halts_weakening; auto.
    now apply RC.Ext.new_key_Submap.
Qed.

Lemma fT_outputs_halts_rsf (r: resource) (Rc : ℜ) (V: 𝐕) (t1 t2: Λ) :
  fT_inputs_halts (Rc⁺)%rc V t1 <[rsf[r]]> -> V⌊r⌋ = Some (⩽ t2 … ⩾) -> 
  fT_outputs_halts (Rc⁺)%rc (⌈r ⤆ ⩽ … t1 ⩾⌉ V) [] t2 <[rsf[r]]>.
Proof.
  intros [HltV [Hlt1 _]] HfiV.
  repeat split.
  - apply RE.halts_add; split; auto.
  - apply ST.halts_nil.
  - apply HltV in HfiV; auto.
  - exists <[rsf[r]]>; split; auto; reflexivity.
Qed.

Lemma fT_outputs_halts_wh (Rc Rc': ℜ) (V V': 𝐕) (W: 𝐖) (t1 t2 t3: Λ) :
  (Rc ⊆ Rc')%rc -> 
  (Rc⁺)%rc = V⁺ ->
  (Rc'⁺)%rc = V'⁺ ->
  halts (Rc⁺)%rc t3 ->
  fT_outputs_halts (Rc'⁺)%rc V' W t1 t2 ->
  fT_outputs_halts (Rc'⁺)%rc V' 
                   (((V⁺)%re, S (V⁺)%re, <[[⧐ {V⁺%re} – {(V'⁺)%re - (V⁺)%re}] t3]>) :: W) t1 t2.
Proof.
  intros Hsub Heq Heq' Hlt [HltV [HltW [Hlt1 Hlt2]]].
  repeat split; auto.
  constructor; auto.
  rewrite Heq, Heq' in *.
  apply halts_weakening; auto.
  rewrite <- Heq.
  rewrite <- Heq'.
  apply RC.Ext.new_key_Submap; auto.
Qed.

(** ---- *)

Section props.

(** ** Preservation - Functional *)

Hint Resolve VContext.Wf_empty ST.Wf_nil Resources.Wf_empty : core.

(** *** Preservation of well-formedness through the functional transition 

  Suppose a functional transition (1), if input components ([V], [st] and [sf]) are well-formed under [V⁺] (2,3,4), then output components ([V1], [st'], [sf'] and [W]) are well-formed under [V1⁺] (5). In addition, we can state that [V⁺] is lower or equal to [V1⁺] (6).
*)
Lemma functional_preserves_Wf (V V1 : 𝐕) (W : 𝐖) (st st' sf sf' : Λ) :

               (* (1) *) ⪡ V ; st ; sf ⪢ ⭆ ⪡ V1 ; st' ; sf' ; W ⪢ ->
        (* (2) *) V⁺ ⊩ V -> (* (3) *) (V⁺ ⊩ st)%tm -> (* (4) *) (V⁺ ⊩ sf)%tm ->
  (* ------------------------------------------------------------------------------ *)
       (* (5) *) V1⁺ ⊩ V1 /\ (V1⁺ ⊩ st')%tm /\ (V1⁺ ⊩ sf')%tm /\ (ST.Wf (V1⁺)%re W) /\ 
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
  - assert ((V⁺)%re ⊩ <[t st]>)%tm.
    { constructor; inversion Hvt; now subst. }
    do 5 (split; auto).
  (* fT_first *)
  - inversion Hvst; inversion Hvt; subst; fold Term.Wf in *; clear Hvst Hvt. 
    destruct IHfT as [HvV1 [Hvst' [Hvt'' [HvW Hlt]]]]; auto.
    repeat split; auto; try (now destruct HvW); try (constructor); auto.
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
         apply ST.Wf_app. 
         split; auto.
         now apply ST.shift_preserves_wf_2.
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
      now apply Term.shift_preserves_wf.
    + do 3 (split; auto); split; try lia.
      apply ST.Wf_cons; split; auto.
      repeat split; try (unfold Resource.Wf; lia).
      apply Term.shift_preserves_wf_2; auto; lia.
Qed.

(** *** Preservation of environment's keys through the functional transition 
 
  Suppose a functional transition (1), we state that all keys in [V] are in [V1], i.e. we do not forget keys during the transition.
*)
Lemma functional_preserves_keys (V V1 : 𝐕) (W : 𝐖) (sv sv' sf sf' : Λ) :
  
       (* (1) *) ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ ->
  (* ---------------------------------------------------------- *)
       (forall (r : resource), r ∈ V -> r ∈ V1) /\ V⁺ <= V1⁺.
Proof.
  intro fT; induction fT; auto.
  (* fT_comp *)
  - destruct IHfT1, IHfT2; split; auto; lia.
  (* fT_rsf *)
  - split.
    -- intros r' HIn. 
       destruct (Resource.eq_dec r r'); subst; apply RE.add_in_iff; auto.
    -- apply RE.add_id in H.
       rewrite <- H.
       do 3 rewrite RE.Ext.new_key_add_max; lia.
  (* fT_wh *)
  - destruct IHfT as [HIn Hleq].
    split.
    -- intros r HInV. 
       apply HIn.
       do 2 rewrite RE.add_in_iff.
       do 2 right.
       now rewrite RE.shift_in_new_key.
    -- do 2 rewrite RE.Ext.new_key_add_max in Hleq; lia.
Qed.

(** *** W properties *)
Lemma functional_W_props (V V1 : 𝐕) (W : 𝐖) (sv sv' sf sf' : Λ) :

       ⪡ V ; sv ; sf ⪢ ⭆ ⪡ V1 ; sv' ; sf' ; W ⪢ -> 
  (* --------------------------------------------------------------- *)
       NoDup (ST.keys W) /\
       (forall (r: resource), r ∈ (RE.diff V1 V) <-> (In r (ST.keys W))) /\
       (~ (W = []) -> (V1⁺)%re = (ST.new_key W) /\ (ST.new_key W) > (V⁺)%re).
Proof.
  intro fT; induction fT; auto.
  (* fT_arr *)
  - split; try constructor.
    -- intro r; split; intro HIn. 
       + apply RE.diff_in_iff in HIn as []; contradiction.
       + inversion HIn.
    -- intro Hc; exfalso; now apply Hc.
  (* fT_comp *)
  - destruct IHfT1 as [HNoD1 [HDom1 HnEmp1]];
    destruct IHfT2 as [HNoD2 [HDom2 HnEmp2]].

    (* clean *)
    move HNoD2 before HNoD1; move HDom2 before HDom1.
    (* clean *)

    split.
    {
      apply ST.NoDup_keys_app; auto.
      - now apply ST.NoDup_keys_shift.
      - intros r HIn.
        rewrite <- HDom2 in HIn.
        apply RE.diff_in_iff in HIn as [HIn HnIn].
        intro HIn'.
        destruct W.
        -- simpl in *; contradiction.
        -- remember (p :: W) as W1.
           destruct HnEmp1.
           + rewrite HeqW1; symmetry; apply nil_cons.
           + rewrite H in HIn'.
             rewrite ST.keys_in_shift_new_key in HIn'.
             rewrite <- HDom1 in HIn'.
             apply RE.diff_in_iff in HIn' as [HIn' HnIn'].
             contradiction.
    }
    split.
    {
      split. 
      - intros HIn.
        rewrite ST.keys_in_app.
        apply RE.diff_in_iff in HIn as [HIn HnIn].
        destruct (RE.In_dec V1 r).
        -- assert (Hdiff: r ∈ RE.diff V1 V).
           { apply RE.diff_in_iff; split; auto. }
           rewrite HDom1 in Hdiff.
           destruct W.
           + simpl in *; inversion Hdiff.
           + remember (p :: W) as W1.
             destruct HnEmp1.
             ++ rewrite HeqW1; symmetry; apply nil_cons.
             ++ rewrite H.
                rewrite ST.keys_in_shift_new_key; auto.
        -- assert (Hdiff: r ∈ RE.diff V2 V1).
           { apply RE.diff_in_iff; split; auto. }
           rewrite HDom2 in Hdiff; now right.
      - intro HIn.
        rewrite ST.keys_in_app in HIn; destruct HIn as [HIn|HIn].
        -- destruct W.
           + simpl in *; inversion HIn.
           + remember (p :: W) as W1.
             destruct HnEmp1.
             ++ rewrite HeqW1; symmetry; apply nil_cons.
             ++ rewrite H in HIn.
                rewrite ST.keys_in_shift_new_key in HIn; auto.
                rewrite <- HDom1 in HIn.
                rewrite RE.diff_in_iff in *.
                destruct HIn as [HIn HnIn].
                split; auto.
                apply functional_preserves_keys in fT2 as [Heq _]; auto.
        -- rewrite <- HDom2 in HIn.
           rewrite RE.diff_in_iff in *.
           destruct HIn as [HIn HnIn].
           split; auto.
           intro HIn'.
           apply HnIn.
           apply functional_preserves_keys in fT1 as [Heq _]; auto.
    }
    {
      rewrite ST.new_key_app.
      destruct W.
      - simpl in *.
        destruct W'.
        -- contradiction.
        -- intros. 
           remember (p :: W') as W1.
           destruct HnEmp2; auto.
           split; auto.
           apply functional_preserves_keys in fT1 as [_ ]; lia.
      - remember (p :: W) as W1.
        intros.
        destruct HnEmp1.
        -- rewrite HeqW1; symmetry; apply nil_cons.
        -- rewrite H0.
           rewrite ST.new_key_shift_refl; auto.
           rewrite <- H0.
           destruct W'.
           + simpl.
             rewrite max_l; try lia.
             apply ST.eqDom'_new_key in HDom2; auto.
             simpl in HDom2; split; try lia.
             apply functional_preserves_keys in fT2 as IH.
             destruct IH as [HIn ].
             rewrite RE.new_key_diff with (m := V1); auto.
             rewrite HDom2; lia.
           + remember (p0 :: W') as W2.
             destruct HnEmp2.
             ++ rewrite HeqW2; symmetry; apply nil_cons.
             ++ rewrite <- H2 in *; lia.
    }  
  (* fT_rsf *)
  - simpl; split; intros; try constructor.
    -- split; intros.
       + apply RE.diff_in_iff in H0 as [HIn HnIn].
         apply RE.add_in_iff in HIn as [|HIn].
         ++ subst.
            exfalso; apply HnIn.
            exists (Cell.inp v).
            now apply RE.find_2.
         ++ contradiction.
       + inversion H0.
    -- intro Hc; contradiction.
  (* fT_wh *)
  - destruct IHfT as [HNoD [HDom HnEmp]].
    split.
    {
      simpl in *.
      constructor.
      - intros [|HIn]; try lia.
        rewrite <- HDom in HIn.
        apply RE.diff_in_iff in HIn as [_ HnIn].
        do 2 rewrite RE.add_in_iff in HnIn.
        apply HnIn; auto.
      - constructor; auto.
        intro HIn.
        rewrite <- HDom in HIn.
        apply RE.diff_in_iff in HIn as [_ HnIn].
        rewrite RE.add_in_iff in HnIn.
        apply HnIn; auto.
    }
    split.
    {
      split.
      - rewrite RE.diff_in_iff.
        intros [HIn HnIn].
        simpl.
        destruct (Resource.eq_dec (V⁺)%re r); subst; auto.
        destruct (Resource.eq_dec (S (V⁺))%re r); subst; auto.
        do 2 right.
        rewrite <- HDom.
        rewrite RE.diff_in_iff; split; auto.
        do 2 rewrite RE.add_in_iff; intros [|[|]]; try lia.
        now rewrite RE.shift_in_new_key in H.
      - simpl; intros [|[|HIn]]; subst.
      + rewrite RE.diff_in_iff; split.
        ++ apply functional_preserves_keys in fT as [HIn _].
           apply HIn.
           do 2 rewrite RE.add_in_iff; auto.
        ++ apply RE.Ext.new_key_notin; lia.
      + rewrite RE.diff_in_iff; split.
        ++ apply functional_preserves_keys in fT as [HIn _].
           apply HIn.
           rewrite RE.add_in_iff; auto.
        ++ apply RE.Ext.new_key_notin; lia.
      + rewrite <- HDom in HIn.
        rewrite RE.diff_in_iff in *.
        destruct HIn as [HIn HnIn].
        split; auto.
        do 2 rewrite RE.add_in_iff in HnIn.
        intro; apply HnIn.
        do 2 right.
        now rewrite RE.shift_in_new_key.
    }
    {
      intros; split; try (now simpl; lia).
      destruct W.
      - apply ST.eqDom'_new_key in HDom; auto.
        simpl in HDom.
        apply functional_preserves_keys in fT as IH.
        destruct IH as [HIn ].
        rewrite RE.new_key_diff
        with (m := (⌈S (V⁺) ⤆ ⩽ unit … ⩾ ⌉ (⌈V⁺ ⤆ ⩽ [⧐{V⁺} – 2] i … ⩾ ⌉ ([⧐V⁺ – 2] V)))) 
        at 1; auto.
        do 2 rewrite RE.Ext.new_key_add_max.
        rewrite ST.new_key_cons.
        simpl ([] ⁺)%sk.
        rewrite RE.shift_new_refl; auto.
        replace (RE.diff V1 (⌈ S (V ⁺) ⤆ ⩽ unit … ⩾ ⌉ (⌈ V ⁺ ⤆ ⩽ [⧐{V ⁺} – 2] i … ⩾ ⌉ ([⧐V ⁺ – 2] V))) ⁺) with 0.
        lia.
      - remember (p :: W) as W1.
        destruct HnEmp.
        -- rewrite HeqW1; symmetry; apply nil_cons.
        -- rewrite ST.new_key_cons.
           rewrite <- H0.
           do 2 rewrite RE.Ext.new_key_add_max in H1.
           lia.
    }
Qed. 

Definition isvalueof (n : lvl) (t v : Λ) := n ⊨ t ⟼⋆ v /\ Term.value v.


Lemma isvalueof_eT (n : lvl) (t t' : Λ) (v : Λ) :
  n ⊨ t ⟼ t' -> isvalueof n t v -> isvalueof n t' v.
Proof.
  intros HeT [HmeT Hv].
  split; auto.
  revert t' HeT Hv.
  induction HmeT; intros.
  - apply evaluate_not_value in HeT; contradiction.
  - eapply evaluate_deterministic in H; eauto; subst; auto.
Qed.

Lemma isvalueof_eT' (n : lvl) (t t' : Λ) (v : Λ) :
  n ⊨ t ⟼ t' -> isvalueof n t' v -> isvalueof n t v.
Proof.
  intros HeT [HmeT Hv].
  split; auto.
  transitivity t'; auto.
  now apply eT_to_MeT.
Qed.


Lemma isvalueof_first (n : lvl) (t v : Λ) :
  isvalueof n <[first(t)]> <[first(v)]> -> isvalueof n t v.
Proof.
  intros [HmeT Hvt]; inversion Hvt; subst.
  split; auto.
  clear Hvt.
  dependent induction HmeT; subst; auto.
  - reflexivity.
  - inversion H; subst.
    transitivity t'; auto.
    now apply eT_to_MeT.
Qed.

Lemma isvalueof_first' (n : lvl) (t v : Λ) :
  isvalueof n t v -> isvalueof n <[first(t)]> <[first(v)]>.
Proof.
  intros [HmeT Hvt]; split; auto.
  now apply multi_first.
Qed.

Lemma isvalueof_compl (n : lvl) (t1 t2 v : Λ) :
  halts n t2 ->
  isvalueof n t1 v ->
  exists v', isvalueof n t2 v' /\ isvalueof n <[t1 >>> t2]> <[v >>> v']>.
Proof.
  intros [v' [HmeT' Hv']] [HmeT Hv].
  exists v'; split.
  - split; auto.
  - split; auto.
    transitivity <[v >>> t2]>.
    -- now apply multi_comp1.
    -- now apply multi_comp2.
Qed.

Lemma isvalueof_compr (n : lvl) (t1 t2 v : Λ) :
  halts n t1 ->
  isvalueof n t2 v ->
  exists v', isvalueof n t1 v' /\ isvalueof n <[t1 >>> t2]> <[v' >>> v]>.
Proof.
  intros [v' [HmeT' Hv']] [HmeT Hv].
  exists v'; split.
  - split; auto.
  - split; auto.
    transitivity <[v' >>> t2]>.
    -- now apply multi_comp1.
    -- now apply multi_comp2.
Qed.

Lemma isvalueof_wh (n : lvl) (i t v : Λ) :
  halts n i ->
  isvalueof (S (S n)) t v -> 
  exists v', isvalueof n i v' /\ isvalueof n <[wormhole(i;t)]> <[wormhole(v';v)]>.
Proof.
  intros [v' [HmeT' Hv']] [HmeT Hv].
  exists v'.
  split; split; auto.
  transitivity <[wormhole(v';t)]>.
  - now apply multi_wh1.
  - now apply multi_wh2.
Qed.

Lemma isvalueof_shift (n m : lvl) (t v : Λ) :
  n <= m ->
  isvalueof m  <[ [⧐ n – {m - n}] t]> v ->
  exists v', isvalueof n t v' /\ v =  <[[⧐ n – {m - n}] v']>.
Proof.
  intros Hle [HmeT Hv].
  apply multi_evaluate_shift_e in HmeT as [t' [HmeT]]; auto; subst.
  rewrite <- Term.shift_value_iff in Hv.
  exists t'; split; auto.
  split; auto.
Qed.


Inductive alt_wt : ℜ -> Λ -> Τ -> list (ℜ * Λ * Τ * Τ) -> Prop :=
  | awt_unit (Re : ℜ) : alt_wt Re <[unit]> <[𝟙]> nil

  | awt_pair (Re : ℜ) (t1 t2 : Λ) (α β : Τ) l1 l2 : 
      alt_wt Re t1 α l1 ->
      alt_wt Re t2 β l2 ->
      alt_wt Re <[⟨t1,t2⟩]> <[α × β]> (List.app l1 l2)

  | awt_abs (Re : ℜ) x (t : Λ) (α β : Τ) :

    ∅%vc ⋅ Re ⊢ (\x, t) ∈ (α → β) ->
    alt_wt Re <[\x, t]> <[α → β]> nil

  | awt_arr (Re Re' : ℜ) (t : Λ) (α β : Τ) :

         (Re' = Re)%rc ->
         ∅%vc ⋅ Re' ⊢ t ∈ (α → β) -> 
         alt_wt Re <[arr(t)]> <[α ⟿ β ∣ ∅%s]> [(Re',t,α,β)]

  | awt_first (Re : ℜ) (R : resources) (t : Λ) (α β τ : Τ) l :

         alt_wt Re t <[α ⟿ β ∣ R]> l  ->
         alt_wt Re <[first(t)]> <[(α × τ) ⟿ (β × τ) ∣ R]> l

  | awt_comp (Re : ℜ) (R R1 R2 : resources) (t1 t2 : Λ) (α β τ : Τ) l1 l2 :

         alt_wt Re t1 <[α ⟿ τ ∣ R1]> l1 -> (R = (R1 ∪ R2))%s -> 
         alt_wt Re t2 <[τ ⟿ β ∣ R2]> l2 ->
         alt_wt Re <[t1 >>> t2]> <[α ⟿ β ∣ R]> (List.app l1 l2)

  | awt_rsf (Re : ℜ) (r : resource) (τin τout : Τ) :

              Re ⌊r⌋%rc = Some (τin,τout) ->
         alt_wt Re <[rsf[r]]> <[τin ⟿ τout ∣ \{{r}}]> nil

  | awt_wh (Re : ℜ) (R R' : resources) (t1 t2 : Λ) (α β τ : Τ) l1 l2 :

         (R = R' \ \{{ (Re⁺)%rc; (S (Re⁺)%rc) }})%s -> 

         alt_wt Re t1 τ l1 ->
         alt_wt (⌈(S (Re⁺)) ⤆ (τ,<[𝟙]>)⌉ (⌈Re⁺ ⤆ (<[𝟙]>,τ)⌉ Re))%rc t2 <[α ⟿ β ∣ R']> l2 ->
        alt_wt Re <[wormhole(t1;t2)]> <[α ⟿ β ∣ R]> (List.app l1 l2).

#[export] Instance awt_iff : 
  Proper (RC.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> iff) alt_wt.
Proof.
  intros Rc Rc' HeqRc t' t Heqt ty' ty Heqty l' l Heql; subst.
  split; intro Hawt.
  - revert Rc' HeqRc.
    induction Hawt; intros; try (now constructor; auto).
    -- constructor; now rewrite <- HeqRc.
    -- constructor; auto.
       now rewrite H.
    -- econstructor; eauto.
    -- constructor; now rewrite <- HeqRc.
    -- apply awt_wh with (τ := τ) (R' := R'); auto.
       + rewrite <- HeqRc; auto.
       + apply IHHawt2.
         rewrite <- HeqRc; reflexivity.
  - revert Rc HeqRc.
    induction Hawt; intros; try (now constructor; auto).
    -- constructor; now rewrite HeqRc.
    -- constructor; auto.
       now rewrite H.
    -- econstructor; eauto.
    -- constructor; now rewrite HeqRc.
    -- apply awt_wh with (τ := τ) (R' := R'); auto.
       + rewrite HeqRc; auto.
       + apply IHHawt2.
         rewrite HeqRc; reflexivity.
Qed.

Lemma wt_to_awt (Rc : ℜ) (v : Λ) (τ : Τ) :
  value(v) -> ∅%vc ⋅ Rc ⊢ v ∈ τ -> exists l, alt_wt Rc v τ l.
Proof.
  revert Rc τ; induction v; intros Rc τ Hv Hwt; 
  inversion Hv; subst;
  inversion Hwt; subst;
  try (now exists nil; constructor; auto).
  - apply IHv1 in H5 as [l1 Hawt1]; auto.
    apply IHv2 in H7 as [l2 Hawt2]; auto.
    exists (List.app l1 l2).
    constructor; auto. 
  - exists [(Rc,v,α,β)].
    now constructor.
  - apply IHv in H1 as [l Hawt]; auto.
    exists l; constructor; auto.
  - apply IHv1 in H3 as [l1 Hawt1]; auto.
    apply IHv2 in H7 as [l2 Hawt2]; auto.
    exists (List.app l1 l2).
    econstructor; eauto.
  - apply IHv1 in H8 as [l1 Hawt1]; auto.
    apply IHv2 in H10 as [l2 Hawt2]; auto.
    exists (List.app l1 l2).
    econstructor; eauto.
Qed.

(* Theorem weakening_ℜ_gen (k k' : lvl) (Γ : Γ) (Re Re1 : ℜ) (t : Λ) (τ : Τ) :

        (* (1) *) k <= Re⁺ ->  (* (2) *) k <= k' -> (* (3) *) k' - k = Re1⁺ - Re⁺ ->
         (* (4) *) (([⧐ k – (k' - k)] Re) ⊆ Re1)%rc -> (* (5) *) Γ ⋅ Re ⊢ t ∈ τ -> 
  (* ------------------------------------------------------------------------------------ *)
       ([⧐ k – (k' - k)] Γ)%vc ⋅ Re1 ⊢ {Term.shift k (k' - k) t} ∈ [⧐ k – {k' - k}] τ.
Proof.
  intros Hle Hle' Heq Hsub wt; revert Re1 k k' Hle Hle' Hsub Heq.
  induction wt; intros Re1 n m Hle Hle' Hsub Heq; simpl; auto.
  (* variable *)
  - constructor; now apply VC.shift_find_iff.
  (* abstraction *)
  - constructor.
    -- rewrite <- VC.shift_add; now apply IHwt.
    -- assert (Re⁺ <= Re1⁺).
       { 
         apply RC.Ext.new_key_Submap in Hsub. 
         now rewrite <- RC.shift_new_key_le in Hsub.
       }
       apply (Typ.shift_preserves_wf_gen (Re⁺)); auto; lia. 
  (* application *)
  - apply wt_app with (α := <[[⧐n – {m - n}] α]>); auto.
  (* fst *)
  - simpl in *; apply wt_fst with (β := <[[⧐ n – {m - n}] β]>); auto.
  (* snd *)
  - simpl in *; apply wt_snd with (α := <[[⧐ n – {m - n}] α]>); auto.
  (* first *)
  - econstructor; eauto. 
    assert (Re⁺ <= Re1⁺).
    { 
      apply RC.Ext.new_key_Submap in Hsub. 
      now rewrite <- RC.shift_new_key_le in Hsub.
    }
    apply Typ.shift_preserves_wf_gen with (Re⁺); auto; lia.
  (* comp *)
  - econstructor; eauto.
    -- rewrite <- Resources.shift_union.
       now rewrite H.
    -- rewrite <- Resources.shift_inter; rewrite <- H0. 
       now rewrite Resources.shift_empty.
  (* rsf *)
  - rewrite Resources.shift_singleton; constructor.
    apply RC.Submap_find with (m :=  ([⧐ n – m - n] Re)); auto.
    apply RC.shift_find_iff with (lb := n) (k := m - n) in H; auto.
  (* wormhole *)
  - assert (Hle1 : Re⁺ <= Re1⁺). 
    { 
      apply RC.Ext.new_key_Submap in Hsub. 
      now rewrite <- RC.shift_new_key_le in Hsub.
    }
    eapply wt_wh with (τ := <[[⧐ n – {m - n}] τ]>) (R' := ([⧐ n – m - n] R')%rs); auto.
    -- rewrite H; rewrite Resources.shift_diff.
       repeat rewrite Resources.shift_add_notin.
       + unfold Resource.shift. 
         rewrite <- Nat.leb_le in Hle; rewrite Hle.
         replace (n <=? S (Re⁺)) with true.
         ++ rewrite Resources.shift_empty. 
            rewrite Heq; simpl.
            now replace (Re⁺ + (Re1⁺ - Re⁺)) with (Re1⁺) by lia.
        ++ symmetry; rewrite Nat.leb_le in *; lia.
      + intro HIn; inversion HIn.
      + rewrite Resources.St.add_notin_spec; split; auto. 
        intro HIn; inversion HIn.
    -- apply Typ.shift_preserves_wf_gen with (Re⁺); auto; lia.
    -- apply Typ.shift_preserves_wf_gen with (Re⁺); auto; lia.
    -- apply IHwt2; rewrite RC.new_key_wh in *; try lia. 
       + repeat rewrite RC.shift_add_notin.
         ++ unfold PairTyp.shift; simpl; unfold Resource.shift.
           replace (n <=? S (Re⁺)) with true; replace (n <=? Re⁺) with true;
           try (symmetry; rewrite Nat.leb_le; lia).
           replace (Re⁺ + (m - n)) with (Re1⁺) by lia.
           replace (S (Re ⁺) + (m - n)) with (S (Re1⁺)) by lia.
           now repeat apply RC.Submap_add.
        ++ apply RC.Ext.new_key_notin; lia.
        ++ apply RC.Ext.new_key_notin.
           rewrite RC.Ext.new_key_add_max; lia.
      + rewrite RC.new_key_wh; lia.
Qed. *)

Definition all_arrow_halting (Rc : ℜ) (t : Λ) (τ : Τ) :=
  forall v, isvalueof (Rc⁺)%rc t v ->
  forall l, alt_wt Rc v τ l -> 
  forall Rc' t' α β, List.In (Rc',t',α,β) l -> 
  forall v', halts (Rc'⁺)%rc v' -> ∅%vc ⋅ Rc' ⊢ v' ∈ α -> halts (Rc'⁺)%rc <[t' v']>.

Lemma all_arrow_halting_eT (Rc : ℜ) (t t' : Λ) (τ : Τ) :
  (Rc⁺)%rc ⊨ t ⟼ t' -> all_arrow_halting Rc t τ -> all_arrow_halting Rc t' τ.
Proof.
  intros HeT Harrlt v Hivo l Hawt Rc' t1 ty ty' HIn v' Halt Hwt.
  apply isvalueof_eT' with (t := t) in Hivo; auto.
  apply Harrlt in Hivo.
  apply Hivo with (v' := v') in HIn; auto.
Qed.

Lemma all_arrow_halting_first (Rc : ℜ) (t : Λ) (ty ty1 ty' : Τ) R :
  all_arrow_halting Rc <[ first( t) ]> <[ ty × ty1 ⟿ ty' × ty1 ∣ R ]> ->
  all_arrow_halting Rc t <[ ty ⟿ ty' ∣ R ]>.
Proof.
  intros Harrlt v Hivo l Halt Rc' t' α β HIn v' Hlt Hwt.
  apply isvalueof_first' in Hivo.
  apply Harrlt in Hivo.
  apply Hivo with (v' := v') in HIn; auto.
  now constructor.
Qed.

Lemma all_arrow_halting_wh (Rc : ℜ) (i t : Λ) (τ ty ty' : Τ) R :
  (Rc ⁺ ⊩ Rc)%rc ->
  halts (Rc ⁺)%rc i ->
  ∅%vc ⋅ Rc ⊢ i ∈ τ ->
  all_arrow_halting Rc <[ wormhole( i; t) ]> 
                       <[ ty ⟿ ty' ∣ (R \ \{{ (Rc ⁺)%rc; S (Rc ⁺)%rc}})%s ]> ->
  all_arrow_halting (⌈ S (Rc ⁺) ⤆ (τ, <[ 𝟙 ]>) ⌉ (⌈ Rc ⁺ ⤆ (<[ 𝟙 ]>, τ) ⌉ Rc))%rc t 
                    <[ ty ⟿ ty' ∣ R]>.
Proof.
  intros Hwf Hlt Hwti Harrlt v Hivo l Hawt Rc' t' α β HIn v' Halt Hwt.
  unfold all_arrow_halting in Harrlt.
  rewrite RC.new_key_wh in Hivo.
  eapply isvalueof_wh in Hivo as [v'' [Hivo' Hivo'']]; eauto.
  specialize (Harrlt <[wormhole( v''; v)]> Hivo'').
  assert (Hawt' : exists l', alt_wt Rc v'' τ l').
  { 
    destruct Hivo' as [HmeT Hv].
    apply multi_preserves_typing with (t' := v'') in Hwti; auto.
    apply wt_to_awt; auto.  
  }
  destruct Hawt' as [l' Hawt'].
  specialize (Harrlt (l'++l)).
  destruct Harrlt with (Rc' := Rc') (t' := t') (α := α) (β := β) (v' := v'); auto.
  - econstructor; eauto; reflexivity.
  - apply in_or_app; auto.
  - exists x; auto.
Qed.

Lemma all_arrow_halting_comp (Rc : ℜ) (t1 t2 : Λ) (γ β τ : Τ) (R1 R2 : resources) :
  (Rc ⁺ ⊩ Rc)%rc ->
  halts (Rc ⁺)%rc t1 ->
  halts (Rc ⁺)%rc t2 ->
  ∅%vc ⋅ Rc ⊢ t1 ∈ (γ ⟿ τ ∣ R1) ->
  ∅%vc ⋅ Rc ⊢ t2 ∈ (τ ⟿ β ∣ R2) ->
  all_arrow_halting Rc <[ t1 >>> t2 ]> <[ γ ⟿ β ∣ (R1 ∪ R2)%s ]> ->
  all_arrow_halting Rc t1 <[γ ⟿ τ ∣ R1 ]> /\
  all_arrow_halting Rc t2 <[ τ ⟿ β ∣ R2 ]>.
Proof.
  intros Hwf Hlt1 Hlt2 Hwt1 Hwt2 Harrlt; split.
  - intros v Hivo l Hawt Rc' t' ty ty' HIn v' Halt Hwt.
    unfold all_arrow_halting in Harrlt.
    apply isvalueof_compl with (t2 := t2) in Hivo as [v'' [Hivo Hivo']]; auto.
    specialize (Harrlt <[v >>> v'']> Hivo').
    destruct Hivo as [HmeT Hv].
    apply multi_preserves_typing with (t' := v'') in Hwt2; auto.
    apply wt_to_awt in Hwt2 as [l2 Hawt2]; auto.
    specialize (Harrlt (List.app l l2)).
    destruct Harrlt with (Rc' := Rc') (t' := t') (α := ty) (β := ty') (v' := v'); auto.
    -- econstructor; eauto; reflexivity.
    -- apply in_or_app; auto.
    -- exists x; auto.
  - intros v Hivo l Hawt Rc' t' ty ty' HIn v' Halt Hwt.
    unfold all_arrow_halting in Harrlt.
    apply isvalueof_compr with (t1 := t1) in Hivo as [v'' [Hivo Hivo']]; auto.
    specialize (Harrlt <[v'' >>> v]> Hivo').
    destruct Hivo as [HmeT Hv].
    apply multi_preserves_typing with (t' := v'') in Hwt1; auto.
    apply wt_to_awt in Hwt1 as [l1 Hawt1]; auto.
    specialize (Harrlt (List.app l1 l)).
    destruct Harrlt with (Rc' := Rc') (t' := t') (α := ty) (β := ty') (v' := v'); auto.
    -- econstructor; eauto; reflexivity.
    -- apply in_or_app; auto.
    -- exists x; auto.
Qed.

Lemma all_arrow_halting_weakening (Rc Rc' : ℜ) (t : Λ) (τ : Τ) :
  (Rc ⁺ ⊩ Rc)%rc ->
  (Rc ⊆ Rc')%rc ->
  all_arrow_halting Rc t τ -> all_arrow_halting Rc' <[[⧐{(Rc⁺)%rc} – {(Rc'⁺)%rc - (Rc⁺)%rc}] t]> τ.
Proof.
  intros Hwf Hsub Harrlt v Hivo l Hawt Rc1 t' ty ty' HIn v' Halt Hwt.
  apply RC.Ext.new_key_Submap in Hsub as Hle.
  apply isvalueof_shift in Hivo as [v1 [Hivo ]]; auto; subst.
  apply Harrlt in Hivo.
Admitted.

(* 
Hypothesis all_arrow_halting : forall Rc t α β,
  ∅%vc ⋅ Rc ⊢ arr(t) ∈ (α ⟿ β ∣ ∅%s) -> forall v, ∅%vc ⋅ Rc ⊢ v ∈ α -> halts (Rc⁺)%rc <[t v]>. *)

(** *** Typing preservation through functional transition

  Suppose well-typed expression [sv], [sf], that halt, under [Rc] (1,2,4,5). In addition, suppose that [V] halts (3) and is well-formed regards of [Rc] (7). If there is a transition (6), then we can prove the following properties:
  - each data mapped with a resource name present in [R] has to be unused in [V] (8);
  - each data mapped with a resource name not present in [R'] but present in [V] 
    has to be unchanged in [V1] (9);
  - we can found a context [Re1] and a resource set [R'] such as :
    - the resource context [Rc] is a subset of [Re1] (10);
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

                all_arrow_halting Rc t <[α ⟿ β ∣ R]> ->
                fT_inputs_halts (Rc⁺)%rc V st t ->

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
          fT_outputs_halts (Rc1⁺)%rc V1 W st' t' /\

          (* typing preserved *)
          ∅%vc ⋅ Rc1 ⊢ st' ∈ β /\ ∅%vc ⋅ Rc1 ⊢ t' ∈ (α ⟿ β ∣ R') /\

          (* properties about resource context and environment preserved *)
          WF(Rc1,V1) /\

          (* properties of [W] *)
          (forall (r r' : resource) (v : Λ), 
            (In (r,r',v) W) -> exists (α : Τ), 
                               ∅%vc ⋅ Rc1 ⊢ v ∈ α /\
                               Rc1⌊r⌋%rc = Some (<[𝟙]>,α) /\ 
                               Rc1⌊r'⌋%rc = Some (α,<[𝟙]>)) /\

          (* properties of [R'] *)
          (* (14) *) (forall (r : resource), (r ∈ (R' \ R))%s -> (In r (ST.keys W)) /\ (r ∉ V)) /\
          (* (15) *) (forall (r : resource), (r ∈ R')%s -> RE.used r V1).
Proof.
  intros Harrlt Hltinp Hwt Hwtst fT; revert Rc R α β Harrlt Hltinp Hwt Hwtst.
  induction fT; intros Rc R γ β Harrlt Hltinp Hwt Hwst HWF;
  
  apply WF_ec_Wf in HWF as HvRc; destruct HvRc as [HvRc HvV];
  apply WF_ec_new in HWF as Hnew;
  
  move HvRc before HWF; move HvV before HvRc; move Hnew before HWF.
  (* fT_eT_sf *)
  - 
    (* clean *)
    move Rc before W; move R before Rc; move γ before R; move β before γ; move fT after IHfT;
    rename fT into HfT; rename H into HeT; move HeT after HfT.
    (* clean *)

    rewrite <- Hnew in HeT.
    apply evaluate_preserves_typing with (t' := t') in Hwt as Hwt'; auto.
    apply fT_inputs_halts_eT_r with (t2' := t') in Hltinp; auto.
    apply all_arrow_halting_eT with (t' := t') in Harrlt; auto.
    
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
    apply fT_inputs_halts_eT_l with (t1 := st); auto.

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
      eapply Harrlt with (v := <[arr(t)]>) (l := [(Rc,t,γ,β)]) (β := β) (Rc' := Rc); eauto.
      - constructor; auto; reflexivity.
      - now constructor.
      - simpl; auto.
      - destruct Hltinp as [_ []]; auto.
    }
    split.
    (** The output value is well-typed. *)
    { apply (wt_app _ _ _ _ γ); auto. }
    do 3 (split; auto).
    (** [W] is empty then we cannot deduce anything. *)
    { intros r r' v Hc; inversion Hc. }
    (** The set of ressource is empty the we cannot deduce anything. *)
    { split; intros r Hc; inversion Hc. } 
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
                   [HWF' [HwtW [HInRW Husd]]]]]]]]]]]].

    apply WF_ec_new in HWF' as Hnew'; auto.

    (* clean *)
    move Rc' before Rc; move R' before R; move Hwtv1' before Hwv1; clear Hwv1;
    move Hwt' before Hwt; clear Hwt; move HWF' before HWF; 
    move HsubRc before γ; move HsubR before γ; move Hltout before Hltinp;
    move Husd before Hunsd; move Hnew' before Hnew.
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
    apply all_arrow_halting_first in Harrlt; auto.
    
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
                    [HWF' [HwtW1 [HInRW1 Husd1]]]]]]]]]]]].

    (* clean *)
    move Rc' before Rc; move R1' before R1; move Hwst' before Hwst; move Hwt1' before Hwt1.
    move HsubRc before R1'; move HsubR1 before HsubRc; move HWF' before HWF; 
    move Hltout before Hltinp; move Husd1 before Hunsd1.
    (* clean *)


    apply WF_ec_new in HWF' as Hnew'; move Hnew' before Hnew.
    apply (fT_inputs_halts_comp_r Rc _ V _ _ st _ t1 _ t2) in Hltout as Hltinp''; auto.
    apply (weakening_ℜ _ _ Rc') in Hwt2 as Hwt2''; auto.
    rewrite Hnew, Hnew' in Hltinp'', Hwt2''.
    rewrite <- Hnew' in Hltinp'' at 1.
    apply IHfT2 with (R := R2) (β := β) in Hwst' as IH2; auto; clear IHfT2.

    destruct IH2 as [Hunsd2 [Hlcl2 [Rc'' [R2' [HsubRc' [HsubR2 [Hltout' [Hwst'' [Hwt2' 
                    [HWF'' [HwtW2 [HInRW2 Husd2]]]]]]]]]]]]. 
                  
    (* clean *)
    move Rc'' before Rc'; move R2' before R2; move Hwst'' before Hwst'; move Hwt2' before Hwt2;
    move HsubRc' before HsubRc; move HsubR2 before HsubR1; move HWF'' before HWF'; 
    move Hltout' before Hltout; move Husd2 before Husd1; move Hunsd2 before Hunsd1; 
    move Hlcl2 before Hlcl1; move Hwt2 before Hwt1; move HwtW2 before HwtW1; move HInRW2 before HInRW1; clear Hwt2'' Hltinp''.
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
        -- apply functional_W_props in fT1 as [_ [H _]].
           assert (HInW' : In r' (ST.keys W)) by auto.
           rewrite <- H in HInW. 
           assert ((r' ∈ R2' \ R2)%s).
           { rewrite RS.diff_spec; split; auto. }
           apply HInRW2 in H0 as [_ HIn].
           apply RE.diff_in_iff in HInW as [HIn' _].
           contradiction.
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
    { 
      intros r r' v HIn.
      apply in_app_or in HIn as [HIn|HIn].
      - destruct W.
        -- simpl in *; inversion HIn.
        -- remember (p :: W) as W1.
           apply functional_W_props in fT1 as [_ [HeqDom HnEmp]].
           destruct HnEmp.
           + rewrite HeqW1; symmetry; apply nil_cons.
           + apply ST.shift_in_e in HIn as [tp [Heq HIn]]; subst.
             destruct tp as [[rg rs] v'].
             simpl in Heq; inversion Heq.
             subst; clear Heq.
             rewrite <- ST.shift_in in HIn.
             remember (p::W) as W1.
             apply (HwtW1 _ _ _) in HIn as HI.
             destruct HI as [α [Hwfv [Hwtrg Hwtrs]]].
             exists α.
             split.
             ++ apply weakening_ℜ; auto. 
                now apply WF_ec_Wf in HWF' as [].
             ++ apply RC.Wf_find with (lb := (Rc'⁺)%rc) in Hwtrg as HI.
                * destruct HI as [Hwfrg _].
                  rewrite Resource.shift_wf_refl; auto.
                  apply (RC.Submap_find _ _ Rc' Rc'') in Hwtrg; auto.
                  split; auto.
                  apply RC.Wf_find with (lb := (Rc'⁺)%rc) in Hwtrs as HI.
                  ** destruct HI as [Hwfrs _].
                     rewrite Resource.shift_wf_refl; auto.
                     apply (RC.Submap_find _ _ Rc' Rc'') in Hwtrs; auto.
                  ** now apply WF_ec_Wf in HWF' as [].
                * now apply WF_ec_Wf in HWF' as [].
      - eapply HwtW2 in HIn; eauto.
    }
    split.
    {
      intros r HIn.
      apply RS.diff_spec in HIn as [HIn HnIn]. 
      apply RS.union_notin_spec in HnIn as [HnInR1 HnInR2].
      apply RS.union_spec in HIn as [HInR1' | HInR2'].
      - destruct (HInRW1 r) as [HInW HnInV]; try (apply RS.diff_spec; split; auto).
        split; auto.
        apply ST.keys_in_app; left.
        apply functional_W_props in fT1 as [_ [H HnEmp]].
        assert (r ∈ V1).
        { 
          rewrite <- H in HInW.
          apply RE.diff_in_iff in HInW as []; auto. 
        }
        destruct (H r) as [_ HInV1]; auto.
        rewrite <- (Resource.shift_wf_refl (Rc'⁺)%rc (Rc''⁺ - Rc'⁺)%rc r); auto.
        -- apply ST.keys_in_shift; auto.
        -- apply RE.Ext.new_key_in in H0.
           rewrite Hnew'.
           auto.
      - destruct (HInRW2 r).
        -- rewrite RS.diff_spec; split; auto.
        -- split; auto.
           + apply ST.keys_in_app; now right.
           + intros HInV; apply H0.
             apply functional_preserves_keys in fT1 as []; auto.
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
    {
      destruct Hltinp as [HltV [Hltst Hlt]].
      apply halts_comp in Hlt as [Hlt1 Hlt2].
      apply all_arrow_halting_comp with (τ := τ) in Harrlt as [Harrlt1 Harrlt2]; auto.
      rewrite <- Hnew, <- Hnew'.
      apply all_arrow_halting_weakening; auto.
    }
    {
      destruct Hltinp as [HltV [Hltst Hlt]].
      apply halts_comp in Hlt as [Hlt1 Hlt2].
      apply all_arrow_halting_comp with (τ := τ) in Harrlt as [Harrlt1 Harrlt2]; auto.
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
    split.
    (** The stock is empty then we cannot deduce anything. *)
    { intros r' r'' v' Hc; inversion Hc. }
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

    assert (Hltinp': fT_inputs_halts (Rc⁺)%rc V st <[wormhole(i;t)]>) by auto.
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
                   [HWF' [HwtW1 [HInRW1 Husd1]]]]]]]]]]]].
    
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
            apply Term.shift_preserves_wf. 
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
      intros r r' v [|HIn].
      - inversion H; subst; clear H.
        exists τ.
        split.
        -- rewrite <- Hnew', <- Hnew.
           apply weakening_ℜ; auto.
           now apply RC.Submap_wh_1 in HsubRc.
        -- split.
           + apply (RC.Ext.Submap_find (Rc⁺)%rc (<[𝟙]>,τ)) in HsubRc as HfiRc.
             ++ rewrite <- Hnew. auto.
             ++ rewrite RC.add_neq_o; auto.
                rewrite RC.add_eq_o; auto.
           + apply (RC.Ext.Submap_find (S (Rc⁺)%rc) (τ,<[𝟙]>)) in HsubRc as HfiRc.
             ++ rewrite <- Hnew. auto.
             ++ rewrite RC.add_eq_o; auto.
      - now apply (HwtW1 _ _ _) in HIn.
    }
    split; auto.
    {
      intros r HIn.
      apply RS.diff_spec in HIn as [HInR1 HnInR]. 
      rewrite Heq in HnInR.
      apply RS.diff_notin_spec in HnInR as [HnInR' | HIn].
      - destruct (HInRW1 r); try (now apply RS.diff_spec).
        split.
        -- simpl; auto.
        -- intro HIn.
           apply H0.
           do 2 rewrite RE.add_in_iff.
           rewrite RE.shift_in_new_key; auto.
      - rewrite <- Hnew.
        repeat rewrite RS.add_spec in HIn. 
        destruct HIn as [Heq' | [Heq' | HIn]]; try inversion HIn; subst.
        -- split.
           + simpl; auto.
           + rewrite Hnew.
             apply RE.Ext.new_key_notin; auto.
        -- split.
           + simpl; auto.
           + rewrite Hnew.
             apply RE.Ext.new_key_notin; auto.
    }
    {
      eapply all_arrow_halting_wh; eauto.
      apply Resources.eq_leibniz in Heq; subst.
      assumption.
    }
Qed.

(** ---- *)

(** ** Progress - Functional *)
Hint Resolve VContext.Wf_empty ST.Wf_nil Resources.Wf_empty : core.


Lemma progress_of_functional_value_gen (Rc: ℜ) (m n: list lvl) (V : 𝐕) (tv t: Λ) (α β : Τ) (R : resources) :

       (* (1) *) value(t) -> (* (2) *) halts (Rc⁺)%rc tv -> (* (3) *) RE.halts (Rc⁺)%rc V -> 
                all_arrow_halting Rc <[[⧐⧐ m – n] t]> <[α ⟿ β ∣ R]> ->

       (* (4) *) ∅%vc ⋅ Rc ⊢ [⧐⧐ m – n] t ∈ (α ⟿ β ∣ R) -> (* (5) *) ∅%vc ⋅ Rc ⊢ tv ∈ α ->

       (* (6) *) WF(Rc,V) -> (* (7) *)(forall (r : resource), (r ∈ R)%s -> RE.unused r V) ->
  (* ------------------------------------------------------------------------------------------ *)
       exists (V1 : 𝐕) (tv' t' : Λ) (W : 𝐖),
                                      ⪡ V ; tv ; [⧐⧐ m – n] t ⪢ ⭆ ⪡ V1 ; tv' ; t' ; W ⪢.
Proof.
  revert Rc m n V tv α β R.
  induction t;
  intros Rc m n V tv τ1 τ1' R Hvalt Hltv HltV Harrlt Hwt Hwtv HWF Hunsd;
  inversion Hvalt; subst; clear Hvalt.

  - rewrite Term.multi_shift_unit in *; inversion Hwt.
  - rewrite Term.multi_shift_abs  in *; inversion Hwt.
  - rewrite Term.multi_shift_pair in *; inversion Hwt.
 
  (* [arr] term *)
  - rewrite Term.multi_shift_arr in *.
    inversion Hwt; subst.
    exists V, <[([⧐⧐ m – n] t) tv]>, <[arr([⧐⧐ m – n] t)]>, [].
    now constructor.
 
  (* [first] term *)
  - 
    (* clean *)
    move Rc after t; move m before t; move n before m; move V before Rc;
    move tv before t; move τ1 before tv; move τ1' before τ1; move R before Rc.
    rename H0 into Hvt; move Hvt before HltV; move Hunsd after Hltv.
    (* clean *)

    rewrite Term.multi_shift_first in *. 
    inversion Hwt; subst.
    destruct Hltv as [tv' [HmeT Hvtv']].
    apply WF_ec_Wf in HWF as HI.
    destruct HI as [HwfRc HwfV].
    apply multi_preserves_typing with (t' := tv') in Hwtv as Hwtv'; auto.

    (* clean *)
    move α before tv; move τ before α; move β before α; clear Hwt;
    rename H4 into Hwt; move Hwt before Hwtv; rename H6 into Hwfτ;
    move tv' before tv; move Hwtv' before Hwtv.
    (* clean *)

    inversion Hvtv'; subst; inversion Hwtv'; subst.

    (* clean *)
    rename H into Hv1; rename H0 into Hv2; move Hv1 before Hvt;
    clear Hvtv'; move Hv2 before Hv1; rename H6 into Hwtv1;
    rename H8 into Hwtv2; move Hwtv1 before Hwtv'; clear Hwtv';
    move Hwtv2 before Hwtv1; move v1 before t; move v2 before v1.
    (* clean *)

    apply (IHt Rc m n V v1 α β R Hvt) in Hwtv1 as HI; auto; clear IHt.
    -- destruct HI as [V1 [v1' [t' [W fT]]]].
       
       (* clean *)
       move V1 before V; move v1' before tv; move t' before v1';
       move W before V1.
       (* clean *)

       exists V1, <[⟨v1',[⧐ {V⁺} – {V1⁺ - V⁺}] v2⟩]>, <[first(t')]>, W.
       rewrite (WF_ec_new Rc V) in HmeT; auto.
       apply fT_MeT_sv with (st' := <[ ⟨ v1, v2 ⟩ ]>); auto.
       now constructor.
    -- exists v1; split; auto; reflexivity.
    -- now apply all_arrow_halting_first in Harrlt. 

  (* [rsf] term *)
  - rewrite Term.multi_shift_rsf in *.
    inversion Hwt; subst.

    (* clean *)
    clear Hwt; rename H3 into Hfi; move HWF after Hfi.
    (* clean *)

    assert (Hunsd': RE.unused ([⧐⧐m – n] r)%r V).
    -- apply Hunsd. 
       now apply RS.singleton_spec.
    -- clear Hunsd. 
       apply RE.unused_find_e in Hunsd' as [v Hfi'].

       exists (⌈([⧐⧐ m – n] r)%r ⤆ ⩽ … tv ⩾ ⌉ V), v, <[rsf[([⧐⧐ m – n] r)%r]]>, [].
       now constructor.

  (* [comp] term *)
  - rewrite Term.multi_shift_comp in *. 
    inversion Hwt; subst.

    (* clean *)
    move Rc after t1; move m before t1; move n before m; move V before Rc;
    move tv before t1; move τ1 before tv; move τ1' before τ1; move R before Rc;
    move R1 before R; move R2 before R1; move τ before τ1; move t2 before t1;
    move Hunsd after Hltv; clear Hwt; rename H1 into Hvt1; rename H2 into Hvt2;
    rename H8 into Hwt1; rename H9 into HeqR; move Hwt1 after Hwtv;
    rename H10 into Hwt2; move Hwt2 before Hwt1; rename H11 into HneqR12.
    (* clean *)

    assert (Hunsd1: forall r : resource, (r ∈ R1)%s -> RE.unused r V).
    { 
      intros r HIn.
      apply Hunsd; rewrite HeqR.
      rewrite RS.union_spec; auto. 
    }
    assert (Hunsd2: forall r : resource, (r ∈ R2)%s -> RE.unused r V).
    { 
      intros r HIn.
      apply Hunsd; rewrite HeqR.
      rewrite RS.union_spec; auto. 
    }

    (* clean *)
    move Hunsd1 before Hunsd; move Hunsd2 before Hunsd1; clear Hunsd.
    (* clean *)
  
    apply WF_ec_Wf in HWF as HI; destruct HI as [HwfRc HwfV].
    apply Resources.eq_leibniz in HeqR; subst.
    assert (Hlt1 : halts (Rc ⁺)%rc <[ [⧐⧐m – n] t1 ]>).
    { 
      exists  <[ [⧐⧐m – n] t1 ]>; split; try reflexivity.
      now apply Term.multi_shift_value_iff.
    }
    assert (Hlt2 : halts (Rc ⁺)%rc <[ [⧐⧐m – n] t2 ]>).
    { 
      exists  <[ [⧐⧐m – n] t2 ]>; split; try reflexivity.
      now apply Term.multi_shift_value_iff.
    }
    eapply all_arrow_halting_comp 
    with (t1 := <[ [⧐⧐m – n] t1]>) (γ := τ1) (R1 := R1) in Hwt2 as HI; auto.
    destruct HI as  [Harrlt1 Harrlt2].
    
    apply (IHt1 Rc m n V tv τ1 τ R1) in Hwtv as HfT; clear IHt1; auto.
    destruct HfT as [V1 [tv' [t1' [W1 fT1]]]].

    (* clean *)
    move V1 before V; move tv' before tv; move t1' before t2; move W1 before V1.
    (* clean *)

    apply (functional_preserves_typing_gen Rc _ _ _ _ _ _ _ τ1 τ R1) 
    in fT1 as HI; auto.
    -- destruct HI as [_ [HfiVV1 [Rc' [R1' [HsubRc [HsubR1 [Hltout [Hwtv' [Hwt1'
                      [HWF' _]]]]]]]]]].
                      
       (* clean *)
       move Rc' before Rc; move R1' before R1; move fT1 before IHt2;
       move Hltout before Hunsd2; move Hwtv' before Hwtv; move Hwt1' before Hwt1;
       move HWF' before HWF; move HfiVV1 after Hunsd1.
       (* clean *)

       apply (weakening_ℜ _ _ Rc') in Hwt2 as Hwt2'; auto.
       rewrite <- Term.multi_shift_cons in Hwt2'.
       destruct Hltout as [HltV1 [HltW1 [Hltv' Hlt1']]].

       (* clean *)
       move Hwt2' before Hwt2.
       (* clean *)

       apply (IHt2 Rc' (Rc⁺ :: m)%rc ((Rc'⁺ - Rc⁺) :: n)%rc V1 tv' τ τ1' R2) in Hwtv' as HfT; auto.
       + destruct HfT as [V2 [tv'' [t2' [W2 fT2]]]].

         (* clean *)
         move V2 before V1; move tv'' before tv'; move t2' before t1'; move W2 before W1.
         move fT2 before fT1; clear IHt2.
         (* clean *)

         rewrite (WF_ec_new Rc' V1) in fT2; auto.
         rewrite (WF_ec_new Rc V) in fT2; auto.
         
         exists V2, tv'', <[([⧐ {V1⁺} – {V2⁺ - V1⁺}] t1') >>> t2']>, 
                         ((ST.shift (V1⁺)%re (V2⁺ - V1⁺)%re W1) ++ W2).
         apply (fT_comp _ tv'); auto.

       + admit.

       + intros r HIn.
         apply Hunsd2 in HIn as Hunsd.
         apply RE.unused_find_e in Hunsd as [v Hfi].

         (* clean *)
         move r before tv'; move v before tv'.
         (* clean *)

         apply typing_Re_R with (r := r) in Hwt2 as HIn'; auto.
         ++ rewrite (WF_ec_In Rc V) in HIn'; auto.
            destruct (RS.In_dec r R1) as [HInR1 | HnInR1].
            * exfalso.
              assert (r ∉ ∅)%s. { intro c. inversion c. }
              apply H; clear H.
              rewrite HneqR12.
              rewrite RS.inter_spec; split; auto.
            * apply (RE.Wf_in (V⁺)) in HIn' as Hwfr; auto.
              rewrite (RE.shift_find_iff (V⁺) (V1⁺ - V⁺)) in Hfi.
              rewrite Resource.shift_wf_refl in Hfi; auto.
              simpl in Hfi.
              rewrite HfiVV1 in Hfi; auto.
              apply (RE.unused_find _ <[[⧐{V ⁺} – {V1 ⁺ - V ⁺}] v]>); auto.
         ++ now apply Term.multi_shift_value_iff.

    -- repeat split; auto. 

  (* [wormhole] term *)
  - 
    (* clean *)
    move Rc before t2; move m before t2; move n before m;
    move V before Rc; move tv before t2; move τ1 before tv; move τ1' before τ1;
    move R before Rc; clear IHt1; rename H1 into Hvt1; rename H2 into Hvt2;
    move Hunsd before IHt2.
    (* clean *)

    rewrite Term.multi_shift_wh in *. 
    inversion Hwt; subst.
    apply WF_ec_Wf in HWF as H; destruct H as [HwfRe HwfV].

    (* clean *)
    move R' before R; move τ before τ1'; rename H6 into HeqR;
    rename H7 into Hwfτ1; rename H8 into Hwfτ1'; rename H9 into Hwt1;
    move Hwt1 before Hwt; rename H10 into Hwt2; move Hwt2 before Hwt1;
    clear Hwt.  
    (* clean *)

    apply (weakening_ℜ_wh _ _ _ <[𝟙]> τ) in Hwtv; auto.
    apply (IHt2 _ m n
                  (⌈S (V⁺) ⤆ ⩽<[unit]> … ⩾⌉ (⌈V⁺ ⤆ ([⧐ V⁺ – 2] ⩽ ([⧐⧐ m – n] t1) … ⩾)%cl⌉ 
                    ([⧐ V⁺ – 2] V)))
    ) with (β := τ1') (R := R') in Hwtv as HfT; auto. 
    -- destruct HfT as [V1 [tv' [t2' [W fT]]]]. 
    
       (* clean *)
       clear IHt2; move V1 before V; move tv' before tv; move t2' before tv';
       move W before V1; move fT before n.
       (* clean *)

       exists V1, tv', t2', 
              (((V⁺)%re, S (V⁺)%re, <[[⧐ {(V⁺)%re} – {(V1⁺ - V⁺)%re}] ([⧐⧐ m – n] t1)]>) :: W).
       rewrite (WF_ec_new Rc V) in fT; auto.
       now apply fT_wh.

    -- rewrite RC.new_key_wh.
       replace (S (S (Rc⁺)%rc)) with ((Rc⁺)%rc + 2) by lia.
       now apply halts_weakening_1.

    -- rewrite RC.new_key_wh.
       apply RE.halts_add; split; simpl.
       + exists <[unit]>; split; now auto.
       + apply RE.halts_add; split; simpl.
         ++ exists <[ [⧐ {V⁺} – 2] [⧐⧐ m – n] t1 ]>; split; auto.
            * reflexivity.
            * apply Term.shift_value_iff.
              now apply Term.multi_shift_value_iff.
         ++ replace (S (S (Rc⁺)%rc)) with ((Rc⁺)%rc + 2) by lia.
            rewrite (WF_ec_new Rc V) in *; auto.
            now apply RE.halts_weakening_1.
    
    -- apply Resources.eq_leibniz in HeqR; subst. 
       apply all_arrow_halting_wh with (i := <[[⧐⧐m – n] t1]>); auto.
       exists  <[ [⧐⧐m – n] t1 ]>; split; try reflexivity.
       now apply Term.multi_shift_value_iff.

    -- apply well_typed_implies_Wf in Hwt1 as Hv; auto.
       destruct Hv; apply WF_ec_wh; auto.

    -- intros r HIn.
       destruct (Resource.eq_dec r (S (V⁺))) as [| Hneq]; subst.
       + apply RE.unused_add_eq; auto; now simpl.
       + apply RE.unused_add_neq; auto.
         destruct (Resource.eq_dec r (V⁺)) as [| Hneq']; subst.
         ++ apply RE.unused_add_eq; auto; now simpl.
         ++ apply RE.unused_add_neq; auto.
            rewrite RE.unused_shift_Wf; auto.
            apply Hunsd; rewrite HeqR.
            apply RS.diff_spec; split; auto.
            rewrite (WF_ec_new Rc V); auto.
            do 2 (apply RS.add_notin_spec; split; auto).
            intro c; inversion c.
Admitted.

(** *** Progress of the functional transition 

  Suppose well-typed expressions [t] and [tv], which halt (1,2), under [Rc] (4,5). In addition, suppose that [V] halts (3) and is well-formed regards of [Rc] (6). If all resources used by [t] is unused at the beginning (7), then it exists a functional transition (8) where its outputs halt (9,10,11).
*)
Theorem progress_of_functional (Rc : ℜ) (V : 𝐕) (tv t : Λ) (α β : Τ) (R : resources) :

                 (* (1) *) fT_inputs_halts (Rc⁺)%rc V tv t ->
                all_arrow_halting Rc t <[α ⟿ β ∣ R]> ->


            (* (4) *) ∅%vc ⋅ Rc ⊢ t ∈ (α ⟿ β ∣ R) -> (* (5) *) ∅%vc ⋅ Rc ⊢ tv ∈ α ->
       (* (6) *) WF(Rc,V) -> (* (7) *) (forall (r : resource), (r ∈ R)%s -> RE.unused r V) ->

  (* ------------------------------------------------------------------------------------------ *)
       (exists (V1 : 𝐕) (tv' t' : Λ) (W : 𝐖), 
       (*  (8) *) ⪡ V ; tv ; t ⪢ ⭆ ⪡ V1 ; tv' ; t' ; W ⪢ /\
       (*  (9) *) fT_outputs_halts (V1⁺) V1 W tv' t').
Proof. 
  intros [HltV [Hltv Hlt]].
  destruct Hlt as [t' [meT Hvt']]; revert V tv α β R HltV Hltv Hvt'.
  induction meT as [t | t t1 t' HeT];
  intros V tv α β R HltV Hltv Hvt Harrlt Hwt Hwtv HWF Hunsd.
  (* t is a value *)
  - rewrite <- (Term.multi_shift_nil t) in Hwt.
    apply (progress_of_functional_value_gen _ _ _ V tv t α β R) in Hwt as fT; auto.    
    destruct fT as [V1 [tv' [t' [W fT]]]].
    rewrite Term.multi_shift_nil in *.
    exists V1, tv', t', W; split; auto.
    apply (functional_preserves_typing_gen Rc _ _ _ _ _ _ _ α β R) in fT; auto.
    -- destruct fT as [_ [_ [Rc1 [R' [_ [_ [Hltout [_ [_ [HWF' _]]]]]]]]]].
       rewrite <- (WF_ec_new Rc1 V1); auto.
    -- repeat split; auto.
       exists t; split; now auto.
  (* t can be reduced at least one time *)
  - clear meT.
    apply WF_ec_Wf in HWF as Hv; destruct Hv as [HvRe HvV].
    apply evaluate_preserves_typing with (t' := t1) in Hwt as Hwt1; auto.
    apply (IHmeT V tv α β) in Hwt1 as IH; auto.
    -- destruct IH as [V1 [tv' [t1' [W [HfT Hltout]]]]].
       exists V1, tv', t1', W; split; auto. 
       apply fT_eT_sf with (t' := t1); auto.
       now rewrite <- (WF_ec_new Rc V).
    -- apply all_arrow_halting_eT with t; auto.
Qed.

(** ---- *)

(** ** Safey - Functional *)

(** *** Resources safety 

  Suppose well-typed expressions [t] and [tv], which halt (1,2), under [Rc] (6,7). In addition, [V] halts (3) and is well-formed regards of [Rc] (4), and all resources used by [t] is unused at the beginning (5). We can state that:
  - it exists a functional transition (8), i.e. there are no stuck situation and consequently no multiple interations with the same resource;
  - used resources are still in the set at the end (9);
  - all resources not in [R] are unused during the functional transition (10);
  - all resources in [R'\R] are new and stored in [W] (11);
  - all resources in [R] are used during the functional transition (12).
*)
Theorem safety_resources_interaction (Rc : ℜ) (V : 𝐕) (t tv : Λ) (α β : Τ) (R : resources) :

                   (* (1) *) fT_inputs_halts (Rc⁺)%rc V tv t ->
                all_arrow_halting Rc t <[α ⟿ β ∣ R]> ->


      (* (4) *) WF(Rc,V) -> (* (5) *) (forall (r : resource), (r ∈ R)%s -> RE.unused r V) ->
             (* (6) *) ∅%vc ⋅ Rc ⊢ t ∈ (α ⟿ β ∣ R) -> (* (7) *) ∅%vc ⋅ Rc ⊢ tv ∈ α -> 
  (* ------------------------------------------------------------------------------------------ *)

       exists (R' : resources) (V1 : 𝐕) (tv' t' : Λ) (W: 𝐖), 
            (*  (8) *) ⪡ V ; tv ; t ⪢ ⭆ ⪡ V1 ; tv' ; t' ; W ⪢ /\

            (*  (9) *) (R ⊆ R')%s    /\
            (* (10) *)(forall (r : resource), (r ∉ R)%s /\ (r ∈ V) -> 
                          ([⧐ (V⁺) – ((V1⁺) - (V⁺))] V) ⌊r⌋ = V1 ⌊r⌋) /\
            (* (11) *) (forall (r : resource), (r ∈ (R' \ R))%s -> (In r (ST.keys W)) /\ (r ∉ V)) /\ 
            (* (12) *) (forall (r : resource), (r ∈ R)%s -> RE.used r V1).
Proof.
  intros Hltinp Harrlt Hwf Hunsd Hwt Hwtv.
  apply (progress_of_functional Rc V tv t _ β R) in Hwtv as fT; auto.
  destruct fT as [V1 [tv' [t' [W [HfT Hltout]]]]].

  (* clean *)
  move tv before t; move tv' before tv; move t' before t; move V1 before V;
  move W before V1.
  (* clean *)

  apply (functional_preserves_typing_gen Rc V V1 W _ tv' t t' _ β R) in Hwtv as preserve; auto.
  destruct preserve as [_ [HeqVV1 [_ [R' 
                       [_ [HsubR' [_ [_ [_ [_ [_ [HIn Hunsd']]]]]]]]]]]].
  exists R', V1, tv', t', W. 
  repeat (split; auto).
Qed.

End props.