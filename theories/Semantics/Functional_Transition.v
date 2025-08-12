From Coq Require Import Lia Morphisms Lists.List FinFun Program.
From Mecha Require Import Resource Term Typ Cell Triplet
                          VContext RContext REnvironment Stock
                          Type_System Evaluation_Transition
                          SyntaxNotation EnvNotation.
Import ListNotations.

(** * Semantics - Functional

  Wormholes’s dynamic semantics is split in three sets of transition rules: the evaluation transition, defined in [Evaluation_Transition.v], which extends standard B-reduction; the functional transition which performs the logical instant, and the temporal transition, defined in [Temporal_Transition.v], which corresponds to the reactivity of the program: it initializes the resources values, performs the instant via the functional transition and updates the system. In this file, we focus on the functional transition.
*)


(** ** Definition - Functional *)

Open Scope renvironment_scope.

(** *** Well-formed environment-context 

  For subsequent proofs we define a well-formed property between the resource context ([Rc]) and the resource environment ([V]). They need four property: (1) their domain matches; (2,3) they are both well-formed under their new key; (4) and each pair (types, cell) is well-typed under the empty variable context and the resource context [Rc].
*)
Definition well_formed_ec (Rc : ℜ) (V : 𝐕) :=
  (* (1) *) RE.eqDom Rc V /\ 
  (* (2) *) (Rc⁺ ⊩ Rc)%rc /\  (* (3) *) V⁺ ⊩ V /\
  (* (4) *) (forall (r : resource) (A B : Τ) (v : 𝑣),
                Rc⌊r⌋%rc = Some (A,B) -> V⌊r⌋ = Some v -> 
                match v with
                  | (⩽ v' … ⩾) => (∅)%vc ⋅ Rc ⊢ v' ∈ B
                  | (⩽ … v' ⩾) => (∅)%vc ⋅ Rc ⊢ v' ∈ A
                end).

Notation "'WF(' Rc , V )" := (well_formed_ec Rc V) (at level 50).


(** *** Gathering of halts properties *)

Definition fT_inputs_halts (m: lvl) (V: 𝐕) (t1 t2: Λ) :=
  halts_re m V /\ halts m t1 /\ halts m t2.

Definition fT_outputs_halts (m: lvl) (V: 𝐕) (W: 𝐖) (t1 t2: Λ) :=
  halts_re m V /\ halts_sk m W /\ halts m t1 /\ halts m t2.

(** *** Internal [arr t] terms *)

Inductive alt_wt : Λ -> list Λ -> Prop :=
  | awt1_unit : alt_wt <[unit]> nil

  | awt1_pair (t1 t2 : Λ) l1 l2 : 
      alt_wt t1 l1 ->
      alt_wt t2 l2 ->
      alt_wt <[⟨t1,t2⟩]> (l1 ++ l2)

  | awt1_abs x (C:Τ) (t : Λ) : alt_wt <[\x:C, t]> nil

  | awt1_arr (t : Λ) :
      alt_wt <[arr(t)]> [t]

  | awt1_first (t : Λ) (C:Τ) l :
      alt_wt t l -> alt_wt <[first(C:t)]> l

  | awt1_comp (t1 t2 : Λ) l1 l2 :
      alt_wt t1 l1 -> alt_wt t2 l2 ->
      alt_wt <[t1 >>> t2]> (l1 ++ l2)

  | awt1_rsf (r : resource) :
      alt_wt <[rsf[r]]> nil

  | awt1_wh (t1 t2 : Λ) l1 l2 :
      alt_wt t1 l1 ->
      alt_wt t2 l2 ->
      alt_wt <[wormhole(t1;t2)]> (l1 ++ l2).

(** *** Halts for all inner [arr t] terms *)

Definition halts_arr Rc (t : Λ) :=
  forall v, isvalueof (Rc⁺)%rc t v ->
  forall l, alt_wt v l -> 
  forall t', List.In t' l -> 
  forall v' Rc' A B, 
      (Rc ⊆ Rc')%rc /\ 
      (halts (Rc'⁺)%rc v' /\ 
      ∅%vc ⋅ Rc' ⊢ t' ∈ (A → B) /\ 
      ∅%vc ⋅ Rc' ⊢ v' ∈ A) -> halts (Rc'⁺)%rc <[t' v']>.

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

  | fT_first (v1 v1' v2 t t' : Λ) (A C : Τ) (V V1 : 𝐕) (W : 𝐖) :

                        ⪡ V ; v1 ; t ⪢ ⭆ ⪡ V1 ; v1' ; t' ; W ⪢ ->
  (* ------------------------------------------------------------------------------------------ *)
       ⪡ V ; ⟨v1,v2⟩ ; first(C:t) ⪢ ⭆ ⪡ V1 ; ⟨v1',[⧐ {V⁺} – {V1⁺ - V⁺}] v2⟩ ; first(C:t') ; W ⪢

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

Module RSS := RS.St.

(** *** [alt_wt] properties *)


Lemma value_to_awt (v : Λ) : 
  value(v) -> exists l', alt_wt v l'.
Proof.
  induction v; intro Hv; inversion Hv; subst;
  try (now exists []; constructor).
  - apply IHv1 in H1 as [l1 Hawt1].
    apply IHv2 in H2 as [l2 Hawt2].
    now exists (l1 ++ l2); constructor.
  - exists [v]; constructor.
  - apply IHv in H0 as [l Hawt].
    now exists l; constructor.
  - apply IHv1 in H1 as [l1 Hawt1].
    apply IHv2 in H2 as [l2 Hawt2].
    now exists (l1 ++ l2); constructor.
  - apply IHv1 in H1 as [l1 Hawt1].
    apply IHv2 in H2 as [l2 Hawt2].
    now exists (l1 ++ l2); constructor.
Qed. 

Definition shift_list (m n : lvl) (l : list Λ) :=
  List.map (Term.shift m n) l.

Lemma shift_in_e' m n v l :
  In v (shift_list m n l) -> 
  exists v', Logic.eq v (Term.shift m n v').
Proof.
  revert v; induction l; simpl; intros.
  - inversion H.
  - destruct H; subst.
    -- now exists a. 
    -- apply IHl in H as [v' Heq]; subst.
       now exists v'.
Qed.

Lemma shift_list_app m n l1 l2 : 
  (shift_list m n (l1 ++ l2)) = ((shift_list m n l1) ++ (shift_list m n l2)).
Proof.
  unfold shift_list. apply map_app.
Qed.

Lemma shift_list_eq_iff m n l1 l2 :
  shift_list m n l1 = shift_list m n l2 <-> l1 = l2.
Proof.
  split.
  - revert l2; induction l1.
    -- simpl; intros l2 Heq.
       destruct l2; auto. 
       simpl in *.
       inversion Heq.
    -- intros; destruct l2; simpl in *.
       + inversion H.
       + inversion H; f_equal.
         ++ rewrite Term.shift_eq_iff; now rewrite H1.
         ++ now apply IHl1.
  - intros; now subst.
Qed.

Lemma shift_in' m n v l : In v l <-> In (Term.shift m n v) (shift_list m n l).
Proof.
  split.
  - revert v. induction l; intros; simpl in *; auto.
    destruct H; subst; auto.
  - revert v. induction l; intros; simpl in *; auto.
    destruct H; subst; auto.
    left.
    now rewrite <- Term.shift_eq_iff in H.
Qed.

Lemma alt_wt_list_e m n t l :
  value(t) ->
  alt_wt (Term.shift m n t) l ->
  exists l', Logic.eq l (shift_list m n l').
Proof.
  revert m n l; induction t; intros m n l Hv Hawt;
  inversion Hv; subst; inversion Hawt; subst; auto;
  try (now exists []; simpl).
  - apply IHt1 in H3 as [l1' Heq]; auto; subst.
    apply IHt2 in H5 as [l2' Heq]; auto; subst.
    exists (l1' ++ l2').
    now rewrite shift_list_app.
  - now exists [t]; simpl.
  - apply IHt1 in H3 as [l1' Heq]; auto; subst.
    apply IHt2 in H5 as [l2' Heq]; auto; subst.
    exists (l1' ++ l2').
    now rewrite shift_list_app.
  - apply IHt1 in H3 as [l1' Heq]; auto; subst.
    apply IHt2 in H5 as [l2' Heq]; auto; subst.
    exists (l1' ++ l2').
    now rewrite shift_list_app.
Qed.

Lemma alt_wt_weakening m n t l :
  alt_wt t l ->
  alt_wt <[ [⧐m – n] t ]> (shift_list m n l).
Proof.
  intro arrlt.
  revert m n; induction arrlt; intros m n.
  - simpl; constructor.
  - rewrite shift_list_app; simpl; constructor; auto.
  - simpl; constructor.
  - simpl; constructor.
  - simpl; constructor; auto.
  - rewrite shift_list_app; simpl; constructor; auto.
  - simpl; constructor.
  - rewrite shift_list_app; simpl; constructor; auto.
Qed.

Lemma alt_wt_deterministic t l l' :
  alt_wt t l -> alt_wt t l' -> l = l'.
Proof.
 revert l l'.
 induction t; intros l l' Hawt Hawt'; 
 inversion Hawt; subst; inversion Hawt'; subst; auto.
 - apply IHt1 with (l := l1) in H2; auto; subst.
   apply IHt2 with (l := l2) in H5; auto; subst.
   reflexivity.
 - apply IHt1 with (l := l1) in H2; auto; subst.
   apply IHt2 with (l := l2) in H5; auto; subst.
   reflexivity.
 - apply IHt1 with (l := l1) in H2; auto; subst.
   apply IHt2 with (l := l2) in H5; auto; subst.
   reflexivity.
Qed. 

(** *** [halts_arr] properties *)

Lemma halts_arr_eT Rc (t t' : Λ) :
  (Rc⁺)%rc ⊨ t ⟼ t' -> halts_arr Rc t -> halts_arr Rc t'.
Proof.
  intros HeT Harrlt v Hivo l Hawt t1 HIn v' Rc' ty ty' [Hsub [Hlt [Hwt Hwt']]].
  apply isvalueof_eT' with (t := t) in Hivo; auto.
  apply Harrlt in Hivo.
  eapply Hivo with (v' := v') in HIn; eauto.
Qed.

Lemma halts_arr_first Rc (C:Τ) (t : Λ) :
  halts_arr Rc <[ first(C:t) ]> ->
  halts_arr Rc t.
Proof.
  intros Harrlt v Hivo l Hawt t1 HIn v' Rc' ty ty' [Hsub [Hlt [Hwt Hwt']]].
  apply isvalueof_first' with (C := C) in Hivo.
  apply Harrlt in Hivo.
  eapply Hivo with (v' := v') in HIn; eauto.
  now constructor.
Qed.

Lemma halts_arr_first' Rc (C:Τ) (t : Λ) :
  halts_arr Rc t ->
  halts_arr Rc <[ first(C:t) ]>.
Proof.
  intros Harrlt v Hivo l Hawt t1 HIn v' Rc' ty ty' [Hsub [Hlt [Hwt Hwt']]].
  apply isvalueof_first_e in Hivo as HI.
  destruct HI as [v1 ]; subst.
  apply isvalueof_first in Hivo.
  apply Harrlt in Hivo.
  eapply Hivo with (v' := v') in HIn; eauto.
  now inversion Hawt; subst.
Qed.

Lemma halts_arr_wh Rc C (i t : Λ) :
  halts (Rc⁺)%rc i ->
  halts_arr Rc <[wormhole(i; t)]> ->
  halts_arr (RC.Raw.add (S (Rc⁺))%rc (C,<[𝟙]>) (RC.Raw.add (Rc⁺)%rc (<[𝟙]>,C) Rc)) t.
Proof.  
  intros Hlt Harrlt v Hivo l Hawt t1 HIn v' Rc' ty ty' [Hsub [Hlt' [Hwt Hwt']]].
  unfold halts_arr in Harrlt.
  rewrite RC.new_key_wh in Hivo.
  eapply isvalueof_wh in Hivo as [v'' [Hivo' Hivo'']]; eauto.
  specialize (Harrlt <[wormhole( v''; v)]> Hivo'').
  destruct Hivo' as [HmeT Hv].
  apply value_to_awt in Hv as [l' Hawt'].
  specialize (Harrlt (l'++l)).
  destruct Harrlt with (t' := t1) (v' := v') (Rc' := Rc') (A := ty) (B := ty'); auto.
  - econstructor; eauto; reflexivity.
  - apply in_or_app; auto.
  - split; auto. 
    apply RC.Submap_wh_1 in Hsub; auto.
  - exists x; auto.
Qed.

Lemma halts_arr_comp Rc (t1 t2 : Λ) :
  halts (Rc⁺)%rc t1 ->
  halts (Rc⁺)%rc t2 ->
  halts_arr Rc <[ t1 >>> t2 ]> ->
  halts_arr Rc t1 /\ halts_arr Rc t2.
Proof.
  intros Hlt1 Hlt2 Harrlt; split.
  - intros v Hivo l Hawt t' HIn v' Rc' ty ty' [Hsub [Hlt' [Hwt Hwt']]].
    apply isvalueof_compl with (t2 := t2) in Hivo as [v'' [Hivo Hivo']]; auto.
    specialize (Harrlt <[v >>> v'']> Hivo').
    destruct Hivo as [HmeT Hv].
    apply value_to_awt in Hv as [l2 Hawt2]; auto.
    specialize (Harrlt (l ++ l2)).
    destruct Harrlt with (Rc' := Rc') (t' := t') (A := ty) (B := ty') (v' := v'); auto.
    -- econstructor; eauto; reflexivity.
    -- apply in_or_app; auto.
    -- exists x; auto.
  - intros v Hivo l Hawt t' HIn v' Rc' ty ty' [Hsub [Hlt' [Hwt Hwt']]].
    apply isvalueof_compr with (t1 := t1) in Hivo as [v'' [Hivo Hivo']]; auto.
    specialize (Harrlt <[v'' >>> v]> Hivo').
    destruct Hivo as [HmeT Hv].
    apply value_to_awt in Hv as [l1 Hawt1]; auto.
    specialize (Harrlt (l1 ++ l)).
    destruct Harrlt with (Rc' := Rc') (t' := t') (A := ty) (B := ty') (v' := v'); auto.
    -- econstructor; eauto; reflexivity.
    -- apply in_or_app; auto.
    -- exists x; auto.
Qed.

Lemma halts_arr_comp' Rc (t1 t2 : Λ) :
  halts_arr Rc t1 /\ halts_arr Rc t2 ->
  halts_arr Rc <[ t1 >>> t2 ]>.
Proof.
  intros [Harrlt1 Harrlt2] v Hivo l Hawt t' 
         HIn v' Rc' ty ty' [Hsub [Hlt' [Hwt Hwt']]].
  apply isvalueof_comp_e in Hivo as HI. 
  destruct HI as [v1 [v2 ]]; subst.
  apply isvalueof_comp in Hivo as [Hivo1 Hivo2].
  inversion Hawt; subst.
  apply in_app_or in HIn as [HIn | HIn].
  - unfold halts_arr in Harrlt1. 
    eapply (Harrlt1 v1 Hivo1 l1 H1); eauto.
  - unfold halts_arr in Harrlt2. 
    eapply (Harrlt2 v2 Hivo2 l2 H3); eauto.
Qed.

Lemma halts_arr_weakening Rc Rc' (t : Λ):
  (Rc ⊆ Rc')%rc ->
  halts_arr Rc t -> halts_arr Rc' <[[⧐ {Rc⁺%rc} – {(Rc'⁺)%rc - (Rc⁺)%rc}] t]>.
Proof.
  intros Hle Harrlt v Hivo l Hawt t' HIn v' Rc'' ty ty' [Hsub [Hlt' [Hwt Hwt']]].
  apply RC.Ext.new_key_Submap in Hle as Hnew.
  apply isvalueof_shift in Hivo as [v'' [Hivo ]]; auto; subst.
  apply Harrlt in Hivo as HI.
  destruct Hivo as [HmeT Hv].
  apply alt_wt_list_e in Hawt as HI'; auto.
  destruct HI' as [l' ]; subst.
  apply value_to_awt in Hv as Hawt'.
  destruct Hawt' as [l'' Hawt'].
  apply alt_wt_weakening with (m := (Rc⁺)%rc) (n := (Rc'⁺)%rc - (Rc⁺)%rc) in Hawt' as Hawt''.
  apply alt_wt_deterministic with (l := (shift_list (Rc⁺)%rc ((Rc'⁺)%rc - (Rc⁺)%rc) l')) in Hawt''; auto.
  rewrite shift_list_eq_iff in Hawt''; subst.
  clear Hawt.
  specialize (HI l'' Hawt').
  apply shift_in_e' in HIn as HI'.
  destruct HI' as [t1 ]; subst.
  rewrite <- shift_in' in HIn.
  specialize (HI t1 HIn v' Rc'' ty ty').
Admitted.

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
  forall (r : resource) (A B : Τ) (v : 𝑣),
    Rc⌊r⌋%rc = Some (A,B) ->  V⌊r⌋ = Some v  -> 
    match v with
      | (⩽ v' … ⩾) => ∅%vc ⋅ Rc ⊢ v' ∈ B
      | (⩽ … v' ⩾) => ∅%vc ⋅ Rc ⊢ v' ∈ A
    end.
Proof. 
  intros [_ [_ [_ Hwt]]] r v A B HfRe HfV. 
  now apply (Hwt r). 
Qed.

#[export] Instance WF_ec_iff : Proper (RC.eq ==> RE.eq ==> iff) well_formed_ec.
Proof.
  intros Rc Re1 HeqRe V V1 HeqV; unfold well_formed_ec. 
  split; intros [HeqDom [HvRe [HvV Hwt]]].
  - rewrite <- HeqRe, <- HeqV; repeat (split; auto).
    intros r A B v Hfi Hfi'; destruct v;
    rewrite <- HeqRe, <- HeqV in *;
    eapply Hwt in Hfi'; eauto.
  - rewrite HeqRe, HeqV; repeat (split; auto).
    intros r A B v Hfi Hfi'; destruct v;
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
  WF(Rc,V) -> forall r A B, 
  Rc⌊r⌋%rc = Some(A, B) -> exists v, (V⌊r⌋ = Some v)%type.
Proof. 
  intros [HeqDom _] r A B HfRe.
  now apply (RE.eqDom_find Rc _ HeqDom r A B).
Qed.

Corollary WF_ec_max (Rc : ℜ) (V : 𝐕):
  WF(Rc,V) -> max(Rc)%rc = max(V).
Proof. intros [HeqDom _]; now apply RE.eqDom_max. Qed.

Corollary WF_ec_new (Rc : ℜ) (V : 𝐕):
  WF(Rc,V) -> Rc⁺%rc = V⁺.
Proof. intros [HeqDom _]; now apply RE.eqDom_new. Qed.


Lemma WF_ec_wh (Rc : ℜ) (V : 𝐕) (A : Τ) (i : Λ) :
  (Rc⁺%rc ⊩ A)%ty -> (Rc⁺%rc ⊩ i)%tm -> ∅%vc ⋅ Rc ⊢ i ∈ A ->
  WF(Rc,V) ->
  WF((RC.Raw.add (S (Rc⁺)%rc) (A,<[𝟙]>) (RC.Raw.add (Rc⁺)%rc (<[𝟙]>,A) Rc)),
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
  - intros r C B v HfRe HfV.
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
         rewrite RC.new_key_wh; lia.
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

Lemma WF_ec_rsf (Rc: ℜ) (V : 𝐕) (r: resource) (A B: Τ) (i v : Λ) :
  ∅%vc ⋅ Rc ⊢ i ∈ A -> (Rc ⌊ r ⌋)%rc = Some (A, B) -> V⌊r⌋ = Some (⩽ v … ⩾) ->
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

Lemma fT_inputs_halts_first (Rc: ℜ) (V: 𝐕) (C:Τ) (t1 t2 t3: Λ) :
  fT_inputs_halts (Rc⁺)%rc V <[⟨t1, t2⟩]> <[first(C:t3)]> -> fT_inputs_halts (Rc⁺)%rc V t1 t3.
Proof.
  intros [HltV [Hltpair Hltfirst]]. 
  do 2 (split; auto).
  - now apply halts_pair in Hltpair as [].
  - now apply halts_first in Hltfirst.
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

Lemma fT_inputs_halts_wh  (Rc: ℜ) (V: 𝐕) (C: Τ) (t1 t2 t3: Λ) :
  (Rc⁺)%rc = V⁺ ->
  fT_inputs_halts (Rc⁺)%rc V t1 <[wormhole(t2;t3)]> ->
  fT_inputs_halts ((⌈S (Rc⁺) ⤆ (C, <[𝟙]>)⌉ (⌈Rc⁺ ⤆ (<[𝟙]>, C)⌉ Rc))⁺)%rc
                  (⌈S (V⁺) ⤆ ⩽ unit … ⩾⌉ (⌈V⁺ ⤆ ([⧐V ⁺ – 2] ⩽ t2 … ⩾)%cl⌉ 
                  ([⧐ V⁺ – 2] V))) <[[⧐ {V⁺} – 2] t1]> t3.
Proof.
  intros Heq [HltV [Hlt1 Hltwh]].
  apply halts_wh in Hltwh as [Hlt2 Hlt3].
  repeat split; auto.
  - rewrite RC.new_key_wh.
    rewrite Heq.
    apply halts_re_add; split. 
    -- exists <[unit]>; simpl; split; auto; reflexivity.
    -- apply halts_re_add; split.
       + replace (S (S (V⁺))) with (V⁺ + 2) by lia.
         rewrite <- Heq.
         apply halts_weakening_1; auto.
       + rewrite <- Heq. 
         replace (S (S (Rc⁺)%rc)) with ((Rc⁺)%rc + 2) by lia.
         apply halts_re_weakening_1; auto.
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
  apply halts_sk_nil.
Qed.

Lemma fT_outputs_halts_first (Rc Rc': ℜ) (V V': 𝐕) (W: 𝐖) (C : Τ) (t1 t1' t2 t3 t3': Λ) :
  (Rc ⊆ Rc')%rc -> 
  fT_inputs_halts (Rc⁺)%rc V <[⟨t1, t2⟩]> <[first(C:t3)]> ->
  fT_outputs_halts (Rc'⁺)%rc V' W t1' t3' ->
  fT_outputs_halts (Rc'⁺)%rc V' W <[⟨t1', [⧐{(Rc⁺)%rc} – {(Rc'⁺)%rc - (Rc⁺)%rc}] t2⟩]> <[first(C:t3')]>.
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
  - apply halts_sk_app; split; auto.
    apply halts_sk_weakening; auto.
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
  - apply halts_re_add; split; auto.
  - apply halts_sk_nil.
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
    apply Typ.Wf_weakening with (k := V⁺); auto.
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

(** *** Preservation of typing through functional transition 

  Suppose a resource context [Rc], two resource environments [V] and [V1], a stock [W], terms [st], [st'], [t] and [t'], two types [A] and [B], and finally a resource set [R].

  If:
  - All inner [arr t] terms in [t] halts (1);
  - The input components halts (2);
  - [t] is typed as [(A ⟿ B ∣ R)] regards of [Rc] (3);
  - [st] is typed as [A] regards of [Rc] (4);
  - There is a functional transition (5) and
  - [Rc] and [V] are well-formed (6)
  then there exists [Rc1] and [R'] such as :
  - All resources in [R] are unused in [V] (7);
  - All resources in [V] and not in [R] are unchanged in [V1] (8);
  - [Rc] is included in [Rc1] (9);
  - [R] is included in [R'] (10);
  - The output components halts (11);
  - All inner [arr t] terms in [t'] halts (12);
  - [t'] is typed as [(A ⟿ B ∣ R')] regards of [Rc1] (13);
  - [st'] is typed as [A] regards of [Rc1] (14);
  - [Rc1] and [V1] are well-formed (15);
  - All terms in [W] are well typed and resources are know by [Rc1] (16);
  - All new resources are in [W] and not in [V] (17) and
  - All resources in [R'] are used in [V1] (18).
*)
Theorem functional_preserves_typing (Rc : ℜ) (V V1 : 𝐕) (W : 𝐖) (st st' t t' : Λ) 
                                                                      (A B : Τ) (R : resources) :

                (* (1) *) halts_arr Rc t ->
                (* (2) *) fT_inputs_halts (Rc⁺)%rc V st t ->

           (* (3) *) ∅%vc ⋅ Rc ⊢ t ∈ (A ⟿ B ∣ R) -> (* (4) *) ∅%vc ⋅ Rc ⊢ st ∈ A -> 
          (* (5) *) ⪡ V ; st ; t ⪢ ⭆ ⪡ V1 ; st' ; t' ; W ⪢ -> (* (6) *) WF(Rc,V) ->
  (* ------------------------------------------------------------------------------------------- *)
       
       
       (* (7) *)(forall (r : resource), (r ∈ R)%s -> RE.unused r V) /\
       (* (8) *)(forall (r : resource), (r ∉ R)%s /\ (r ∈ V) -> 
                                                ([⧐ (V⁺) – ((V1⁺) - (V⁺))] V) ⌊r⌋ = V1 ⌊r⌋) /\

       exists (Rc1 : ℜ) (R' : resources),

          (* inputs included in outputs *)
          (*  (9) *) (Rc ⊆ Rc1)%rc /\ 
          (* (10) *) (R ⊆ R')%s /\

          (* outputs halts *)
          (* (11) *) fT_outputs_halts (Rc1⁺)%rc V1 W st' t' /\

          (* (12) *) halts_arr Rc1 t' /\

          (* typing preserved *)
          (* (13) *) ∅%vc ⋅ Rc1 ⊢ st' ∈ B /\ 
          (* (14) *) ∅%vc ⋅ Rc1 ⊢ t' ∈ (A ⟿ B ∣ R') /\

          (* properties about resource context and environment preserved *)
          (* (15) *) WF(Rc1,V1) /\

          (* properties of [W] *)
          (* (16) *) 
            (forall (r r' : resource) (v : Λ), 
            (In (r,r',v) W) -> exists (A : Τ), 
                               ∅%vc ⋅ Rc1 ⊢ v ∈ A /\
                               Rc1⌊r⌋%rc = Some (<[𝟙]>,A) /\ 
                               Rc1⌊r'⌋%rc = Some (A,<[𝟙]>)) /\

          (* properties of [R'] *)
          (* (17) *) (forall (r : resource), (r ∈ (R' \ R))%s -> (In r (ST.keys W)) /\ (r ∉ V)) /\
          (* (18) *) (forall (r : resource), (r ∈ R')%s -> RE.used r V1).
Proof.
  intros Harrlt Hltinp Hwt Hwtst fT; revert Rc R A B Harrlt Hltinp Hwt Hwtst.
  induction fT; intros Rc R A' B Harrlt Hltinp Hwt Hwst HWF;
  
  apply WF_ec_Wf in HWF as HvRc; destruct HvRc as [HvRc HvV];
  apply WF_ec_new in HWF as Hnew;
  
  move HvRc before HWF; move HvV before HvRc; move Hnew before HWF.
  (* fT_eT_sf *)
  - 
    (* clean *)
    move Rc before W; move R before Rc; move A' before R; move B before A'; move fT after IHfT;
    rename fT into HfT; rename H into HeT; move HeT after HfT.
    (* clean *)

    rewrite <- Hnew in HeT.
    apply evaluate_preserves_typing with (t' := t') in Hwt as Hwt'; auto.
    apply fT_inputs_halts_eT_r with (t2' := t') in Hltinp; auto.
    apply halts_arr_eT with (t' := t') in Harrlt; auto.
    
  (* fT_eT_sv *)
  - 
    (* clean *)
    move Rc before W; move R before Rc; move A' before R; move B before A'; move fT after IHfT;
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
    (** Outputs of the functional transition halt thanks to the hypothesis [halts_arr]. *)
    {
      apply fT_outputs_halts_arr; auto.
      specialize (Harrlt <[arr(t)]>).
      assert (isvalueof (Rc ⁺)%rc <[ arr( t) ]> <[ arr( t) ]>).
      { split; try reflexivity; auto. }
      specialize (Harrlt H [t]).
      eapply Harrlt with (B := B) (Rc' := Rc); eauto.
      - constructor; auto; reflexivity.
      - now constructor.
      - split.
        -- apply RC.Ext.Submap_refl.
        -- split; eauto.  
        destruct Hltinp as [_ []]; auto.
    }
    do 2 (split; auto).
    (** The output value is well-typed. *)
    { apply (wt_app _ _ _ _ A'); auto. }
    do 3 (split; auto).
    (** [W] is empty then we cannot deduce anything. *)
    { intros r r' v Hc; inversion Hc. }
    (** The set of ressource is empty the we cannot deduce anything. *)
    { split; intros r Hc; inversion Hc. } 
  (* fT_first *)
  -
    (* clean *)
    inversion Hwst; subst; move Rc before W; move R before Rc;
    clear A Hwst; rename A0 into A; rename B0 into A'; rename H3 into Hwv1; rename H5 into Hwv2;
    inversion Hwt; subst; clear Hwt; rename H4 into Hwt; rename H8 into Hvγ; rename B0 into B.
    move A before R; move B before A; move A' before B; move Hvγ before HvRc.
    (* clean *)

    apply (fT_inputs_halts_first _ _ _ _ v2 _) in Hltinp as Hltinp'.
    apply IHfT with (R := R) (B := B) in Hwv1 as IH; auto; clear IHfT;
    try (now apply halts_arr_first in Harrlt; auto).
    destruct IH as [Hunsd [Hlcl [Rc' [R' [HsubRc [HsubR [Hltout [Hwtv1' [Hwt' 
                   [Harrlt' [HWF' [HwtW [HInRW Husd]]]]]]]]]]]]].

    apply WF_ec_new in HWF' as Hnew'; auto.

    (* clean *)
    move Rc' before Rc; move R' before R; move Hwtv1' before Hwv1; clear Hwv1;
    move Hwt' before Hwt; clear Hwt; move HWF' before HWF; 
    move HsubRc before A'; move HsubR before A'; move Hltout before Hltinp;
    move Husd before Hunsd; move Hnew' before Hnew.
    (* clean *)

    do 2 (split; auto).
    exists Rc', R'.

    rewrite <- Hnew, <- Hnew'.
    do 2 (split; auto); split.
    (* Outputs of the functional transition halt. *)
    { now apply (fT_outputs_halts_first _ _ V _ _ _ v1 _ _ t). }
    split.
    { 
      now apply halts_arr_first'.
    }
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
    move Rc before W'; move A' before t2'; move B before A'; move C before A';
    move R1 before Rc; move R2 before Rc; move Hwt1 before Hwst; move Hwt2 before Hwt1.
    (* clean *)

    apply (fT_inputs_halts_comp_l) in Hltinp as Hltinp'.
    assert (halts (Rc ⁺)%rc t1 /\ halts (Rc ⁺)%rc t2).
    {
     destruct Hltinp as [_ [_ Hltinp]].
     apply halts_comp in Hltinp; auto. 
    }
    destruct H as [Hlt1 Hlt2].
    apply halts_arr_comp in Harrlt as [Harrlt1 Harrlt2]; auto.
    apply IHfT1 with (R := R1) (B := C) in Hwst as IH1; auto; clear IHfT1.
    destruct IH1 as [Hunsd1 [Hlcl1 [Rc' [R1' [HsubRc [HsubR1 [Hltout [Hwst' [Hwt1' 
                    [Harrlt1' [HWF' [HwtW1 [HInRW1 Husd1]]]]]]]]]]]]].

    (* clean *)
    move Rc' before Rc; move R1' before R1; move Hwst' before Hwst; move Hwt1' before Hwt1.
    move HsubRc before R1'; move HsubR1 before HsubRc; move HWF' before HWF; 
    move Hltout before Hltinp; move Husd1 before Hunsd1.
    (* clean *)


    apply WF_ec_new in HWF' as Hnew'; move Hnew' before Hnew.
    apply (fT_inputs_halts_comp_r Rc _ V _ _ st _ t1 _ t2) in Hltout as Hltinp''; auto.
    apply (weakening_ℜ _ _ Rc') in Hwt2 as Hwt2''; auto.
    apply halts_arr_weakening with (Rc' := Rc') in Harrlt2 as Harrlt2'; auto.
    rewrite Hnew, Hnew' in Hltinp'', Hwt2'', Harrlt2'.
    rewrite <- Hnew' in Hltinp'' at 1.
    apply (IHfT2 Rc' R2 C B Harrlt2' Hltinp'' Hwt2'' Hwt1') in HWF' as IH2; auto; clear IHfT2.

    destruct IH2 as [Hunsd2 [Hlcl2 [Rc'' [R2' [HsubRc' [HsubR2 [Hltout' 
                    [Harrlt2'' [Hwst'' [Hwt2' [HWF'' [HwtW2 [HInRW2 Husd2]]]]]]]]]]]]]. 
                  
    (* clean *)
    move Rc'' before Rc'; move R2' before R2; move Hwst'' before Hwst'; move Hwt2' before Hwt2;
    move HsubRc' before HsubRc; move HsubR2 before HsubR1; move HWF'' before HWF'; 
    move Hltout' before Hltout; move Husd2 before Husd1; move Hunsd2 before Hunsd1; 
    move Hlcl2 before Hlcl1; move Hwt2 before Hwt1; move HwtW2 before HwtW1; move HInRW2 before HInRW1; clear Hwt2'' Hltinp''.
    (* clean *)          

    apply WF_ec_new in HWF'' as Hnew''; move Hnew'' before Hnew'.

    assert (HEmp' : (∅ = R1' ∩ R2')%s).
    {
      symmetry; apply RSS.empty_is_empty_1; unfold RSS.Empty.
      intros r' HIn; apply RSS.inter_spec in HIn as [HIn1 HIn2].

      (** 
      4 cases: 
      - r' ∈ R1 ∧ r' ∈ R2 (contradiction)
      - r' ∈ R1 ∧ r' ∉ R2 
      - r' ∉ R1 ∧ r' ∈ R2 
      - r' ∉ R1 ∧ r' ∉ R2
      *)
      destruct (RSS.In_dec r' R1) as [HInR1 | HnInR1]; 
      destruct (RSS.In_dec r' R2) as [HInR2 | HnInR2].
      - symmetry in HEmp; apply RSS.empty_is_empty_2 in HEmp.
        apply (HEmp r'). apply RSS.inter_spec; split; auto.

      - destruct (HInRW2 r') as [_ HnInV1].
        -- rewrite RSS.diff_spec; split; auto.
        -- apply Hunsd1 in HInR1 as HInV.
           apply Husd2 in HIn2 as HInV'.
          apply RE.unused_in in HInV.
          apply functional_preserves_keys with (r := r') in fT1 as HInV1; auto.
    
      - destruct (HInRW1 r') as [_ HnInV].
        -- rewrite RSS.diff_spec; split; auto.
        -- apply HnInV.
          rewrite <- (WF_ec_In Rc V HWF r').
          destruct Hltinp as [_ [_ Hltcomp]].
          apply halts_comp in Hltcomp as [_ [v2 [HmeT Hv2]]].
          apply multi_preserves_typing with (t' := v2) in Hwt2; auto.
          apply (typing_Re_R (∅)%vc _ v2 C B R2); auto.

      - destruct (HInRW1 r') as [HInW _].
        -- rewrite RSS.diff_spec; split; auto.
        -- apply Husd1 in HIn1.
           apply RE.used_in in HIn1.
           assert ((r' ∈ R2' \ R2)%s).
           { rewrite RSS.diff_spec; split; auto. }
           apply HInRW2 in H as [_ HIn].
           contradiction.
    }

    move HEmp' before HEmp; split.
    (** All resources in [R1 ∪ R2] must be unused in the input resource environment [V]. *)
    {
      intros r HIn.
      apply RSS.union_spec in HIn as [HIn | HIn]; auto.

      destruct Hltinp as [_ [_ Hltcomp]].
      apply halts_comp in Hltcomp as [_ [v2 [HmeT Hv2]]].
      apply multi_preserves_typing with (t' := v2) in Hwt2; auto.
      apply (typing_Re_R (∅)%vc Rc v2 C B R2) in HIn as HInRc; auto.
      apply Hunsd2 in HIn.
      apply RE.unused_find_e in HIn as [v HfiV1].
      rewrite (WF_ec_In Rc V HWF r) in HInRc.
      destruct (RSS.In_dec r R1) as [| Hneq]; auto.
      destruct (Hlcl1 r); auto.
      apply RE.shift_find_e_1 in HfiV1 as Heq.
      destruct Heq as [[r'] [v']]. 
      destruct v'; try (simpl in *; now inversion H0).
      subst; rewrite H0 in *; clear H0.
      rewrite <- RE.shift_find_iff in HfiV1.
      apply (RE.unused_find _ t).
      rewrite Resource.shift_wf_refl; auto.
      apply WF_ec_Wf in HWF as [_ HwfV].
      apply (RE.Wf_find (V⁺)) in HfiV1 as []; auto.
    }
    split.
    (** All unused resources values are unchanged. *)
    {
      intros r [HnInR HInV]. 
      apply RSS.union_notin_spec in HnInR as [HnInR1 HnInR2].
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
      rewrite RSS.union_spec in *; destruct HIn as [HIn | HIn]; auto.
    }
    rewrite <- Hnew', <- Hnew''.
    split.
    (** Outputs of the functional transition halt. *)
    { now apply (fT_outputs_halts_comp _ _ V1 _ _ _ st'). }
    split.
    {
      apply halts_arr_comp'; split; auto.
      apply halts_arr_weakening; auto.
    }
    do 2 (split; auto).
    (** The output program is well-typed. *)
    {
      apply (wt_comp _ _ _ R1' R2' _ _ _ _ C); auto; try reflexivity.
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
             destruct HI as [A [Hwfv [Hwtrg Hwtrs]]].
             exists A.
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
      apply RSS.diff_spec in HIn as [HIn HnIn]. 
      apply RSS.union_notin_spec in HnIn as [HnInR1 HnInR2].
      apply RSS.union_spec in HIn as [HInR1' | HInR2'].
      - destruct (HInRW1 r) as [HInW HnInV]; try (apply RSS.diff_spec; split; auto).
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
        -- rewrite RSS.diff_spec; split; auto.
        -- split; auto.
           + apply ST.keys_in_app; now right.
           + intros HInV; apply H0.
             apply functional_preserves_keys in fT1 as []; auto.
    }
    { 
      intros r HIn.
      apply RSS.union_spec in HIn as [HIn | HIn]; auto.
      apply Husd1 in HIn as Husd.
      apply RE.used_in in Husd as HInV1.
      destruct (RSS.In_dec r R2) as [HInR2 | HnInR2]; auto.
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
      apply RSS.singleton_spec in HIn; subst.
      now apply (RE.unused_find _ v).
    }
    split.
    (** Despite [r] all resources in [V] have their value unchanged. *)
    {
      intros r' [HnIn HIn].
      apply RSS.singleton_notin_spec in HnIn.
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
    do 2 (split; auto).
    (* The output value is well-typed. *)
    { apply (WF_ec_well_typed _ V HWF _ _ _ (⩽ v … ⩾)) in HfiRc; auto. }
    do 2 (split; auto).
    { now apply (WF_ec_rsf _ _ _ A' B _ v). }
    split.
    (** The stock is empty then we cannot deduce anything. *)
    { intros r' r'' v' Hc; inversion Hc. }
    split.
    {
      intros r' HIn.
      apply RSS.diff_spec in HIn as []; contradiction.
    }
    {
      intros r' HIn.
      apply RSS.singleton_spec in HIn; subst.
      rewrite <- RE.used_add_eq; constructor.
    }

  (* fT_wh *)
  - 
    (* clean *)
    inversion Hwt; subst; move Rc before W; move R before Rc; move R' before R.
    move C before R'; move A' before C; move B before A'; rename H6 into Heq; rename H7 into Hvγ; 
    rename H8 into Hvβ; rename H9 into Hwi; rename H10 into Hwt';
    move Hwt after Hwst; move Hwi after Hwt.
    (* clean *)

    assert (Hltinp': fT_inputs_halts (Rc⁺)%rc V st <[wormhole(i;t)]>) by auto.
    destruct Hltinp' as [HltV [Hltst Hltwh]].
    apply halts_wh in Hltwh as [Hlti Hlt'].
    apply weakening_ℜ_wh with (A := <[𝟙]>) (B := C) in Hwst as Hwst'; auto.
    rewrite Hnew in Hwst' at 3.

    apply well_typed_implies_Wf in Hwi as HI; auto.
    destruct HI as [Hwfi Hwfτ].

    apply (WF_ec_wh _ _ C i) in HWF as HWF1; auto.

    apply (fT_inputs_halts_wh _ _ C _ _ _ Hnew) in Hltinp as Hltinp'.

    apply halts_arr_wh with (C := C) in Harrlt as Harrlt'; auto.

    apply IHfT in Hwt' as IH; auto; clear IHfT HWF1 Hltinp'.
    destruct IH as [Hunsd [Hlcl [Rc' [R1 [HsubRc [HsubR [Hltout 
                   [Harrlt'' [Hwst'' [Hwt'' [HWF' [HwtW1 [HInRW1 Husd1]]]]]]]]]]]]].
    
    apply WF_ec_new in HWF' as Hnew'.
       
    split.
    {
      intros r HIn; rewrite Heq in HIn. 
      apply RSS.diff_spec in HIn as [HInR' HnIn].
      repeat rewrite RSS.add_notin_spec in HnIn; destruct HnIn as [Hneq [Hneq' _]].
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
          apply RSS.diff_notin_spec in HInR as [HnIn | HIn]; auto.
          rewrite <- (WF_ec_In Rc V) in HInV; auto.
          apply RC.Ext.new_key_in in HInV. 
          do 2 rewrite RSS.add_spec in HIn.
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
      apply RSS.diff_spec in HIn as [HIn _]. 
      now apply HsubR.   
    }
    split.
    { 
      apply (fT_outputs_halts_wh Rc); auto.
      now apply RC.Submap_wh_1 in HsubRc.
    }
    do 5 (split; auto).
    {
      intros r r' v [|HIn].
      - inversion H; subst; clear H.
        exists C.
        split.
        -- rewrite <- Hnew', <- Hnew.
           apply weakening_ℜ; auto.
           now apply RC.Submap_wh_1 in HsubRc.
        -- split.
           + apply (RC.Ext.Submap_find (Rc⁺)%rc (<[𝟙]>,C)) in HsubRc as HfiRc.
             ++ rewrite <- Hnew. auto.
             ++ rewrite RC.add_neq_o; auto.
                rewrite RC.add_eq_o; auto.
           + apply (RC.Ext.Submap_find (S (Rc⁺)%rc) (C,<[𝟙]>)) in HsubRc as HfiRc.
             ++ rewrite <- Hnew. auto.
             ++ rewrite RC.add_eq_o; auto.
      - now apply (HwtW1 _ _ _) in HIn.
    }
    split; auto.
    {
      intros r HIn.
      apply RSS.diff_spec in HIn as [HInR1 HnInR]. 
      rewrite Heq in HnInR.
      apply RSS.diff_notin_spec in HnInR as [HnInR' | HIn].
      - destruct (HInRW1 r); try (now apply RSS.diff_spec).
        split.
        -- simpl; auto.
        -- intro HIn.
           apply H0.
           do 2 rewrite RE.add_in_iff.
           rewrite RE.shift_in_new_key; auto.
      - rewrite <- Hnew.
        repeat rewrite RSS.add_spec in HIn. 
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
Qed.

(** ---- *)

(** ** Progress - Functional *)
Hint Resolve VContext.Wf_empty ST.Wf_nil Resources.Wf_empty : core.


Lemma progress_of_functional_value_gen (Rc: ℜ) (m n: list lvl) (V : 𝐕) (tv t: Λ) (A B : Τ) (R : resources) :

       (* (1) *) value(t) -> (* (2) *) halts (Rc⁺)%rc tv -> (* (3) *) halts_re (Rc⁺)%rc V -> 
                halts_arr Rc <[[⧐⧐ m – n] t]> ->

       (* (4) *) ∅%vc ⋅ Rc ⊢ [⧐⧐ m – n] t ∈ (A ⟿ B ∣ R) -> (* (5) *) ∅%vc ⋅ Rc ⊢ tv ∈ A ->

       (* (6) *) WF(Rc,V) -> (* (7) *)(forall (r : resource), (r ∈ R)%s -> RE.unused r V) ->
  (* ------------------------------------------------------------------------------------------ *)
       exists (V1 : 𝐕) (tv' t' : Λ) (W : 𝐖),
                                      ⪡ V ; tv ; [⧐⧐ m – n] t ⪢ ⭆ ⪡ V1 ; tv' ; t' ; W ⪢.
Proof.
  revert Rc m n V tv A B R.
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
    rename A into C; rename A0 into A.
    move A before tv; move C before A; move B before A; clear Hwt;
    rename H4 into Hwt; move Hwt before Hwtv; rename H7 into Hwfτ;
    move tv' before tv; move Hwtv' before Hwtv.
    (* clean *)

    inversion Hvtv'; subst; inversion Hwtv'; subst.

    (* clean *)
    rename H into Hv1; rename H0 into Hv2; move Hv1 before Hvt;
    clear Hvtv'; move Hv2 before Hv1; rename H6 into Hwtv1;
    rename H8 into Hwtv2; move Hwtv1 before Hwtv'; clear Hwtv';
    move Hwtv2 before Hwtv1; move v1 before t; move v2 before v1.
    (* clean *)

    apply (IHt Rc m n V v1 A B R Hvt) in Hwtv1 as HI; auto; clear IHt.
    -- destruct HI as [V1 [v1' [t' [W fT]]]].
       
       (* clean *)
       move V1 before V; move v1' before tv; move t' before v1';
       move W before V1.
       (* clean *)

       exists V1, <[⟨v1',[⧐ {V⁺} – {V1⁺ - V⁺}] v2⟩]>, 
                  <[first({Typ.multi_shift m n C}:t')]>, W.
       rewrite (WF_ec_new Rc V) in HmeT; auto.
       apply fT_MeT_sv with (st' := <[ ⟨ v1, v2 ⟩ ]>); auto.
       apply fT_first.
       now constructor.
       apply fT.
    -- exists v1; split; auto; reflexivity.
    -- now apply halts_arr_first in Harrlt. 

  (* [rsf] term *)
  - rewrite Term.multi_shift_rsf in *.
    inversion Hwt; subst.

    (* clean *)
    clear Hwt; rename H3 into Hfi; move HWF after Hfi.
    (* clean *)

    assert (Hunsd': RE.unused ([⧐⧐m – n] r)%r V).
    -- apply Hunsd. 
       now apply RSS.singleton_spec.
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
    move R1 before R; move R2 before R1; move C before τ1; move t2 before t1;
    move Hunsd after Hltv; clear Hwt; rename H1 into Hvt1; rename H2 into Hvt2;
    rename H8 into Hwt1; rename H9 into HeqR; move Hwt1 after Hwtv;
    rename H10 into Hwt2; move Hwt2 before Hwt1; rename H11 into HneqR12.
    (* clean *)

    assert (Hunsd1: forall r : resource, (r ∈ R1)%s -> RE.unused r V).
    { 
      intros r HIn.
      apply Hunsd; rewrite HeqR.
      rewrite RSS.union_spec; auto. 
    }
    assert (Hunsd2: forall r : resource, (r ∈ R2)%s -> RE.unused r V).
    { 
      intros r HIn.
      apply Hunsd; rewrite HeqR.
      rewrite RSS.union_spec; auto. 
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
    eapply halts_arr_comp in Harrlt as HI; auto.
    destruct HI as  [Harrlt1 Harrlt2].
    
    apply (IHt1 Rc m n V tv τ1 C R1) in Hwtv as HfT; clear IHt1; auto.
    destruct HfT as [V1 [tv' [t1' [W1 fT1]]]].

    (* clean *)
    move V1 before V; move tv' before tv; move t1' before t2; move W1 before V1.
    (* clean *)

    apply (functional_preserves_typing Rc _ _ _ _ _ _ _ τ1 C R1) 
    in fT1 as HI; auto.
    -- destruct HI as [_ [HfiVV1 [Rc' [R1' [HsubRc [HsubR1 [Hltout 
                      [Harrlt1' [Hwtv' [Hwt1' [HWF' _]]]]]]]]]]].
                      
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

       apply (IHt2 Rc' (Rc⁺ :: m)%rc ((Rc'⁺ - Rc⁺) :: n)%rc V1 tv' C τ1' R2) in Hwtv' as HfT; auto.
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

       + rewrite Term.multi_shift_cons.
         apply halts_arr_weakening; auto.

       + intros r HIn.
         apply Hunsd2 in HIn as Hunsd.
         apply RE.unused_find_e in Hunsd as [v Hfi].

         (* clean *)
         move r before tv'; move v before tv'.
         (* clean *)

         apply typing_Re_R with (r := r) in Hwt2 as HIn'; auto.
         ++ rewrite (WF_ec_In Rc V) in HIn'; auto.
            destruct (RSS.In_dec r R1) as [HInR1 | HnInR1].
            * exfalso.
              assert (r ∉ ∅)%s. { intro c. inversion c. }
              apply H; clear H.
              rewrite HneqR12.
              rewrite RSS.inter_spec; split; auto.
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
    move R' before R; move C before τ1'; rename H6 into HeqR;
    rename H7 into Hwfτ1; rename H8 into Hwfτ1'; rename H9 into Hwt1;
    move Hwt1 before Hwt; rename H10 into Hwt2; move Hwt2 before Hwt1;
    clear Hwt.  
    (* clean *)

    apply (weakening_ℜ_wh _ _ _ <[𝟙]> C) in Hwtv; auto.
    apply (IHt2 _ m n
                  (⌈S (V⁺) ⤆ ⩽<[unit]> … ⩾⌉ (⌈V⁺ ⤆ ([⧐ V⁺ – 2] ⩽ ([⧐⧐ m – n] t1) … ⩾)%cl⌉ 
                    ([⧐ V⁺ – 2] V)))
    ) with (B := τ1') (R := R') in Hwtv as HfT; auto. 
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
       apply halts_re_add; split; simpl.
       + exists <[unit]>; split; now auto.
       + apply halts_re_add; split; simpl.
         ++ exists <[ [⧐ {V⁺} – 2] [⧐⧐ m – n] t1 ]>; split; auto.
            * reflexivity.
            * apply Term.shift_value_iff.
              now apply Term.multi_shift_value_iff.
         ++ replace (S (S (Rc⁺)%rc)) with ((Rc⁺)%rc + 2) by lia.
            rewrite (WF_ec_new Rc V) in *; auto.
            now apply halts_re_weakening_1.
    
    -- apply Resources.eq_leibniz in HeqR; subst.
       apply halts_arr_wh with (i := <[[⧐⧐m – n] t1]>); auto.
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
            apply RSS.diff_spec; split; auto.
            rewrite (WF_ec_new Rc V); auto.
            do 2 (apply RSS.add_notin_spec; split; auto).
            intro c; inversion c.
Qed.

(** *** Progress of the functional transition 

  Suppose well-typed expressions [t] and [tv], which halt (1), under [Rc] (3,4). In addition, suppose that [V] halts (1) and is well-formed regards of [Rc] (5). Finally, we also suppose that all inner [arr t] terms in [t] halts (2). If all resources used by [t] is unused at the beginning (6), then it exists a functional transition (7) where its outputs halt (8).
*)
Theorem progress_of_functional (Rc : ℜ) (V : 𝐕) (tv t : Λ) (A B : Τ) (R : resources) :

      (* (1) *) fT_inputs_halts (Rc⁺)%rc V tv t ->
      (* (2) *) halts_arr Rc t ->


      (* (3) *) ∅%vc ⋅ Rc ⊢ t ∈ (A ⟿ B ∣ R) -> 
      (* (4) *) ∅%vc ⋅ Rc ⊢ tv ∈ A ->
      (* (5) *) WF(Rc,V) -> 
      (* (6) *) (forall (r : resource), (r ∈ R)%s -> RE.unused r V) ->

  (* ------------------------------------------------------------------------------------------ *)
       (exists (V1 : 𝐕) (tv' t' : Λ) (W : 𝐖), 
       (*  (7) *) ⪡ V ; tv ; t ⪢ ⭆ ⪡ V1 ; tv' ; t' ; W ⪢ /\
       (*  (8) *) fT_outputs_halts (V1⁺) V1 W tv' t').
Proof. 
  intros [HltV [Hltv Hlt]].
  destruct Hlt as [t' [meT Hvt']]; revert V tv A B R HltV Hltv Hvt'.
  induction meT as [t | t t1 t' HeT];
  intros V tv A B R HltV Hltv Hvt Harrlt Hwt Hwtv HWF Hunsd.
  (* t is a value *)
  - rewrite <- (Term.multi_shift_nil t) in Hwt.
    apply (progress_of_functional_value_gen _ _ _ V tv t A B R) in Hwt as fT; auto.    
    destruct fT as [V1 [tv' [t' [W fT]]]].
    rewrite Term.multi_shift_nil in *.
    exists V1, tv', t', W; split; auto.
    apply (functional_preserves_typing Rc _ _ _ _ _ _ _ A B R) in fT; auto.
    -- destruct fT as [_ [_ [Rc1 [R' [_ [_ [Hltout [_ [_ [_ [HWF' _]]]]]]]]]]].
       rewrite <- (WF_ec_new Rc1 V1); auto.
    -- repeat split; auto.
       exists t; split; now auto.
  (* t can be reduced at least one time *)
  - clear meT.
    apply WF_ec_Wf in HWF as Hv; destruct Hv as [HvRe HvV].
    apply evaluate_preserves_typing with (t' := t1) in Hwt as Hwt1; auto.
    apply (IHmeT V tv A B) in Hwt1 as IH; auto.
    -- destruct IH as [V1 [tv' [t1' [W [HfT Hltout]]]]].
       exists V1, tv', t1', W; split; auto. 
       apply fT_eT_sf with (t' := t1); auto.
       now rewrite <- (WF_ec_new Rc V).
    -- apply halts_arr_eT with t; auto.
Qed.

(** ---- *)

(** ** Safety - Functional *)

(** *** Resources safety 

  Suppose well-typed expressions [t] and [tv], which halt (1,2), under [Rc] (6,7). In addition, [V] halts (3) and is well-formed regards of [Rc] (4), and all resources used by [t] is unused at the beginning (5). We can state that:
  - it exists a functional transition (8), i.e. there are no stuck situation and consequently no multiple interations with the same resource;
  - used resources are still in the set at the end (9);
  - all resources not in [R] are unused during the functional transition (10);
  - all resources in [R'\R] are new and stored in [W] (11);
  - all resources in [R] are used during the functional transition (12).
*)
Theorem safety_resources_interaction (Rc : ℜ) (V : 𝐕) (t tv : Λ) (A B : Τ) (R : resources) :

                   (* (1) *) fT_inputs_halts (Rc⁺)%rc V tv t ->
                halts_arr Rc t ->


      (* (4) *) WF(Rc,V) -> (* (5) *) (forall (r : resource), (r ∈ R)%s -> RE.unused r V) ->
             (* (6) *) ∅%vc ⋅ Rc ⊢ t ∈ (A ⟿ B ∣ R) -> (* (7) *) ∅%vc ⋅ Rc ⊢ tv ∈ A -> 
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
  apply (progress_of_functional Rc V tv t _ B R) in Hwtv as fT; auto.
  destruct fT as [V1 [tv' [t' [W [HfT Hltout]]]]].

  (* clean *)
  move tv before t; move tv' before tv; move t' before t; move V1 before V;
  move W before V1.
  (* clean *)

  apply (functional_preserves_typing Rc V V1 W _ tv' t t' _ B R) in Hwtv as preserve; auto.
  destruct preserve as [_ [HeqVV1 [_ [R' 
                       [_ [HsubR' [_ [_ [_ [_ [_ [_ [HIn Hunsd']]]]]]]]]]]]].
  exists R', V1, tv', t', W. 
  repeat (split; auto).
Qed.

End props.