From Coq Require Import Lia Morphisms Lists.List Arith.
From Mecha Require Import Resource Resources Term Typ Cell VContext RContext  
                          Type_System Evaluation_Transition Functional_Transition 
                          REnvironment SREnvironment Stock OREnvironment.
Import ResourceNotations TermNotations TypNotations CellNotations ListNotations
       VContextNotations RContextNotations REnvironmentNotations OREnvironmentNotations
       SREnvironmentNotations ResourcesNotations SetNotations StockNotations.

(** * Semantics - Temporal

  Wormholes’s dynamic semantics is split in three sets of transition rules: the evaluation transition, defined in [Evaluation_Transition.v], which extends standard β-reduction; the functional transition which performs the logical instant, defined in [Functional_Transition.v], and the temporal transition which corresponds to the reactivity of the program: it initializes the resources values, performs the instant via the functional transition and updates the system. In this file, we focus on the temporal transition.
*)


(** ** Definition - Temporal *)

Module RE := REnvironment.
Module SRE := SREnvironment.
Module ORE := OREnvironment.
Module ST := Stock.
Module RC := RContext.


(** *** Well-formed environments-context *)

Definition well_formed_in_ec (Re : ℜ) (S : 𝐄) (W : 𝐖) :=
  (* (1) *) (forall (r : resource), (r ∈ Re)%rc <->  (r ∈ W)%sk \/ (r ∈ S)%sr) /\ 
            (forall (r : resource), ((r ∈ W)%sk -> (r ∉ S)%sr) /\ ((r ∈ S)%sr -> (r ∉ W)%sk)) /\
  (* (2) *) (Re⁺ ⊩ Re)%rc /\  (* (3) *) (S⁺ ⊩ S)%sr /\ (W⁺ ⊩ W)%sk /\
  (* (4) *) (forall (r : resource) (α : πΤ) (v : Λ), Re⌊r⌋%rc = Some α -> 
              (S⌊r⌋%sr = Some v -> (∅)%vc ⋅ Re ⊢ {Term.shift (S⁺)%sr ((max (S⁺)%sr (W⁺)%sk) - (S⁺)%sr) v} ∈ {snd α}) /\
              (W⌊r⌋%sk = Some v -> (∅)%vc ⋅ Re ⊢ v ∈ {snd α})) /\
            (~ ST.eq W ST.empty -> (W⁺)%sk > (S⁺)%sr) /\
            (forall (r : resource) (α : πΤ), (r ∈ (ST.writers W))%s -> Re⌊r⌋%rc = Some α -> (snd α) = <[𝟙]>).
                                             

Definition well_formed_out_ec (Re : ℜ) (S : o𝐄) (W : 𝐖) :=
  (* (1) *) (forall (r : resource), (r ∈ Re)%rc <->  (r ∈ W)%sk \/ (r ∈ S)%or) /\ 
  (* (2) *) (Re⁺ ⊩ Re)%rc /\  (* (3) *) (S⁺ ⊩ S)%or /\ (W⁺ ⊩ W)%sk /\ (S⁺)%or <= (W⁺)%sk /\ 
  (* (4) *) (forall (r : resource) (α : πΤ), Re⌊r⌋%rc = Some α -> 
                match S⌊r⌋%or with
                  | Some v => OptTerm.prop_opt (fun v => (∅)%vc ⋅ Re ⊢ {Term.shift (S⁺)%or ((W⁺)%sk - (S⁺)%or) v} ∈ {fst α}) v
                  | _ =>  match W⌊r⌋%sk with 
                            | Some v => (∅)%vc ⋅ Re ⊢ v ∈ {fst α}
                            | _ => False
                          end
                end).

Notation "'WFᵢₙ(' Re , S , W )" := (well_formed_in_ec Re S W) (at level 50).
Notation "'WFₒᵤₜ(' Re , S , W )" := (well_formed_out_ec Re S W) (at level 50).


(** *** Temporal transition *)

(** **** Initialize the input resource environment 

  The input resource environment consists of locals resources (from W) and global resources (from S). Global resources, at the first instant, are well formed under S. After that, they must be shift in order to be well formed under the maximum between W⁺ and S⁺ because W may contains local resources which are, by construction, greater than global resources. 
*)
Definition init_input_env (S : 𝐄) (W : 𝐖) : 𝐕 :=
  ST.init_locals W (SRE.init_globals (SRE.shift (S⁺)%sr ((max (S⁺)%sr (W⁺)%sk) - (S⁺)%sr) S)).

Definition temporal (S : 𝐄) (S' : o𝐄) (P P' : Λ) (W W' : 𝐖) :=

  (** (1) Initialize the local memory [Vin] with global and local resources. *)
  let Vin := init_input_env S W in

  exists (Vout : 𝐕) Wnew _tv,
  (** (2) Perform the instant with the functional transition. *)                  
  ⪡ Vin ; unit ; P ⪢ ⭆ ⪡ Vout ; _tv ; P' ; Wnew ⪢ /\

  (** (3) Update the global and local resources. *)               
  (S' = ORE.update_globals ([⧐ (S⁺)%sr – (Vout⁺ - (S⁺)%sr)%re] S)%sr Vout)%or /\
  (W' = (ST.update_locals (W ∪ Wnew) Vout))%sk.


(** [ERROR]
    W' should be the union between updated W and updated Wnew.
*)

Notation "'⟦' S ';' W ';' P '⟧' '⟾' '⟦' S1 ';' W1 ';' P1 '⟧'" := (temporal S S1 P P1 W W1) 
(at level 30, S constr, S1 constr, P custom wh, P1 custom wh, W constr, W1 constr, no associativity).


(** ---- *)

(** ** Property - Temporal *)

Lemma temporal_preserves_global_keys (S : 𝐄) (S' : o𝐄) (P P' : Λ) (W W' : 𝐖) :
  ⟦S ; W ; P⟧ ⟾ ⟦S' ; W' ; P'⟧ -> (forall (k : resource), (k ∈ S)%sr <-> (k ∈ S')%or). 
Proof.
  intros [Vin [Wnew [_tv [_ [Heq _]]]]] k.
  rewrite Heq; rewrite <- ORE.update_globals_keys.
  now rewrite SRE.shift_in_new_key.
Qed.

Lemma temporal_preserves_local_keys (S : 𝐄) (S' : o𝐄) (P P' : Λ) (W W' : 𝐖) :
  ⟦S ; W ; P⟧ ⟾ ⟦S' ; W' ; P'⟧ -> (forall (k : resource), (k ∈ W)%sk -> (k ∈ W')%sk).
Proof. 
  intros [Vout [Wnew [_tv [HfT [_ Heq]]]]] k HIn.
  rewrite Heq; clear Heq.
  rewrite ST.update_locals_in_iff.
  rewrite ST.union_spec; auto.
Qed.

(** *** [init_input_env] property *)

Lemma init_input_env_in_iff (S: 𝐄) (W: 𝐖) (r: resource) : 
  (r ∈ W)%sk \/ (r ∈ S)%sr <-> r ∈ init_input_env S W.
Proof.
  unfold init_input_env.
  rewrite ST.init_locals_in_iff.
  rewrite SRE.init_globals_in_iff.
  now rewrite SRE.shift_in_new_key.
Qed.

Lemma init_input_env_new_key (S: 𝐄) (W: 𝐖) :
  (init_input_env S W)⁺ = max (S⁺)%sr (W⁺)%sk.
Proof.
  unfold init_input_env.
  rewrite ST.init_locals_new_key.
  replace (Nat.max (S ⁺)%sr (W ⁺)%sk) with (Nat.max (W ⁺)%sk (S ⁺)%sr) by lia.
  f_equal.
  rewrite SRE.init_globals_new_key.
  rewrite SRE.shift_new_refl_spec; auto.
Qed.

(** *** [unused] property *)

(*
Lemma resource_used_init_unused 
  (Re : ℜ) (V : 𝐕) (S : 𝐄) (W : 𝐖) (t : Λ) (α β : Τ) (R : resources) :

  ∅%vc ⋅ Re ⊢ t ∈ (α ⟿ β ∣ R) -> 
  halts (Re⁺)%rc t -> WF(Re,V) ->
  (V = ST.init_locals W (SRE.init_globals S))%re ->
  (forall r, (r ∈ R)%s -> RE.unused r V).
Proof.
  intros Hwt Hlt Hwf Heq r HInR; rewrite Heq.
  apply WF_ec_valid in Hwf as H.
  destruct H as [HvRe HvV].
  destruct Hlt as [t' [HmeT Hvt']].
  apply multi_preserves_typing with (t' := t') in Hwt; auto.
  apply typing_Re_R with (r := r) in Hwt; auto.
  rewrite (WF_ec_In Re V) in Hwt; auto.
  rewrite Heq in Hwt.
  apply ST.init_locals_in_iff in Hwt as [HIn | HIn].
  - now apply ST.init_locals_in_unused.
  - apply ST.init_locals_unused.
    apply SRE.init_globals_in_unused.
    now rewrite <- SRE.init_globals_in_iff.
Qed.
*)

(** *** [well_formed_in_ec] property *)

Lemma WF_in_ec_empty_locals (Rc: ℜ) (S: 𝐄) :
  (
    (forall (r : resource), (r ∈ Rc)%rc <-> (r ∈ S)%sr) /\ 
    (Rc⁺ ⊩ Rc)%rc /\  (S⁺ ⊩ S)%sr /\
    (forall (r : resource) (α : πΤ) (v : Λ), Rc⌊r⌋%rc = Some α -> 
                                             S⌊r⌋%sr = Some v -> (∅)%vc ⋅ Rc ⊢ v ∈ {snd α})
  ) 
  <-> 
   WFᵢₙ(Rc, S, (∅)%sk).
Proof.
  split.
  - intros [HeqDom [HvRc [HvS Hwt]]].
    unfold well_formed_in_ec.
    split.
    -- intro r; split.
       + rewrite HeqDom; auto.
       + intros [Hc | HIn].
         ++ exfalso; revert Hc.
            apply ST.empty_in_spec.
         ++ rewrite HeqDom; auto.
    -- split.
       + intro r; split.
         ++ intros Hc HIn; revert Hc.
            apply ST.empty_in_spec.
         ++ intro Hc.
            apply ST.empty_in_spec.
       + do 2 (split; auto); split.
         ++ apply ST.valid_empty_spec.
         ++ split.
            * intros r πα v HfRc.
              split; intro Hfi.
              ** replace (Nat.max (S⁺)%sr (∅⁺)%sk - (S⁺)%sr) with 0.
                 { 
                  rewrite Term.shift_zero_refl.
                  apply (Hwt r); auto.
                 }
                 { rewrite ST.new_key_empty_spec; lia. }
              ** inversion Hfi.
            * split.
              ** intro Hc.
                 exfalso; apply Hc; reflexivity.
              ** simpl; intros r πα HIn.
                 inversion HIn.
  - intros [HeqDom [_ [HvRc [HvS [_ [Hwt _]]]]]].
    split.
    -- intro r; split; intro HIn.
       + rewrite HeqDom in HIn.
         destruct HIn as [HIn |]; auto.
         exfalso; revert HIn.
         apply ST.empty_in_spec.
       + rewrite HeqDom; auto.
    -- do 2 (split; auto).
       intros r πα v HfRc HfS.
       apply (Hwt _ _ v) in HfRc as HI.
       destruct HI as [Hwt' _].
       replace (Nat.max (S⁺)%sr (∅⁺)%sk - (S⁺)%sr) with 0 in Hwt'.
       { 
        rewrite Term.shift_zero_refl in Hwt'.
        apply Hwt'; auto.
       }
       { rewrite ST.new_key_empty_spec; lia. }
Qed.

#[export] Instance WF_in_eq : 
 Proper (RContext.eq ==> SRE.eq ==> ST.eq ==> iff) well_formed_in_ec.
Proof.
  intros Re Re1 HeqRe S S' HeqS W W' HeqW; split.
  - intros [HeqDom [HDisj [HvRc [HvS [HvW [Hwt [Hgt Hwt']]]]]]].  
    split.
    -- intro r; rewrite <- HeqS, <- HeqW, <- HeqRe; auto.
    -- split.
       + intro r; rewrite <- HeqS, <- HeqW; auto.
       + split; try (now rewrite <- HeqRe).
         split; try (now rewrite <- HeqS).
         split; try (now rewrite <- HeqW).
         split.
         ++ intros r πα v.
            rewrite <- HeqW.
            rewrite <- HeqS.
            rewrite <- HeqRe.
            auto.
         ++ split.
            * rewrite <- HeqS.
              rewrite <- HeqW.
              apply Hgt.
            * intros r πα. 
              rewrite <- HeqW.
              rewrite <- HeqRe.
              apply (Hwt' r πα).
  - intros [HeqDom [HDisj [HvRc [HvS [HvW [Hwt [Hgt Hwt']]]]]]].  
    split.
    -- intro r; rewrite HeqS, HeqW, HeqRe; auto.
    -- split.
       + intro r; rewrite HeqS, HeqW; auto.
       + split; try (now rewrite HeqRe).
         split; try (now rewrite HeqS).
         split; try (now rewrite HeqW).
         split.
         ++ intros r πα v.
            rewrite HeqW.
            rewrite HeqS.
            rewrite HeqRe.
            auto.
         ++ split.
            * rewrite HeqS.
              rewrite HeqW.
              apply Hgt.
            * intros r πα. 
              rewrite HeqW.
              rewrite HeqRe.
              apply (Hwt' r πα).
Qed.


Lemma WF_in_ec_to_WF_ec (Re : ℜ) (S : 𝐄) (W : 𝐖) :
  WFᵢₙ(Re, S, W) -> WF(Re,init_input_env S W).
Proof.
  intros [HeqDom [HneqDom [HvRe [HvS [HvW [Hwt [HnInW HeqWw]]]]]]]; split.
  - intro x.
    rewrite <- init_input_env_in_iff; auto. 
  - split; auto; split.
    -- rewrite init_input_env_new_key.
       unfold init_input_env.
       apply ST.init_locals_valid.
       + admit.
       + apply SRE.init_globals_valid.
         destruct (Nat.leb_spec0  (S⁺)%sr (W ⁺)%sk).
       admit.
    -- intros r α β v Hfi HfV.
       apply ST.init_locals_find_inp_spec in HfV as H.
       + destruct H as [v' Heq]; subst.
         apply ST.init_locals_find_spec_1 in HfV as [HfW | HfW].
         ++ simpl in *.
            apply Hwt with (v := v') in Hfi as H.
            destruct H as [_ HwtW].
            apply HwtW in HfW; auto.
         ++ apply RE.init_writers_find_spec in HfW as H.
            destruct H as [HInW | HfS].
            * apply HeqWw with (α := (α,β)) in HInW as Heq; auto.
              simpl in *; subst.
              rewrite RE.init_writers_in_spec in HfW; auto.
              inversion HfW; subst; constructor.
            * rewrite SRE.init_globals_shift in HfS. 
              apply RE.shift_find_e_spec_1 in HfS as H.
              destruct H as [[r' Heq] [d Heqd]]; subst.
              destruct d as [t | t]; simpl in *; inversion Heqd; subst; clear Heqd.
              replace (Cell.inp <[[⧐{(S ⁺)%sr} – {(max (S⁺)%sr (W⁺)%sk) - (S ⁺)%sr}] t]>)
              with (Cell.shift (S⁺)%sr ((max (S⁺)%sr (W⁺)%sk) - (S⁺)%sr) (Cell.inp t)) 
              in HfS by now simpl.
              rewrite <- RE.shift_find_iff in HfS.
              rewrite SRE.init_globals_find_iff in HfS.
              rewrite Resource.shift_valid_refl in Hfi.
              ** apply Hwt with (v := t) in Hfi.
                 destruct Hfi as [HwtS _].
                 apply HwtS in HfS; auto.
              ** apply (SRE.valid_find_spec (S⁺)%sr) in HfS as [H _]; auto.
       + intros r' HfS.
         now apply SRE.init_globals_find_e_spec in HfS.
Admitted.

(** ---- *)

(** ** Preservation - Temporal *)


Section preservation.


Hypothesis all_arrow_halting : forall Re t α β,
  ∅%vc ⋅ Re ⊢ arr(t) ∈ (α ⟿ β ∣ ∅%s) -> forall v, ∅%vc ⋅ Re ⊢ v ∈ α -> halts (Re⁺)%rc <[t v]>.

Theorem temporal_preserves_typing (Re : ℜ) (S : 𝐄) (S' : o𝐄) (W W' : 𝐖) (P P' : Λ) (R : resources) :

                    (* (1) *) halts (Re⁺)%rc P -> (* (2) *) SRE.halts (S⁺)%sr S -> 
                     (* (3) *) ST.halts (Re⁺)%rc W -> (* (4) *) WFᵢₙ(Re,S,W) ->

       (* (1) *) ∅%vc ⋅ Re ⊢ P ∈ (𝟙 ⟿ 𝟙 ∣ R) -> (* (3) *) ⟦ S ; W ; P ⟧ ⟾ ⟦ S' ; W' ; P' ⟧ ->
  (* -------------------------------------------------------------------------------------------- *)
       exists (Re1 : ℜ) (R1 : resources),
          (* (4) *) (R ⊆ R1)%s /\ (* (5) *) (Re ⊆ Re1)%rc /\ (* (6) *) WFₒᵤₜ(Re1,S',W') /\
          (* (7) *) ∅%vc ⋅ Re1 ⊢ P' ∈ (𝟙 ⟿ 𝟙 ∣ R1) /\ 
     
          (* (9) *) halts (Re1⁺)%rc P' /\ (* (10) *) ORE.halts (Re1⁺)%rc S' /\ 
          (* (10) *) ST.halts (Re1⁺)%rc W'.
Proof.
  intros HltP HltS HltW HWF HwtP HTT.
  destruct HTT as [Vin [Vout [Wnew [_tv [HeqV [fT [HeqS' HeqW']]]]]]].

  move Vin before R; move Vout before Vin; move Wnew before W'; 
  move _tv before P'; move fT before HwtP.

  apply WF_in_ec_to_WF_ec in HWF as HWF'.
  rewrite <- HeqV in HWF'.
  apply (functional_preserves_typing_gen 
              all_arrow_halting Re _ _ _ _ _ _ _ <[𝟙]> <[𝟙]> R) in fT as IH; auto.
  - destruct IH as 
    [Hunsd [Hunc [Re1 [R1 [HsubRe [HsubR [HwfFT1 
    [HwtW [HW [Husd [_ [HwtP' [HlP' [_ [HlVout HlWnew]]]]]]]]]]]]]]].
    exists Re1, R1.
    do 2 (split; auto); split.
    -- admit.
    -- split; auto; split; auto; split.
       + rewrite HeqS'.
         apply ORE.halts_update_globals; auto.
         rewrite <- (WF_ec_new Re1 Vout); auto.
         apply SRE.halts_weakening; auto.
         admit.
       + rewrite HeqW'.
         apply ST.halts_update_locals; auto.
  - now exists <[unit]>; split; auto.
  - rewrite HeqV.
    apply ST.halts_init_locals; auto.
    apply SRE.halts_init_globals; auto.
    admit.
Admitted.

End preservation.

(** ---- *)


(** ** Progress - Temporal *)

(** ---- *)


(** ** Safety - Temporal *)