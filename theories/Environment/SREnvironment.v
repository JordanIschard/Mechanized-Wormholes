From Coq Require Import Lia Arith.PeanoNat Morphisms.
From Mecha Require Import Resource Resources Term REnvironment Cell.
From DeBrLevel Require Import LevelInterface MapLevelInterface MapLevel MapExtInterface MapExt.
Import ResourceNotations TermNotations REnvironmentNotations CellNotations
       ResourcesNotations SetNotations.


(** * Environment - Simple Resource Environment

  In the functional transition there are two kind of environment: the resource environment and the stock. The former, defined in [REnvironment.v], represents the local memory during an instant. The latter, defined in [Stock.v], keeps local resource names with their initial value. In addition, in the temporal transition we also need a simple map between resource names and terms.
*)

(** ** Module - Virtual Resource Environment - Reader *)
Module SREnvironment <: IsLvlET.

Include MapLvlD.MakeLvlMapLVLD Term.
Import Raw Ext.

Module ET := Evaluation_Transition.
Module RE := REnvironment.

(** *** Definition *)

(** **** Initialize an environment

  For each instant, local resource names that represent a reading interaction have their memory cells initialized as unused with a certain term. Same idea for global input resource names in the temporal transition. This function takes a reader environment [rs] and an environement [V] and produces an environment where all resource names in [rs] are initialized.
*)
Definition init_func (r : resource) (v : Λ) (V : 𝐕) := (⌈ r ⤆ ⩽ v … ⩾ ⌉ V)%re.

Definition init_readers (t : t) (V : 𝐕) := fold init_func t V.
Definition init_globals (t : t) : 𝐕 := init_readers t (∅)%re.


(** **** Update the resource environment 

  For each instant, the resource environment is updated at the end. Each local resources may have a new initial term for the next instant. We defined [update_readers] which takes a stock [W] and a resource environment [V] and produces a new stock.
*)
Definition update_readers_func (V : 𝐕) (r : resource) (v : Λ) (rs : t) : t :=
  match (V⌊r⌋)%re with 
    | Some (⩽ … v' ⩾) =>  add r v' rs
    |  _ => add r v rs
  end.

Definition update_readers (rs : t) (V : 𝐕) : t := fold (update_readers_func V) rs empty.

(** **** Halts 

  In the functional transition proofs, we assume that all elements in the virtual resource environment [W] halts. Thus, we define this property here with [For_all].
  An environment has the halting property if and only if each term in it halts. 
*)
Definition halts (k : lvl) := For_all (fun _ d => ET.halts k d).

(** *** Property *)

(** **** [extend] property *)
 
Lemma extend_Empty_left_spec (rs rs' : t) :
  Empty rs -> eq (extend rs rs') rs'.
Proof.
  intro HEmp; unfold extend.
  apply Empty_eq_spec in HEmp.
  rewrite fold_init; eauto.
  - apply fold_identity.
  - repeat red; intros; subst; now rewrite H1.
Qed.

Lemma extend_Empty_right_spec (rs rs' : t) :
  Empty rs' -> eq (extend rs rs') rs.
Proof. intro HEmp; unfold extend; now rewrite fold_Empty; eauto. Qed.

Lemma extend_add_right_spec (r : resource) (v : Λ) (rs rs' : t) :
  ~ (In r rs') -> eq (extend rs (add r v rs')) (add r v (extend rs rs')).
Proof.
  intro HnIn; unfold extend; rewrite fold_Add; eauto.
  - reflexivity.
  - intros k' k Heqk d' d Heqd c c' Heqc; subst; now rewrite Heqc.
  - apply diamond_add.
  - unfold SREnvironment.Add; reflexivity.
Qed.

Lemma valid_extend_spec (k : lvl) (rs rs' : t) :
  valid k rs -> valid k rs' -> valid k (extend rs rs').
Proof.
  revert rs; induction rs' using map_induction; intros rs Hvrs Hvrs'.
  - rewrite extend_Empty_right_spec; auto.
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    rewrite extend_add_right_spec; auto.
    apply valid_add_notin_spec in Hvrs' as [Hvx [Hve Hvrs'1]]; auto.
    apply valid_add_spec; auto.
Qed.

(** **** [new_key] property *)

Lemma new_key_max_spec (x: lvl) (v : Λ) (t : t) :
  ~ In x t -> new_key (add x v t) = max (new_key t) (S x).
Proof.
  intro HnIn.
  destruct (Nat.leb_spec0 (new_key t) (S x)) as [Hle | Hgt].
  - rewrite new_key_add_ge_spec; auto; lia.
  - rewrite new_key_add_lt_spec; auto; lia.
Qed.

(** **** [init_readers] property *)

#[export] Instance init_func_proper :
 Proper (Logic.eq ==> Logic.eq ==> RE.eq ==> RE.eq) init_func.
Proof.
  intros k' k Heqk d' d Heqd V V' HeqV; subst; unfold init_func.
  now rewrite HeqV.
Qed.

Lemma init_func_diamond : Diamond RE.eq init_func.
Proof.
  unfold init_func; intros k k' d d' rs rs1 rs' Hneq Heq Heq'.
  rewrite <- Heq; rewrite <- Heq'.
  now rewrite RE.add_add_2; auto.
Qed.

#[local] Hint Resolve init_func_proper init_func_diamond RE.Equal_equiv : core.

Lemma init_readers_Empty_spec (rs : t) (V : 𝐕) :
  Empty rs -> RE.eq (init_readers rs V) V.
Proof.
  intro Hemp; unfold init_readers.
  rewrite fold_Empty with (eqA := RE.eq); now auto.
Qed.

Lemma init_readers_add_spec (r : resource) (v : Λ) (rs : t) (V : 𝐕) :
  ~ (In r rs) ->
  RE.eq (init_readers (add r v rs) V) (⌈ r ⤆ (⩽ v … ⩾)⌉ (init_readers rs V))%re. 
Proof.
  unfold init_readers; intro HnIn.
  rewrite fold_Add with (eqA := RE.eq); eauto.
  - unfold init_func at 1; reflexivity.
  - red; reflexivity.
Qed.

#[export] Instance init_readers_proper : Proper (eq ==> RE.eq ==> RE.eq) init_readers.
Proof.
  intros rs rs' Heqrs V V' HeqV; unfold init_readers.
  eapply fold_Proper with (eqA := RE.eq); now eauto.
Qed.

Lemma init_readers_find_spec_1 (rs : t) (V : 𝐕) (r : resource) (v : 𝑣) :
  ((init_readers rs V)⌊r⌋)%re = Some v -> 
  find r rs = Some (Cell.extract v) \/ V⌊r⌋%re = Some v.
Proof.
  revert r v; induction rs using map_induction; intros r v Hfi.
  - rewrite init_readers_Empty_spec in Hfi; auto.
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_readers_add_spec in Hfi; auto.
    rewrite RE.add_o in Hfi; destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- inversion Hfi; subst; clear Hfi.
       left; rewrite add_eq_o; auto.
    -- apply IHrs1 in Hfi as [Hfi | Hfi]; auto.
       left; now rewrite add_neq_o.
Qed. 

Lemma init_readers_find_spec (rs : t) (V : 𝐕) (r : resource) (v : 𝑣) :
  ((init_readers rs V)⌊r⌋)%re = Some v -> In r rs \/ V⌊r⌋%re = Some v.
Proof.
  revert r v; induction rs using map_induction; intros r v Hfi.
  - rewrite init_readers_Empty_spec in Hfi; auto.
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_readers_add_spec in Hfi; auto.
    rewrite RE.add_o in Hfi; destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- now rewrite add_in_iff; repeat left.
    -- rewrite add_in_iff.
       apply IHrs1 in Hfi as [HIn | Hfi]; auto.
Qed.


Lemma init_readers_find_inp_spec (rs : t) (V : 𝐕) (r : resource) (v : 𝑣) :
  (forall r, V⌊r⌋%re = Some v -> exists v', v = Cell.inp v') ->
  ((init_readers rs V)⌊r⌋)%re = Some v -> exists v', v = Cell.inp v'. 
Proof.
  revert r v; induction rs using map_induction; intros r v HV Hfi.
  - rewrite init_readers_Empty_spec in Hfi; auto.
    now apply (HV r).
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_readers_add_spec in Hfi; auto.
    rewrite RE.add_o in Hfi; destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- inversion Hfi; subst; now exists e.
    -- apply IHrs1 in Hfi; auto.
Qed.

Lemma init_readers_in_iff  (rs : t) (V : 𝐕) (r : resource) :
  (r ∈ (init_readers rs V))%re <-> In r rs \/ (r ∈ V)%re.
Proof.
  revert r; induction rs using map_induction; intro r; split.
  - rewrite init_readers_Empty_spec; auto.
  - intros [HIn | HIn].
    -- destruct HIn as [v HM].
       exfalso; now apply (H r v).
    -- rewrite init_readers_Empty_spec; auto.
  - intro HIn.
    unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_readers_add_spec in HIn; auto.
    rewrite add_in_iff.
    apply RE.add_in_iff in HIn as [| HIn]; subst; auto.
    apply IHrs1 in HIn as [HIn | HIn]; auto.
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    rewrite add_in_iff.
    rewrite init_readers_add_spec; auto.
    rewrite RE.add_in_iff.
    intros [[Heq | HIn] | HIn]; subst; auto; 
    right; rewrite IHrs1; auto.
Qed.


Lemma init_readers_in_unused (rs : t) (V : 𝐕) (r : resource) :
  In r rs -> REnvironment.unused r (init_readers rs V).
Proof.
  revert r; induction rs using map_induction; intros r HIn.
  - exfalso; destruct HIn as [v HM]; now apply (H r v).
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_readers_add_spec; auto; 
    apply add_in_iff in HIn as [| HIn]; subst.
    -- apply RE.unused_add_eq_spec; now red.
    -- assert (Hneq : r <> x) by (intro; subst; contradiction).
       apply RE.unused_add_neq_spec; auto.
Qed.

Lemma init_readers_unused (r : resource) (V : 𝐕) (rs : t) :
  RE.unused r V -> RE.unused r (init_readers rs V).
Proof.
  revert r; induction rs using map_induction; intros r Hunsd.
  - rewrite init_readers_Empty_spec; auto.
  - unfold SREnvironment.Add in *; rewrite H0 in *; clear H0.
    rewrite init_readers_add_spec; auto.
    destruct (Resource.eq_dec r x) as [| Hneq]; subst.
    -- apply RE.unused_add_eq_spec; now red.
    -- apply RE.unused_add_neq_spec; auto.
Qed.

Lemma init_readers_add_remove (r : resource) (v : Λ) (rs : t) (V : 𝐕) :
  RE.eq (init_readers (add r v rs) V) (init_readers (add r v rs) (RE.Raw.remove r V)).
Proof.
  revert r v V; induction rs using map_induction; intros r v V.
  - rewrite init_readers_add_spec.
    -- rewrite init_readers_add_spec.
       + do 2 (rewrite init_readers_Empty_spec; auto).
         clear H rs; revert r v; induction V using RE.map_induction; intros r v.
         ++ assert (RE.eq (RE.Raw.remove r V) V).
            { 
              unfold RE.eq; rewrite RE.remove_id.
              intros [v1 HM]; now apply (H r v1).
            }
            now rewrite H0.
         ++ unfold RE.Add in H0; rewrite H0 in *; clear H0.
            destruct (Resource.eq_dec r x) as [| Hneq]; subst.
            * rewrite RE.add_shadow.
              rewrite RE.add_remove_1.
              now rewrite RE.add_shadow.
            * rewrite RE.add_add_2; auto.
              rewrite RE.remove_add_2; auto.
              symmetry.
              rewrite RE.add_add_2; auto.
              now rewrite IHV1.
       + intros [v1 HM]; now apply (H r v1).
    -- intros [v1 HM]; now apply (H r v1).
  - unfold SREnvironment.Add in *; rewrite H0 in *; clear H0.
    destruct (Resource.eq_dec r x) as [| Hneq]; subst.
    -- rewrite add_shadow.
       now apply IHrs1.
    -- rewrite add_add_2; auto.
       rewrite init_readers_add_spec.
       + symmetry; rewrite init_readers_add_spec.
         ++ now rewrite <- IHrs1.
         ++ rewrite add_in_iff; intros [|]; subst; contradiction.
       + rewrite add_in_iff; intros [|]; subst; contradiction.
Qed.

Lemma init_readers_add_spec_1 (r : resource) (v : 𝑣) (rs : t) (V : 𝐕) :
  ~ (In r rs) ->
  RE.eq (init_readers rs (⌈r ⤆ v⌉ V))%re (⌈r ⤆ v⌉ (init_readers rs V))%re. 
Proof.
  revert r v V; induction rs using map_induction; intros r v V HnIn.
  - now do 2 (rewrite init_readers_Empty_spec; auto).
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    assert (r <> x /\ ~In r rs1).
    { 
      split; intro; subst.
      - apply HnIn.
        rewrite add_in_iff; auto.
      - apply HnIn.
        rewrite add_in_iff; auto.
    }
    destruct H0 as [Hneq HnIn'].
    do 2 (rewrite init_readers_add_spec; auto).
    rewrite RE.add_add_2; auto.
    now rewrite IHrs1; auto.
Qed.


Lemma init_readers_new_key (V : 𝐕) (t : t) : ((init_readers t V)⁺)%re = max (new_key t) (V⁺)%re.
Proof.
  revert V.
  induction t using map_induction; intro V.
  - rewrite new_key_Empty_spec; auto; simpl.
    rewrite init_readers_Empty_spec; auto.
  - unfold SREnvironment.Add in *; rewrite H0 in *; clear H0.
    rewrite init_readers_add_remove.
    rewrite init_readers_add_spec; auto.
    rewrite new_key_max_spec; auto.
    rewrite RE.new_key_max_spec.
    + rewrite IHt1.
      destruct (RE.In_dec V x).
      ++ apply RE.new_key_in_remove_spec_1 in i as HI.
         rewrite HI; lia.
      ++ apply RE.remove_id in n.
         rewrite n; lia.
    + rewrite init_readers_in_iff; intros [|]; auto.
      rewrite RE.remove_in_iff in H0.
      destruct H0; auto.
Qed.

(** **** [init_globals] property *)

Lemma init_globals_Empty_spec (t : t) :
  Empty t -> RE.eq (init_globals t) (∅)%re.
Proof. apply init_readers_Empty_spec. Qed.

Lemma init_globals_add_spec (r : resource) (v : Λ) (t : t) :
  ~ (In r t) ->
  RE.eq (init_globals (add r v t)) (⌈ r ⤆ (⩽ v … ⩾)⌉ (init_globals t))%re. 
Proof. apply init_readers_add_spec. Qed.

#[export] Instance init_globals_proper : Proper (eq ==> RE.eq) init_globals.
Proof. unfold init_globals; intros t t' Heqt; now rewrite Heqt. Qed.  

Lemma init_globals_find_spec (t : t) (r : resource) (v : 𝑣) :
  ((init_globals t)⌊r⌋)%re = Some v -> In r t.
Proof. 
  intros Hfi. 
  apply init_readers_find_spec in Hfi as [HIn | Hfi]; auto.
  inversion Hfi.
Qed.

Lemma init_globals_in_iff  (t : t) (r : resource) :
  (r ∈ (init_globals t))%re <-> In r t.
Proof.
  split; intros HIn. 
  - apply init_readers_in_iff in HIn as [HIn | HIn]; auto.
    inversion HIn; inversion H.
  - now apply init_readers_in_iff; left.
Qed. 

Lemma init_globals_find_iff (t : t) (v : Λ) (r : resource) : 
  ((init_globals t)⌊r⌋)%re = Some (⩽v …⩾) <-> find r t = Some v.
Proof.
  revert r v; induction t using map_induction; intros r v; split; intro Hfi.
  - rewrite init_globals_Empty_spec in Hfi; auto. 
    inversion Hfi.
  - apply Empty_eq_spec in H.
    rewrite H in Hfi.
    inversion Hfi.
  - unfold SREnvironment.Add in *; rewrite H0 in *; clear H0.
    rewrite init_globals_add_spec in Hfi; auto.
    destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- rewrite RE.add_eq_o in Hfi; auto.
       inversion Hfi; subst; clear Hfi.
       now rewrite add_eq_o.
    -- rewrite RE.add_neq_o in Hfi; auto.
       rewrite add_neq_o; auto.
       now rewrite <- IHt1.
  - unfold SREnvironment.Add in *; rewrite H0 in *; clear H0.
    rewrite init_globals_add_spec; auto.
    destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- rewrite add_eq_o in Hfi; auto.
       inversion Hfi; subst; clear Hfi.
       now rewrite RE.add_eq_o.
    -- rewrite add_neq_o in Hfi; auto.
       rewrite RE.add_neq_o; auto.
       now rewrite IHt1.
Qed.

Lemma init_globals_in_unused (t : t) (r : resource) :
  In r t -> RE.unused r (init_globals t).
Proof. apply init_readers_in_unused. Qed.

Lemma init_globals_find_e_spec (t : t) (v : 𝑣) (r : resource) : 
  ((init_globals t)⌊r⌋)%re = Some v -> exists v', (v = ⩽ v' … ⩾)%type.
Proof.
  revert r v; induction t using map_induction; intros r v Hfi.
  - rewrite init_globals_Empty_spec in Hfi; auto.
    inversion Hfi.
  - unfold SREnvironment.Add in *; rewrite H0 in *; clear H0.
    rewrite init_globals_add_spec in Hfi; auto.
    destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- rewrite RE.add_eq_o in Hfi; auto.
       inversion Hfi; subst; clear Hfi.
       now exists e.
    -- rewrite RE.add_neq_o in Hfi; auto.
       now apply (IHt1 r v).
Qed.

Lemma init_globals_valid (k : lvl) (t : t) :
  valid k t <-> (k ⊩ init_globals t)%re.
Proof.
  induction t using map_induction; split; intro Hvt.
  - rewrite init_globals_Empty_spec; auto.
    apply RE.valid_empty_spec.
  - now apply valid_Empty_spec.
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    apply valid_add_notin_spec in Hvt as [Hvx [Hve Hvt]]; auto.
    rewrite init_globals_add_spec; auto.
    apply RE.valid_add_notin_spec.
    -- now rewrite init_globals_in_iff.
    -- repeat split; auto.
       now rewrite <- IHt1.
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_globals_add_spec in Hvt; auto.
    apply RE.valid_add_notin_spec in Hvt as [Hvx [Hve Hvt]]; auto.
    -- apply valid_add_notin_spec; auto.
       repeat split; auto.
       now rewrite IHt1.
    -- now rewrite init_globals_in_iff.
Qed.

Lemma init_globals_shift (m n : lvl) (t : t) :
  RE.eq (init_globals (shift m n t)) ([⧐ m – n] (init_globals t))%re.
Proof.
  induction t using map_induction.
  - rewrite shift_Empty_spec; auto.
    rewrite init_globals_Empty_spec; auto.
    rewrite RE.shift_Empty_spec; try reflexivity.
    apply RE.empty_1.
  - unfold SREnvironment.Add in *; rewrite H0; clear H0.
    rewrite shift_add_spec.
    rewrite init_globals_add_spec.
    -- rewrite init_globals_add_spec; auto.
       rewrite RE.shift_add_spec; simpl.
       now rewrite IHt1.
    -- now rewrite <- shift_in_iff.
Qed.

Lemma init_globals_new_key (t : t) : ((init_globals t)⁺)%re = new_key t.
Proof.
  induction t using map_induction.
  - rewrite new_key_Empty_spec; auto.
    rewrite init_globals_Empty_spec; auto.
  - unfold SREnvironment.Add in *; rewrite H0 in *; clear H0.
    rewrite init_globals_add_spec; auto.
    apply new_key_add_spec with (v := e) in H as H1.
    destruct H1 as [[Heq Hle] | [Heq Hgt]].
    -- rewrite Heq.
       rewrite RE.Ext.new_key_add_ge_spec; auto. 
       + now rewrite init_globals_in_iff.
       + now rewrite IHt1.
    -- rewrite Heq.
       rewrite RE.Ext.new_key_add_lt_spec; auto. 
       + now rewrite init_globals_in_iff.
       + now rewrite IHt1.
Qed.

(** **** [update_readers] property *)

#[export] Instance update_readers_func_proper :
 Proper (RE.eq ==> Logic.eq ==> Logic.eq ==> eq ==> eq) update_readers_func.
Proof.
  intros V V' HeqV k' k Heqk d' d Heqd rs rs' Heqrs; subst. 
  unfold update_readers_func; rewrite HeqV.
  destruct (V' ⌊k⌋)%re; try now rewrite Heqrs.
  destruct r; now rewrite Heqrs.
Qed.

#[export] Instance update_readers_func_1_proper (V : 𝐕) :
 Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) (update_readers_func V).
Proof. intros k' k Heqk d' d Heqd rs rs' Heqrs; subst; now rewrite Heqrs. Qed.

Lemma update_readers_func_diamond (V : 𝐕) : Diamond eq (update_readers_func V).
Proof.
  unfold update_readers_func; intros k k' d d' rs rs1 rs' Hneq Heq Heq'.
  destruct (V ⌊k⌋)%re; destruct (V ⌊k'⌋)%re; 
  try (destruct r); try (destruct r0); 
  rewrite <- Heq; rewrite <- Heq';
  now rewrite add_add_2; auto.
Qed.

#[local] Hint Resolve update_readers_func_1_proper update_readers_func_proper 
                      update_readers_func_diamond RE.Equal_equiv : core.

Lemma update_readers_Empty_spec (rs : t) (V : 𝐕) :
  Empty rs -> Empty (update_readers rs V).
Proof.
  intro Hemp; unfold update_readers.
  rewrite fold_Empty with (eqA := eq); now auto.
Qed.

Lemma update_readers_Empty_iff (rs : t) (V : 𝐕) :
  Empty rs -> eq (update_readers rs V) empty.
Proof.
  intro Hemp; unfold update_readers.
  rewrite fold_Empty with (eqA := eq); now auto.
Qed.

Lemma update_readers_empty_spec (V : 𝐕) :
  eq (update_readers empty V) empty.
Proof.
  unfold update_readers.
  rewrite fold_Empty with (eqA := eq); now auto.
Qed.

Lemma update_readers_Add_some_inp_spec (r : resource) (v v' : Λ) (rs rs' : t) (V : 𝐕) :
  ~ (In r rs) -> SREnvironment.Add r v rs rs' -> (V⌊r⌋)%re = Some (Cell.inp v') ->
  eq (update_readers rs' V) (add r v (update_readers rs V)). 
Proof.
  unfold update_readers; intros HnIn HA Hfi.
  rewrite fold_Add with (eqA := eq); eauto.
  unfold update_readers_func at 1. 
  now rewrite Hfi.
Qed.

Lemma update_readers_Add_some_out_spec (r : resource) (v v' : Λ) (rs rs' : t) (V : 𝐕) :
  ~ (In r rs) -> SREnvironment.Add r v rs rs' -> (V⌊r⌋)%re = Some (Cell.out v') ->
  eq (update_readers rs' V) (add r v' (update_readers rs V)). 
Proof.
  unfold update_readers; intros HnIn HA Hfi.
  rewrite fold_Add with (eqA := eq); eauto.
  unfold update_readers_func at 1. 
  now rewrite Hfi.
Qed.

Lemma update_readers_Add_none_spec (r : resource) (v : Λ) (rs rs' : t) (V : 𝐕) :
  ~ (In r rs) -> SREnvironment.Add r v rs rs' -> (V⌊r⌋)%re = None ->
  eq (update_readers rs' V) (add r v (update_readers rs V)). 
Proof.
  unfold update_readers; intros HnIn HA Hfi.
  rewrite fold_Add with (eqA := eq); eauto.
  unfold update_readers_func at 1.
  now rewrite Hfi.
Qed.

Lemma update_readers_add_some_inp_spec (r : resource) (v v' : Λ) (rs : t) (V : 𝐕) :
  ~ (In r rs) -> (V⌊r⌋)%re = Some (Cell.inp v') ->
  eq (update_readers (add r v rs) V) (add r v (update_readers rs V)). 
Proof.
  unfold update_readers; intros HnIn Hfi.
  rewrite fold_Add with (eqA := eq); eauto.
  - unfold update_readers_func at 1. 
    now rewrite Hfi.
  - red; reflexivity.
Qed.

Lemma update_readers_add_some_out_spec (r : resource) (v v' : Λ) (rs : t) (V : 𝐕) :
  ~ (In r rs) -> (V⌊r⌋)%re = Some (Cell.out v') ->
  eq (update_readers (add r v rs) V) (add r v' (update_readers rs V)). 
Proof.
  unfold update_readers; intros HnIn Hfi.
  rewrite fold_Add with (eqA := eq); eauto.
  - unfold update_readers_func at 1. 
    now rewrite Hfi.
  - red; reflexivity.
Qed.

Lemma update_readers_add_none_spec (r : resource) (v : Λ) (rs : t) (V : 𝐕) :
  ~ (In r rs) -> (V⌊r⌋)%re = None ->
  eq (update_readers (add r v rs) V) (add r v (update_readers rs V)). 
Proof.
  unfold update_readers; intros HnIn Hfi.
  rewrite fold_Add with (eqA := eq); eauto.
  - unfold update_readers_func at 1.
    now rewrite Hfi.
  - red; reflexivity.
Qed.

#[export] Instance update_readers_proper : Proper (eq ==> RE.eq ==> eq) update_readers.
Proof.
  intros rs rs' Heqrs V V' HeqV; revert rs' Heqrs V V' HeqV. 
  induction rs using map_induction; intros rs' Heqrs V V' HeqV.
  - rewrite update_readers_Empty_iff; auto.
    rewrite Heqrs in H.
    rewrite update_readers_Empty_iff; now auto.
  - destruct ((V⌊x⌋)%re) eqn:Hfi.
    -- destruct r. 
       + rewrite (update_readers_Add_some_inp_spec x e λ rs1 rs2); auto.
         symmetry.
         rewrite (update_readers_Add_some_inp_spec x e λ rs1 rs'); auto.
         ++ rewrite <- IHrs1 with (V := V) (V' := V'); now auto.
         ++ unfold SREnvironment.Add in *; now rewrite <- Heqrs.
         ++ now rewrite <- HeqV.
       + rewrite (update_readers_Add_some_out_spec x e λ rs1 rs2); auto.
         symmetry.
         rewrite (update_readers_Add_some_out_spec x e λ rs1 rs'); auto.
         ++ rewrite <- IHrs1 with (V := V) (V' := V'); now auto.
         ++ unfold SREnvironment.Add in *; now rewrite <- Heqrs.
         ++ now rewrite <- HeqV.
    -- rewrite (update_readers_Add_none_spec x e rs1 rs2); auto.
       symmetry.
       rewrite (update_readers_Add_none_spec x e rs1 rs'); auto.
       + rewrite <- IHrs1 with (V := V) (V' := V'); now auto.
       + unfold SREnvironment.Add in *; now rewrite <- Heqrs.
       + now rewrite <- HeqV.
Qed.

Lemma update_readers_in_iff  (rs : t) (V : 𝐕) (r : resource) :
  In r (update_readers rs V) <-> In r rs.
Proof.
  revert r; induction rs using map_induction; intro r; split.
  - rewrite update_readers_Empty_iff; auto; intro HIn.
    inversion HIn; inversion H0.
  - intro HIn.
    destruct HIn as [v HM].
    exfalso; now apply (H r v).
  - intro HIn.
    unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    rewrite add_in_iff.
    destruct ((V⌊x⌋)%re) eqn:Hfi.
    -- destruct r0.
       + rewrite update_readers_add_some_inp_spec with (v' := λ) in HIn; auto.
         apply add_in_iff in HIn as [Heq | HIn]; auto.
         right; now rewrite <- IHrs1.
       + rewrite update_readers_add_some_out_spec with (v' := λ) in HIn; auto.
         apply add_in_iff in HIn as [Heq | HIn]; auto.
         right; now rewrite <- IHrs1.
    -- rewrite update_readers_add_none_spec in HIn; auto.
       apply add_in_iff in HIn as [Heq | HIn]; auto.
       right; now rewrite <- IHrs1.
  - intro HIn.
    unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    destruct ((V⌊x⌋)%re) eqn:Hfi.
    -- destruct r0.
       + rewrite update_readers_add_some_inp_spec with (v' := λ); auto.
         rewrite add_in_iff.
         apply add_in_iff in HIn as [Heq | HIn]; auto.
         right; now rewrite IHrs1.
       + rewrite update_readers_add_some_out_spec with (v' := λ); auto.
         rewrite add_in_iff.
         apply add_in_iff in HIn as [Heq | HIn]; auto.
         right; now rewrite IHrs1.
    -- rewrite update_readers_add_none_spec; auto.
       rewrite add_in_iff.
       apply add_in_iff in HIn as [Heq | HIn]; auto.
       right; now rewrite IHrs1.
Qed.

(** **** [halts] property *)

Lemma halts_union_spec (k : lvl) (rs rs': t) :
  halts k rs /\ halts k rs' -> halts k (extend rs rs').
Proof.
  unfold halts; intros [HFa HFa'] r v Hfi.
  apply find_2 in Hfi. 
  apply extend_mapsto_iff in Hfi as [HM | [HM _]]; apply find_1 in HM.
  - now apply (HFa' r).
  - now apply (HFa r).
Qed.

Lemma halts_add_spec (k : lvl) (r : resource) (v : Λ) (rs : t) :
  (ET.halts k v) /\ halts k rs -> halts k (add r v rs).
Proof.
  intros [Hltv Hlts] r' v' Hfi.
  rewrite add_o in Hfi; destruct (Resource.eq_dec r r') as [| Hneq]; subst.
  - inversion Hfi; subst; auto.
  - apply Hlts in Hfi; auto.
Qed.

Lemma halts_add_iff (k : lvl) (r : resource) (v : Λ) (rs : t) :
  ~ (In r rs) -> 
  halts k (add r v rs) <-> (ET.halts k v) /\ halts k rs.
Proof.
  intros HIn; split.
  - unfold halts; intro HFa.
    apply For_all_add_notin_spec in HFa; auto.
  - apply halts_add_spec.
Qed.

Lemma halts_weakening (m n : lvl) (rs : t) : 
  m <= n -> halts m rs -> halts n (shift m (n - m) rs).
Proof.
  intros Hle Hlt r v Hfi. 
  apply shift_find_e_spec_1 in Hfi as HI.
  destruct HI as [[r' Heqr'] [v' Heqv']]; subst.
  rewrite <- shift_find_iff in Hfi. 
  apply ET.halts_weakening; auto; apply Hlt in Hfi; now simpl in *.
Qed.

Lemma halts_weakening_1 (m n : lvl) (rs : t) : 
  halts m rs -> halts (m + n) (shift m n rs).
Proof.
  intro Hlt; replace n with ((m + n) - m) at 2 by lia.
  apply halts_weakening; auto; lia.
Qed.

Lemma halts_init_readers (k : lvl) (rs : t) (V : 𝐕) :
  halts k rs -> RE.halts k V -> RE.halts k (init_readers rs V).
Proof.
  induction rs using map_induction; intros Hltrs HltV.
  - now rewrite init_readers_Empty_spec.
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_readers_add_spec; auto.
    apply RE.halts_add_spec; simpl.
    apply halts_add_iff in Hltrs as [Hkte Htlrs1]; auto. 
Qed.

Lemma halts_init_globals (k : lvl) (rs : t) :
  halts k rs -> RE.halts k (init_globals rs).
Proof.
  intro Hlt; apply halts_init_readers; auto.
  intros r d Hfi; inversion Hfi.
Qed.

Lemma halts_update_readers (k : lvl) (rs : t) (V : 𝐕) :
  halts k rs -> RE.halts k V -> halts k (update_readers rs V).
Proof.
  induction rs using map_induction; intros Hltrs HltV.
  - now rewrite update_readers_Empty_iff.
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    destruct ((V⌊x⌋)%re) eqn:Hfi.
    -- destruct r.
       + rewrite update_readers_add_some_inp_spec; eauto.
         rewrite halts_add_iff in *; auto.
         ++ destruct Hltrs; split; auto.
         ++ now rewrite update_readers_in_iff.
       + rewrite update_readers_add_some_out_spec; eauto.
         rewrite halts_add_iff in *; auto.
         ++ destruct Hltrs; split; auto.
            apply HltV in Hfi; now simpl in *.
         ++ now rewrite update_readers_in_iff.
    -- rewrite update_readers_add_none_spec; eauto.
       rewrite halts_add_iff in *; auto.
       ++ destruct Hltrs; split; auto.
       ++ now rewrite update_readers_in_iff.
Qed.

(** **** Morphism *)

#[export] Instance in_SREnvironment : Proper (Logic.eq ==> eq ==> iff) In.
Proof. intros k' k Heqk rs rs' Heqrs; subst; now rewrite Heqrs. Qed.

#[export] Instance Add_SREnvironment : 
  Proper (Resource.eq ==> Term.eq ==> eq ==> eq ==> iff) (@SREnvironment.Add Term.t).
Proof.
  intros k' k Heqk d d' Heqd rs rs' Heqrs rs1 rs1' Heqrs1; unfold SREnvironment.Add.
  now rewrite Heqk, Heqd, Heqrs, Heqrs1. 
Qed.

#[export] Instance halts_SREnvironment : Proper (Logic.eq ==> eq ==> iff) halts. 
Proof. unfold halts; intros m n Heqm rs rs' Heqrs; subst; now rewrite Heqrs. Qed.

End SREnvironment.

(** ---- *)

(** ** Notation - Virtual Resource Environment - Reader *)

Module SREnvironmentNotations.

(** *** Scope *)
Declare Scope srenv_scope.
Delimit Scope srenv_scope with sr.

(** *** Notation *)
Definition 𝐄 := SREnvironment.t.

Notation "t '⁺'" := (SREnvironment.Ext.new_key t) (at level 16) : srenv_scope.
Notation "∅" := SREnvironment.Raw.empty (at level 0, no associativity) : srenv_scope. 
Notation "r '∉' t" := (~ (SREnvironment.Raw.In r t)) (at level 75, no associativity) : srenv_scope. 
Notation "'isEmpty(' t ')'" := (SREnvironment.Empty t) (at level 20, no associativity) : srenv_scope. 
Notation "'Add'" := (SREnvironment.Add) (at level 20, no associativity) : srenv_scope. 
Notation "t '⌊' x '⌋'"  := (SREnvironment.Raw.find x t) (at level 15, x constr) : srenv_scope.
Notation "'max(' t ')'"  := (SREnvironment.Ext.max_key t) (at level 15) : srenv_scope.
Notation "⌈ x ⤆ v '⌉' t" := (SREnvironment.Raw.add x v t) 
                             (at level 15, x constr, v constr) : srenv_scope.
Notation "'[⧐' lb '–' k ']' t" := (SREnvironment.shift lb k t) 
                                   (at level 65, right associativity) : srenv_scope.

Infix "⊆" := SREnvironment.Submap (at level 60, no associativity) : srenv_scope. 
Infix "∈" := SREnvironment.Raw.In (at level 60, no associativity) : srenv_scope. 
Infix "=" := SREnvironment.eq : srenv_scope.
Infix "∪" := SREnvironment.extend : srenv_scope.
Infix "⊩" := SREnvironment.valid (at level 20, no associativity) : srenv_scope.

(** *** Morphism *)

Import SREnvironment.

#[export] Instance equiv_sr : Equivalence SREnvironment.eq := _.
#[export] Instance max_sr : Proper (eq ==> Logic.eq) (Ext.max_key) := Ext.max_key_eq.
#[export] Instance new_sr : Proper (eq ==> Logic.eq) (Ext.new_key) := Ext.new_key_eq.
#[export] Instance in_sr : Proper (Logic.eq ==> SREnvironment.eq ==> iff) (SREnvironment.Raw.In) := _.
#[export] Instance find_sr : Proper (Logic.eq ==> eq ==> Logic.eq) (Raw.find) := _.
#[export] Instance Empty_sr : Proper (SREnvironment.eq ==> iff) (SREnvironment.Empty) := _.
#[export] Instance Add_sr : 
  Proper (Resource.eq ==> Term.eq ==> eq ==> eq ==> iff) (@SREnvironment.Add Term.t) := _.
#[export] Instance add_sr : 
  Proper (Resource.eq ==> Term.eq ==> eq ==> eq) (@Raw.add Term.t) := _.
#[export] Instance Submap_sr : Proper (eq ==> eq ==> iff) Submap := _.
#[export] Instance Submap_sr_po : PreOrder SREnvironment.Submap := Submap_po.
#[export] Instance valid_sr : Proper (Logic.eq ==> SREnvironment.eq ==> iff) SREnvironment.valid := _.
#[export] Instance shift_sr : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.
#[export] Instance halts_sr: Proper (Logic.eq ==> SREnvironment.eq ==> iff) SREnvironment.halts := _.

End SREnvironmentNotations.