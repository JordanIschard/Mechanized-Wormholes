From Coq Require Import Lia Arith.PeanoNat Morphisms.
From Mecha Require Import Resource Resources Term REnvironment Cell.
From DeBrLevel Require Import LevelInterface MapLevelInterface MapLevelLVLD MapExtInterface MapExt.
Import ResourceNotations TermNotations REnvironmentNotations CellNotations
       ResourcesNotations SetNotations.


(** * Environment - Simple Resource Environment

  For the temporal transition, we need to define a map that binds global resources with terms. Indeed, it simulates the information that come from the external environment.
*)

(** ** Module - Simple Resource Environment *)
Module SREnvironment <: IsLvlET.

Include MakeLvlMapLVLD Term.
Import Raw Ext.

Module ET := Evaluation_Transition.
Module RE := REnvironment.

(** *** Definitions *)

(** **** Initialize an environment

  For each instant, global resources are initialized with a certain term. Consequently, we define [init_globals] that takes a simple environment [sr] and an environement [V] and produces an environment where all resource names in [sr] are initialized.
*)
Definition init_func (r: resource) (v: Λ) (V: 𝐕) := (⌈ r ⤆ ⩽ v … ⩾ ⌉ V)%re.

Definition init_g (sr: t) (V: 𝐕) := fold init_func sr V.

Definition init_globals (sr: t) : 𝐕 := init_g sr (∅)%re.


(** **** Halts 

  An environment holds the halting property if and only if each term in it halts. 
*)
Definition halts (k : lvl) := For_all (fun _ d => ET.halts k d).

(** *** Properties *)

(** **** [extend] properties *)
 
Lemma extend_Empty_left (sr sr' : t) :
  Empty sr -> eq (extend sr sr') sr'.
Proof.
  intro HEmp; unfold extend.
  apply Empty_eq in HEmp.
  rewrite fold_init; eauto.
  - apply fold_identity.
  - repeat red; intros; subst; now rewrite H1.
Qed.

Lemma extend_Empty_right (sr sr' : t) :
  Empty sr' -> eq (extend sr sr') sr.
Proof. intro HEmp; unfold extend; now rewrite fold_Empty; eauto. Qed.

Lemma extend_add_right (r: resource) (v: Λ) (sr sr' : t) :
  ~ (In r sr') -> eq (extend sr (add r v sr')) (add r v (extend sr sr')).
Proof.
  intro HnIn; unfold extend; rewrite fold_Add; eauto.
  - reflexivity.
  - intros k' k Heqk d' d Heqd c c' Heqc; subst; now rewrite Heqc.
  - apply diamond_add.
  - unfold SREnvironment.Add; reflexivity.
Qed.

Lemma Wf_extend (k : lvl) (sr sr' : t) :
  Wf k sr -> Wf k sr' -> Wf k (extend sr sr').
Proof.
  revert sr; induction sr' using map_induction; intros sr Hvrs Hvrs'.
  - rewrite extend_Empty_right; auto.
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    rewrite extend_add_right; auto.
    apply Wf_add_notin in Hvrs' as [Hvx [Hve Hvrs'1]]; auto.
    apply Wf_add; auto.
Qed.

Lemma extend_new_key (sr sr': t) :
  new_key (extend sr sr') = max (new_key sr) (new_key sr').
Proof.
  revert sr.
  induction sr' using map_induction; intro sr.
  - rewrite extend_Empty_right; auto.
    rewrite (new_key_Empty sr'); auto; lia.
  - unfold SREnvironment.Add in H0; rewrite H0; clear H0.
    rewrite extend_add_right; auto.
    do 2 rewrite new_key_add_max.
    rewrite IHsr'1; lia.
Qed.

(** **** [new_key] properties *)

Lemma new_key_Wf (k: lvl) (sr: t) : Wf k sr -> new_key sr <= k.
Proof.
  induction sr using map_induction; intro Hwf.
  - rewrite new_key_Empty; auto; lia.
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    apply Wf_add_notin in Hwf as [Hwfx [_ Hwf]]; auto.
    apply IHsr1 in Hwf.
    unfold Resource.Wf in Hwfx.
    rewrite new_key_add_max; lia.
Qed.

(** **** [init_g] properties *)

#[export] Instance init_func_eq : Proper (Logic.eq ==> Logic.eq ==> RE.eq ==> RE.eq) init_func.
Proof.
  intros k' k Heqk d' d Heqd V V' HeqV; subst; unfold init_func.
  now rewrite HeqV.
Qed.

Lemma init_func_diamond : Diamond RE.eq init_func.
Proof.
  unfold init_func; intros k k' d d' sr rs1 sr' Hneq Heq Heq'.
  rewrite <- Heq; rewrite <- Heq'.
  now rewrite RE.add_add_2; auto.
Qed.

#[local] Hint Resolve init_func_eq init_func_diamond RE.Equal_equiv : core.

Lemma init_g_Empty (sr: t) (V: 𝐕) :
  Empty sr -> RE.eq (init_g sr V) V.
Proof.
  intro Hemp; unfold init_g.
  rewrite fold_Empty with (eqA := RE.eq); now auto.
Qed.

Lemma init_g_add (r: resource) (v: Λ) (sr: t) (V: 𝐕) :
  ~ (In r sr) ->
  RE.eq (init_g (add r v sr) V) (⌈ r ⤆ (⩽ v … ⩾)⌉ (init_g sr V))%re. 
Proof.
  unfold init_g; intro HnIn.
  rewrite fold_Add with (eqA := RE.eq); eauto.
  - unfold init_func at 1; reflexivity.
  - red; reflexivity.
Qed.

#[export] Instance init_g_proper : Proper (eq ==> RE.eq ==> RE.eq) init_g.
Proof.
  intros sr sr' Heqrs V V' HeqV; unfold init_g.
  eapply fold_Proper with (eqA := RE.eq); now eauto.
Qed.

Lemma init_g_find_1 (sr: t) (V: 𝐕) (r: resource) (v : 𝑣) :
  ((init_g sr V)⌊r⌋)%re = Some v -> 
  find r sr = Some (Cell.extract v) \/ V⌊r⌋%re = Some v.
Proof.
  revert r v; induction sr using map_induction; intros r v Hfi.
  - rewrite init_g_Empty in Hfi; auto.
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_g_add in Hfi; auto.
    rewrite RE.add_o in Hfi; destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- inversion Hfi; subst; clear Hfi.
       left; rewrite add_eq_o; auto.
    -- apply IHsr1 in Hfi as [Hfi | Hfi]; auto.
       left; now rewrite add_neq_o.
Qed. 

Lemma init_g_find (sr: t) (V: 𝐕) (r: resource) (v : 𝑣) :
  ((init_g sr V)⌊r⌋)%re = Some v -> In r sr \/ V⌊r⌋%re = Some v.
Proof.
  revert r v; induction sr using map_induction; intros r v Hfi.
  - rewrite init_g_Empty in Hfi; auto.
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_g_add in Hfi; auto.
    rewrite RE.add_o in Hfi; destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- now rewrite add_in_iff; repeat left.
    -- rewrite add_in_iff.
       apply IHsr1 in Hfi as [HIn | Hfi]; auto.
Qed.

Lemma init_g_find_inp (sr: t) (V: 𝐕) (r: resource) (v : 𝑣) :
  (forall r, V⌊r⌋%re = Some v -> exists v', v = Cell.inp v') ->
  ((init_g sr V)⌊r⌋)%re = Some v -> exists v', v = Cell.inp v'. 
Proof.
  revert r v; induction sr using map_induction; intros r v HV Hfi.
  - rewrite init_g_Empty in Hfi; auto.
    now apply (HV r).
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_g_add in Hfi; auto.
    rewrite RE.add_o in Hfi; destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- inversion Hfi; subst; now exists e.
    -- apply IHsr1 in Hfi; auto.
Qed.

Lemma init_g_in_iff  (sr: t) (V: 𝐕) (r: resource) :
  (r ∈ (init_g sr V))%re <-> In r sr \/ (r ∈ V)%re.
Proof.
  revert r; induction sr using map_induction; intro r; split.
  - rewrite init_g_Empty; auto.
  - intros [HIn | HIn].
    -- destruct HIn as [v HM].
       exfalso; now apply (H r v).
    -- rewrite init_g_Empty; auto.
  - intro HIn.
    unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_g_add in HIn; auto.
    rewrite add_in_iff.
    apply RE.add_in_iff in HIn as [| HIn]; subst; auto.
    apply IHsr1 in HIn as [HIn | HIn]; auto.
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    rewrite add_in_iff.
    rewrite init_g_add; auto.
    rewrite RE.add_in_iff.
    intros [[Heq | HIn] | HIn]; subst; auto; 
    right; rewrite IHsr1; auto.
Qed.

Lemma init_g_in_unused (sr: t) (V: 𝐕) (r: resource) :
  In r sr -> REnvironment.unused r (init_g sr V).
Proof.
  revert r; induction sr using map_induction; intros r HIn.
  - exfalso; destruct HIn as [v HM]; now apply (H r v).
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_g_add; auto; 
    apply add_in_iff in HIn as [| HIn]; subst.
    -- apply RE.unused_add_eq; now red.
    -- assert (Hneq : r <> x) by (intro; subst; contradiction).
       apply RE.unused_add_neq; auto.
Qed.

Lemma init_g_unused (r: resource) (V: 𝐕) (sr: t) :
  RE.unused r V -> RE.unused r (init_g sr V).
Proof.
  revert r; induction sr using map_induction; intros r Hunsd.
  - rewrite init_g_Empty; auto.
  - unfold SREnvironment.Add in *; rewrite H0 in *; clear H0.
    rewrite init_g_add; auto.
    destruct (Resource.eq_dec r x) as [| Hneq]; subst.
    -- apply RE.unused_add_eq; now red.
    -- apply RE.unused_add_neq; auto.
Qed.

Lemma init_g_add_remove (r: resource) (v: Λ) (sr: t) (V: 𝐕) :
  RE.eq (init_g (add r v sr) V) (init_g (add r v sr) (RE.Raw.remove r V)).
Proof.
  revert r v V; induction sr using map_induction; intros r v V.
  - rewrite init_g_add.
    -- rewrite init_g_add.
       + do 2 (rewrite init_g_Empty; auto).
         clear H sr; revert r v; induction V using RE.map_induction; intros r v.
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
       now apply IHsr1.
    -- rewrite add_add_2; auto.
       rewrite init_g_add.
       + symmetry; rewrite init_g_add.
         ++ now rewrite <- IHsr1.
         ++ rewrite add_in_iff; intros [|]; subst; contradiction.
       + rewrite add_in_iff; intros [|]; subst; contradiction.
Qed.

Lemma init_g_add_1 (r: resource) (v : 𝑣) (sr: t) (V: 𝐕) :
  ~ (In r sr) ->
  RE.eq (init_g sr (⌈r ⤆ v⌉ V))%re (⌈r ⤆ v⌉ (init_g sr V))%re. 
Proof.
  revert r v V; induction sr using map_induction; intros r v V HnIn.
  - now do 2 (rewrite init_g_Empty; auto).
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    assert (r <> x /\ ~In r sr1).
    { 
      split; intro; subst.
      - apply HnIn.
        rewrite add_in_iff; auto.
      - apply HnIn.
        rewrite add_in_iff; auto.
    }
    destruct H0 as [Hneq HnIn'].
    do 2 (rewrite init_g_add; auto).
    rewrite RE.add_add_2; auto.
    now rewrite IHsr1; auto.
Qed.

Lemma init_g_new_key (V: 𝐕) (t : t) : ((init_g t V)⁺)%re = max (new_key t) (V⁺)%re.
Proof.
  revert V.
  induction t using map_induction; intro V.
  - rewrite new_key_Empty; auto; simpl.
    rewrite init_g_Empty; auto.
  - unfold SREnvironment.Add in *; rewrite H0 in *; clear H0.
    rewrite init_g_add_remove.
    rewrite init_g_add; auto.
    rewrite new_key_add_max; auto.
    rewrite RE.Ext.new_key_add_max.
    rewrite IHt1.
    destruct (RE.In_dec V x).
    + apply RE.new_key_in_remove_1 in i as HI.
      rewrite HI; lia.
    + apply RE.remove_id in n.
      rewrite n; lia.
Qed.

Lemma init_g_Wf (k : lvl) (V: 𝐕) (t : t) :
  Wf k t /\ (k ⊩ V)%re -> (k ⊩ init_g t V)%re.
Proof.
  revert k V.
  induction t using map_induction; intros k V  [Hvt HvV].
  - rewrite init_g_Empty; auto.
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    apply Wf_add_notin in Hvt as [Hvx [Hve Hvt1]]; auto.
    rewrite init_g_add_remove.
    rewrite init_g_add; auto.
    apply RE.Wf_add_notin.
    -- rewrite init_g_in_iff; intros [|]; auto.
       apply RE.remove_in_iff in H0 as []; auto.
    -- do 2 (split; auto).
       apply IHt1; split; auto.
       now apply RE.Wf_remove.
Qed.

(** **** [init_globals] properties *)

Lemma init_globals_Empty (t : t) :
  Empty t -> RE.eq (init_globals t) (∅)%re.
Proof. apply init_g_Empty. Qed.

Lemma init_globals_add (r: resource) (v: Λ) (t : t) :
  ~ (In r t) ->
  RE.eq (init_globals (add r v t)) (⌈ r ⤆ (⩽ v … ⩾)⌉ (init_globals t))%re. 
Proof. apply init_g_add. Qed.

#[export] Instance init_globals_eq : Proper (eq ==> RE.eq) init_globals.
Proof. unfold init_globals; intros t t' Heqt; now rewrite Heqt. Qed.  

Lemma init_globals_find (t : t) (r: resource) (v : 𝑣) :
  ((init_globals t)⌊r⌋)%re = Some v -> In r t.
Proof. 
  intros Hfi. 
  apply init_g_find in Hfi as [HIn | Hfi]; auto.
  inversion Hfi.
Qed.

Lemma init_globals_in_iff  (t : t) (r: resource) :
  (r ∈ (init_globals t))%re <-> In r t.
Proof.
  split; intros HIn. 
  - apply init_g_in_iff in HIn as [HIn | HIn]; auto.
    inversion HIn; inversion H.
  - now apply init_g_in_iff; left.
Qed. 

Lemma init_globals_find_iff (t : t) (v: Λ) (r: resource) : 
  ((init_globals t)⌊r⌋)%re = Some (⩽v …⩾) <-> find r t = Some v.
Proof.
  revert r v; induction t using map_induction; intros r v; split; intro Hfi.
  - rewrite init_globals_Empty in Hfi; auto. 
    inversion Hfi.
  - apply Empty_eq in H.
    rewrite H in Hfi.
    inversion Hfi.
  - unfold SREnvironment.Add in *; rewrite H0 in *; clear H0.
    rewrite init_globals_add in Hfi; auto.
    destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- rewrite RE.add_eq_o in Hfi; auto.
       inversion Hfi; subst; clear Hfi.
       now rewrite add_eq_o.
    -- rewrite RE.add_neq_o in Hfi; auto.
       rewrite add_neq_o; auto.
       now rewrite <- IHt1.
  - unfold SREnvironment.Add in *; rewrite H0 in *; clear H0.
    rewrite init_globals_add; auto.
    destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- rewrite add_eq_o in Hfi; auto.
       inversion Hfi; subst; clear Hfi.
       now rewrite RE.add_eq_o.
    -- rewrite add_neq_o in Hfi; auto.
       rewrite RE.add_neq_o; auto.
       now rewrite IHt1.
Qed.

Lemma init_globals_in_unused (t : t) (r: resource) :
  In r t -> RE.unused r (init_globals t).
Proof. apply init_g_in_unused. Qed.

Lemma init_globals_find_e (t : t) (v : 𝑣) (r: resource) : 
  ((init_globals t)⌊r⌋)%re = Some v -> exists v', (v = ⩽ v' … ⩾)%type.
Proof.
  revert r v; induction t using map_induction; intros r v Hfi.
  - rewrite init_globals_Empty in Hfi; auto.
    inversion Hfi.
  - unfold SREnvironment.Add in *; rewrite H0 in *; clear H0.
    rewrite init_globals_add in Hfi; auto.
    destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- rewrite RE.add_eq_o in Hfi; auto.
       inversion Hfi; subst; clear Hfi.
       now exists e.
    -- rewrite RE.add_neq_o in Hfi; auto.
       now apply (IHt1 r v).
Qed.

Lemma init_globals_Wf (k : lvl) (t : t) :
  Wf k t <-> (k ⊩ init_globals t)%re.
Proof.
  induction t using map_induction; split; intro Hvt.
  - rewrite init_globals_Empty; auto.
    apply RE.Wf_empty.
  - now apply Wf_Empty.
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    apply Wf_add_notin in Hvt as [Hvx [Hve Hvt]]; auto.
    rewrite init_globals_add; auto.
    apply RE.Wf_add_notin.
    -- now rewrite init_globals_in_iff.
    -- repeat split; auto.
       now rewrite <- IHt1.
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_globals_add in Hvt; auto.
    apply RE.Wf_add_notin in Hvt as [Hvx [Hve Hvt]]; auto.
    -- apply Wf_add_notin; auto.
       repeat split; auto.
       now rewrite IHt1.
    -- now rewrite init_globals_in_iff.
Qed.

Lemma init_globals_shift (m n : lvl) (t : t) :
  RE.eq (init_globals (shift m n t)) ([⧐ m – n] (init_globals t))%re.
Proof.
  induction t using map_induction.
  - rewrite shift_Empty; auto.
    rewrite init_globals_Empty; auto.
    rewrite RE.shift_Empty; try reflexivity.
    apply RE.empty_1.
  - unfold SREnvironment.Add in *; rewrite H0; clear H0.
    rewrite shift_add.
    rewrite init_globals_add.
    -- rewrite init_globals_add; auto.
       rewrite RE.shift_add; simpl.
       now rewrite IHt1.
    -- now rewrite <- shift_in_iff.
Qed.

Lemma init_globals_new_key (t : t) : ((init_globals t)⁺)%re = new_key t.
Proof.
  induction t using map_induction.
  - rewrite new_key_Empty; auto.
    rewrite init_globals_Empty; auto.
  - unfold SREnvironment.Add in *; rewrite H0 in *; clear H0.
    rewrite init_globals_add; auto.
    rewrite new_key_add_max.
    rewrite RE.Ext.new_key_add_max; lia.
Qed.

(** **** [halts] properties *)

Lemma halts_Empty (k: lvl) (t: t) : Empty t -> halts k t.
Proof.
  intros HEmp k' v Hfi.
  exfalso.
  apply find_2 in Hfi.
  apply (HEmp k' v Hfi).
Qed.

Lemma halts_union (k : lvl) (sr sr': t) :
  halts k sr /\ halts k sr' -> halts k (extend sr sr').
Proof.
  unfold halts; intros [HFa HFa'] r v Hfi.
  apply find_2 in Hfi. 
  apply extend_mapsto_iff in Hfi as [HM | [HM _]]; apply find_1 in HM.
  - now apply (HFa' r).
  - now apply (HFa r).
Qed.

Lemma halts_add (k : lvl) (r: resource) (v: Λ) (sr: t) :
  (ET.halts k v) /\ halts k sr -> halts k (add r v sr).
Proof.
  intros [Hltv Hlts] r' v' Hfi.
  rewrite add_o in Hfi; destruct (Resource.eq_dec r r') as [| Hneq]; subst.
  - inversion Hfi; subst; auto.
  - apply Hlts in Hfi; auto.
Qed.

Lemma halts_add_iff (k : lvl) (r: resource) (v: Λ) (sr: t) :
  ~ (In r sr) -> 
  halts k (add r v sr) <-> (ET.halts k v) /\ halts k sr.
Proof.
  intros HIn; split.
  - unfold halts; intro HFa.
    apply For_all_add_notin in HFa; auto.
  - apply halts_add.
Qed.

Lemma halts_weakening (m n : lvl) (sr: t) : 
  m <= n -> halts m sr -> halts n (shift m (n - m) sr).
Proof.
  intros Hle Hlt r v Hfi. 
  apply shift_find_e_1 in Hfi as HI.
  destruct HI as [[r' Heqr'] [v' Heqv']]; subst.
  rewrite <- shift_find_iff in Hfi. 
  apply ET.halts_weakening; auto; apply Hlt in Hfi; now simpl in *.
Qed.

Lemma halts_weakening_1 (m n : lvl) (sr: t) : 
  halts m sr -> halts (m + n) (shift m n sr).
Proof.
  intro Hlt; replace n with ((m + n) - m) at 2 by lia.
  apply halts_weakening; auto; lia.
Qed.

Lemma halts_init_g (k : lvl) (sr: t) (V: 𝐕) :
  halts k sr -> RE.halts k V -> RE.halts k (init_g sr V).
Proof.
  induction sr using map_induction; intros Hltrs HltV.
  - now rewrite init_g_Empty.
  - unfold SREnvironment.Add in H0; rewrite H0 in *; clear H0.
    rewrite init_g_add; auto.
    apply RE.halts_add; simpl.
    apply halts_add_iff in Hltrs as [Hkte Htlrs1]; auto. 
Qed.

Lemma halts_init_globals (k : lvl) (sr: t) :
  halts k sr -> RE.halts k (init_globals sr).
Proof.
  intro Hlt; apply halts_init_g; auto.
  intros r d Hfi; inversion Hfi.
Qed.

(** *** Morphisms *)

#[export] Instance srenvironment_in_iff : Proper (Logic.eq ==> eq ==> iff) In.
Proof. intros k' k Heqk sr sr' Heqrs; subst; now rewrite Heqrs. Qed.

#[export] Instance srenvironment_Add_iff : 
  Proper (Resource.eq ==> Term.eq ==> eq ==> eq ==> iff) (@SREnvironment.Add Term.t).
Proof.
  intros k' k Heqk d d' Heqd sr sr' Heqrs rs1 rs1' Heqrs1; unfold SREnvironment.Add.
  now rewrite Heqk, Heqd, Heqrs, Heqrs1. 
Qed.

#[export] Instance srenvironment_halts_iff : Proper (Logic.eq ==> eq ==> iff) halts. 
Proof. unfold halts; intros m n Heqm sr sr' Heqrs; subst; now rewrite Heqrs. Qed.

End SREnvironment.

(** ---- *)

(** ** Notation - Simple Resource Environment *)

Module SREnvironmentNotations.

(** *** Scope *)
Declare Scope srenv_scope.
Delimit Scope srenv_scope with sr.

(** *** Notations *)
Definition 𝐄 := SREnvironment.t.

Notation "t '⁺'" := (SREnvironment.Ext.new_key t) (at level 16) : srenv_scope.
Notation "∅" := SREnvironment.Raw.empty (at level 0, no associativity) : srenv_scope. 
Notation "r '∉' t" := (~ (SREnvironment.Raw.In r t)) (at level 75, no associativity) : srenv_scope. 
Notation "'isEmpty(' t ')'" := (SREnvironment.Empty t) (at level 20, no associativity) : srenv_scope. 
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
Infix "⊩" := SREnvironment.Wf (at level 20, no associativity) : srenv_scope.

(** *** Morphisms *)

Import SREnvironment.

#[export] Instance srenvironment_equiv_eq : Equivalence SREnvironment.eq := _.

#[export] Instance srenvironment_max_eq : Proper (eq ==> Logic.eq) (Ext.max_key) := Ext.max_key_eq.

#[export] Instance srenvironment_new_eq : Proper (eq ==> Logic.eq) (Ext.new_key) := Ext.new_key_eq.

#[export] Instance srenvironment_in_iff : 
  Proper (Logic.eq ==> SREnvironment.eq ==> iff) (SREnvironment.Raw.In) := _.

#[export] Instance srenvironment_find_eq : Proper (Logic.eq ==> eq ==> Logic.eq) (Raw.find) := _.

#[export] Instance srenvironment_Empty_iff : 
  Proper (SREnvironment.eq ==> iff) (SREnvironment.Empty) := _.

#[export] Instance srenvironment_Add_iff : 
  Proper (Resource.eq ==> Term.eq ==> eq ==> eq ==> iff) (@SREnvironment.Add Term.t) := _.

#[export] Instance srenvironment_add_eq : 
  Proper (Resource.eq ==> Term.eq ==> eq ==> eq) (@Raw.add Term.t) := _.

#[export] Instance srenvironment_Submap_iff : Proper (eq ==> eq ==> iff) Submap := _.

#[export] Instance srenvironment_Submap_po : PreOrder SREnvironment.Submap := Submap_po.

#[export] Instance srenvironment_Wf_iff : 
  Proper (Logic.eq ==> SREnvironment.eq ==> iff) SREnvironment.Wf := _.

#[export] Instance srenvironment_shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.

#[export] Instance srenvironment_halts_iff: 
  Proper (Logic.eq ==> SREnvironment.eq ==> iff) SREnvironment.halts := _.

End SREnvironmentNotations.