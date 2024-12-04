From Coq Require Import Lia Arith.PeanoNat Classical_Prop Morphisms SetoidList.
From Mecha Require Import Resource Resources Term Cell.
From Mecha Require Evaluation_Transition.
From DeBrLevel Require Import LevelInterface MapLevelInterface MapLevelLVLD MapExtInterface MapExt.
Import ResourceNotations TermNotations CellNotations 
       ResourcesNotations SetNotations.



(** * Environment - Resource Environment

  The functional transition, defined in [Functional_Transition.v], requires a local memory represented by an environment. We defined here the resource environment which maps resource names with memory cells, defined in [Cell.v]. This environment is an interface between the program and the outside.
*)

(** ** Module - Resource Environment *)
Module REnvironment <: IsLvlET.

(** *** Definitions *)
Include MakeLvlMapLVLD Cell.
Import Raw Ext.

Open Scope cell_scope.
Open Scope term_scope.

Module ET := Evaluation_Transition.
Module RS := Resources.St.

(** **** Initialize an environment

  For each instant, local resource names that represent a writing interaction have their memory cells initialized as unused with a [unit] term. This function takes a resource set [rs] and an environement [V] and produces an environment where all resource names in [rs] are initialized.
*)
Definition init_writers_func (r: resource) (V: t) : t := add r (⩽ unit … ⩾) V.

Definition init_writers (rs: resources) (V: t) := RS.fold (init_writers_func) rs V.

(** **** Halts 

  In the functional transition proofs, we assume that all elements in the input resource environment halts. Thus, we define this property here with [For_all].
  An environment has the halting property if and only if each term in it halts. 
*)
Definition halts (k : lvl) := For_all (fun _ d => ET.halts k (Cell.extract d)).

(** *** To be used or not to be *)

Definition   used r (V: t) : Prop := Cell.opt_used (find r V). 
Definition unused r (V: t) : Prop := Cell.opt_unused (find r V).

(** *** Properties *)

(** **** [unused] and [used] properties *)

#[export] Instance unused_iff : Proper (Logic.eq ==> eq ==> iff) unused.
Proof.
  intros r' r Heqr V V' HeqV; subst; unfold unused,Cell.opt_unused.
  now rewrite HeqV.
Qed.

Lemma unused_Empty (r: resource) (V: t) :
  Empty V -> ~ (unused r V).
Proof.
  unfold unused, Cell.opt_unused; intros Hemp Husd.
  assert (HnIn : ~ In r V).
  - intros [v HM]; now apply (Hemp r v).
  - apply not_in_find in HnIn.
    rewrite HnIn in Husd; contradiction. 
Qed.

Lemma unused_add (r r': resource) (v: 𝑣) (V: t) :
  (unused r (add r' v V)) -> (Cell.unused v) \/ (unused r V).
Proof.
  unfold unused, Cell.opt_unused; intro Husd; 
  destruct (Resource.eq_dec r r') as [Heq | Hneq]; subst.
  - rewrite add_eq_o in Husd; auto.
  - rewrite add_neq_o in Husd; auto.
Qed.

Lemma unused_add_1 (r r': resource) (v: 𝑣) (V: t) :
  (Cell.unused v) /\ (unused r V) -> (unused r (add r' v V)).
Proof.
  unfold unused, Cell.opt_unused; intros [HCusd Husd].
  destruct (Resource.eq_dec r r') as [Heq | Hneq]; subst.
  - rewrite add_eq_o; auto.
  - rewrite add_neq_o; auto.
Qed.

Lemma unused_add_eq (r: resource) (v: 𝑣) (V: t) :
  (Cell.unused v) <-> (unused r (add r v V)).
Proof. 
  unfold unused, Cell.opt_unused; split; intro Husd.
  - rewrite add_eq_o; auto.
  - rewrite add_eq_o in Husd; auto. 
Qed.

Lemma unused_add_neq (r r': resource) (v: 𝑣) (V: t) :
  r <> r' -> (unused r V) <-> (unused r (add r' v V)).
Proof. 
  unfold unused, Cell.opt_unused; split; intro Husd.
  - rewrite add_neq_o; auto.
  - rewrite add_neq_o in Husd; auto. 
Qed.

Lemma unused_find_e (r: resource) (V: t) :
  unused r V -> exists (v: Λ), Logic.eq (find r V) (Some (⩽v … ⩾)).
Proof.
  unfold unused; intro unsd.
  destruct (find r V) eqn:Hfi; simpl in *; try contradiction.
  destruct r0; simpl in *; try contradiction.
  now exists λ.
Qed.

Lemma unused_find_iff (r: resource) (V V': t) :
  find r V = find r V' -> unused r V <-> unused r V'.
Proof.
  intro Hfi; unfold unused; destruct (find r V); 
  rewrite <- Hfi; simpl; try (split; auto).
Qed.

Lemma unused_find (r: resource) (v: Λ) (V: t) :
  find r V = Some (⩽v … ⩾) -> unused r V.
Proof. intro Hfi; unfold unused; rewrite Hfi; now simpl. Qed.

Lemma unused_shift_Wf (m n : lvl) (r: resource) (V: t) : 
  Wf m V -> unused r (shift m n V) <-> unused r V.
Proof.
  intro HvV; split; intro Hunsd.
  - apply unused_find_e in Hunsd as [v Hfi].
    apply shift_find_e_1 in Hfi as HI.
    destruct HI as [[r' Heqr] [v' Heqv]]; subst.
    destruct v'; simpl in *; inversion Heqv; subst; clear Heqv.
    replace (⩽ [⧐m – n] λ … ⩾) with (([⧐m – n] ⩽ λ … ⩾)) in Hfi by auto.
    rewrite <- shift_find_iff in Hfi.
    apply (Wf_find m) in Hfi as HI; auto.
    destruct HI as [Hvr' _].
    rewrite Resource.shift_wf_refl; auto.
    now apply unused_find in Hfi.
  - apply unused_find_e in Hunsd as [v Hfi].
    apply (Wf_find m) in Hfi as HI; auto.
    destruct HI as [Hvr' _].
    rewrite <- (Resource.shift_wf_refl m n r); auto.
    apply (unused_find _ <[[⧐m – n] v]>).
    replace (⩽ [⧐m – n] v … ⩾) with (([⧐m – n] ⩽ v … ⩾)) by auto.
    now rewrite <- shift_find_iff.
Qed.
    
Lemma unused_in (r: resource) (V: t) : unused r V -> In r V.
Proof.
  unfold unused.
  destruct (find r V) eqn:Hfi; simpl; intros.
  - exists r0; now apply find_2.
  - inversion H.
Qed.

#[export] Instance used_iff : Proper (Logic.eq ==> eq ==> iff) used.
Proof.
  intros r' r Heqr V V' HeqV; subst; unfold used,Cell.opt_used.
  now rewrite HeqV.
Qed.

Lemma used_Empty (r: resource) (V: t) :
  Empty V -> ~ (used r V).
Proof.
  unfold used, Cell.opt_used; intros Hemp Husd.
  assert (HnIn : ~ In r V).
  - intros [v HM]; now apply (Hemp r v).
  - apply not_in_find in HnIn.
    rewrite HnIn in Husd; contradiction. 
Qed.

Lemma used_add (r r': resource) (v: 𝑣) (V: t) :
  (used r (add r' v V)) -> (Cell.used v) \/ (used r V).
Proof.
  unfold used, Cell.opt_used; intro Husd; 
  destruct (Resource.eq_dec r r') as [Heq | Hneq]; subst.
  - rewrite add_eq_o in Husd; auto.
  - rewrite add_neq_o in Husd; auto.
Qed.

Lemma used_add_1 (r r': resource) (v: 𝑣) (V: t) :
  (Cell.used v) /\ (used r V) -> (used r (add r' v V)).
Proof.
  unfold used, Cell.opt_used; intros [HCusd Husd].
  destruct (Resource.eq_dec r r') as [Heq | Hneq]; subst.
  - rewrite add_eq_o; auto.
  - rewrite add_neq_o; auto.
Qed.

Lemma used_add_eq (r: resource) (v: 𝑣) (V: t) :
  (Cell.used v) <-> (used r (add r v V)).
Proof. 
  unfold used, Cell.opt_used; split; intro Husd.
  - rewrite add_eq_o; auto.
  - rewrite add_eq_o in Husd; auto. 
Qed.

Lemma used_add_neq (r r': resource) (v: 𝑣) (V: t) :
  r <> r' -> (used r V) <-> (used r (add r' v V)).
Proof. 
  unfold used, Cell.opt_used; split; intro Husd.
  - rewrite add_neq_o; auto.
  - rewrite add_neq_o in Husd; auto. 
Qed.

Lemma used_find_e (r: resource) (V: t) :
  used r V -> exists (v: Λ), Logic.eq (find r V) (Some (⩽… v⩾)).
Proof.
  unfold used; intro unsd.
  destruct (find r V) eqn:Hfi; simpl in *; try contradiction.
  destruct r0; simpl in *; try contradiction.
  now exists λ.
Qed.

Lemma used_find_iff (r: resource) (V V': t) :
  find r V = find r V' -> used r V <-> used r V'.
Proof.
  intro Hfi; unfold used; destruct (find r V); 
  rewrite <- Hfi; simpl; try (split; auto).
Qed.

Lemma used_find (r: resource) (v: Λ) (V: t) :
  find r V = Some (⩽… v⩾) -> used r V.
Proof. intro Hfi; unfold used; rewrite Hfi; now simpl. Qed.

Lemma used_shift_Wf (m n : lvl) (r: resource) (V: t) : 
  Wf m V -> used r (shift m n V) <-> used r V.
Proof.
  intro HvV; split; intro Hunsd.
  - apply used_find_e in Hunsd as [v Hfi].
    apply shift_find_e_1 in Hfi as HI.
    destruct HI as [[r' Heqr] [v' Heqv]]; subst.
    destruct v'; simpl in *; inversion Heqv; subst; clear Heqv.
    replace (⩽…  [⧐m – n] λ⩾) with (([⧐m – n] ⩽…  λ⩾)) in Hfi by auto.
    rewrite <- shift_find_iff in Hfi.
    apply (Wf_find m) in Hfi as HI; auto.
    destruct HI as [Hvr' _].
    rewrite Resource.shift_wf_refl; auto.
    now apply used_find in Hfi.
  - apply used_find_e in Hunsd as [v Hfi].
    apply (Wf_find m) in Hfi as HI; auto.
    destruct HI as [Hvr' _].
    rewrite <- (Resource.shift_wf_refl m n r); auto.
    apply (used_find _ <[[⧐m – n] v]>).
    replace (⩽… [⧐m – n] v⩾) with (([⧐m – n] ⩽…  v⩾)) by auto.
    now rewrite <- shift_find_iff.
Qed.

Lemma used_in (r: resource) (V: t) : used r V -> In r V.
Proof.
  unfold used.
  destruct (find r V) eqn:Hfi; simpl; intros.
  - exists r0; now apply find_2.
  - inversion H.
Qed.

(** **** [new_key] properties *)

Lemma new_key_wh (v v' : 𝑣) (V: t) :
  new_key (add (S (new_key V)) v 
          (add (new_key V) (Cell.shift (new_key V) 2 v') 
                           (shift (new_key V) 2 V))) = S (S (new_key V)).
Proof.
  repeat rewrite new_key_add_l; auto.
  rewrite shift_new_refl; auto.
Qed.

Lemma new_key_le_remove (x: lvl) (t: t) :
  (new_key (remove x t)) <= (new_key t).
Proof.
  revert x.
  induction t using map_induction; intros y.
  - rewrite new_key_Empty.
    -- rewrite new_key_Empty; auto.
    -- intros x v HM.
       apply remove_3 in HM.
       apply (H x v HM).
  - unfold Add in H0; rewrite H0 in *; clear H0.
    destruct (Resource.eq_dec x y) as [Heq | Hneq]; subst.
    -- rewrite remove_add_1.
       rewrite new_key_add_max.
       specialize (IHt1 y); lia.
    -- rewrite remove_add_2; auto.
       do 2 rewrite new_key_add_max.
       specialize (IHt1 y); lia.
Qed.

Lemma new_key_in_remove (x: lvl) (t: t) :
  In x t -> new_key t = (S x) \/ new_key t = (new_key (remove x t)).
Proof.
  intros HIn.
  apply new_key_in in HIn as Hlt.
  assert (HIn': In x t) by assumption.
  destruct HIn as [v Hfi].
  apply find_1 in Hfi.
  apply add_id in Hfi.
  rewrite <- Hfi.
  rewrite <- add_remove_1 at 1 2.
  assert (HnIn: ~ In x (remove x t)).
  - rewrite remove_in_iff; intros []; auto.
  - rewrite new_key_add_max.
    rewrite remove_add_1; lia.
Qed.


Lemma new_key_in_remove_1 (x: lvl) (t: t) :
  In x t -> new_key t = max (S x) (new_key (remove x t)).
Proof.
  intros HIn.
  apply new_key_in in HIn as Hlt.
  assert (HIn': In x t) by assumption.
  destruct HIn as [v Hfi].
  apply find_1 in Hfi.
  apply add_id in Hfi.
  rewrite <- Hfi.
  rewrite <- add_remove_1 at 1.
  assert (HnIn: ~ In x (remove x t)).
  - rewrite remove_in_iff; intros []; auto.
  - rewrite new_key_add_max.
    rewrite remove_add_1; lia.
Qed.

(** **** [Wf] properties *)

Lemma Wf_remove (k x: lvl) (t: t) : Wf k t -> Wf k (remove x t).
Proof.
  revert k x. 
  induction t using map_induction; intros k y Hvt.
  - apply Wf_Empty.
    intros x v HM.
    apply remove_3 in HM.
    apply (H x v HM).
  - unfold Add in H0; rewrite H0 in *; clear H0.
    apply Wf_add_notin in Hvt as [Hvx [Hve Hvt]]; auto.
    destruct (Resource.eq_dec y x); subst.
    -- rewrite remove_add_1.
       now apply IHt1.
    -- rewrite remove_add_2; auto.
       apply Wf_add_notin; auto.
       rewrite remove_in_iff; intros []; auto.
Qed.

(** **** [init_writers] properties *)

#[export] Instance init_writers_func_eq : Proper (Logic.eq ==> eq ==> eq) init_writers_func.
Proof. 
  unfold init_writers_func; intros k' k Heqk V V' HeqV. 
  subst; now rewrite HeqV. 
Qed.

Lemma init_writers_func_transpose : transpose eq init_writers_func.
Proof. 
  unfold init_writers_func; intros k k' V. 
  destruct (Resource.eq_dec k k') as [Heq | Hneq]; subst.
  - reflexivity.
  - now rewrite add_add_2; auto.
Qed.

#[local] Hint Resolve init_writers_func_eq init_writers_func_transpose : core.

Lemma init_writers_Empty (rs: resources) (V: t) : RS.Empty rs -> eq (init_writers rs V) V.
Proof.
  intro Hemp; unfold init_writers.
  apply RS.empty_is_empty_1 in Hemp.
  rewrite RS.fold_equal with (eqA := eq); eauto.
  now rewrite RS.fold_empty.
Qed.

Lemma init_writers_add (r: resource) (rs: resources) (V: t) :
  (r ∉ rs)%s ->
  eq (init_writers (RS.add r rs) V) (add r (⩽ unit … ⩾) (init_writers rs V)). 
Proof.
  unfold init_writers; intro HnIn.
  now rewrite RS.fold_add with (eqA := eq); auto.
Qed.

Lemma init_writers_in_unused (rs: resources) (V: t) (r: resource) :
  (r ∈ rs)%s -> unused r (init_writers rs V).
Proof.
  revert r; induction rs using RS.set_induction; intros r HIn.
  - unfold RS.Empty in H. 
    exfalso; now apply (H r).
  - apply RS.Add_inv in H0; subst.
    rewrite init_writers_add; auto.
    apply RS.add_spec in HIn as [Heq | HIn]; subst. 
    -- apply unused_add_eq; now red.
    -- assert (r <> x) by (intro; subst; contradiction).
       apply unused_add_neq; auto. 
Qed.

Lemma init_writers_find (rs: resources) (V: t) (r: resource) (v: 𝑣) :
  find r (init_writers rs V) = Some v -> (r ∈ rs)%s \/ find r V = Some v.
Proof.
  revert r v; induction rs using RS.set_induction; intros r v Hfi.
  - rewrite init_writers_Empty in Hfi; auto.
  - apply RS.Add_inv in H0; subst.
    rewrite init_writers_add in Hfi; auto.
    destruct (Resource.eq_dec x r) as [Heq | Hneq]; subst.
    -- left; rewrite RS.add_spec; auto.
    -- rewrite add_neq_o in Hfi; auto.
       apply IHrs1 in Hfi as [HIn | Hfi]; auto.
       left; rewrite RS.add_spec; auto.
Qed.

Lemma init_writers_find_inp (rs: resources) (V: t) (r: resource) (v: 𝑣) :
  (forall r, find r V = Some v -> exists v', Logic.eq v (Cell.inp v')) ->
  find r (init_writers rs V) = Some v -> exists v', Logic.eq v (Cell.inp v'). 
Proof.
  revert r v; induction rs using RS.set_induction; intros r v Ht Hfi.
  - rewrite init_writers_Empty in Hfi; auto.
    now apply (Ht r).
  - apply RS.Add_inv in H0; subst.
    rewrite init_writers_add in Hfi; auto.
    destruct (Resource.eq_dec x r) as [Heq | Hneq]; subst.
    -- rewrite add_eq_o in Hfi; auto.
       inversion Hfi; subst; now exists Term.tm_unit.
    -- rewrite add_neq_o in Hfi; auto.
       now apply (IHrs1 r).
Qed.

Lemma init_writers_in_iff (rs: resources) (V: t) (r: resource) :
  In r (init_writers rs V) <-> (r ∈ rs)%s \/ In r V.
Proof.
  revert r; induction rs using RS.set_induction; intro r; split.
  - intro HIn. rewrite init_writers_Empty in HIn; auto.
  - intros [HIn | HIn].
    -- exfalso. now apply (H r).
    -- now rewrite init_writers_Empty.
  - intro HIn; apply RS.Add_inv in H0; subst. 
    rewrite init_writers_add in HIn; auto.
    apply add_in_iff in HIn as [Heq | HIn]; subst.
    -- left; rewrite RS.add_spec; auto.
    -- apply IHrs1 in HIn as [HIn | HIn]; auto.
       left; rewrite RS.add_spec; auto.
  - intros [HIn | HIn]; apply RS.Add_inv in H0; subst.
    -- rewrite init_writers_add; auto.
       rewrite add_in_iff.
       apply RS.add_spec in HIn as [Heq | HIn]; auto.
       right; rewrite IHrs1; now left.
    -- rewrite init_writers_add; auto.
       rewrite add_in_iff; right.
       rewrite IHrs1; now right. 
Qed. 

Lemma init_writers_in (rs: resources) (V: t) (r: resource) :
  (r ∈ rs)%s -> find r (init_writers rs V) = Some (Cell.inp <[unit]>).
Proof.
  revert r; induction rs using RS.set_induction; intros r HIn.
  - exfalso; now apply (H r).
  - apply RS.Add_inv in H0; subst.
    rewrite init_writers_add; auto.
    destruct (Resource.eq_dec r x) as [| Hneq]; subst.
    -- now rewrite add_eq_o.
    -- rewrite add_neq_o; auto.
       apply RS.add_spec in HIn as [| HIn]; subst; auto.
       contradiction.
Qed.

Lemma init_writers_unused (r: resource) (rs: resources) (V: t) :
  unused r V -> unused r (init_writers rs V).
Proof.
  revert r; induction rs using RS.set_induction; intro r.
  - rewrite init_writers_Empty; auto.
  - apply RS.Add_inv in H0; subst.
    rewrite init_writers_add; auto.
    destruct (Resource.eq_dec r x) as [| Hneq]; subst; intro Hunsd.
    -- apply unused_add_eq; now red.
    -- apply unused_add_neq; auto.
Qed.

Lemma init_writers_add_remove (r: resource) (rs: resources) (V: t) :
  REnvironment.eq (init_writers (r +: rs)%s V) (init_writers (r +: rs)%s (remove r V)).
Proof.
  revert r V; induction rs using RS.set_induction; intros r V.
  - do 2 rewrite init_writers_add by apply H.
    -- apply (init_writers_Empty rs V) in H as H'; rewrite H'; clear H'.
       apply (init_writers_Empty rs (remove r V)) in H as H'; rewrite H'; clear H'.
       clear H rs; revert r. 
       induction V using map_induction; intro r.
       + assert (REnvironment.eq (remove r V) V).
         { 
          unfold REnvironment.eq; rewrite remove_id.
          intros [v1 HM]; now apply (H r v1).
         }
         now rewrite H0.
       + unfold Add in H0; rewrite H0 in *; clear H0.
         destruct (Resource.eq_dec r x) as [| Hneq]; subst.
         ++ rewrite add_shadow.
            rewrite add_remove_1.
            now rewrite add_shadow.
         ++ rewrite add_add_2; auto.
            rewrite remove_add_2; auto.
            symmetry.
            rewrite add_add_2; auto.
            now rewrite IHV1.
  - apply RS.Add_inv in H0; subst. 
    destruct (Resource.eq_dec r x) as [| Hneq]; subst.
    -- replace (x +: (x +: rs1))%s with (x +: rs1)%s; auto.
       apply RS.eq_leibniz.
       symmetry; rewrite RS.add_equal; try reflexivity.
       rewrite RS.add_spec; now left.
    -- replace (r +: (x +: rs1))%s with (x +: (r +: rs1))%s; auto.
       + do 2 rewrite (init_writers_add x) 
         by (rewrite RS.add_spec; intros [|]; auto).
         now rewrite <- IHrs1.
       + apply RS.eq_leibniz.
         now rewrite RS.add_add.
Qed.

Lemma init_writers_new_key (V: t) (rs: resources) : 
  new_key (init_writers rs V) = max (Resources.new_key rs) (new_key V).
Proof.
  revert V.
  induction rs using RS.set_induction; intro V.
  - rewrite Resources.new_key_Empty; auto; simpl.
    rewrite init_writers_Empty; auto.
  - apply RS.Add_inv in H0; subst.
    rewrite init_writers_add_remove.
    rewrite init_writers_add; auto.
    rewrite Resources.new_key_add_max; auto.
    rewrite new_key_add_max.
    rewrite IHrs1.
    destruct (In_dec V x).
    + apply new_key_in_remove_1 in i as HI.
      rewrite HI; lia.
    + apply remove_id in n.
      rewrite n; lia.
Qed.

Lemma init_writers_Wf (k : lvl) (V: t) (t : resources) :
  (k ⊩ t)%rs /\ Wf k V -> Wf k (init_writers t V).
Proof.
  revert k V.
  induction t using RS.set_induction; intros k V  [Hvt HvV].
  - rewrite init_writers_Empty; auto.
  - apply RS.Add_inv in H0; subst.
    apply Resources.Wf_add_iff in Hvt as [Hvx Hvt1].
    rewrite init_writers_add_remove.
    rewrite init_writers_add; auto.
    apply Wf_add_notin.
    -- rewrite init_writers_in_iff; intros [|]; auto.
       apply remove_in_iff in H0 as []; auto.
    -- do 2 (split;auto).
       + constructor.
       + apply IHt1; split; auto.
         now apply Wf_remove.
Qed.

(** **** [Wf] properties *)

Lemma Wf_wh (v v' : 𝑣) (V: t) :
  Wf (new_key V) V -> ((new_key V) ⊩ v)%cl -> ((new_key V) ⊩ v')%cl -> 
  Wf (S (S (new_key V))) 
        (add (S (new_key V)) v 
        (add (new_key V) (Cell.shift (new_key V) 2 v') (shift (new_key V) 2 V))).
Proof.
  intros HvV Hvv Hvv'; do 2 try rewrite Wf_add_notin.
  - repeat split; try (unfold Resource.Wf; lia). 
    -- apply Cell.Wf_weakening with (k := new_key V); auto.
    -- replace (S (S (new_key V))) with ((new_key V) + 2) by lia. 
       now apply Cell.shift_preserves_wf_1.
    -- replace (S (S (new_key V))) with ((new_key V) + 2) by lia. 
       now apply shift_preserves_wf_1.  
  - apply new_key_notin; auto; rewrite shift_new_refl; auto.
  - apply new_key_notin; rewrite new_key_add_l; auto.
    rewrite shift_new_refl; auto.
Qed.

Lemma Wf_wh_full (v v' : 𝑣) (V: t) :
  Wf (new_key V) V -> ((new_key V) ⊩ v)%cl -> ((new_key V) ⊩ v')%cl -> 
  Wf (new_key 
          ((add (S (new_key V)) v 
          (add (new_key V) (Cell.shift (new_key V) 2 v') (shift (new_key V) 2 V))))) 
        (add (S (new_key V)) v 
        (add (new_key V) (Cell.shift (new_key V) 2 v') (shift (new_key V) 2 V))).
Proof.
  intros HvV Hvv Hvv'.
  rewrite new_key_wh; now apply Wf_wh.
Qed.

(** **** [halts] properties *)

Lemma halts_add (k : lvl) (r: resource) (v: 𝑣) (V: t) :
  (ET.halts k (Cell.extract v)) /\ halts k V -> halts k (add r v V).
Proof.
  intros [Hltv Hltm] r' v' Hfi.
  destruct (Resource.eq_dec r r') as [| Hneq]; subst.
  - rewrite add_eq_o in Hfi; auto.
    inversion Hfi; subst; auto.
  - rewrite add_neq_o in Hfi; auto.
    now apply Hltm in Hfi.
Qed.

Lemma halts_init_writers (k : lvl) (rs: resources) (V: t) :
  halts k V -> halts k (init_writers rs V).
Proof.
  induction rs using Resources.St.set_induction; intro Hlt.
  - now rewrite init_writers_Empty.
  - apply RS.Add_inv in H0; subst.
    rewrite init_writers_add; auto.
    apply halts_add; split; auto.
    red; exists <[unit]>; split.
    -- apply ET.multi_unit.
    -- now constructor.
Qed.

Lemma halts_weakening (m n : lvl) (V: t) : 
  m <= n -> halts m V -> halts n (shift m (n - m) V).
Proof.
  intros Hle Hlt r v Hfi. 
  apply shift_find_e_1 in Hfi as HI.
  destruct HI as [[r' Heqr'] [v' Heqv']]; subst.
  rewrite <- shift_find_iff in Hfi. 
  destruct v'; simpl in *; 
  apply ET.halts_weakening; auto; apply Hlt in Hfi; now simpl in *.
Qed.

Lemma halts_weakening_1 (m n : lvl) (V: t) : 
  halts m V -> halts (m + n) (shift m n V).
Proof.
  intro Hlt; replace n with ((m + n) - m) at 2 by lia.
  apply halts_weakening; auto; lia.
Qed.

(** *** Morphisms *)

#[export] Instance renvironment_in_iff : Proper (Logic.eq ==> eq ==> iff) In.
Proof. intros k' k Heqk V V' HeqV; subst; now rewrite HeqV. Qed.

#[export] Instance renvironment_Add_iff : 
  Proper (Resource.eq ==> Cell.eq ==> eq ==> eq ==> iff) (@Add Cell.t).
Proof.
  intros k' k Heqk d d' Heqd V V' HeqV V1 V1' HeqV1; unfold Add.
  now rewrite Heqk, Heqd, HeqV, HeqV1. 
Qed.

#[export] Instance renvironment_halts_iff : Proper (Logic.eq ==> eq ==> iff) halts. 
Proof. unfold halts; intros m n Heqm V V' HeqV; subst; now rewrite HeqV. Qed.

End REnvironment.

(** ---- *)

(** ** Notation - Resource Environment *)

Module REnvironmentNotations.

(** *** Scope *)
Declare Scope renvironment_scope.
Delimit Scope renvironment_scope with re.

(** *** Notations *)
Definition 𝐕 := REnvironment.t.

Notation "∅" := REnvironment.Raw.empty (at level 0, no associativity) : renvironment_scope. 
Notation "t '⁺'" := (REnvironment.Ext.new_key t) (at level 16) : renvironment_scope.
Notation "r '∉' t" := (~ (REnvironment.Raw.In r t)) 
                       (at level 75, no associativity) : renvironment_scope. 
Notation "'isEmpty(' t ')'" := (REnvironment.Empty t) (at level 20, no associativity) : renvironment_scope. 
Notation "'Add'" := (REnvironment.Add) (at level 20, no associativity) : renvironment_scope. 
Notation "t '⌊' x '⌋'"  := (REnvironment.Raw.find x t) (at level 15, x constr) : renvironment_scope.
Notation "'max(' t ')'"  := (REnvironment.Ext.max_key t) (at level 15) : renvironment_scope.
Notation "⌈ x ⤆ v '⌉' t"  := (REnvironment.Raw.add x v t) 
                              (at level 15, x constr, v constr) : renvironment_scope.
Notation "'[⧐' lb '–' k ']' t" := (REnvironment.shift lb k t) 
                                   (at level 65, right associativity) : renvironment_scope.

Infix "⊆" := REnvironment.Submap (at level 60, no associativity) : renvironment_scope. 
Infix "∈" := REnvironment.Raw.In (at level 60, no associativity) : renvironment_scope. 
Infix "=" := REnvironment.eq : renvironment_scope.
Infix "⊩" := REnvironment.Wf (at level 20, no associativity) : renvironment_scope.

(** *** Morphisms *)

Import REnvironment.

#[export] Instance renvionment_equiv_eq : Equivalence REnvironment.eq := _.

#[export] Instance renvionment_max_eq : Proper (eq ==> Logic.eq) (Ext.max_key) := Ext.max_key_eq.

#[export] Instance renvionment_new_eq : Proper (eq ==> Logic.eq) (Ext.new_key) := Ext.new_key_eq. 

#[export] Instance renvionment_in_iff :  Proper (Logic.eq ==> eq ==> iff) (Raw.In) := _.

#[export] Instance renvionment_find_eq : Proper (Logic.eq ==> eq ==> Logic.eq) (Raw.find) := _.

#[export] Instance renvionment_Empty_iff : Proper (eq ==> iff) (Empty) := _.

#[export] Instance renvionment_Add_iff : 
  Proper (Resource.eq ==> Cell.eq ==> eq ==> eq ==> iff) (@REnvironment.Add Cell.t) := _.

#[export] Instance renvionment_add_eq : 
  Proper (Resource.eq ==> Cell.eq ==> REnvironment.eq ==> REnvironment.eq) (@Raw.add Cell.t) := _.

#[export] Instance renvionment_remove_eq : 
  Proper (Resource.eq ==> eq ==> eq) (@Raw.remove Cell.t) := _.

#[export] Instance renvionment_Submap_iff : Proper (eq ==> eq ==> iff) Submap := _.

#[export] Instance renvionment_Submap_po : PreOrder Submap := Submap_po.

#[export] Instance renvionment_Wf_iff : Proper (Logic.eq ==> eq ==> iff) Wf := _.

#[export] Instance renvionment_shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.

#[export] Instance renvionment_halts_iff : Proper (Logic.eq ==> eq ==> iff) halts := _. 

#[export] Instance renvionment_unused_iff : Proper (Logic.eq ==> eq ==> iff) unused := _.

#[export] Instance renvionment_used_iff : Proper (Logic.eq ==> eq ==> iff) used := _.

End REnvironmentNotations.