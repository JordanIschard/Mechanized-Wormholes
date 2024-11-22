From Coq Require Import Lia Arith.PeanoNat Classical_Prop Morphisms SetoidList.
From Mecha Require Import Resource Resources Term Cell REnvironment Sample.
From Mecha Require Evaluation_Transition.
From DeBrLevel Require Import LevelInterface MapLevelInterface MapLevel MapExtInterface MapExt.
Import ResourceNotations TermNotations CellNotations SampleNotations 
       ResourcesNotations SetNotations REnvironmentNotations.

(** * Environment - I/O Sample *)


(** ** Module - I/O Sample *)

Module Samples <: IsLvlET.

(** *** Definition *)

Include MapLvlD.MakeLvlMapLVLD Sample.
Import Raw Ext.

Module RE := REnvironment.
Module Sp := Sample. 

Open Scope renvironment_scope.

(** **** Next function *)

Definition nexts_core_func (v : σ) := Cell.inp (Sp.next v). 
Definition nexts_func (r : resource) (v : σ) (V : 𝐕) := ⌈r ⤆ (nexts_core_func v)⌉ V.

Definition nexts (t : t) : 𝐕 := fold nexts_func t ∅.

(** **** Put function *)

Definition puts_core_func (r : resource) (v : σ) (V : 𝐕) :=
  match V⌊r⌋ with 
    | Some (⩽ … v' ⩾) =>  (Sp.put (Some v') v)
    |  _ => (Sp.put None v) 
  end.

Definition puts_func (V : 𝐕) (r : resource) (v : σ) (t : t) :=
  add r (puts_core_func r v V) t.

Definition puts (V : 𝐕) (t : t) := fold (puts_func V) t empty.

(** **** Halts *)

Definition halts (k : lvl) := For_all (fun _ d => Sp.halts k d).

(** *** Property *)

Hint Resolve RE.eq_equiv : core.

(** *** Property *)

(** **** [nexts] property *)

#[export] Instance nexts_func_eq : Proper (Logic.eq ==> Logic.eq ==> RE.eq ==> RE.eq) nexts_func.
Proof.
  unfold nexts_func; intros r' r Heqr v' v Heqv V V' HeqV; subst.
  now rewrite HeqV.
Qed.

Lemma nexts_func_diamond : Diamond REnvironment.eq nexts_func.
Proof.
  intros r r' v v' V V1 V2 Hneq HeqV1 HeqV2; unfold nexts_func in *.
  rewrite <- HeqV1, <- HeqV2; now rewrite RE.add_add_2; auto.
Qed.

#[export] Hint Resolve nexts_func_eq nexts_func_diamond : core.

Lemma nexts_Empty (t : t) : Empty t -> ((nexts t) = ∅).
Proof.  intro HEmp ; unfold nexts; rewrite fold_Empty; auto. Qed.

Lemma nexts_Add_notin_spec (x : resource) (v : σ) (t t' : t) : 
  ~ In x t -> Samples.Add x v t t' -> 
  ((nexts t') = ⌈x ⤆ (Cell.inp (Sample.next v))⌉ (nexts t))%re.
Proof.
  intros HnIn HAdd; unfold nexts. 
  rewrite fold_Add with (eqA := RE.eq) (i := ∅); eauto.
  unfold nexts_func, nexts_core_func; now simpl.
Qed.

Lemma nexts_add_notin_spec (x : resource) (v : σ) (t : t) : 
  ~ In x t -> ((nexts (add x v t)) = ⌈x ⤆ (Cell.inp (Sample.next v))⌉ (nexts t))%re.
Proof.
  intro HnIn; unfold nexts. 
  rewrite fold_Add with (eqA := RE.eq) (i := ∅); eauto.
  - unfold nexts_func, nexts_core_func; now simpl.
  - now unfold Samples.Add.
Qed.

#[export] Instance nexts_eq : Proper (eq ==> RE.eq) nexts.
Proof.
  intros t t' Heqt; revert t' Heqt. 
  induction t using map_induction; intros t' Heqt.
  - rewrite nexts_Empty; auto.
    rewrite Heqt in H.
    now rewrite nexts_Empty.
  - rewrite nexts_Add_notin_spec; eauto.
    assert (Samples.Add x e t1 t').
    { unfold Samples.Add in *; now rewrite <- Heqt. }
    now symmetry; rewrite nexts_Add_notin_spec; eauto.
Qed.

Lemma nexts_in_iff (r : resource) (t : t) : In r t <-> r ∈ (nexts t).
Proof.
  revert r; induction t using map_induction; intro r.
  - split; intro HIn.
    -- exfalso; destruct HIn as [v HM].
       now apply (H r v).
    -- rewrite nexts_Empty in HIn; auto.
       inversion HIn; subst; inversion H0.
  - split; intros HIn; 
    unfold Samples.Add in H0; rewrite H0 in *; clear H0.
    -- rewrite nexts_add_notin_spec; auto.
       apply add_in_iff in HIn as [| HIn]; subst;
       rewrite RE.add_in_iff; auto.
       now right; rewrite <- IHt1.
    -- rewrite nexts_add_notin_spec in HIn; auto.
       apply RE.add_in_iff in HIn as [| HIn]; subst;
       rewrite add_in_iff; auto.
       now right; rewrite IHt1.
Qed.

Lemma nexts_Empty_eq (t : t) : Empty t <-> RE.Empty (nexts t).
Proof.
  split; intros HEmp r v HM.
  - rewrite nexts_Empty in HM; auto.
    inversion HM.
  - assert (HIn: In r t) by (now exists v).
    apply nexts_in_iff in HIn as [v' HM']. 
    now apply (HEmp r v').
Qed.

Lemma nexts_remove_spec (r : resource) (t : t) : 
  (RE.Raw.remove r (nexts t) = (nexts (remove r t)))%re.
Proof.
  revert r; induction t using map_induction; intro r.
  - rewrite nexts_Empty; auto.
    rewrite nexts_Empty.
    -- apply (RE.remove_id ∅ r); intro c; inversion c; inversion H0.
    -- intros r' v HM. 
       apply remove_mapsto_iff in HM as [_ HM].
       now apply (H r' v).
  - unfold Samples.Add in H0; rewrite H0 in *; clear H0.
    rewrite nexts_add_notin_spec; auto.
    apply RE.Equal_mapsto_iff; intros r' v; split; intro HM.
    -- apply RE.find_2; apply RE.find_1 in HM.
       destruct (Resource.eq_dec r x) as [| Hneq']; subst.
       + rewrite RE.remove_add_1 in HM. 
         assert (RE.eq (nexts (remove x (add x e t1))) (nexts (remove x t1)))
         by now rewrite remove_add_1.
         rewrite H0; clear H0.
         now rewrite <- IHt1.
       + rewrite RE.remove_add_2 in HM; auto. 
         assert (RE.eq (nexts (remove r (add x e t1))) (nexts (add x e (remove r t1))))
         by now rewrite remove_add_2; auto.
         rewrite H0; clear H0.
         rewrite nexts_add_notin_spec.
         ++ destruct (Resource.eq_dec r' x) as [| Hneq'']; subst.
            * rewrite RE.add_eq_o in *; auto.
            * rewrite RE.add_neq_o in *; auto.
              now rewrite <- IHt1.
         ++ intro HIn.  
            rewrite remove_neq_in_iff in HIn; auto.
    -- apply RE.find_2; apply RE.find_1 in HM. 
       destruct (Resource.eq_dec r x) as [| Hneq']; subst.
       + rewrite RE.remove_add_1; rewrite IHt1.
         assert (RE.eq (nexts (remove x (add x e t1))) (nexts (remove x t1)))
         by now rewrite remove_add_1.
         now rewrite H0 in HM; clear H0.
       + rewrite RE.remove_add_2; auto.
         assert (RE.eq (nexts (remove r (add x e t1))) (nexts (add x e (remove r t1))))
         by now rewrite remove_add_2; auto.
         rewrite H0 in HM; clear H0.
         rewrite nexts_add_notin_spec in HM.
         ++ destruct (Resource.eq_dec r' x) as [| Hneq'']; subst.
            * rewrite RE.add_eq_o in *; auto.
            * rewrite RE.add_neq_o in *; auto.
              now rewrite <- IHt1 in HM.
         ++ intro HIn.  
            rewrite remove_neq_in_iff in HIn; auto.
Qed.


Lemma nexts_add_iff (r : resource) (v : σ) (t : t) : 
  ((nexts (add r v t)) = ⌈r ⤆ (Cell.inp (Sample.next v))⌉ (nexts t))%re.
Proof.
  destruct (In_dec t r) as [HIn | HnIn].
  - transitivity (nexts (add r v (remove r t))).
    -- now rewrite add_remove_1.
    -- rewrite nexts_add_notin_spec.
       + intro y; destruct (Resource.eq_dec r y) as [| Hneq]; subst.
         ++ do 2 (rewrite RE.add_eq_o; auto).
         ++ do 2 (rewrite RE.add_neq_o; auto).
            rewrite <- nexts_remove_spec.
            rewrite RE.remove_neq_o; auto.
       + rewrite remove_in_iff; intros []; lia.
  - now apply nexts_add_notin_spec.
Qed.

Lemma nexts_find_e_spec (r : resource) (v : 𝑣) (t : t) :
  (nexts t)⌊r⌋ = Some v -> exists rf, (v = nexts_core_func rf)%type.
Proof.
  revert r v; induction t using map_induction; intros r v Hfi.
  - rewrite nexts_Empty in Hfi; auto; inversion Hfi.
  - unfold Samples.Add in H0; rewrite H0 in *; clear H0. 
    rewrite nexts_add_iff in Hfi.
    destruct (Resource.eq_dec x r) as [| Hneq]; subst.
    -- rewrite RE.add_eq_o in Hfi; auto.
       inversion Hfi; subst; clear Hfi; now exists e.
    -- rewrite RE.add_neq_o in Hfi; auto.
       now apply (IHt1 r).
Qed.

Lemma nexts_find_spec (r : resource) (v : σ) (t : t) :
  find r t = Some v -> (nexts t)⌊r⌋ = Some (nexts_core_func v).
Proof.
  revert r v; induction t using map_induction; intros r v Hfi.
  - exfalso; apply (H r v).
    now apply find_2.
  - unfold Samples.Add in H0; rewrite H0 in *; clear H0.
    rewrite nexts_add_iff.  
    destruct (Resource.eq_dec r x) as [| Hneq]; subst.
    -- rewrite add_eq_o in Hfi; auto; inversion Hfi; subst; clear Hfi.
       rewrite RE.add_eq_o; auto.
    -- rewrite add_neq_o in Hfi; auto.
       rewrite RE.add_neq_o; auto.
Qed.

Lemma nexts_unused_in_spec (r : resource) (t : t) : In r t -> RE.unused r (nexts t).
Proof.
  revert r; induction t using map_induction; 
  unfold RE.unused in *; intros r HIn.
  - exfalso; destruct HIn as [v HM]. 
    now apply (H r v).
  - unfold Samples.Add in *; rewrite H0 in *; clear H0.
    rewrite nexts_add_iff; unfold Cell.opt_unused in *. 
    destruct (Resource.eq_dec r x) as [| Hneq]; subst.
    -- rewrite RE.add_eq_o; auto; now red.
    -- apply add_in_iff in HIn as [| HIn]; subst; try lia.
       apply IHt1 in HIn.
       rewrite RE.add_neq_o; auto.
Qed.   

Lemma nexts_new_key (t : t) : (new_key t) = (RE.Ext.new_key (nexts t)).
Proof.
  induction t using map_induction.
  - rewrite Ext.new_key_Empty_spec; auto. 
    rewrite nexts_Empty; auto.
  - unfold Samples.Add in H0; rewrite H0 in *; clear H0.
    rewrite nexts_add_iff.
    destruct (Resource.leb_spec (new_key t1) (S x)) as [Hle | Hlt].
    -- rewrite Ext.new_key_add_ge_spec; auto.
       rewrite nexts_in_iff in H.
       rewrite RE.Ext.new_key_add_ge_spec; auto; lia.
    -- rewrite Ext.new_key_add_lt_spec; auto. 
       rewrite nexts_in_iff in H.
       rewrite RE.Ext.new_key_add_lt_spec; auto; lia.
Qed.

(** **** [puts] property *)

#[export] Instance puts_func_eq :
  Proper (RE.eq ==> Logic.eq ==> Logic.eq ==> eq ==> eq) puts_func.
Proof.
  intros V V' HeqV r' r Heqr v' v Heqv t t' Heqt; subst.
  unfold puts_func, puts_core_func; now rewrite Heqt, HeqV.
Qed.

#[export] Instance puts_func_eq' (V : 𝐕) :
  Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) (puts_func V).
Proof. intros r' r Heqr v' v Heqv t t' Heqt; subst; now rewrite Heqt. Qed.

Lemma puts_func_diamond (V : 𝐕) : Diamond Equal (puts_func V).
Proof.
  intros r r' v v' t t1 t2 Hneq Heq1 Heq2.
  rewrite <- Heq1, <- Heq2; unfold puts_func.
  now rewrite add_add_2. 
Qed.

Hint Resolve puts_func_eq puts_func_eq' puts_func_diamond eq_equiv: core.

Lemma puts_Empty (V : 𝐕) (t : t) : Empty t -> eq (puts V t) empty.
Proof. intro HEmp; unfold puts; rewrite fold_Empty; now auto. Qed.

Lemma puts_Add_spec (r : resource) (v : σ) (V : 𝐕) (t t' : t) : 
  ~ In r t -> Samples.Add r v t t' -> eq (puts V t') ((puts_func V) r v (puts V t)).
Proof. intros HnIn HA; unfold puts; now rewrite fold_Add; eauto. Qed.

Lemma puts_add_notin_spec (r : resource) (v : σ) (V : 𝐕) (t : t) : 
  ~ In r t -> eq (puts V (add r v t)) ((puts_func V) r v (puts V t)).
Proof. 
  intros HnIn; rewrite puts_Add_spec; eauto.
  - reflexivity.
  - now unfold Samples.Add.
Qed.

#[export] Instance puts_eq : Proper (RE.eq ==> eq ==> eq) puts.
Proof.
  intros V V' HeqV t t' Heqt; revert t' Heqt V V' HeqV.
  induction t using map_induction; intros t' Heqt V V' HeqV.
  - rewrite puts_Empty; auto.
    rewrite Heqt in H.
    now rewrite puts_Empty; auto.
  - rewrite puts_Add_spec; eauto.
    assert (Samples.Add x e t1 t') by (unfold Samples.Add; now rewrite <- Heqt).
    symmetry; rewrite puts_Add_spec; eauto.
    rewrite (IHt1 t1) with (V' := V); try reflexivity.
    -- unfold puts_func, puts_core_func.
       now rewrite HeqV.
    -- now symmetry.
Qed.

Lemma puts_Add_spec_1 (r : resource) (v : σ) (V : 𝐕) (t t' : t) : 
  ~ In r t -> Samples.Add r v t t' -> 
  Samples.Add r (puts_core_func r v V) (puts V t) (puts V t').
Proof.
  intros HIn HA; unfold Samples.Add in *.
  rewrite HA in *; rewrite puts_add_notin_spec; now auto. 
Qed.

Lemma puts_find_spec (r : resource) (v : σ) (V : 𝐕) (t : t) :
 find r t = Some v -> find r (puts V t) = Some (puts_core_func r v V).
Proof.
  revert r v; induction t using map_induction; intros r v Hfi.
  - exfalso; apply (H r v); now apply find_2.
  - unfold Samples.Add in H0; rewrite H0 in *; clear H0.
    rewrite puts_add_notin_spec; auto.
    destruct (Resource.eq_dec r x); subst.
    -- rewrite add_eq_o in Hfi; auto; inversion Hfi; subst; clear Hfi.
       unfold puts_func,puts_core_func.
       rewrite add_eq_o; auto. 
    -- unfold puts_func.
       rewrite add_neq_o in *; auto. 
Qed.

Lemma puts_Empty_iff (V : 𝐕) (t : t) : Empty t <-> Empty (puts V t).
Proof.
  split; intros HEmp.
  - apply puts_Empty with (V := V) in HEmp; rewrite HEmp.
    apply empty_1.
  - intros r v HM; apply find_1 in HM.
    apply puts_find_spec with (V := V) in HM.
    apply (HEmp r (puts_core_func r v V)).
    now apply find_2.
Qed.

Lemma puts_is_empty_iff (V : 𝐕) (t : t) : is_empty t = is_empty (puts V t).
Proof.
  destruct (is_empty t) eqn:H.
  - symmetry. apply is_empty_2 in H. apply is_empty_1. 
    now apply puts_Empty_iff.
  - destruct (is_empty (puts V t)) eqn:H1; auto.
    apply is_empty_2 in H1.
    rewrite <- puts_Empty_iff in H1.
    apply is_empty_1 in H1; rewrite H in *.
    inversion H1.
Qed.

Lemma puts_In_iff r (V : 𝐕) (t : t) : In r t <-> In r (puts V t).
Proof.
  revert r V; induction t using map_induction; intros r V.
  - split; intro HIn.
    -- exfalso; destruct HIn as [v HMap]. 
       now apply (H r v).
    -- exfalso; destruct HIn as [v HMap].
       rewrite puts_Empty_iff with (V := V) in H.
       now apply (H r v).
  - split; intro HIn;
    unfold Samples.Add in *; rewrite H0 in *; clear H0.
    -- rewrite puts_add_notin_spec; auto; unfold puts_func.
       rewrite add_in_iff in *.
       destruct HIn as [| HIn]; subst; auto.
       right; now rewrite <- IHt1.
    -- rewrite puts_add_notin_spec in HIn; auto.
       unfold puts_func in HIn. 
       rewrite add_in_iff in *.
       destruct HIn as [| HIn]; subst; auto.
       right; now rewrite (IHt1 r V).
Qed. 

Lemma puts_max_spec (V : 𝐕) (t : t) : max_key t = max_key (puts V t).
Proof.
  revert V; induction t using map_induction; intro V.
  - rewrite max_key_Empty_spec; auto.
    rewrite puts_Empty; auto.
  - unfold Samples.Add in *; rewrite H0 in *; clear H0.
    rewrite puts_add_notin_spec; auto; unfold puts_func.
    apply max_key_add_spec with (v := e) in H as HI; auto.
    destruct HI as [[Heq Hle] | [Heq Hgt]]; subst.
    -- rewrite max_key_add_ge_spec; auto.
       rewrite (IHt1 V) in Hle.
       rewrite max_key_add_ge_spec; auto.
       now rewrite <- puts_In_iff.
    -- rewrite max_key_add_lt_spec; auto.
       rewrite (IHt1 V) in Hgt.
       rewrite max_key_add_lt_spec; auto.
       now rewrite <- puts_In_iff.
Qed.

Lemma puts_new_spec (V : 𝐕) (t : t) : new_key t = new_key (puts V t).
Proof.
  unfold new_key; destruct (is_empty t) eqn:Hempt.
  - rewrite puts_is_empty_iff with (V := V) in Hempt.
    rewrite Hempt; reflexivity.
  - rewrite puts_is_empty_iff with (V := V) in Hempt.
    rewrite Hempt; f_equal; apply puts_max_spec.
Qed.

(** **** [halts] property *)

#[export] Instance halts_eq : Proper (Logic.eq ==> eq ==> iff) halts.
Proof.
  intros k' k Heqk t t' Heqt; subst; unfold halts; now rewrite Heqt.
Qed.

Lemma halts_add_spec (k : lvl) (x : resource) (v : σ) (t : t) :
  (Sample.halts k v) /\ halts k t -> halts k (add x v t).
Proof. intros [Hltv Hltm]; apply For_all_add_spec; auto. Qed. 

Lemma halts_add_spec_1 (k : lvl) (x : resource) (v : σ) (t : t) :
  ~ In x t -> halts k (add x v t) -> (Sample.halts k v) /\ halts k t.
Proof. 
  intros HIn Hlt. 
  apply For_all_add_notin_spec in Hlt as [Hlt Hlt']; auto.
Qed.

Lemma halts_weakening (m n :lvl) (t : t) : 
  m <= n -> halts m t -> halts n (shift m (n - m) t).
Proof.
  induction t using map_induction; intros Hle Hlt.
  - rewrite shift_Empty_spec; auto.
    now apply For_all_Empty_spec.
  - unfold Samples.Add in *; rewrite H0 in *; clear H0.
    rewrite shift_add_spec.
    apply For_all_add_notin_spec in Hlt as [Hlt Hlt']; auto.
    apply For_all_add_spec; split.
    -- now apply Sp.halts_weakening.
    -- now apply IHt1.
Qed.

Lemma halts_nexts (k : lvl) (t : t) : halts k t -> RE.halts k (nexts t).
Proof.
  induction t using map_induction; intros Hlt.
  - rewrite nexts_Empty_eq in H.
    now apply RE.For_all_Empty_spec.
  - unfold Samples.Add in *; rewrite H0 in *; clear H0.
    rewrite nexts_add_notin_spec; auto.
    apply For_all_add_notin_spec in Hlt as [Hlt Hlt']; auto.
    apply RE.For_all_add_spec; split.
    -- simpl; now apply Sp.halts_next.
    -- now apply IHt1.
Qed.

Lemma halts_puts (k : lvl) (V : 𝐕) (t : t) :
  halts k t -> RE.halts k V -> halts k (puts V t).
Proof.
  induction t using map_induction; intros Hlt HlV.
  - rewrite (puts_Empty_iff V) in H.
    now apply For_all_Empty_spec.
  - unfold Samples.Add in *; rewrite H0 in *; clear H0.
    rewrite puts_add_notin_spec; auto.
    apply For_all_add_notin_spec in Hlt as [Hlt Hlt']; auto.
    apply For_all_add_spec; split.
    -- unfold puts_core_func; destruct (V⌊x⌋) eqn:Hfi.
       + destruct r.
         ++ now apply Sp.halts_put_None.
         ++ apply Sp.halts_put_Some; auto.
            apply HlV in Hfi; now simpl in *.
       + now apply Sp.halts_put_None.
    -- now apply IHt1.
Qed.

(** **** Morphism *)

#[export] Instance in_eq : Proper (Logic.eq ==> eq ==> iff) In.
Proof. intros r' r Heqr t t' Heqt; subst; now rewrite Heqt. Qed.

#[export] Instance Add_eq : 
  Proper (Resource.eq ==> Logic.eq ==> eq ==> eq ==> iff) (@OP.P.Add Sample.t).
Proof.
  intros r' r Heqr v' v Heqv t t' Heqt t1 t1' Heqt1; subst.
  unfold Samples.Add; now rewrite Heqr, Heqt, Heqt1.
Qed.

End Samples.

(** ---- *)

(** ** Notation - I/O Sample *)

Module SamplesNotations.

(** *** Scope *)
Declare Scope samples_scope.
Delimit Scope samples_scope with sps.

(** *** Notation *)
Definition 𝐒 := Samples.t.

Notation "∅" := Samples.Raw.empty (at level 0, no associativity) : samples_scope. 
Notation "t '⁺'" := (Samples.Ext.new_key t) (at level 16) : samples_scope.
Notation "r '∉' t" := (~ (Samples.Raw.In r t)) 
                       (at level 75, no associativity) : samples_scope. 
Notation "'isEmpty(' t ')'" := (Samples.Empty t) (at level 20, no associativity) : samples_scope. 
Notation "'Add'" := (Samples.Add) (at level 20, no associativity) : samples_scope. 
Notation "t '⌊' x '⌋'"  := (Samples.Raw.find x t) (at level 15, x constr) : samples_scope.
Notation "'max(' t ')'"  := (Samples.Ext.max_key t) (at level 15) : samples_scope.
Notation "⌈ x ⤆ v '⌉' t"  := (Samples.Raw.add x v t) 
                              (at level 15, x constr, v constr) : samples_scope.
Notation "'[⧐' lb '–' k ']' t" := (Samples.shift lb k t) 
                                   (at level 65, right associativity) : samples_scope.

Infix "⊆" := Samples.Submap (at level 60, no associativity) : samples_scope. 
Infix "∈" := Samples.Raw.In (at level 60, no associativity) : samples_scope. 
Infix "=" := Samples.eq : samples_scope.
Infix "⊩" := Samples.valid (at level 20, no associativity) : samples_scope.

(** *** Morphism *)

Import Samples.

#[export] Instance eq_equiv_samples : Equivalence Samples.eq := _.
#[export] Instance max_samples : Proper (eq ==> Logic.eq) (Ext.max_key) := Ext.max_key_eq.
#[export] Instance new_samples : Proper (eq ==> Logic.eq) (Ext.new_key) := Ext.new_key_eq.
#[export] Instance in_samples : Proper (Logic.eq ==> eq ==> iff) (Raw.In) := _.
#[export] Instance find_samples : Proper (Logic.eq ==> eq ==> Logic.eq) (Raw.find) := _.
#[export] Instance Empty_samples : Proper (eq ==> iff) (OP.P.Empty) := _.
#[export] Instance Add_samples : 
  Proper (Resource.eq ==> Logic.eq ==> eq ==> eq ==> iff) (@OP.P.Add Sample.t) := _.
#[export] Instance add_rsamples : 
  Proper (Resource.eq ==> Logic.eq ==> eq ==> eq) (@Raw.add Sample.t) := _.
#[export] Instance Submap_samples : Proper (eq ==> eq ==> iff) Submap := _.
#[export] Instance Submap_samples_po : PreOrder Samples.Submap := Submap_po.
#[export] Instance halts_samples : Proper (Logic.eq ==> eq ==> iff) halts := _.

End SamplesNotations.