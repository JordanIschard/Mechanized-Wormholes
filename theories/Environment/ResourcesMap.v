From Coq Require Import Lia.
From Mecha Require Import Resource Resources Resource Typ REnvironment Cell Term RContext.
From DeBrLevel Require Import LevelInterface PairLevel MapLevelLVLD.
From MMaps Require Import MMaps.
Import ResourceNotations ResourceNotations CellNotations REnvironmentNotations TypNotations
       ResourcesNotations SetNotations RContextNotations TermNotations.

Module ResourcesMap <: IsLvlET.

Include MakeLvlMapLVLD Resource.
Import Raw Ext.

Module RE := REnvironment.

Open Scope renvironment_scope.

(** *** Definition *)

Definition find_data_func (c r r': resource) (v: option resource) :=
  match v with
    | Some _ => v
    | None => if (Resource.eq_dec c r') then Some r else None
  end. 

Definition find_data (r: resource) (m: t) : option resource :=
  fold (find_data_func r) m None.

(** **** Initialize an environment
*)
Definition init_writers_func (r _: resource) (V: 𝐕) : 𝐕 := ⌈r ⤆ (⩽ unit … ⩾)⌉ V.

Definition init_writers (rm: t) (V: 𝐕) := fold (init_writers_func) rm V.

(** *** Properties *)

(** **** [extend] properties *)
 
Lemma extend_Empty_left (rm rm' : t) :
  Empty rm -> eq (extend rm rm') rm'.
Proof.
  intro HEmp; unfold extend.
  apply Empty_eq in HEmp.
  rewrite fold_init; eauto.
  - apply fold_identity.
  - repeat red; intros; subst; now rewrite H1.
Qed.

Lemma extend_Empty_right (rm rm' : t) :
  Empty rm' -> eq (extend rm rm') rm.
Proof. intro HEmp; unfold extend; now rewrite fold_Empty; eauto. Qed.

Lemma extend_add_right (r v: resource) (rm rm' : t) :
  ~ (In r rm') -> eq (extend rm (add r v rm')) (add r v (extend rm rm')).
Proof.
  intro HnIn; unfold extend; rewrite fold_Add; eauto.
  - reflexivity.
  - intros k' k Heqk d' d Heqd c c' Heqc; subst; now rewrite Heqc.
  - apply diamond_add.
  - unfold Add; reflexivity.
Qed.

Lemma Wf_extend (k : lvl) (rm rm' : t) :
  Wf k rm -> Wf k rm' -> Wf k (extend rm rm').
Proof.
  revert rm; induction rm' using map_induction; intros rm Hvrs Hvrs'.
  - rewrite extend_Empty_right; auto.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    rewrite extend_add_right; auto.
    apply Wf_add_notin in Hvrs' as [Hvx [Hve Hvrs'1]]; auto.
    apply Wf_add; auto.
Qed.

Lemma extend_new_key (rm rm': t) :
  new_key (extend rm rm') = max (new_key rm) (new_key rm').
Proof.
  revert rm.
  induction rm' using map_induction; intro rm.
  - rewrite extend_Empty_right; auto.
    rewrite (new_key_Empty rm'); auto; lia.
  - unfold Add in H0; rewrite H0; clear H0.
    rewrite extend_add_right; auto.
    do 2 rewrite new_key_add_max.
    rewrite IHrm'1; lia.
Qed.

(** **** [new_key] properties *)

Lemma new_key_Wf (k: lvl) (rm: t) : Wf k rm -> new_key rm <= k.
Proof.
  induction rm using map_induction; intro Hwf.
  - rewrite new_key_Empty; auto; lia.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    apply Wf_add_notin in Hwf as [Hwfx [_ Hwf]]; auto.
    apply IHrm1 in Hwf.
    unfold Resource.Wf in Hwfx.
    rewrite new_key_add_max; lia.
Qed.

(** **** [init_writers] properties *)

#[export] Instance init_writers_func_eq : 
  Proper (Logic.eq ==> Logic.eq ==> RE.eq ==> RE.eq) init_writers_func.
Proof. 
  unfold init_writers_func; intros k' k Heqk v' v Heqv V V' HeqV. 
  subst; now rewrite HeqV. 
Qed.

Lemma init_writers_diamond : Diamond RE.eq init_writers_func.
Proof.
  intros k k' v v' rm rm' rm1' Hneq Heq Heq'.
  unfold init_writers_func in *.
  rewrite <- Heq, <- Heq'.
  rewrite RE.add_add_2; auto; reflexivity.
Qed.

#[export] Instance renvironment_equiv_eq : Equivalence RE.eq := RE.eq_equiv.

#[local] Hint Resolve init_writers_func_eq renvironment_equiv_eq 
                      init_writers_diamond : core.

Lemma init_writers_Empty (rm: t) (V: 𝐕) : Empty rm -> ((init_writers rm V) = V)%re.
Proof.
  intro Hemp; unfold init_writers.
  rewrite fold_Empty; now auto.
Qed.

Lemma init_writers_add (r v: resource) (rm: t) (V: 𝐕) :
  ~(In r rm) ->
  ((init_writers (add r v rm) V) = (⌈r ⤆ (⩽ unit … ⩾)⌉ (init_writers rm V)))%re. 
Proof.
  unfold init_writers; intro HnIn.
  rewrite fold_add; auto.
  now unfold init_writers_func at 1.
Qed.

#[export] Instance init_writers_eq : Proper (eq ==> RE.eq ==> RE.eq) init_writers.
Proof.
  intros rm rm' Heqrm V V' HeqV; unfold init_writers.
  rewrite fold_init; eauto.
  clear V HeqV; revert rm' Heqrm.
  induction rm using map_induction; intros rm' Heq.
  - do 2 (rewrite init_writers_Empty; auto).
    -- reflexivity.
    -- now rewrite <- Heq.
  - rewrite fold_Add; eauto.
    rewrite fold_Add with (m1 := rm1) (m2 := rm'); eauto.
    -- reflexivity.
    -- now unfold Add in *; rewrite <- Heq.
Qed.

Lemma init_writers_in_unused (rm: t) (V: 𝐕) (r: resource) :
  (In r rm) -> RE.unused r (init_writers rm V).
Proof.
  revert r; induction rm using map_induction; intro r.
  - intros [v HM].
    exfalso; apply (H r v HM).
  - intro HIn. 
    unfold Add in H0; rewrite H0 in *; clear H0. 
    rewrite init_writers_add; auto.
    apply add_in_iff in HIn as [| HIn]; subst. 
    -- apply RE.unused_add_eq; now red.
    -- assert (r <> x) by (intro; subst; contradiction).
       apply RE.unused_add_neq; auto. 
Qed.

Lemma init_writers_find (rm: t) (V: 𝐕) (r: resource) (v: 𝑣) :
  (init_writers rm V)⌊r⌋ = Some v -> (In r rm) \/ V⌊r⌋ = Some v.
Proof.
  revert r v; induction rm using map_induction; intros r v Hfi.
  - rewrite init_writers_Empty in Hfi; auto.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    rewrite init_writers_add in Hfi; auto.
    destruct (Resource.eq_dec x r) as [Heq | Hneq]; subst.
    -- left; rewrite add_in_iff; auto.
    -- rewrite RE.add_neq_o in Hfi; auto.
       apply IHrm1 in Hfi as [HIn | Hfi]; auto.
       left; rewrite add_in_iff; auto.
Qed.

Lemma init_writers_find_inp (rm: t) (V: 𝐕) (r: resource) (v: 𝑣) :
  (forall r, V⌊r⌋ = Some v -> exists v', Logic.eq v (Cell.inp v')) ->
  (init_writers rm V)⌊r⌋ = Some v -> exists v', Logic.eq v (Cell.inp v'). 
Proof.
  revert r v; induction rm using map_induction; intros r v Ht Hfi.
  - rewrite init_writers_Empty in Hfi; auto.
    now apply (Ht r).
  - unfold Add in H0; rewrite H0 in *; clear H0.
    rewrite init_writers_add in Hfi; auto.
    destruct (Resource.eq_dec x r) as [Heq | Hneq]; subst.
    -- rewrite RE.add_eq_o in Hfi; auto.
       inversion Hfi; subst; now exists Term.tm_unit.
    -- rewrite RE.add_neq_o in Hfi; auto.
       now apply (IHrm1 r).
Qed.

Lemma init_writers_in_iff (rm: t) (V: 𝐕) (r: resource) :
  r ∈ (init_writers rm V) <-> (In r rm) \/ r ∈ V.
Proof.
  revert r; induction rm using map_induction; intro r; split.
  - intro HIn. rewrite init_writers_Empty in HIn; auto.
  - intros [[v HM] | HIn].
    -- exfalso.
       now apply (H r v).
    -- now rewrite init_writers_Empty.
  - intro HIn; unfold Add in H0; rewrite H0 in *; clear H0. 
    rewrite init_writers_add in HIn; auto.
    apply RE.add_in_iff in HIn as [Heq | HIn]; subst.
    -- left; rewrite add_in_iff; auto.
    -- apply IHrm1 in HIn as [HIn | HIn]; auto.
       left; rewrite add_in_iff; auto.
  - intros [HIn | HIn]; unfold Add in H0; rewrite H0 in *; clear H0.
    -- rewrite init_writers_add; auto.
       rewrite RE.add_in_iff.
       apply add_in_iff in HIn as [Heq | HIn]; auto.
       right; rewrite IHrm1; now left.
    -- rewrite init_writers_add; auto.
       rewrite RE.add_in_iff; right.
       rewrite IHrm1; now right. 
Qed. 

Lemma init_writers_in (rm: t) (V: 𝐕) (r: resource) :
  (In r rm) -> (init_writers rm V)⌊r⌋ = Some (Cell.inp <[unit]>).
Proof.
  revert r; induction rm using map_induction; intros r HIn.
  - destruct HIn as [v HM]. 
    exfalso; now apply (H r v).
  - unfold Add in H0; rewrite H0 in *; clear H0.
    rewrite init_writers_add; auto.
    destruct (Resource.eq_dec r x) as [| Hneq]; subst.
    -- now rewrite RE.add_eq_o.
    -- rewrite RE.add_neq_o; auto.
       apply add_in_iff in HIn as [| HIn]; subst; auto.
       contradiction.
Qed.

Lemma init_writers_unused (r: resource) (rm: t) (V: 𝐕) :
  RE.unused r V -> RE.unused r (init_writers rm V).
Proof.
  revert r; induction rm using map_induction; intro r.
  - rewrite init_writers_Empty; auto.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    rewrite init_writers_add; auto.
    destruct (Resource.eq_dec r x) as [| Hneq]; subst; intro Hunsd.
    -- apply RE.unused_add_eq; now red.
    -- apply RE.unused_add_neq; auto.
Qed.

Lemma init_writers_add_remove (r v: resource) (rm: t) (V: 𝐕) :
  ((init_writers (add r v rm) V) = (init_writers (add r v rm) (RE.Raw.remove r V)))%re.
Proof.
  revert r V; induction rm using map_induction; intros r V.
  - assert (HnIn: ~ In r rm).
    { intros [v' HM]; now apply (H r v'). } 
    do 2 (rewrite init_writers_add; auto).
    do 2 (rewrite init_writers_Empty; auto).
    induction V using RE.map_induction.
    -- assert (HnIn': r ∉ V).
       { intros [v' HM]; now apply (H0 r v'). } 
       rewrite <- RE.remove_id in HnIn'.
       now rewrite HnIn'.
    -- unfold RE.Add in H1; rewrite H1 in *; clear H1.
       destruct (Resource.eq_dec r x) as [| Hneq]; subst.
        + rewrite RE.add_shadow.
          rewrite RE.add_remove_1.
          now rewrite RE.add_shadow.
        + rewrite RE.add_add_2; auto.
          rewrite RE.remove_add_2; auto.
          symmetry.
          rewrite RE.add_add_2; auto.
          now rewrite IHV1.
  - unfold Add in H0; rewrite H0 in *; clear H0. 
    destruct (Resource.eq_dec r x) as [| Hneq]; subst.
    -- rewrite add_shadow.
       now rewrite IHrm1.
    -- rewrite add_add_2; auto.
       do 2 rewrite (init_writers_add x) 
       by (rewrite add_in_iff; intros [|]; auto).
       now rewrite <- IHrm1.
Qed.

Lemma init_writers_new_key (V: 𝐕) (rm: t) : 
  (init_writers rm V)⁺ = max (new_key rm) (V⁺).
Proof.
  revert V.
  induction rm using map_induction; intro V.
  - rewrite new_key_Empty; auto; simpl.
    rewrite init_writers_Empty; auto.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    rewrite init_writers_add_remove.
    rewrite init_writers_add; auto.
    rewrite new_key_add_max; auto.
    rewrite RE.Ext.new_key_add_max.
    rewrite IHrm1.
    destruct (RE.In_dec V x).
    + apply RE.new_key_in_remove_1 in i as HI.
      rewrite HI; lia.
    + apply RE.remove_id in n.
      rewrite n; lia.
Qed.

Lemma init_writers_Wf (k : lvl) (V: 𝐕) (t : t) :
  (Wf k t) /\ k ⊩ V -> k ⊩ (init_writers t V).
Proof.
  revert k V.
  induction t using map_induction; intros k V  [Hvt HvV].
  - rewrite init_writers_Empty; auto.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    apply Wf_add_notin in Hvt as [Hvx [Hve Hvt1]]; auto.
    rewrite init_writers_add_remove.
    rewrite init_writers_add; auto.
    apply RE.Wf_add_notin.
    -- rewrite init_writers_in_iff; intros [|]; auto.
       apply RE.remove_in_iff in H0 as []; auto.
    -- do 2 (split;auto).
       + constructor.
       + apply IHt1; split; auto.
         now apply RE.Wf_remove.
Qed.

(** **** [halts] properties *)

Lemma halts_init_writers (k : lvl) (rm: t) (V: 𝐕) :
  RE.halts k V -> RE.halts k (init_writers rm V).
Proof.
  induction rm using map_induction; intro Hlt.
  - now rewrite init_writers_Empty.
  - unfold Add in *; rewrite H0 in *; clear H0.
    rewrite init_writers_add; auto.
    apply RE.halts_add; split; auto.
    red; exists <[unit]>; split.
    -- apply Evaluation_Transition.multi_unit.
    -- now constructor.
Qed.

(** *** Morphisms *)

#[export] Instance resourcesmap_in_iff : Proper (Logic.eq ==> eq ==> iff) In.
Proof. intros k' k Heqk rm rm' Heqrs; subst; now rewrite Heqrs. Qed.

#[export] Instance resourcesmap_Add_iff : 
  Proper (Resource.eq ==> Resource.eq ==> eq ==> eq ==> iff) (@Add Resource.t).
Proof.
  intros k' k Heqk d d' Heqd rm rm' Heqrs rs1 rs1' Heqrs1; unfold Add.
  now rewrite Heqk, Heqd, Heqrs, Heqrs1. 
Qed.

End ResourcesMap.

(** ---- *)

(** ** Notation - Virtual Resource Environment - Reader *)

Module ResourcesMapNotations.

(** *** Scope *)
Declare Scope rmap_scope.
Delimit Scope rmap_scope with rm.

(** *** Notations *)

Notation "t '⁺'" := (ResourcesMap.Ext.new_key t) (at level 16) : rmap_scope.
Notation "∅" := ResourcesMap.Raw.empty (at level 0, no associativity) : rmap_scope. 
Notation "r '∉' t" := (~ (ResourcesMap.Raw.In r t)) (at level 75, no associativity) : rmap_scope. 
Notation "'isEmpty(' t ')'" := (ResourcesMap.Empty t) (at level 20, no associativity) : rmap_scope. 
Notation "t '⌊' x '⌋'"  := (ResourcesMap.Raw.find x t) (at level 15, x constr) : rmap_scope.
Notation "'max(' t ')'"  := (ResourcesMap.Ext.max_key t) (at level 15) : rmap_scope.
Notation "⌈ x ⤆ v '⌉' t" := (ResourcesMap.Raw.add x v t) 
                             (at level 15, x constr, v constr) : rmap_scope.
Notation "'[⧐' lb '–' k ']' t" := (ResourcesMap.shift lb k t) 
                                   (at level 65, right associativity) : rmap_scope.

Infix "⊆" := ResourcesMap.Submap (at level 60, no associativity) : rmap_scope. 
Infix "∈" := ResourcesMap.Raw.In (at level 60, no associativity) : rmap_scope. 
Infix "=" := ResourcesMap.eq : rmap_scope.
Infix "∪" := ResourcesMap.extend : rmap_scope.
Infix "⊩" := ResourcesMap.Wf (at level 20, no associativity) : rmap_scope.

(** *** Morphisms *)

Import ResourcesMap.

#[export] Instance resourcesmap_equiv_eq : Equivalence ResourcesMap.eq := _.

#[export] Instance resourcesmap_max_eq : Proper (eq ==> Logic.eq) (Ext.max_key) := Ext.max_key_eq.

#[export] Instance resourcesmap_new_eq : Proper (eq ==> Logic.eq) (Ext.new_key) := Ext.new_key_eq.

#[export] Instance resourcesmap_in_iff : 
  Proper (Logic.eq ==> ResourcesMap.eq ==> iff) (ResourcesMap.Raw.In) := _.

#[export] Instance resourcesmap_find_eq : Proper (Logic.eq ==> eq ==> Logic.eq) (Raw.find) := _.

#[export] Instance resourcesmap_Empty_iff : 
  Proper (ResourcesMap.eq ==> iff) (ResourcesMap.Empty) := _.

#[export] Instance resourcesmap_Add_iff : 
  Proper (Resource.eq ==> Resource.eq ==> eq ==> eq ==> iff) (@ResourcesMap.Add Resource.t) := _.

#[export] Instance resourcesmap_add_eq : 
  Proper (Resource.eq ==> Resource.eq ==> eq ==> eq) (@Raw.add Resource.t) := _.

#[export] Instance resourcesmap_Submap_iff : Proper (eq ==> eq ==> iff) Submap := _.

#[export] Instance resourcesmap_Submap_po : PreOrder ResourcesMap.Submap := Submap_po.

#[export] Instance resourcesmap_Wf_iff : 
  Proper (Logic.eq ==> ResourcesMap.eq ==> iff) ResourcesMap.Wf := _.

#[export] Instance resourcesmap_shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.

End ResourcesMapNotations.