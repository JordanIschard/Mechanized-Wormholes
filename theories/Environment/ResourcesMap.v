From Coq Require Import Lia FinFun.
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

Fixpoint add_list x s :=
  match s with
  | nil => x :: nil
  | y :: l =>
      match Resource.compare x y with
      | Lt => x :: s
      | Eq => s
      | Gt => y :: add_list x l
      end
  end.

Definition find_data_filter (r wW rW: resource) : bool :=
  if (Resource.eq_dec r rW) then true else false. 

Definition find_data (m: t) (r: resource) : option resource :=
  hd_error (fold (fun k _ acc => add_list k acc)%s (filter (find_data_filter r) m) nil).

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

(** **** [find_data_func] properties *)

#[export] Instance find_data_filter_eq (r: resource) :
  Proper (Logic.eq ==> Logic.eq ==> eq ==> eq)
   (fun (k : key) (e : resource) (m : ResourcesMap.Raw.t resource) => 
                              if find_data_filter r k e then add k e m else m).
Proof.
  intros k' k Heqk v' v Heqv rm1 rm1' Heq; subst.
  unfold find_data_filter.
  destruct (Resource.eq_dec r v); auto.
  now rewrite Heq.
Qed.

#[export] Instance df_feq (r: resource):
  Proper (Logic.eq ==> Logic.eq ==> Logic.eq) (find_data_filter r) := _.

Lemma find_data_filter_diamond (r: resource) :
  Diamond eq (fun (k : key) (e : resource) (m : ResourcesMap.Raw.t resource) => 
                                      if find_data_filter r k e then add k e m else m).
Proof.
  intros k k' v v' rm1 rm2 rm2' Hneq Heq Heq'.
  unfold find_data_filter in *.
  destruct (Resource.eq_dec r v); 
  destruct (Resource.eq_dec r v'); subst;
  rewrite <- Heq, <- Heq'; (try now auto).
  now rewrite add_add_2; auto.
Qed.


Hint Resolve  df_feq find_data_filter_eq find_data_filter_diamond : core.

Lemma find_data_filter_Empty (r: resource) (rm: t):
 Empty rm -> eq (filter (find_data_filter r) rm) empty.
Proof.
  intro HEmp.
  rewrite filter_alt.
  now rewrite fold_Empty; auto.
Qed.

Lemma find_data_filter_Empty' (r: resource) (rm: t):
 Empty rm -> Empty (filter (find_data_filter r) rm).
Proof.
  intro HEmp.
  rewrite find_data_filter_Empty; auto.
  apply empty_1.
Qed.

Lemma find_data_filter_Add_eq (r r': resource) (rm rm': t) :
  ~ In r' rm -> Add r' r rm rm' ->
  eq (filter (find_data_filter r) rm') (add r' r (filter (find_data_filter r) rm)).
Proof.
  intros HnIn Hadd.
  rewrite filter_alt at 1.
  rewrite fold_Add; eauto.
  unfold find_data_filter at 1.
  destruct (Resource.eq_dec r r); try contradiction.
  now rewrite <- filter_alt.
Qed.

Lemma find_data_filter_Add_eq_inj (r r': resource) (rm rm': t) :
  ~ In r' rm -> Add r' r rm rm' -> (Injective (fun x => find x rm')) ->
  eq (filter (find_data_filter r) rm') (add r' r empty).
Proof.
  intros HnIn Hadd Hinj.
  rewrite find_data_filter_Add_eq; eauto.
  intro y; destruct (Resource.eq_dec y r') as [| Hneq]; subst.
  - do 2 (rewrite add_eq_o; auto).
  - do 2 (rewrite add_neq_o; auto).
    rewrite filter_find; auto.
    unfold Utils.option_bind.
    destruct (@find resource y rm) eqn:Hfi.
    -- unfold find_data_filter.
       destruct (Resource.eq_dec r r0) as [| Hneq']; subst.
       + apply find_2 in Hfi as Hfi'.
         apply add_2 with (x := r') (e' := r0) in Hfi'; auto.
         apply find_1 in Hfi'.
         unfold Injective in *.
         assert (Hfi'': find r' (add r' r0 rm) = Some r0).
         ++ now rewrite add_eq_o.
         ++ rewrite <- Hfi' in Hfi''.
            specialize (Hinj r' y).
            unfold Add in *; rewrite Hadd in *; clear Hadd.
            apply Hinj in Hfi''.
            subst; contradiction.
       + symmetry.
         apply empty_o.
    -- symmetry.
       apply empty_o.
Qed.

Lemma find_data_filter_Add_eq_wkinj (r r': resource) (rm rm': t) :
  ~ In r' rm -> Add r' r rm rm' -> 
  (forall r r' v, find r rm' = Some v /\ find r' rm' = Some v -> r = r') ->
  eq (filter (find_data_filter r) rm') (add r' r empty).
Proof.
  intros HnIn Hadd Hinj.
  rewrite find_data_filter_Add_eq; eauto.
  intro y; destruct (Resource.eq_dec y r') as [| Hneq]; subst.
  - do 2 (rewrite add_eq_o; auto).
  - do 2 (rewrite add_neq_o; auto).
    rewrite filter_find; auto.
    unfold Utils.option_bind.
    destruct (@find resource y rm) eqn:Hfi.
    -- unfold find_data_filter.
       destruct (Resource.eq_dec r r0) as [| Hneq']; subst.
       + apply find_2 in Hfi as Hfi'.
         apply add_2 with (x := r') (e' := r0) in Hfi'; auto.
         apply find_1 in Hfi'.
         assert (Hfi'': find r' (add r' r0 rm) = Some r0).
         ++ now rewrite add_eq_o.
         ++ destruct (Hinj r' y r0); try contradiction.
            unfold Add in *; rewrite Hadd in *; clear Hadd.
            split; auto.
       + symmetry.
         apply empty_o.
    -- symmetry.
       apply empty_o.
Qed.

Lemma find_data_filter_Add_neq (r r' v: resource) (rm rm': t) :
  ~ In r' rm -> Add r' v rm rm' -> r <> v ->
  eq (filter (find_data_filter r) rm') (filter (find_data_filter r) rm).
Proof.
  intros HnIn Hadd Hneq.
  rewrite filter_alt at 1.
  rewrite fold_Add; eauto.
  unfold find_data_filter at 1.
  destruct (Resource.eq_dec r v); try contradiction.
  now rewrite <- filter_alt.
Qed.

#[export] Instance find_data_filter_eq' (r: resource) : 
  Proper (eq ==> eq) (filter (find_data_filter r)).
Proof.
  intros rm.
  induction rm using map_induction; intros rm' Heq.
  - do 2 (rewrite find_data_filter_Empty; auto).
    -- reflexivity.
    -- now rewrite <- Heq.
  - destruct (Resource.eq_dec r e) as [| Hneq]; subst.
    -- rewrite find_data_filter_Add_eq; eauto.
       symmetry.
       rewrite find_data_filter_Add_eq; eauto.
       + reflexivity.
       + now unfold Add in *; rewrite <- Heq.
    -- rewrite find_data_filter_Add_neq; eauto.
       symmetry.
       rewrite find_data_filter_Add_neq; eauto.
       + reflexivity.
       + now unfold Add in *; rewrite <- Heq.
Qed.


Hint Resolve find_data_filter_eq' : core.

(** **** [find_data] properties *)

#[export] Instance add_r_eq :
  Proper (Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq) 
    (fun (k : key) (_ : resource) (acc : list nat) => add_list k acc) := _.


Lemma add_r_diamond : 
  Diamond Logic.eq (fun (k : key) (_ : resource) (acc : list nat) => add_list k acc).
Proof.
  intros k k' _ _ xs ys zs Hneq Heq Heq'.
  rewrite <- Heq, <- Heq'.
  clear ys zs Heq Heq'.
  revert k k' Hneq.
  induction xs; intros k k' Hneq; simpl.
  - destruct (Resource.compare_spec k k').
    -- rewrite H.
       destruct (Resource.compare_spec k' k); try lia.
    -- now destruct (Resource.compare_spec k' k); try lia.
    -- now destruct (Resource.compare_spec k' k); try lia.
  - destruct (Resource.compare_spec k' a).
    -- destruct (Resource.compare_spec k a).
       + subst; lia.
       + simpl. 
         destruct (Resource.compare_spec k a); try lia.
         destruct (Resource.compare_spec k' k); try lia.
         now destruct (Resource.compare_spec k' a); try lia.
       + simpl.
         destruct (Resource.compare_spec k a); try lia.
         destruct (Resource.compare_spec k' a); try lia.
         apply IHxs in Hneq as H'.
         destruct xs; simpl in *; auto.
    -- destruct (Resource.compare_spec k a); simpl.
       + destruct (Resource.compare_spec k k'); try lia.
         destruct (Resource.compare_spec k a); try lia.
         now destruct (Resource.compare_spec k' a); try lia.
       + destruct (Resource.compare_spec k k'); try lia.
         ++ destruct (Resource.compare_spec k' k); try lia.
            now destruct (Resource.compare_spec k' a); try lia.
         ++ destruct (Resource.compare_spec k' k); try lia.
            now destruct (Resource.compare_spec k a); try lia.
       + destruct (Resource.compare_spec k' a); try lia.
         destruct (Resource.compare_spec k a); try lia.
         now destruct (Resource.compare_spec k k'); try lia.
    -- simpl.
       destruct (Resource.compare_spec k a); try lia; simpl.
       + now destruct (Resource.compare_spec k' a); try lia.
       + destruct (Resource.compare_spec k' a); try lia.
         now destruct (Resource.compare_spec k' k); try lia.
       + destruct (Resource.compare_spec k' a); try lia.
         apply IHxs in Hneq.
         now rewrite Hneq.
Qed.

Hint Resolve add_r_diamond add_r_eq: core.

Lemma find_data_Empty_some (r r': resource) (rm: t) :
  Empty rm -> ~ find_data rm r = Some r.
Proof.
  intros HEmp Hfd.
  unfold find_data in *.
  rewrite fold_Empty in Hfd; auto.
  - inversion Hfd.
  - now apply find_data_filter_Empty'.
Qed.

Lemma find_data_Empty_none (r: resource) (rm: t) :
  Empty rm -> find_data rm r = None.
Proof.
  intros HEmp.
  unfold find_data.
  rewrite fold_Empty; auto.
  now apply find_data_filter_Empty'.
Qed.

Lemma find_data_Add_eq (r r': resource) (rm rm': t) :
  ~ In r' rm -> Add r' r rm rm' -> (Injective (fun x => find x rm')) -> find_data rm' r = Some r'.
Proof.
  intros HnIn Hadd Hinj; unfold find_data.
  rewrite fold_Add with (k := r') (e := r) (m1 := empty); auto.
  - intros [v HM].
    now apply empty_1 in HM.
  - unfold Add.
    apply find_data_filter_Add_eq_inj with (rm := rm); auto.
Qed.

Lemma find_data_Add_wkeq (r r': resource) (rm rm': t) :
  ~ In r' rm -> Add r' r rm rm' -> 
  (forall r r' v, find r rm' = Some v /\ find r' rm' = Some v -> r = r') ->
  find_data rm' r = Some r'.
Proof.
  intros HnIn Hadd Hinj; unfold find_data.
  rewrite fold_Add with (k := r') (e := r) (m1 := empty); auto.
  - intros [v HM].
    now apply empty_1 in HM.
  - unfold Add.
    apply find_data_filter_Add_eq_wkinj with (rm := rm); auto.
Qed.

Lemma find_data_Add_neq (r r' r1: resource) (rm rm': t) :
  ~ In r' rm -> Add r' r1 rm rm' ->  r1 <> r ->
  find_data rm' r = find_data rm r.
Proof.
  intros HnIn Hadd Hneq; unfold find_data.
  assert (eq (filter (find_data_filter r) rm') (filter (find_data_filter r) rm)).
  - eapply find_data_filter_Add_neq; eauto.
  - f_equal.
    eapply fold_Proper; auto.
Qed.

Lemma find_data_eq (r: resource) (rm rm': t) :
  eq rm rm' -> (Injective (fun x => find x rm)) ->
  find_data rm r = find_data rm' r.
Proof.
  revert rm'.
  induction rm using map_induction; intros rm' Heqrm HInj.
  - do 2 (rewrite find_data_Empty_none; auto).
    now rewrite <- Heqrm.
  - destruct (Resource.eq_dec r e) as [| Hneq]; subst.
    -- rewrite (find_data_Add_eq e x rm1); auto.
       rewrite (find_data_Add_eq e x rm1 rm'); auto. 
       + unfold Add in *; now rewrite <- Heqrm.
       + intros z y Hfi.
         apply HInj.
         now rewrite Heqrm.  
    -- rewrite (find_data_Add_neq _ x e rm1); auto.
       rewrite (find_data_Add_neq _ x e rm1 rm'); auto.
       unfold Add in *; now rewrite <- Heqrm.
Qed.  

Lemma find_data_wkeq (r: resource) (rm rm': t) :
  eq rm rm' -> 
  (forall r r' v, find r rm' = Some v /\ find r' rm' = Some v -> r = r') ->
  find_data rm r = find_data rm' r.
Proof.
  revert rm'.
  induction rm using map_induction; intros rm' Heqrm HInj.
  - do 2 (rewrite find_data_Empty_none; auto).
    now rewrite <- Heqrm.
  - destruct (Resource.eq_dec r e) as [| Hneq]; subst.
    -- rewrite (find_data_Add_wkeq e x rm1); auto.
       rewrite (find_data_Add_wkeq e x rm1 rm'); auto. 
       + unfold Add in *; now rewrite <- Heqrm.
       + intros z y v [Hfi Hfi'].
         apply (HInj _ _ v).
         split; now rewrite <- Heqrm.  
    -- rewrite (find_data_Add_neq _ x e rm1); auto.
       rewrite (find_data_Add_neq _ x e rm1 rm'); auto.
       unfold Add in *; now rewrite <- Heqrm.
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