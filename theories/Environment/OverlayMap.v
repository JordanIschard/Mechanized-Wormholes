From Coq Require Import Lia Morphisms.
From DeBrLevel Require Import LevelInterface Level MapLevelInterface MapLevel MapExtInterface 
               MapExt.

(** * Environment - Overlay - Map *)

(** ** Module - Overlay *)
Module OverlayMap (Data : IsLvlETWL) <: IsLvlET.

(** *** Definition *)

Include MapLvlD.MakeLvlMapLVLD Data.
Import Raw Ext.

(** **** ForAll property

  MMaps does not provide a function that check if all elements in the environment satisfy a property [P]. Consequently we define it.
*)
Definition For_all (P : Lvl.t -> Data.t -> Prop) (o : t) := 
  forall k d, find k o = Some d -> P k d.


(** *** Property *)

(** **** [For_all] property *)
Section For_all.

Hypothesis P : Lvl.t -> Data.t -> Prop. 

#[export] Instance For_all_proper : Proper (eq ==> iff) (For_all P).
Proof.
  intros o o' Heqo; unfold For_all; split; intros HFa k d Hfi.
  - rewrite <- Heqo in Hfi; auto.
  - rewrite Heqo in Hfi; auto.
Qed.

Lemma For_all_empty_spec : For_all P empty.
Proof. intros k d Hfi; inversion Hfi. Qed.

Lemma For_all_Empty_spec (o : t) :
  Empty o -> For_all P o.
Proof.
  intros HEmp k d Hfi; apply Empty_eq_spec in HEmp.
  rewrite HEmp in Hfi; inversion Hfi.
Qed.

Lemma For_all_add_spec (k : Lvl.t) (d : Data.t) (o : t) :
 P k d /\ For_all P o -> For_all P (add k d o).
Proof.
  intros [HP HFa] k' d' Hfi.
  destruct (Lvl.eq_dec k' k) as [Heq | Hneq]; subst.
  - rewrite add_eq_o in Hfi; auto.
    inversion Hfi; now subst.
  - rewrite add_neq_o in Hfi; auto.
Qed.

Lemma For_all_add_notin_spec (k : Lvl.t) (d : Data.t) (o : t) :
 ~ In k o ->
 ((P k d /\ For_all P o) <-> For_all P (add k d o)).
Proof.
  intro HnIn; split.
  - apply For_all_add_spec.
  - intro HFa; split.
    -- apply HFa.
       now rewrite add_eq_o.
    -- intros k' d' Hfi. 
       destruct (Lvl.eq_dec k' k) as [Heq | Hneq]; subst.
       + exfalso; apply HnIn.
         exists d'; now apply find_2.
       + apply HFa.
         now rewrite add_neq_o.
Qed.

End For_all.

(** **** [valid] property *)

Lemma valid_update_spec (m k : Lvl.t) (d : Data.t) (o : t) :
  In k o -> valid m o -> Data.valid m d -> valid m (add k d o).
Proof.
  revert k d; induction o using map_induction; intros k d HIn Hvo Hvd.
  - apply Empty_eq_spec in H; rewrite H in *.
    inversion HIn; inversion H0.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    apply valid_add_notin_spec in Hvo as [Hvx [Hve Hvo1]]; auto.
    apply add_in_iff in HIn as [Heq | HIn]; subst.
    -- rewrite add_shadow.
       rewrite valid_add_notin_spec; auto.
    -- destruct (Lvl.eq_dec k x) as [| Hneq]; subst; try contradiction.
       rewrite add_add_2; auto.
       eapply IHo1 in Hvo1; eauto.
       rewrite valid_add_notin_spec; auto.
       rewrite add_in_iff; intros [Hc | Hc]; subst; contradiction.
Qed.

Lemma valid_in_iff (m n k : Lvl.t) (o : t) :
  valid m o -> In k (shift m n o) <-> In k o.
Proof.
  revert k; induction o using map_induction; intros k Hvo; split; intro HIn.
  - rewrite shift_Empty_spec in HIn; auto.
  - rewrite shift_Empty_spec; auto.
  - unfold Add in *; rewrite H0 in *; clear H0. 
    apply valid_add_notin_spec in Hvo as [Hvk [Hvd Hv]]; auto.
    rewrite shift_add_notin_spec in HIn; auto.
    rewrite add_in_iff in *; destruct HIn as [Heq | HIn]; subst.
    -- left; rewrite Level.shift_valid_refl; auto.
    -- right. rewrite <- IHo1; eauto.
  - unfold Add in *; rewrite H0 in *; clear H0. 
    apply valid_add_notin_spec in Hvo as [Hvk [Hvd Hv]]; auto.
    rewrite shift_add_notin_spec; auto.
    rewrite add_in_iff in *; destruct HIn as [Heq | HIn]; subst.
    -- left; rewrite Level.shift_valid_refl; auto.
    -- right. rewrite IHo1; eauto.
Qed.

(** **** [shift] property *)

Lemma new_key_in_spec (k : Lvl.t) (o : t) :
  In k o ->  k < new_key o.
Proof.
  revert k; induction o using map_induction; intros k HIn.
  - exfalso; destruct HIn as [d HM]; now apply (H k d).
  - unfold Add in H0; rewrite H0 in *; clear H0.
    apply add_in_iff in HIn as [Heq | HIn]; subst.
    -- destruct (Lvl.leb_spec (new_key o1) (S k)).
       + rewrite new_key_add_ge_spec; auto; lia.
       + rewrite new_key_add_lt_spec; auto; lia.
    -- apply IHo1 in HIn as Hnew.
       destruct (Lvl.leb_spec (new_key o1) (S x)).
       + rewrite new_key_add_ge_spec; auto; lia.
       + rewrite new_key_add_lt_spec; auto; lia.
Qed.

Lemma shift_gt_iff (m n x y : Lvl.t) :
  x > y <-> (Level.shift m n x) > (Level.shift m n y).
Proof.
  unfold Level.shift; split; intro Hgt;
  destruct (Level.leb_spec m x); destruct (Level.leb_spec m y); lia.
Qed.

Lemma shift_le_spec (m n x : Lvl.t) :
  x <= (Level.shift m n x).
Proof.
  unfold Level.shift; destruct (Level.leb_spec m x); lia.
Qed.

Lemma shift_max_key_gt_iff (m n x : Lvl.t) (o : t) :
  max_key o > x <-> max_key (shift m n o) > (Level.shift m n x).
Proof.
  revert x; induction o using map_induction; intro y.
  - split; intro Hmax.
    -- rewrite max_key_Empty_spec in Hmax; auto; lia.
    -- rewrite shift_Empty_spec in Hmax; auto.
       rewrite max_key_Empty_spec in Hmax; auto; lia.
  - split; intro Hmax;
    unfold Add in H0; rewrite H0 in *; clear H0.
    -- destruct (Level.leb_spec (max_key o1) x) as [Hle | Hgt].
       + rewrite max_key_add_ge_spec in Hmax; auto; try lia.
         rewrite shift_add_spec.
         rewrite (shift_in_iff m n) in H.
         destruct (Level.leb_spec (max_key (shift m n o1)) (Level.shift m n x)) as [Hle' | Hgt'].
         ++ rewrite max_key_add_ge_spec; auto; try lia.
            now apply shift_gt_iff.
         ++ rewrite max_key_add_lt_spec; auto; try lia.
            assert (max_key o1 > x) by (rewrite IHo1; lia); lia.
       + rewrite max_key_add_lt_spec in Hmax; auto; try lia.
         rewrite shift_add_spec.
         rewrite (shift_in_iff m n) in H.
         destruct (Level.leb_spec (max_key (shift m n o1)) (Level.shift m n x)) as [Hle' | Hgt'].
         ++ rewrite IHo1 in Hmax.
            rewrite max_key_add_ge_spec; auto; lia.
         ++ rewrite max_key_add_lt_spec; auto; try lia.
            now rewrite <- IHo1.
    -- rewrite shift_add_spec in Hmax.
       rewrite (shift_in_iff m n) in H.
       destruct (Level.leb_spec (max_key (shift m n o1)) (Level.shift m n x)) as [Hle | Hgt].
       + rewrite max_key_add_ge_spec in Hmax; auto; try lia.
         rewrite <- (shift_in_iff m n) in H.
         destruct (Level.leb_spec (max_key o1) x) as [Hle' | Hgt'].
         ++ rewrite max_key_add_ge_spec; auto; try lia.
            now apply shift_gt_iff in Hmax.
         ++ rewrite max_key_add_lt_spec; auto; try lia.
            rewrite <- shift_gt_iff in Hmax; lia.
       + rewrite max_key_add_lt_spec in Hmax; auto; try lia.
         rewrite <- (shift_in_iff m n) in H.
         destruct (Level.leb_spec (max_key o1) x) as [Hle' | Hgt'].
         ++ rewrite max_key_add_ge_spec; auto; try lia.
            rewrite <- IHo1 in Hmax; lia.
         ++ rewrite max_key_add_lt_spec; auto; try lia.
            rewrite <- IHo1 in Hmax; lia.
Qed. 

Lemma shift_max_key_le_spec (m n : Lvl.t) (o : t) :
  max_key o <= max_key (shift m n o).
Proof.
  induction o using map_induction.
  - now rewrite shift_Empty_spec.
  - unfold Add in H0; rewrite H0; clear H0. 
    rewrite shift_add_spec.
    destruct (Level.leb_spec (max_key o1) x) as [Hle | Hgt].
    -- rewrite max_key_add_ge_spec; auto; try lia.
       rewrite (shift_in_iff m n) in H.
       destruct (Level.leb_spec (max_key (shift m n o1)) (Level.shift m n x)) as [Hle' | Hgt'].
       + rewrite max_key_add_ge_spec; auto; try lia.
         apply shift_le_spec.
       + rewrite max_key_add_lt_spec; auto; try lia.
         assert (Hgt : max_key (shift m n o1) > Level.shift m n x) by lia.
         rewrite <- shift_max_key_gt_iff in Hgt; lia.
    -- rewrite max_key_add_lt_spec; auto; try lia.
       rewrite (shift_in_iff m n) in H.
       destruct (Level.leb_spec (max_key (shift m n o1)) (Level.shift m n x)) as [Hle' | Hgt'].
       + rewrite max_key_add_ge_spec; auto; lia.
       + rewrite max_key_add_lt_spec; auto; lia.
Qed.
       
Lemma shift_new_key_le_spec (m n : Lvl.t) (o : t) :
  new_key o <= new_key (shift m n o).
Proof.
  unfold new_key; destruct (is_empty o) eqn:Hemp; try lia.
  destruct (is_empty (shift m n o)) eqn:Hemp'.
  - apply is_empty_2 in Hemp'. 
    rewrite <- (shift_Empty_iff m n) in Hemp'.
    apply is_empty_1 in Hemp'.
    rewrite Hemp in Hemp'; now inversion Hemp'.
  - assert (max_key o <= max_key (shift m n o)); try lia.
    apply shift_max_key_le_spec.
Qed.

Lemma shift_in_e_spec (m n k : Lvl.t) (o : t) :
  In k (shift m n o) -> exists (k' : Lvl.t), k = Level.shift m n k'.
Proof.
  revert k; induction o using map_induction; intros k HIn.
  - rewrite shift_Empty_spec in HIn; auto.
    exfalso; destruct HIn as [v HM]; now apply (H k v).
  - unfold Add in H0; rewrite H0 in *; clear H0.
    rewrite shift_add_spec in HIn.
    apply add_in_iff in HIn as [Heq | Hneq]; auto.
    now exists x.
Qed.

Lemma shift_find_spec_3 (m n k : Lvl.t) (o o' : t) :
  Level.valid m k -> In k o ->
  find k o = find k o' -> find k (shift m n o) = find k (shift m n o').
Proof.
  intros Hvk HIn Hfi. 
  destruct HIn as [v HfV]; apply find_1 in HfV.
  apply shift_find_iff with (lb := m) (k := n) in HfV as HfV1.
  rewrite Hfi in HfV. 
  apply shift_find_iff with (lb := m) (k := n) in HfV as HfV2.
  rewrite Level.shift_valid_refl in *; auto. 
  now rewrite HfV1, HfV2. 
Qed.

Lemma shift_find_e_spec_1 (m n k : Lvl.t) (d : Data.t) (o : t) :
  find k (shift m n o) = Some d -> 
  (exists k', k = Level.shift m n k') /\ (exists d', (Data.eq d (Data.shift m n d'))).
Proof.
  intro Hfi.
  assert (HIn : In k (shift m n o)). { now exists d; apply find_2. }
  apply shift_in_e_spec in HIn; split; auto.
  destruct HIn as [k' Heq]; subst.
  now apply shift_find_e_spec in Hfi.
Qed.

End OverlayMap.


Module OverlayMapBdl (Data : IsBdlLvlETWL) <: IsBdlLvlET.

Include OverlayMap Data.

Lemma shift_valid_refl (lb k : Lvl.t) (t : t) : valid lb t -> eq (shift lb k t) t.
Proof.
  induction t using map_induction; intro Hvt.
  - now apply shift_Empty_spec.
  - unfold Add in H0; rewrite H0 in *; clear H0.
    apply valid_add_notin_spec in Hvt as [Hvx [Hve Hvt]]; auto. 
    rewrite shift_add_spec.
    rewrite IHt1; auto.
    rewrite Level.shift_valid_refl; auto.

    replace (Data.shift lb k e) with e; try reflexivity.
    apply Data.eq_leibniz.
    now rewrite Data.shift_valid_refl; auto.
Qed.

End OverlayMapBdl.
