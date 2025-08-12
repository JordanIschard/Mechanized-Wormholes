From Coq Require Import Lia Classes.Morphisms FunctionalExtensionality.
From Mecha Require Import Typ Resource SyntaxNotation.
From DeBrLevel Require Import LevelInterface Level MapLevelInterface MapLevelLVLD.

(** * Context - Resource Context

  The type system, defined in [Type_System.v], requires two contexts: a variable context and a resource context. The former is defined in [VContext.v] and the latter is defined here. It is a map which binds resource names with pair types. We use the module [MapLvlD] defined by the library [DeBrLevel].
*)

Module RContext <: IsBdlLvlET.

Include MakeBdlLvlMapLVLD PairTyp.
Import Raw Ext.

Open Scope ptyp_scope.

(** ** Properties *)

(** *** [diff] properties *)

Lemma diff_Empty_l (m m': t) : Empty m -> Empty (diff m m').
Proof.
  intros HEmp k v HM.
  apply diff_mapsto_iff in HM as [].
  apply (HEmp k v); auto.
Qed. 

Lemma diff_Empty_r (m m': t) : Empty m' -> eq (diff m m') m.
Proof.
  intros HEmp.
  apply Equal_mapsto_iff.
  intros k v; split; intro HM.
  - now apply diff_mapsto_iff in HM as [].
  - apply diff_mapsto_iff; split; auto.
    intros [v' HM'].
    apply (HEmp k v' HM').
Qed.

Lemma diff_add_add (x: resource) (v: πΤ) (m m': t) : 
  ~ In x m -> eq (diff (add x v m) (add x v m')) (diff m m').
Proof.
  intro HnIn.
  apply Equal_mapsto_iff.
  intros k v'; split; intro HM.
  - rewrite diff_mapsto_iff in *.
    destruct HM as [HM HnIn']; split.
    -- apply add_mapsto_iff in HM as [[Heq Heq'] | [Hneq HM]]; subst.
       + exfalso.
         apply HnIn'.
         rewrite add_in_iff; auto.
       + auto.
    -- intro HIn; apply HnIn'.
       rewrite add_in_iff; auto.
  - rewrite diff_mapsto_iff in *.
    destruct HM as [HM HnIn']; split.
    -- destruct (R.eq_dec k x) as [| Hneq]; subst.
       + exfalso.
         apply HnIn.
         now exists v'.
       + rewrite add_mapsto_new; auto.
    -- intro HIn. 
       destruct (R.eq_dec k x) as [| Hneq]; subst.
       + exfalso.
         apply HnIn.
         now exists v'.
       + apply add_in_iff in HIn as [|]; auto.
Qed.

Lemma diff_Submap_in (x: resource) (m m': t) :
  Submap m m' -> In x m' <-> In x (diff m' m) \/ In x m.
Proof.
  intro Hsub; split; intro HIn.
  - destruct (In_dec m x); auto.
    rewrite diff_in_iff.
    left; now split.
  - destruct HIn.
    -- now apply diff_in_iff in H as [].
    -- now apply (Submap_in _ _ m') in H.
Qed. 

(** *** [new_key] properties *)

Lemma new_key_diff (m m': t) :
  Submap m m' -> new_key m' = max (new_key (diff m' m)) (new_key m).
Proof.
  revert m'.
  induction m using map_induction; intros m' Hsub.
  - rewrite (new_key_Empty m); auto.
    rewrite diff_Empty_r; auto; lia.
  - unfold Add in *; rewrite H0 in *; clear H0.
    rewrite new_key_add_max.
    apply Submap_add_2 in Hsub as Hsub'; auto.
    apply (Submap_Add_find x e m1) in Hsub as HIn; auto.
    -- apply add_id in HIn.
       rewrite <- add_remove_1 in HIn.
       rewrite <- HIn.
       rewrite new_key_add_max.
       rewrite diff_add_add.
       + rewrite IHm1; try lia.
         unfold Submap; split.
         ++ intros y HIn1.
            rewrite remove_in_iff.
            destruct (R.eq_dec x y) as [| Hneq]; subst.
            * contradiction.
            * apply (Submap_in _ _ m') in HIn1; auto.
         ++ intros k v v' Hfi1 Hfi'.
            apply find_1 in Hfi1,Hfi'.
            apply remove_3bis in Hfi'.
            apply find_2 in Hfi1,Hfi'.
            destruct Hsub'.
            apply (H1 k _ _ Hfi1 Hfi').
       + rewrite remove_in_iff; intros []; auto.
    -- unfold Add; reflexivity.
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

(** *** specific Wormholes properties *)

Lemma Submap_wh (m : t) (v v' : πΤ) :
  Submap m (add (S (new_key m)) v (add (new_key m) v' m)).
Proof.
  repeat apply Submap_add_1; try reflexivity.
  - apply new_key_notin.
    rewrite new_key_add_max; lia.
  - apply new_key_notin; lia. 
Qed.

Lemma Submap_wh_1 (m m' : t) (v v' : πΤ) :
  Submap (add (S (new_key m)) v (add (new_key m) v' m)) m' -> Submap m m'.
Proof.
  intro HSub.
  apply Submap_Add 
  with (m := (add (new_key m) v' m)) (x := (S (new_key m))) (v := v) in HSub.
  - apply Submap_Add with (m := m) (x := (new_key m)) (v := v') in HSub; auto.
    -- apply new_key_notin; auto.
    -- unfold Add; reflexivity.
  - apply new_key_notin.
    rewrite new_key_add_max; lia.
  - unfold Add; reflexivity. 
Qed.

Lemma new_key_wh (m : t) (v v' : πΤ) :
  new_key (add (S (new_key m)) v (add (new_key m) v' m)) = S (S (new_key m)).
Proof. do 2 rewrite new_key_add_max; lia. Qed.

Lemma Wf_wh (m : t) (v v' : πΤ) :
  Wf (new_key m) m -> (new_key m) ⊩ v -> (new_key m) ⊩ v' -> 
  Wf (S (S (new_key m))) (add (S (new_key m)) v (add (new_key m) v' m)).
Proof.
  intros Hvm Hvv Hvv'. 
  apply Wf_add_notin.
  - rewrite add_in_iff; intro Ha. 
    destruct Ha as [Heq | HIn]; try lia.
    apply new_key_notin in HIn; auto.
  - repeat split. 
    -- unfold R.Wf; lia.
    -- apply PairTyp.Wf_weakening with (k := new_key m); auto.
    -- apply Wf_add_notin.
       + apply new_key_notin; lia.
       + repeat split.
         ++ unfold R.Wf; lia.
         ++ apply PairTyp.Wf_weakening with (k := new_key m); auto.
         ++ apply Wf_weakening with (k := new_key m); auto.
Qed.

Lemma Wf_wh_full (m : t) (v v' : πΤ) :
  Wf (new_key m) m -> (new_key m) ⊩ v -> (new_key m) ⊩ v' -> 
  Wf (new_key (add (S (new_key m)) v (add (new_key m) v' m)))
        (add (S (new_key m)) v (add (new_key m) v' m)).
Proof.
  intros Hvm Hvv Hvv'.
  rewrite new_key_wh; now apply Wf_wh.
Qed.

(** *** Morphisms *)

#[export] Instance rcontext_in_iff : Proper (Logic.eq ==> eq ==> iff) In.
Proof. intros x y Heqx c c' Heqc; subst; now rewrite Heqc. Qed.

#[export] Instance rcontext_find_eq : Proper (Logic.eq ==> eq ==> Logic.eq) find.
Proof. intros x y Heqx c c' Heqc; subst; now rewrite Heqc. Qed.

#[export] Instance rcontext_Empty_iff : Proper (eq ==> iff) Empty.
Proof. intros c c' Heq; now rewrite Heq. Qed.

#[export] Instance rcontext_Add_iff : 
  Proper (R.eq ==> PairTyp.eq ==> eq ==> eq ==> iff) (@Add PairTyp.t).
Proof. 
  intros x x' HeqV ty ty' HeqT c c' Heq c1 c1' Heq1.
  apply PairTyp.eq_leibniz in HeqT; subst.
  unfold Add; now rewrite HeqV, Heq, Heq1.
Qed.

#[export] Instance rcontext_add_eq : 
  Proper (R.eq ==> PairTyp.eq ==> eq ==> eq) (@add PairTyp.t).
Proof. 
  intros x x' HeqV ty ty' HeqT c c' Heq.
  apply PairTyp.eq_leibniz in HeqT; subst.
  now rewrite HeqV, Heq. 
Qed. 

End RContext.