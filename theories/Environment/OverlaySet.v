From Coq Require Import Lia.
From DeBrLevel Require Import LevelInterface Level Levels. 

(** * Environment - Overlay - Set *)

(** ** Module - Overlay *)
Module OverlaySet <: IsBdlLvlFullOTWL.

Include Levels.
Import St.

Lemma valid_in_iff (lb k r : Lvl.t) (s : t):
  valid lb s -> In r (shift lb k s) <-> In r s.
Proof.
  induction s using set_induction; intro Hv; split.
  - intro HIn; rewrite shift_Empty_spec in *; auto; inversion HIn.
  - intro HIn; unfold Empty in *; exfalso; now apply (H r).
  - intro HIn; apply Add_inv in H0; subst. rewrite shift_add_notin_spec in *; auto.
    apply valid_add_spec in Hv as [Hvr Hv]. rewrite add_spec in HIn; destruct HIn; subst.
    -- rewrite Level.shift_valid_refl; auto; rewrite add_spec; now left.
    -- rewrite add_spec; right. rewrite <- IHs1; eauto.
  - intro HIn; apply Add_inv in H0; subst. rewrite shift_add_notin_spec in *; auto.
    apply valid_add_spec in Hv as [Hvr Hv]. rewrite add_spec in HIn; destruct HIn; subst.
    -- rewrite Level.shift_valid_refl; auto; rewrite add_spec; now left.
    -- rewrite add_spec; right. rewrite IHs1; eauto.
Qed.

End OverlaySet.