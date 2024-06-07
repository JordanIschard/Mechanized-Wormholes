From Coq Require Import Lia Arith.PeanoNat Classical_Prop.
From Mecha Require Import Resource Term REnvironment Cell ReadStock WriteStock.
From DeBrLevel Require Import LevelInterface MapExt PairLevel.
From MMaps Require Import MMaps.
Import ResourceNotations TermNotations CellNotations REnvironmentNotations
       ReadStockNotations WriteStockNotations.

(** * Environment - Virtual Resource Environment

  W, defined in [Stock.v], is in charge of keeping bound resources
  and initial terms of each removed wh term. In the original paper,
  W is a set of triplets, which can be cumbersome to treat. We decide
  to split W into two data structures: a map and a set. 

*)
Module Stock <: IsLvlET.

Include IsLvlPairET ReadStock WriteStock.

(** ** Definition *)

Definition get_r (t : Stock.t) : 𝐖ᵣ := fst t.
Definition get_w (t : Stock.t) : 𝐖ₔ := snd t.

Definition empty : Stock.t := (∅ᵣₖ,∅ₔₖ). 

Definition to_RS (st : Stock.t) : resources :=
  ReadStock.to_RS (get_r st) (get_w st).

Definition init_virtual (st : Stock.t) (V : REnvironment.t) :=
  ReadStock.init_virtual (get_r st) (WriteStock.init_virtual (get_w st)  V).

Definition add (r r' : resource) (v : Λ) (W : Stock.t) : Stock.t :=
  (⌈ r ⤆ v ⌉ᵣₖ (get_r W),(r' +: (get_w W))%wk).

Definition union (W W' : Stock.t) :=
  (((get_r W) ∪ (get_r W'))%rk, ((get_w W) ∪ (get_w W'))%wk).

Definition In (r : resource) (W : Stock.t) :=
  (r ∈ᵣₖ (get_r W)) \/ (r ∈ (get_w W))%wk.

Definition update (W : Stock.t) (V : REnvironment.t) :=
  (ReadStock.map_update (get_r W) V,get_w W).

Definition find (r : resource) (W : Stock.t) := (fst W) ⌊r⌋ᵣₖ.

Definition halts k st := ReadStock.halts k (get_r st).

(** ** Initialized *)

Lemma init_virtual_unused : forall sk V,
  REnvironment.For_all (fun _ v => Cell.unused v) V ->
  REnvironment.For_all (fun _ v => Cell.unused v) (init_virtual sk V).
Proof.
  intros; unfold init_virtual; 
  apply ReadStock.init_virtual_Forall_unused.
  apply WriteStock.init_virtual_Forall_unused.
  assumption.
Qed.

Lemma init_virtual_unused_1 : forall sk V,
  (forall r v, V ⌈r ⩦ v⌉ᵣᵦ -> Cell.unused v) ->
  forall r v, (init_virtual sk V) ⌈r ⩦ v⌉ᵣᵦ -> Cell.unused v.
Proof.
  intros. 
  assert ( REnvironment.For_all (fun _ v => Cell.unused v) V ->
           REnvironment.For_all (fun _ v => Cell.unused v) (init_virtual sk V)).
  - apply init_virtual_unused.
  - unfold REnvironment.For_all in *.
    eapply H1; eauto.
Qed.

(** ** In *)

Lemma empty_in_spec : forall r, ~ In r empty.
Proof.
  intros; unfold In,empty; simpl. intro. destruct H.
  - revert H. apply ReadStock.not_in_empty.
  - inversion H.
Qed.

Lemma add_spec : forall W x r r' v,
  In x (add r r' v W) <-> x = r \/ x = r' \/ In x W.
Proof.
  intros; unfold add,In in *; destruct W; simpl in *; split; intros.
  - destruct H.
    -- destruct (Resource.eq_dec x r); subst. 
       + now left.
       + rewrite ReadStock.add_neq_in_iff in H; auto.
    -- rewrite WriteStock.add_spec in H; destruct H; auto.
  - destruct H; subst.
    -- left. apply ReadStock.add_in_iff; now left.
    -- destruct H; subst.
       + right; rewrite WriteStock.add_spec; now left.
       + destruct H.
         ++ left; rewrite ReadStock.add_in_iff; now right.
         ++ right; rewrite WriteStock.add_spec; now right.
Qed.

Lemma union_spec : forall r W W', 
  In r (union W W') <-> In r W \/ In r W'.
Proof.
  intros; unfold In,union in *; destruct W,W'; simpl in *; split; intros.
  - destruct H.
    -- apply ReadStock.map_union_spec in H; destruct H; auto.
    -- apply WriteStock.union_spec in H; destruct H; auto.
  - destruct H as [[H | H] | [H | H]]; rewrite ReadStock.map_union_spec;
    rewrite WriteStock.union_spec; auto.
Qed.

Lemma union_find_spec : forall r v W W',
  find r (union W W') = Some v -> find r W = Some v \/ find r W' = Some v.
Proof.
  intros. destruct W,W'; unfold find in *; simpl in *.
  apply ReadStock.find_2 in H. apply ReadStock.extend_mapsto_iff in H;
  destruct H.
  - apply ReadStock.find_1 in H; auto.
  - destruct H; apply ReadStock.find_1 in H; auto.
Qed.

(** ** Morphism from RStock to Resources *)

Lemma to_RS_empty_spec : to_RS empty = ∅ᵣₛ.
Proof.
  unfold to_RS. rewrite ReadStock.to_RS_empty_spec.
  now simpl.
Qed.

Lemma to_RS_in_spec : forall W r,
  In r W <-> (r ∈ to_RS W)%rs.
Proof.
  split; unfold In,to_RS; destruct W; simpl; intros; 
  now apply ReadStock.to_RS_in_spec_2.
Qed.

Lemma to_RS_union_spec : forall W W' r,
  (r ∈ (to_RS (union W W')))%rs <-> (r ∈ (to_RS W))%rs \/ (r ∈ (to_RS W'))%rs.
Proof.
 intros; repeat rewrite <- to_RS_in_spec; now rewrite union_spec.
Qed.

(** ** Valid *)

Lemma valid_empty_spec : forall lb,
  valid lb empty.
Proof.
  intros; split; simpl.
  - apply ReadStock.valid_Empty_spec; apply ReadStock.empty_1.
  - apply WriteStock.valid_empty_spec.
Qed.

Lemma valid_add_spec : forall lb r r' v W,
  lb ⊩ᵣ r -> lb ⊩ᵣ r' -> lb ⊩ₜₘ v -> valid lb W ->
  valid lb (add r r' v W).
Proof.
  intros lb r r' v W Hvr Hvr' Hvv HvW.
  unfold valid in *; destruct W; simpl in *. destruct HvW. split.
  - apply ReadStock.valid_add_spec; auto.
  - apply WriteStock.valid_unfold. intro.
    intros; rewrite WriteStock.add_spec in H1; destruct H1; subst; auto.
    apply WriteStock.valid_unfold in H0. now apply H0.
Qed.

Lemma valid_union_spec : forall lb W W',
  valid lb W /\ valid lb W' -> valid lb (union W W').
Proof.
  intros lb W W' [HvW HvW']; destruct W,W'; unfold valid in *; simpl in *.
  destruct HvW,HvW'. split.
  - apply ReadStock.valid_map_union_spec; auto.
  - rewrite WriteStock.valid_union_spec; split; auto.
Qed.

Lemma valid_in_spec : forall lb r W,
  In r W -> valid lb W -> lb ⊩ᵣ r.
Proof.
  intros; unfold In,valid in *; destruct W; simpl in *.
  destruct H,H0.
  - eapply ReadStock.valid_in_spec in H; eauto.
  - eapply WriteStock.valid_in_spec; eauto.
Qed.

(** ** Shift *)

Lemma shift_in_spec : forall lb k r W,
  In r W <-> In ([⧐ᵣ lb ≤ k] r) (shift lb k W).
Proof.
  split; intros; unfold In,shift in *; destruct W; 
  simpl in *; destruct H.
  - left. now apply ReadStock.shift_in_spec.
  - right; now apply WriteStock.shift_in_spec.
  - left. rewrite ReadStock.shift_in_spec; eauto.
  - right; rewrite WriteStock.shift_in_spec; eauto.
Qed.

Lemma shift_in_e_spec : forall lb k r W,
  In r (shift lb k W) -> exists r', r =  ([⧐ᵣ lb ≤ k] r').
Proof.
  unfold In,shift; destruct W; simpl; intros; destruct H.
  - apply ReadStock.shift_in_e_spec in H; auto.
  - apply WriteStock.shift_in_e_spec in H; destruct H as [x [H _]].
    now exists x.
Qed.

(** ** Halts *)

#[export]
Instance halts_eq: 
 Proper (Logic.eq ==> Stock.eq ==> iff) halts.
Proof.
  repeat red; intros; subst.
  destruct x0,y0; unfold halts,eq,RelationPairs.RelProd in *; simpl in *.
  repeat red in H0; destruct H0. 
  unfold RelationPairs.RelCompFun in *; simpl in *.
  split; intros.
  - now rewrite <- H.
  - now rewrite H.
Qed.

Lemma halts_init_virtual : forall k W V,
  halts k W -> 
  REnvironment.halts k V ->
  REnvironment.halts k (init_virtual W V).
Proof.
  unfold init_virtual; intros; destruct W. 
  unfold halts in H; simpl in *.
  apply ReadStock.halts_init_virtual; auto.
  apply WriteStock.halts_init_virtual; assumption.
Qed.

Lemma halts_update : forall k W V,
  REnvironment.halts k V ->
  halts k W ->
  halts k (update W V).
Proof.
  intros. unfold halts,update; simpl; destruct W; simpl.
  apply ReadStock.halts_update; auto.
Qed.

(* il faut halts_add_spec halts_weakening halts_union_spec *)

Lemma halts_weakening : forall k k' t, k <= k' -> halts k t -> halts k' (shift k (k' - k) t).
Proof.
  intros. unfold halts,shift in *; destruct t0; simpl in *.
  apply ReadStock.halts_weakening; assumption.
Qed.

Lemma halts_union_spec k s1 s2 :
  halts k s1 /\ halts k s2 -> halts k (union s1 s2).
Proof.
  unfold halts; destruct s1,s2; simpl in *; intros.
  apply ReadStock.halts_union_spec; assumption.
Qed.

Lemma halts_add_spec k x x1 v s :
  (ET_Definition.halts k v) /\ halts k s -> halts k (add x x1 v s).
Proof.
  intros []; unfold halts, add in *; destruct s; simpl in *.
  apply ReadStock.halts_add_spec; now split.
Qed.

End Stock.

Module StockNotations.

(** ** Scope *)
Declare Scope stock_scope.
Delimit Scope stock_scope with sk.

(** ** Notations *)
Definition 𝐖 := Stock.t.

Infix "∈ₛₖ" := Stock.In (at level 20, no associativity).
Infix "=" := Stock.eq : stock_scope.
Infix "∪" := Stock.union : stock_scope.
Infix "⊩ₛₖ" := Stock.valid (at level 20, no associativity).

Notation "r '∉ₛₖ' W" := (~ (Stock.In r W)) (at level 20, no associativity). 
                                                                      
Notation "∅ₛₖ" := Stock.empty (at level 20, no associativity). 
Notation "R '⌊' x '⌋ₛₖ'"  := (Stock.find x R) (at level 15, x constr).
Notation "⌈ x ~ x' ⤆ v '⌉ₛₖ' R"  := (Stock.add x x' v R) (at level 15, 
                                                                          x constr, v constr).
Notation "R ⌈ x ⩦ v '⌉ₛₖ'"  := (Stock.find x R = Some v) (at level 15, x constr, v constr).
Notation "R ⌈ x ⩦ ⊥ '⌉ₛₖ'"  := (Stock.find x R = None) (at level 15, x constr).
Notation "'[⧐ₛₖ' lb '≤' k ']' t" := (Stock.shift lb k t) (at level 45, 
                                                                      right associativity).

(** ** Morphisms *)

#[export]
Instance halts_eq: 
 Proper (Logic.eq ==> Stock.eq ==> iff) Stock.halts.
Proof. apply Stock.halts_eq. Qed.

End StockNotations.