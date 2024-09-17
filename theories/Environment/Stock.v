(* From Coq Require Import Lia Arith.PeanoNat Classical_Prop.
From Mecha Require Import Resource Resources Term REnvironment Cell ReadStock.
From DeBrLevel Require Import LevelInterface MapExt PairLevel.
From MMaps Require Import MMaps.
Import ResourceNotations TermNotations CellNotations REnvironmentNotations
       ReadStockNotations ResourcesNotations SetNotations.

(** * Environment - Virtual Resource Environment

   In the functional transition there are two kind of environment: the resource environment and the stock. The former, defined in [REnvironment.v], represents the local memory during an instant. The latter, defined here, keeps local resource names with their initial value. This environment is split into a map, defined in [ReadStock.v], which maps local resource names, used for a reading interaction, to terms, and a set which keeps 'writing' local resource names.   
*)

(** ** Module - Virtual Resource Environment *)
Module Stock <: IsLvlET.

Include IsLvlPairET ReadStock Resources.
Open Scope resources_scope.
Open Scope set_scope.

(** *** Definition *)

Definition get_r (t : Stock.t) : 𝐖ᵣ := fst t.
Definition get_w (t : Stock.t) : resources := snd t.

Definition empty : Stock.t := (∅%rk,∅). 

(* Definition to_RS (st : Stock.t) : resources :=
  ReadStock.to_RS (get_r st) (get_w st). *)

Definition env_from_stock (st : Stock.t) (V : 𝐕) : 𝐕 :=
  ReadStock.env_to_renv (get_r st) (REnvironment.init_env_from_set (get_w st)  V).

Definition add (r r' : resource) (v : Λ) (W : Stock.t) : Stock.t :=
  (⌈ r ⤆ v ⌉ (get_r W),r' +: (get_w W))%rk.

Definition union (W W' : Stock.t) :=
  (((get_r W) ∪ (get_r W'))%rk, (get_w W) ∪ (get_w W')).

Definition In (r : resource) (W : Stock.t) :=
  (r ∈ (get_r W))%rk \/ (r ∈ (get_w W)).

Definition update (W : Stock.t) (V : 𝐕) :=
  (ReadStock.env_from_renv (get_r W) V,get_w W).

Definition find (r : resource) (W : Stock.t) := (fst W) ⌊r⌋%rk.

Definition halts k st := ReadStock.halts k (get_r st).

(** *** [env_from_stock] property *)

Lemma env_from_stock_unused : forall sk V,
  REnvironment.For_all (fun _ v => Cell.unused v) V ->
  REnvironment.For_all (fun _ v => Cell.unused v) (env_from_stock sk V).
Proof.
  intros; unfold env_from_stock.
  apply ReadStock.env_to_renv_Forall_unused.
  now apply REnvironment.init_env_from_set_Forall_unused.
Qed.

Lemma env_from_stock_unused_1 : forall sk V,
  (forall r v, V⌊r⌋%re = Some v -> Cell.unused v) ->
  forall r v, (env_from_stock sk V)⌊r⌋%re = Some v -> Cell.unused v.
Proof.
  intros. 
  assert (REnvironment.For_all (fun _ v => Cell.unused v) V ->
          REnvironment.For_all (fun _ v => Cell.unused v) (env_from_stock sk V)).
  - apply env_from_stock_unused.
  - unfold REnvironment.For_all in *.
    eapply H1; eauto.
Qed.

Lemma env_from_stock_in_iff : forall r sk V,
  (r ∈ (env_from_stock sk V))%re <-> In r sk \/ (r ∈ V)%re.
Proof.
  intros. split; unfold env_from_stock, In.
  - destruct sk; simpl; intro HIn.
    apply ReadStock.env_to_renv_in_iff in HIn as [HIn | HIn]; auto.
    apply REnvironment.init_env_from_set_in_iff in HIn as [HIn | HIn]; auto.
  - destruct sk; simpl; intros [[HIn | HIn] | HIn].
    -- apply ReadStock.env_to_renv_in_iff; now left.
    -- apply ReadStock.env_to_renv_in_iff; right.
       apply REnvironment.init_env_from_set_in_iff; now left.
    -- apply ReadStock.env_to_renv_in_iff; right.
       apply REnvironment.init_env_from_set_in_iff; now right.
Qed.

Lemma env_from_stock_find_spec : forall r v sk V,
 (env_from_stock sk V)⌊r⌋%re = Some v -> In r sk \/ V⌊r⌋%re = Some v.
Proof.
  intros; unfold env_from_stock, In in *; destruct sk; simpl in *.
  apply ReadStock.env_to_renv_find_spec in H as [| H]; auto.
  apply REnvironment.init_env_from_set_find_spec in H as [|]; auto.
Qed.
    
(** ** [In] property  *)

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
    -- rewrite Resources.St.add_spec in H; destruct H; auto.
  - destruct H; subst.
    -- left. apply ReadStock.add_in_iff; now left.
    -- destruct H; subst.
       + right; rewrite Resources.St.add_spec; now left.
       + destruct H.
         ++ left; rewrite ReadStock.add_in_iff; now right.
         ++ right; rewrite Resources.St.add_spec; now right.
Qed.

Lemma union_spec : forall r W W', 
  In r (union W W') <-> In r W \/ In r W'.
Proof.
  intros; unfold In,union in *; destruct W,W'; simpl in *; split; intros.
  - destruct H.
    -- apply ReadStock.map_union_spec in H; destruct H; auto.
    -- apply Resources.St.union_spec in H; destruct H; auto.
  - destruct H as [[H | H] | [H | H]]; rewrite ReadStock.map_union_spec;
    rewrite Resources.St.union_spec; auto.
Qed.


(** ** [find] property *)

Lemma union_find_spec : forall r v W W',
  find r (union W W') = Some v -> find r W = Some v \/ find r W' = Some v.
Proof.
  intros. destruct W,W'; unfold find in *; simpl in *.
  apply ReadStock.find_2 in H. apply ReadStock.extend_mapsto_iff in H;
  destruct H.
  - apply ReadStock.find_1 in H; auto.
  - destruct H; apply ReadStock.find_1 in H; auto.
Qed.

(** ** [valid] poperty *)

Lemma valid_empty_spec : forall lb, valid lb empty.
Proof.
  intros; split; simpl.
  - apply ReadStock.valid_Empty_spec; apply ReadStock.empty_1.
  - apply Resources.valid_empty_spec.
Qed.

Lemma valid_add_spec : forall lb r r' v W,
  (lb ⊩ r)%r -> (lb ⊩ r')%r -> (lb ⊩ v)%tm -> valid lb W -> valid lb (add r r' v W).
Proof.
  intros lb r r' v W Hvr Hvr' Hvv HvW.
  unfold valid in *; destruct W; simpl in *. destruct HvW. split.
  - apply ReadStock.valid_add_spec; auto.
  - apply Resources.valid_unfold. intro.
    intros; rewrite Resources.St.add_spec in H1; destruct H1; subst; auto.
Qed.

Lemma valid_union_spec : forall lb W W',
  valid lb W /\ valid lb W' -> valid lb (union W W').
Proof.
  intros lb W W' [HvW HvW']; destruct W,W'; unfold valid in *; simpl in *.
  destruct HvW,HvW'. split.
  - apply ReadStock.valid_map_union_spec; auto.
  - apply Resources.valid_union_iff; split; auto.
Qed.

Lemma valid_in_spec : forall lb r W,
  In r W -> valid lb W -> (lb ⊩ r)%r.
Proof.
  intros; unfold In,valid in *; destruct W; simpl in *.
  destruct H,H0.
  - eapply ReadStock.valid_in_spec in H; eauto.
  - eapply Resources.valid_in_spec; eauto.
Qed.


(** ** [shift] property *)

Lemma shift_in_iff : forall lb k r W,
  In r W <-> In ([⧐ lb – k] r)%r (shift lb k W).
Proof.
  split; intros; unfold In,shift in *; destruct W; 
  simpl in *; destruct H.
  - left. now apply ReadStock.shift_in_iff.
  - right; now apply Resources.shift_in_iff.
  - left. rewrite ReadStock.shift_in_iff; eauto.
  - right; rewrite Resources.shift_in_iff; eauto.
Qed.

Lemma shift_in_e_spec : forall lb k r W,
  In r (shift lb k W) -> exists r', (r =  ([⧐ lb – k] r')%r)%type.
Proof.
  unfold In,shift; destruct W; simpl; intros; destruct H.
  - apply ReadStock.shift_in_e_spec in H; auto.
  - apply Resources.shift_in_e_spec in H; destruct H as [x [H _]].
    now exists x.
Qed.


(** ** [halts] property *)

#[export] Instance halts_eq: Proper (Logic.eq ==> Stock.eq ==> iff) halts.
Proof.
  repeat red; intros; subst.
  destruct x0,y0; unfold halts,eq,RelationPairs.RelProd in *; simpl in *.
  repeat red in H0; destruct H0. 
  unfold RelationPairs.RelCompFun in *; simpl in *.
  split; intros.
  - now rewrite <- H.
  - now rewrite H.
Qed.

Lemma halts_env_from_stock : forall k W V,
  halts k W -> 
  REnvironment.halts k V -> REnvironment.halts k (env_from_stock W V).
Proof.
  unfold env_from_stock; intros; destruct W. 
  unfold halts in H; simpl in *.
  apply ReadStock.halts_env_to_renv; auto.
  now apply REnvironment.halts_init_env_from_set.
Qed.

Lemma halts_update : forall k W V,
  REnvironment.halts k V -> halts k W -> halts k (update W V).
Proof.
  intros. unfold halts,update; simpl; destruct W; simpl.
  apply ReadStock.halts_env_from_renv; auto.
Qed.

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


(** ** Morphism *)

#[export] Instance in_stk : Proper (Logic.eq ==> eq ==> iff) In.
Proof.
  repeat red; intros; subst; split; destruct x0,y0; repeat red in H0; 
  unfold RelationPairs.RelCompFun, In in *; simpl in *; destruct H0;
  intros [|].
  - left; now rewrite <- H.
  - right; now rewrite <- H0.
  - left; now rewrite H.
  - right; now rewrite H0.
Qed.

#[export] Instance find_stk : Proper (Logic.eq ==> eq ==> Logic.eq) find.
Proof.
  repeat red; intros; subst; destruct x0,y0.
  repeat red in H0; unfold find,RelationPairs.RelCompFun in *.
  destruct H0; simpl in *. now rewrite H.
Qed.

#[export] Instance add_stk : 
Proper (Resource.eq ==> Resource.eq ==> Term.eq ==> eq ==> eq) add.
Proof.
  do 5 red; intros; subst; apply Term.eq_leibniz in H1; 
  unfold Resource.eq in *; subst.
  destruct x2,y2; repeat red in H2; repeat red;
  unfold eq, RelationPairs.RelCompFun in *;
  simpl in *; destruct H2; split.
  - intro; now rewrite H.
  - now rewrite H0.
Qed. 

End Stock.

(** ---- *)

(** ** Notation - Virtual Resource Environment *)

Module StockNotations.

(** *** Scope *)
Declare Scope stock_scope.
Delimit Scope stock_scope with sk.

(** *** Notation *)
Definition 𝐖 := Stock.t.

Infix "∈" := Stock.In (at level 60, no associativity) : stock_scope. 
Notation "r '∉' Re" := (~ (Stock.In r Re)) (at level 75, no associativity) : stock_scope. 
Notation "∅" := Stock.empty (at level 0, no associativity) : stock_scope. 
Notation "R '⌊' x '⌋'"  := (Stock.find x R) (at level 15, x constr) : stock_scope.
Notation "⌈ x '~' x1 ⤆ v '⌉' R"  := (Stock.add x x1 v R) (at level 15, 
                                                            x constr, v constr) : stock_scope.

Infix "=" := Stock.eq : stock_scope.
Infix "∪" := Stock.union : stock_scope.

Notation "'[⧐' lb '–' k ']' t" := (Stock.shift lb k t) (at level 65, 
                                                                right associativity) : stock_scope.
Infix "⊩" := Stock.valid (at level 20, no associativity) : stock_scope.

(** *** Morphism *)

Import Stock.

#[export] Instance halts_eq: Proper (Logic.eq ==> eq ==> iff) halts := _.
#[export] Instance in_stk : Proper (Logic.eq ==> eq ==> iff) In := _.
#[export] Instance find_stk : Proper (Logic.eq ==> eq ==> Logic.eq) find := _.
#[export] Instance add_stk : 
  Proper (Resource.eq ==> Resource.eq ==> Term.eq ==> eq ==> eq) add := _.

End StockNotations. *)