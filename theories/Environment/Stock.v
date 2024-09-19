From Coq Require Import Lia.
From Mecha Require Import Resource Resources Term REnvironment Cell ReaderStock.
From DeBrLevel Require Import LevelInterface PairLevel.
From MMaps Require Import MMaps.
Import ResourceNotations TermNotations CellNotations REnvironmentNotations
       ReaderStockNotations ResourcesNotations SetNotations.

(** * Environment - Virtual Resource Environment

  In the functional transition there are two kind of environment: the resource environment and the stock. The former, defined in [REnvironment.v], represents the local memory during an instant. The latter, defined here, keeps local resource names with their initial value. This environment is a pair split into a map, defined in [ReaderStock.v], which maps local resource names, used for a reading interaction, to terms, and a set which keeps 'writing' local resource names.   
*)

(** ** Module - Virtual Resource Environment *)
Module Stock <: IsLvlET.

(** *** Definition *)

Include IsLvlPairET ReaderStock Resources.
Module RE := REnvironment.
Module REA := ReaderStock.
Module RS := Resources.St.

Open Scope resources_scope.
Open Scope set_scope.

(** **** Projections *)
Definition readers (W : t) : 𝐖ᵣ := fst W.
Definition writers (W : t) : resources := snd W.

(** **** Empty stock 

  A stock is empty if and only if both components are empty.
*)
Definition empty : t := (∅%rk,∅). 

(** **** Initialize the resource environment

  For each instant, the resource environment has to be initialize for its global resource names and its local ones. The latter is done by picking information in the stock. We define [init_locals] which takes a stock [W] and a resource environment [V] and produces a new resource environment with all elements of [V] and readers and writers, stored in [W], initialized.
*)
Definition init_locals (W : t) (V : 𝐕) : 𝐕 :=
  REA.init_readers (readers W) (RE.init_writers (writers W)  V).

(** **** Add

  In the stock, we add a three elements: the reader resource name [rr], the writer resource name [rw] and the initial value [v]. [rr] and [v] are added in the first member of the pair, which is a map from [ReaderStock.v], and the last elements is added in the set of writers, i.e. in the second member of the pair.
*)
Definition add (rr rw : resource) (v : Λ) (W : t) : t :=
  (⌈ rr ⤆ v ⌉ (readers W),rw +: (writers W))%rk.

(** **** Union

  The union between two stocks is the point-to-point union between each component.
*)
Definition union (W W' : t) := ((readers W ∪ readers W')%rk, writers W ∪ writers W').

(** **** In

  A resource name is in the stock if it is, at least, in one member of the stock.
*)
Definition In (r : resource) (W : t) := (r ∈ readers W)%rk \/ (r ∈ writers W).

(** **** Find

  A data can be find only in the first member of the stock.
*)
Definition find (r : resource) (W : t) := (readers W) ⌊r⌋%rk.

(** **** Halts

  In the functional transition proofs, we assume that all elements in the input resource environment halts. The resource environment depends on the stock for its initialization in the temporal transition. Consequently, we also need to define the halts property on the stock.
*)
Definition halts (k : lvl) (W : t) := REA.halts k (readers W).

(** *** Property *)

(** **** [init_locals] property *)

Lemma init_locals_in_iff (r : resource) (W : t) (V : 𝐕) :
  (r ∈ (init_locals W V))%re <-> In r W \/ (r ∈ V)%re.
Proof.
  split; unfold init_locals, In; destruct W as [rW wW]; simpl.
  - intro HIn. 
    apply REA.init_readers_in_iff in HIn as [| HIn]; auto.
    apply RE.init_writers_in_iff in HIn as [|]; auto.
  - intro HIns. 
    apply REA.init_readers_in_iff.
    rewrite RE.init_writers_in_iff.
    destruct HIns as [[HIn | HIn] | HIn]; auto.
Qed.

Lemma init_locals_find_spec (r : resource) (v : 𝑣) (W : t) (V : 𝐕) :
 (init_locals W V)⌊r⌋%re = Some v -> In r W \/ V⌊r⌋%re = Some v.
Proof.
  unfold init_locals, In; destruct W as [rW wW]; simpl; intro Hfi. 
  apply REA.init_readers_find_spec in Hfi as [| Hfi]; auto.
  apply RE.init_writers_find_spec in Hfi as [|]; auto.
Qed.
    
(** **** [In] property  *)

Lemma empty_in_spec (r : resource) : ~ In r empty.
Proof.
  unfold In, empty; simpl; intros [HIn | HIn].
  - revert HIn; apply REA.not_in_empty.
  - inversion HIn.
Qed.

Lemma add_spec (r r' k : resource) (v : Λ) (W : t) :
  In k (add r r' v W) <-> k = r \/ k = r' \/ In k W.
Proof.
  unfold add, In; destruct W as [rw wW]; simpl; split.
  - intros [HIn | HIn].
    -- destruct (Resource.eq_dec k r) as [| Hneq]; subst; auto. 
       rewrite REA.add_neq_in_iff in HIn; auto.
    -- apply RS.add_spec in HIn as [|]; auto.
  - rewrite REA.add_in_iff; rewrite RS.add_spec.
    intros [Heq | [Heq | [HIn | HIn]]]; subst; auto.
Qed.

Lemma union_spec (r : resource) (W W' : t) : 
  In r (union W W') <-> In r W \/ In r W'.
Proof.
  unfold In,union; destruct W,W'; simpl.
  rewrite REA.extend_in_iff; rewrite RS.union_spec.
  split; intros [[|] | [|]]; auto.
Qed.


(** **** [find] property *)

Lemma union_find_spec (r : resource) (v : Λ) (W W' : t) :
  find r (union W W') = Some v -> find r W = Some v \/ find r W' = Some v.
Proof.
  unfold find, union; destruct W,W'; simpl; intro HM.
  apply REA.find_2 in HM. 
  apply REA.extend_mapsto_iff in HM as [HM | [HM _]];
  apply REA.find_1 in HM; auto.
Qed.

(** **** [valid] poperty *)

Lemma valid_empty_spec (k : lvl) : valid k empty.
Proof.
  unfold valid, empty; simpl; split.
  - apply REA.valid_empty_spec.
  - apply Resources.valid_empty_spec.
Qed.

Lemma valid_add_spec (k : lvl) (r r' : resource) (v : Λ) (W : t) :
  (k ⊩ r)%r -> (k ⊩ r')%r -> (k ⊩ v)%tm -> valid k W -> valid k (add r r' v W).
Proof.
  unfold valid; destruct W as [rW wW]; simpl. 
  intros Hvr Hvr' Hvv [HvrW HvwW]; split.
  - apply REA.valid_add_spec; auto.
  - apply Resources.valid_unfold; intros r1 HIn.
    apply RS.add_spec in HIn as [|]; subst; auto.
Qed.

Lemma valid_union_spec (k : lvl) (W W' : t) :
  valid k W /\ valid k W' -> valid k (union W W').
Proof.
  unfold valid; destruct W,W'; simpl. 
  intros [[HvrW HvwW] [HvrW' HvwW']]; split.
  - apply REA.valid_extend_spec; auto.
  - apply Resources.valid_union_iff; split; auto.
Qed.

Lemma valid_in_spec (k : lvl) (r : resource) (W : t) :
  In r W -> valid k W -> (k ⊩ r)%r.
Proof.
  unfold In, valid; destruct W as [rW wW]; simpl.
  intros [HIn | HIn] [HvrW HvwW].
  - eapply REA.valid_in_spec in HIn; eauto.
  - eapply Resources.valid_in_spec; eauto.
Qed.

Lemma valid_in_iff (m n k : lvl) (W : t) :
  valid m W -> In k (shift m n W) <-> In k W.
Proof.
  unfold valid, shift, In; destruct W as [rW wW]; simpl.
  intros [Hvr Hvw]; split; intros [HIn | HIn].
  - now left; rewrite ReaderStock.valid_in_iff in HIn.
  - now right; rewrite Resources.valid_in_iff in HIn.
  - now left; rewrite ReaderStock.valid_in_iff.
  - now right; rewrite Resources.valid_in_iff.
Qed.


(** **** [shift] property *)

Lemma shift_in_iff (m n : lvl) (r : resource) (W : t) :
  In r W <-> In ([⧐ m – n] r)%r (shift m n W).
Proof.
  unfold In, shift; destruct W as [rW wW]; simpl; 
  split; intros [HIn | HIn].
  - left. now apply REA.shift_in_iff.
  - right; now apply Resources.shift_in_iff.
  - left. rewrite REA.shift_in_iff; eauto.
  - right; rewrite Resources.shift_in_iff; eauto.
Qed.

Lemma shift_in_e_spec (m n : lvl) (r : resource) (W : t) :
  In r (shift m n W) -> exists r', (r =  ([⧐ m – n] r')%r)%type.
Proof.
  unfold In,shift; destruct W as [rW wW]; simpl; intros [HIn | HIn].
  - apply REA.shift_in_e_spec in HIn; auto.
  - apply Resources.shift_in_e_spec in HIn as [r' [Heq _]]; subst.
    now exists r'.
Qed.

(** **** [halts] property *)

#[export] Instance halts_eq: Proper (Logic.eq ==> eq ==> iff) halts.
Proof.
  unfold halts; intros k' k Heqk W W' Heqst; subst.
  destruct W,W'; repeat red in Heqst; unfold RelationPairs.RelCompFun in Heqst;
  simpl in *; destruct Heqst as [HeqR _].
  now rewrite HeqR.
Qed.

Lemma halts_init_locals (k : lvl) (W : t) (V : 𝐕) :
  halts k W -> RE.halts k V -> RE.halts k (init_locals W V).
Proof.
  unfold halts, init_locals; destruct W as [rW wW]; simpl.
  intros HvrW HvV.
  apply REA.halts_init_readers; auto.
  now apply RE.halts_init_writers.
Qed.

(* Lemma halts_update (k : lvl) (W : t) (V : 𝐕) :
  RE.halts k V -> halts k W -> halts k (update W V).
Proof.
  intros. unfold halts,update; simpl; destruct W; simpl.
  apply REA.halts_env_from_renv; auto.
Qed. *)

Lemma halts_weakening (m n : lvl) (W : t) : 
  m <= n -> halts m W -> halts n (shift m (n - m) W).
Proof.
  unfold halts, shift; destruct W as [rW wW]. 
  simpl; intros Hle HvrW.
  now apply REA.halts_weakening.
Qed.

Lemma halts_union_spec (k : lvl) (W W' : t) :
  halts k W /\ halts k W' -> halts k (union W W').
Proof.
  unfold halts; destruct W,W'; simpl; intro Hlt. 
  now apply REA.halts_union_spec.
Qed.

Lemma halts_add_spec (k : lvl) (r r' : resource) (v : Λ) (W : t) :
  (Evaluation_Transition.halts k v) /\ halts k W -> halts k (add r r' v W).
Proof.
  unfold halts, add; destruct W as [rW wW]; simpl; intro Hv.
  now apply REA.halts_add_spec.
Qed.


(** **** Morphism *)


#[export] Instance in_stk : Proper (Logic.eq ==> eq ==> iff) In.
Proof.
  unfold eq, In; intros k' k Heqk W W' Heqst; subst.
  destruct W,W'; repeat red in Heqst; unfold RelationPairs.RelCompFun in Heqst;
  simpl in *; destruct Heqst as [HeqR HeqW].
  now rewrite HeqR, HeqW.
Qed.

#[export] Instance find_stk : Proper (Logic.eq ==> eq ==> Logic.eq) find.
Proof.
  unfold find, eq; intros k' k Heqk W W' Heqst; subst.
  destruct W,W'; repeat red in Heqst; unfold RelationPairs.RelCompFun in Heqst;
  simpl in *; destruct Heqst as [HeqR HeqW].
  now rewrite HeqR.
Qed.

#[export] Instance add_stk : Proper (Resource.eq ==> Resource.eq ==> Term.eq ==> eq ==> eq) add.
Proof.
  unfold eq, add.
  intros r' r Heqr r1' r1 Heqr1 d d' Heqd W W' Heqst; destruct W,W'. 
  repeat red in Heqst; repeat red; unfold RelationPairs.RelCompFun in *; simpl in *. 
  destruct Heqst as [HeqR HeqW]; rewrite Heqr, Heqr1, Heqd; split.
  - now intro y; rewrite HeqR.
  - now rewrite HeqW.
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
Notation "⌈ x '~' x1 ⤆ v '⌉' R"  := (Stock.add x x1 v R) 
                                     (at level 15, x constr, v constr) : stock_scope.
Notation "'[⧐' lb '–' k ']' t" := (Stock.shift lb k t) 
                                   (at level 65, right associativity) : stock_scope.

Infix "=" := Stock.eq : stock_scope.
Infix "∪" := Stock.union : stock_scope.
Infix "⊩" := Stock.valid (at level 20, no associativity) : stock_scope.

(** *** Morphism *)

Import Stock.

#[export] Instance shift_stk : Proper (Resource.eq ==> Resource.eq ==> eq ==> eq) shift := _.
#[export] Instance valid_stk : Proper (Resource.eq ==> eq ==> iff) valid := _.
#[export] Instance halts_eq: Proper (Logic.eq ==> eq ==> iff) halts := _.
#[export] Instance in_stk : Proper (Logic.eq ==> eq ==> iff) In := _.
#[export] Instance find_stk : Proper (Logic.eq ==> eq ==> Logic.eq) find := _.
#[export] Instance add_stk : Proper (Resource.eq ==> Resource.eq ==> Term.eq ==> eq ==> eq) add := _.

End StockNotations.