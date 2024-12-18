From Coq Require Import Lia.
From Mecha Require Import Resource Resources Term Typ REnvironment 
                          ResourcesMap Cell SREnvironment RContext.
From DeBrLevel Require Import LevelInterface PairLevel.
From MMaps Require Import MMaps.
Import ResourceNotations ResourcesMapNotations 
       TermNotations CellNotations REnvironmentNotations TypNotations
       SREnvironmentNotations ResourcesNotations SetNotations RContextNotations.

(** * Environment - Virtual Resource Environment
*)

(** ** Module - Virtual Resource Environment *)
Module Stock <: IsLvlET.

Include IsLvlPairET SREnvironment ResourcesMap.

Module RE := REnvironment.
Module RC := RContext.
Module SRE := SREnvironment.
Module RM := ResourcesMap.

Open Scope renvironment_scope.

(** *** Definitions *)

(** **** Projections *)
Definition readers (W : t) : 𝐄 := fst W.
Definition writers (W : t) : RM.t := snd W.

(** **** Empty stock 

  A stock is empty if and only if both components are empty.
*)
Definition empty : t := (∅%sr,∅%rm). 

Definition Empty (t : t) : Prop := SRE.Empty (readers t) /\ RM.Empty (writers t).

Definition is_empty (t : t) : bool := SRE.Raw.is_empty (readers t) && RM.Raw.is_empty (writers t).

(** **** Initialize the resource environment *)
Definition init_locals (W : t) (V : 𝐕) : 𝐕 :=
  SRE.init_readers (readers W) (RM.init_writers (writers W)  V).

(** **** Update the resource environment 

  For each instant, the resource environment is updated at the end. Each local resources may have a new initial term for the next instant. We defined [update_locals] which takes a stock [W] and a resource environment [V] and produces a new stock.
*)
Definition update_locals_readers (W: t) (V: 𝐕) :=
  SRE.Raw.fold (fun rr v acc => match RM.find_data rr (writers W) with
                        | None => (⌈rr ⤆ v⌉ acc)%sr
                        | Some rw => match V⌊rw⌋ with
                                      | Some (⩽ … v' ⩾) =>  (⌈rr ⤆ v'⌉ acc)%sr
                                      | _ => (⌈rr ⤆ v⌉ acc)%sr
                                     end
                       end) (readers W) (∅%sr).

Definition update_locals (W : t) (V : 𝐕) : t := 
  (SRE.update_readers (readers W) V, writers W).

(** **** Add *)
Definition add (rr rw : resource) (v : Λ) (W : t) : t :=
  (⌈ rr ⤆ v ⌉ (readers W),(⌈rw ⤆ rr⌉ (writers W))%rm)%sr.

(** **** Union

  The union between two stocks is the point-to-point union between each component.
*)
Definition union (W W' : t) := ((readers W ∪ readers W')%sr, (writers W ∪ writers W')%rm).

(** **** In

  A resource name is in the stock if it is, at least, in one member of the stock.
*)
Definition In (r : resource) (W : t) := (r ∈ readers W)%sr \/ (r ∈ writers W)%rm.

(** **** Find *)
Definition find (r : resource) (W : t) := (readers W) ⌊r⌋%sr.

(** **** Halts

  In the functional transition proofs, we assume that all elements in the input resource environment halts. The resource environment depends on the stock for its initialization in the temporal transition. Consequently, we also need to define the halts property on the stock.
*)
Definition halts (k : lvl) (W : t) := SRE.halts k (readers W).

(** **** New key *)

Definition new_key (W : t) := max ((readers W)⁺)%sr ((writers W)⁺)%rm.

(** **** Domain equality with [RContext] *)

Definition eqDom (Rc : ℜ) (W: t) := forall (r : resource), (r ∈ Rc)%rc <-> In r W.

(** *** Properties *)

(** **** [Empty] properties *)

Lemma Empty_empty : Empty empty.
Proof.
  split; simpl.
  - apply SRE.empty_1.
  - now apply RM.empty_1.
Qed.

Lemma Empty_is_empty (t : t) : Empty t <-> is_empty t = true.
Proof.
  destruct t; unfold Empty, is_empty; simpl; split.
  - intros [HE HE'].
    apply SRE.is_empty_1 in HE; rewrite HE.
    now apply RM.is_empty_1 in HE'; rewrite HE'.
  - rewrite andb_true_iff. 
    intros [HE HE'].
    apply SRE.is_empty_2 in HE.
    apply RM.is_empty_2 in HE'.
    now split.
Qed. 

Lemma not_Empty_is_empty (t : t) : ~ Empty t <-> is_empty t = false.
Proof.
  split.
  - intro HE.
    apply not_true_is_false; intro Hc.
    apply HE.
    now rewrite Empty_is_empty.
  - intros HE Hc.
    revert HE.
    apply eq_true_false_abs. 
    now rewrite <- Empty_is_empty.
Qed. 

Lemma Empty_notin (t : t) : (forall r, ~ In r t) -> Empty t.
Proof.
  intros HnIn.
  destruct t as [rt wt]; unfold In, Empty in *; simpl in *.
  split.
  - intros k v HM.
    apply (HnIn k); left.
    now exists v.
  - intros k v HM.
    apply (HnIn k); right.
    now exists v.
Qed.

Lemma Empty_notin_1 (r : resource) (t : t) : Empty t -> ~ In r t.
Proof.
  unfold Empty, In; destruct t as [rt wt]; simpl.
  intros [HEmp HEmp'] [[v HM] | [v HM]].
  - apply (HEmp r v HM). 
  - apply (HEmp' r v HM).
Qed.

Lemma Empty_unfold (t: t) : Empty t -> ~(exists r, In r t).
Proof.
  intros HEmp [].
  revert H.
  now apply Empty_notin_1.
Qed.

(** **** [init_locals] properties *)

Lemma init_locals_in_iff (r : resource) (W : t) (V : 𝐕) :
  (r ∈ (init_locals W V))%re <-> In r W \/ (r ∈ V)%re.
Proof.
  split; unfold init_locals, In; destruct W as [rW wW]; simpl.
  - intro HIn. 
    apply SRE.init_readers_in_iff in HIn as [| HIn]; auto.
    apply RM.init_writers_in_iff in HIn as [|]; auto.
  - intro HIns. 
    apply SRE.init_readers_in_iff.
    rewrite RM.init_writers_in_iff.
    destruct HIns as [[HIn | HIn] | HIn]; auto.
Qed.

Lemma init_locals_find (r : resource) (v : 𝑣) (W : t) (V : 𝐕) :
 (init_locals W V)⌊r⌋%re = Some v -> In r W \/ V⌊r⌋%re = Some v.
Proof.
  unfold init_locals, In; destruct W as [rW wW]; simpl; intro Hfi. 
  apply SRE.init_readers_find in Hfi as [| Hfi]; auto.
  apply RM.init_writers_find in Hfi as [|]; auto.
Qed.

Lemma init_locals_find_1 (r : resource) (v : 𝑣) (W : t) (V : 𝐕) :
 (init_locals W V)⌊r⌋%re = Some v -> 
 (readers W)⌊r⌋%sr = Some (Cell.extract v) \/ 
 (RM.init_writers (writers W) V)⌊r⌋%re = Some v.
Proof.
  unfold init_locals, In; destruct W as [rW wW]; simpl; intro Hfi. 
  apply SRE.init_readers_find_1 in Hfi as [| Hfi]; auto; right.
Qed.

Lemma init_locals_find_inp (rs : t) (V : 𝐕) (r : resource) (v : 𝑣) :
  (forall r, V⌊r⌋%re = Some v -> exists v', Logic.eq v (Cell.inp v')) ->
  ((init_locals rs V)⌊r⌋)%re = Some v -> exists v', Logic.eq v (Cell.inp v'). 
Proof.
  unfold init_locals; intros Ht Hfi.
  apply SRE.init_readers_find_inp in Hfi; auto.
  intros r' HfV.
  apply RM.init_writers_find_inp in HfV; auto.
Qed.

Lemma init_locals_in_unused (W : t) (V : 𝐕) (r : resource) :
  In r W -> RE.unused r (init_locals W V).
Proof.
  intro HIn; unfold In, init_locals in *; destruct W as [Rw Ww].
  destruct HIn as [HIn | HIn]; simpl in *.
  - now apply SRE.init_readers_in_unused.
  - apply SRE.init_readers_unused. 
    now apply RM.init_writers_in_unused.
Qed.

Lemma init_locals_unused (r : resource) (W : t) (V : 𝐕) :
  RE.unused r V -> RE.unused r (Stock.init_locals W V).
Proof.
  unfold Stock.init_locals; intro Hunsd.
  apply SRE.init_readers_unused.
  now apply RM.init_writers_unused.
Qed.

Lemma init_locals_new_key (V : 𝐕) (t : t) : ((init_locals t V)⁺)%re = max (new_key t) (V⁺)%re.
Proof.
  destruct t; unfold init_locals, new_key; simpl.
  rewrite SRE.init_readers_new_key.
  rewrite RM.init_writers_new_key.
  lia.
Qed.

(** **** [update_locals] properties *)

Lemma update_locals_in_iff (r : resource) (W : t) (V : 𝐕) :
  In r (update_locals W V) <-> In r W.
Proof.
  split; unfold init_locals, In; destruct W as [rW wW]; simpl.
  - intros [HIn |]; auto. 
    apply SRE.update_readers_in_iff in HIn; auto.
  - intros [HIn |]; auto; left. 
    now apply SRE.update_readers_in_iff.
Qed.

Lemma update_locals_Empty (t: t) (V: 𝐕) :
  Empty (update_locals t V) <-> Empty t.
Proof.
  unfold update_locals, Empty.
  destruct t as [rt wt]; simpl; split.
  - intros [HEmp ]; split; auto.
    now rewrite (SRE.update_readers_Empty' _ V).
  - intros [HEmp ]; split; auto.
    now apply SRE.update_readers_Empty.
Qed.

Lemma update_locals_new_key (V : 𝐕) (t : t) :
  new_key (update_locals t V) = new_key t.
Proof.
  destruct t; unfold update_locals, new_key; simpl.
  rewrite SRE.update_readers_new_key.
  lia.
Qed.

Lemma update_locals_Wf (k: lvl) (V : 𝐕) (W: t) :
  Wf k W /\ (k ⊩ V)%re -> Wf k (update_locals W V).
Proof.
  destruct W as [rW wW].
  unfold Wf, update_locals; simpl.
  intros [[Hwfr Hwfw] HwfV].
  split; auto.
  apply SRE.update_readers_Wf; auto.
Qed.

Lemma update_locals_find (r: resource) (v: Λ) (V: 𝐕) (W: t) :
  find r (update_locals W V) = Some v ->
  find r W = Some v \/ V⌊r⌋%re = Some (Cell.out v).
Proof.
  unfold find, update_locals.
  destruct W as [rW wW]; simpl.
  apply SRE.update_readers_find.
Qed.

(** **** [In] properties  *)

Lemma empty_in (r : resource) : ~ In r empty.
Proof.
  unfold In, empty; simpl; intros [HIn | HIn].
  - revert HIn; apply SRE.not_in_empty.
  - revert HIn; apply RM.not_in_empty.
Qed.

Lemma add_in_iff (r r' k : resource) (v : Λ) (W : t) :
  In k (add r r' v W) <-> k = r \/ k = r' \/ In k W.
Proof.
  unfold add, In; destruct W as [rw wW]; simpl; split.
  - intros [HIn | HIn].
    -- destruct (Resource.eq_dec k r) as [| Hneq]; subst; auto. 
       rewrite SRE.add_neq_in_iff in HIn; auto.
    -- destruct (Resource.eq_dec k r') as [| Hneq]; subst; auto. 
       rewrite RM.add_neq_in_iff in HIn; auto.
  - rewrite SRE.add_in_iff; rewrite RM.add_in_iff.
    intros [Heq | [Heq | [HIn | HIn]]]; subst; auto.
Qed.

Lemma union_in_iff (r : resource) (W W' : t) : 
  In r (union W W') <-> In r W \/ In r W'.
Proof.
  unfold In,union; destruct W,W'; simpl.
  rewrite SRE.extend_in_iff; rewrite RM.extend_in_iff.
  split; intros [[|] | [|]]; auto.
Qed.

Lemma In_dec (r: resource) (W: t) : {In r W} + {~ In r W}.
Proof.
  destruct W as [rW wW]; unfold In; simpl.
  destruct (SRE.In_dec rW r) as [HInrW | HnInrW];
  destruct (RM.In_dec wW r) as [HInwW | HnInwW]; auto.
  right; intros [|]; auto.
Qed.

Lemma Empty_union (t1 t2: t) : Empty (union t1 t2) <-> (Empty t1) /\ (Empty t2).
Proof.
  split.
  - intros HEmp.
    apply Empty_unfold in HEmp; split.
    -- apply Empty_notin; intros r HIn.
       apply HEmp.
       exists r.
       rewrite union_in_iff; auto.
    -- apply Empty_notin; intros r HIn.
       apply HEmp.
       exists r.
       rewrite union_in_iff; auto.
  - intros [HEmp1 HEmp2].
    apply Empty_unfold in HEmp1,HEmp2.
    apply Empty_notin.
    intros r HIn.
    apply union_in_iff in HIn as [|].
    -- apply HEmp1.
       now exists r.
    -- apply HEmp2.
       now exists r.
Qed.

(** **** [find] properties *)

Lemma find_union (r : resource) (v : Λ) (W W' : t) :
  find r (union W W') = Some v -> find r W = Some v \/ find r W' = Some v.
Proof.
  unfold find, union; destruct W,W'; simpl; intro HM.
  apply SRE.find_2 in HM. 
  apply SRE.extend_mapsto_iff in HM as [HM | [HM _]];
  apply SRE.find_1 in HM; auto.
Qed.

Lemma find_add_eq (r r': resource) (v: Λ) (W: t) :
  find r (add r r' v W) = Some v.
Proof.
  unfold find, add; destruct W; simpl.
  now apply SRE.add_eq_o.
Qed. 

Lemma find_add_neq (r r' r'': resource) (v: Λ) (W: t) :
  r <> r'' -> find r'' (add r r' v W) = find r'' W.
Proof.
  unfold find, add; destruct W; simpl; intro.
  now apply SRE.add_neq_o.
Qed. 


(** **** [Wf] poperties *)

Lemma Wf_empty (k : lvl) : Wf k empty.
Proof.
  unfold Wf, empty; simpl; split.
  - apply SRE.Wf_empty.
  - apply RM.Wf_empty.
Qed.

Lemma Wf_Empty (k : lvl) (t : t) : Empty t -> Wf k t.
Proof.
  unfold Wf, Empty; destruct t; simpl; split.
  - destruct H.
    now apply SRE.Wf_Empty.
  - destruct H.
    now apply RM.Wf_Empty.
Qed.

Lemma Wf_add (k : lvl) (r r' : resource) (v : Λ) (W : t) :
  (k ⊩ r)%r -> (k ⊩ r')%r -> (k ⊩ v)%tm -> Wf k W -> Wf k (add r r' v W).
Proof.
  unfold Wf; destruct W as [rW wW]; simpl. 
  intros Hvr Hvr' Hvv [HvrW HvwW]; split.
  - apply SRE.Wf_add; auto.
  - apply RM.Wf_add; auto.
Qed.

Lemma Wf_union (k : lvl) (W W' : t) :
  Wf k W /\ Wf k W' -> Wf k (union W W').
Proof.
  unfold Wf; destruct W,W'; simpl. 
  intros [[HvrW HvwW] [HvrW' HvwW']]; split.
  - apply SRE.Wf_extend; auto.
  - apply RM.Wf_extend; auto.
Qed.

Lemma Wf_in (k : lvl) (r : resource) (W : t) :
  In r W -> Wf k W -> (k ⊩ r)%r.
Proof.
  unfold In, Wf; destruct W as [rW wW]; simpl.
  intros [HIn | HIn] [HvrW HvwW].
  - eapply SRE.Wf_in in HIn; eauto.
  - eapply RM.Wf_in; eauto.
Qed.

Lemma Wf_in_iff (m n k : lvl) (W : t) :
  Wf m W -> In k (shift m n W) <-> In k W.
Proof.
  unfold Wf, shift, In; destruct W as [rW wW]; simpl.
  intros [Hvr Hvw]; split; intros [HIn | HIn].
  - now left; rewrite SRE.Wf_in_iff in HIn.
  - now right; rewrite RM.Wf_in_iff in HIn.
  - now left; rewrite SRE.Wf_in_iff.
  - now right; rewrite RM.Wf_in_iff.
Qed.

Lemma init_locals_Wf (k : lvl) (V : 𝐕) (t : t) :
  Wf k t /\ (k ⊩ V)%re -> (k ⊩ init_locals t V)%re.
Proof.
  destruct t as [rW wW]. 
  intros [[HvrW HvrwW] HvV].
  simpl in *. unfold init_locals.
  apply SRE.init_readers_Wf; simpl; split; auto.
  apply RM.init_writers_Wf; simpl; split; auto.
Qed.

(** **** [new_key] properties *)

Lemma new_key_empty : new_key empty = 0.
Proof.
  unfold new_key, empty.
  simpl (readers (∅, ∅%rm) ⁺)%sr.
  simpl (writers (∅%sr, ∅) ⁺)%rm.
  rewrite SRE.Ext.new_key_empty. 
  rewrite RM.Ext.new_key_empty.
  now simpl. 
Qed.

Lemma new_key_Empty (t : t) : Empty t -> new_key t = 0.
Proof.
  destruct t; intros []; simpl in *.
  unfold new_key; simpl.
  rewrite SRE.Ext.new_key_Empty; auto.
  rewrite RM.Ext.new_key_Empty; auto.
Qed.

Lemma new_key_in (r: lvl) (t : t) : 
  In r t -> (r < new_key t)%nat.
Proof.
  destruct t as [rt wt].
  unfold In, new_key; simpl.
  intros [HIn | HIn].
  - apply SRE.Ext.new_key_in in HIn; lia.
  - apply RM.Ext.new_key_in in HIn; lia.
Qed.

Lemma new_key_union (t1 t2: t) :
  new_key (union t1 t2) = max (new_key t1) (new_key t2).
Proof.
  unfold new_key, union; destruct t1, t2; simpl.
  rewrite SRE.extend_new_key.
  rewrite RM.extend_new_key.
  lia.
Qed.

Lemma new_key_Wf (k: lvl) (t: t) : Wf k t -> new_key t <= k.
Proof.
  unfold Wf, new_key; destruct t; simpl.
  intros [Hwf Hwf'].
  apply SRE.new_key_Wf in Hwf.
  apply RM.new_key_Wf in Hwf'.
  lia.
Qed. 

Lemma new_key_add_max (m n: lvl) (v: Λ) (t: t) : 
  new_key (add m n v t) = max (S m) (max (S n) (new_key t)).
Proof.
  destruct t; unfold new_key, add. 
  simpl (readers (⌈ m ⤆ v ⌉ readers (t0, t1), (⌈n ⤆ m⌉  writers (t0, t1))%rm))%sr.
  simpl (writers ((⌈ m ⤆ v ⌉ readers (t0, t1))%sr, (⌈n ⤆ m⌉  writers (t0, t1))%rm)).
  simpl (readers (t0, t1)).
  simpl (writers (t0, t1)).
  rewrite SRE.Ext.new_key_add_max.
  rewrite RM.Ext.new_key_add_max; lia.
Qed.


(** **** [shift] properties *)


Lemma shift_new_refl (lb k : lvl) (t : t) :
  lb >= (new_key t) -> new_key (shift lb k t) = new_key t.
Proof.
  unfold new_key, shift; destruct t; simpl.
  intro Hgeq.
  rewrite SRE.shift_new_refl; try lia.
  rewrite RM.shift_new_refl; lia.
Qed.

Lemma shift_in_iff (m n : lvl) (r : resource) (W : t) :
  In r W <-> In ([⧐ m – n] r)%r (shift m n W).
Proof.
  unfold In, shift; destruct W as [rW wW]; simpl; 
  split; intros [HIn | HIn].
  - left. now apply SRE.shift_in_iff.
  - right; now apply RM.shift_in_iff.
  - left. rewrite SRE.shift_in_iff; eauto.
  - right; rewrite RM.shift_in_iff; eauto.
Qed.

Lemma shift_in_e (m n : lvl) (r : resource) (W : t) :
  In r (shift m n W) -> exists r', (r =  ([⧐ m – n] r')%r)%type.
Proof.
  unfold In,shift; destruct W as [rW wW]; simpl; intros [HIn | HIn].
  - apply SRE.shift_in_e in HIn; auto.
  - apply RM.shift_in_e in HIn; auto.
Qed.

Lemma shift_Empty_iff (m n: lvl) (W: t) :
  Empty W <-> Empty (shift m n W).
Proof.
  split; intro HEmp.
  - apply Empty_unfold in HEmp.
    apply Empty_notin; intros r HIn.
    apply shift_in_e in HIn as HI.
    destruct HI as [r']; subst.
    rewrite <- shift_in_iff in HIn.
    apply HEmp.
    now exists r'.
  - apply Empty_unfold in HEmp.
    apply Empty_notin; intros r HIn.
    rewrite (shift_in_iff m n) in HIn.
    apply HEmp.
    now exists ([⧐m – n] r)%r.
Qed.

Lemma shift_new_key_in_iff (n : lvl) (x : resource) (t : t) :
  In x (shift (new_key t) n t) <-> In x t.
Proof.
  split; intro HIn.
  - apply shift_in_e in HIn as H.
    destruct H as [y Heq]; subst.
    rewrite <- shift_in_iff in HIn.
    apply new_key_in in HIn as Hlt.
    rewrite Resource.shift_wf_refl; auto.
  - apply new_key_in in HIn as Hlt.
    rewrite <- (Resource.shift_wf_refl (new_key t) n x); auto.
    now rewrite <- shift_in_iff.
Qed.

Lemma shift_find_iff (k n : lvl) (r: resource) v (t : t) :
  find r t = Some v <-> find ([⧐ k – n] r)%r (shift k n t) = Some (<[[⧐ k – n] v]>)%tm.
Proof.
  unfold shift, find; destruct t; simpl.
  apply SRE.shift_find_iff.
Qed.

Lemma shift_find_e_1 (k n : lvl) (r: resource) v (t : t) :
  find r (shift k n t) = Some v -> (exists r', (r = ([⧐ k – n] r')%r)%type) /\
                                   (exists v', (v = <[[⧐ k – n] v']>%tm)%type).
Proof.
  unfold find, shift; destruct t; simpl.
  intros Hfi.
  apply SRE.shift_find_e_1 in Hfi; auto.
Qed.

(** **** [halts] properties *)

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
  apply SRE.halts_init_readers; auto.
  now apply RM.halts_init_writers.
Qed.

Lemma halts_update_locals (k : lvl) (W : t) (V : 𝐕) :
  RE.halts k V -> halts k W -> halts k (update_locals W V).
Proof.
  intros HltV HltW; unfold halts,update_locals.
  destruct W as [Rw Ww]; simpl.
  apply SRE.halts_update_readers; auto.
Qed.

Lemma halts_weakening (m n : lvl) (W : t) : 
  m <= n -> halts m W -> halts n (shift m (n - m) W).
Proof.
  unfold halts, shift; destruct W as [rW wW]. 
  simpl; intros Hle HvrW.
  now apply SRE.halts_weakening.
Qed.

Lemma halts_union (k : lvl) (W W' : t) :
  halts k W /\ halts k W' -> halts k (union W W').
Proof.
  unfold halts; destruct W,W'; simpl; intro Hlt. 
  now apply SRE.halts_union.
Qed.

Lemma halts_add (k : lvl) (r r' : resource) (v : Λ) (W : t) :
  (Evaluation_Transition.halts k v) /\ halts k W -> halts k (add r r' v W).
Proof.
  unfold halts, add; destruct W as [rW wW]; simpl; intro Hv.
  now apply SRE.halts_add.
Qed.

Lemma halts_Empty (k: resource) (t: t) : Empty t -> halts k t.
Proof.
  destruct t as [rt wt]; unfold Empty, halts; simpl.
  intros [HEmp _].
  now apply SRE.halts_Empty.
Qed.

(** **** Morphisms *)


#[export] Instance stock_in_iff : Proper (Logic.eq ==> eq ==> iff) In.
Proof.
  unfold eq, In; intros k' k Heqk W W' Heqst; subst.
  destruct W,W'; repeat red in Heqst; unfold RelationPairs.RelCompFun in Heqst;
  simpl in *; destruct Heqst as [HeqR HeqW].
  now rewrite HeqR, HeqW.
Qed.

#[export] Instance stock_find_eq : Proper (Logic.eq ==> eq ==> Logic.eq) find.
Proof.
  unfold find, eq; intros k' k Heqk W W' Heqst; subst.
  destruct W,W'; repeat red in Heqst; unfold RelationPairs.RelCompFun in Heqst;
  simpl in *; destruct Heqst as [HeqR HeqW].
  now rewrite HeqR.
Qed.

#[export] Instance stock_add_eq : Proper (Resource.eq ==> Resource.eq ==> Term.eq ==> eq ==> eq) add.
Proof.
  unfold eq, add.
  intros r' r Heqr r1' r1 Heqr1 d d' Heqd W W' Heqst; destruct W,W'. 
  repeat red in Heqst; repeat red; unfold RelationPairs.RelCompFun in *; simpl in *. 
  destruct Heqst as [HeqR HeqW]; rewrite Heqr, Heqr1, Heqd; split.
  - now intro y; rewrite HeqR.
  - now rewrite HeqW.
Qed. 

#[export] Instance stock_new_key_eq : Proper (eq ==> Logic.eq) new_key.
Proof.
  intros [rt1 wt1] [rt2 wt2] Heq.
  repeat red in Heq; unfold RelationPairs.RelCompFun in Heq; simpl in *.
  destruct Heq as [Heqr Heqw].
  unfold new_key; simpl.
  now rewrite Heqr, Heqw.
Qed.

#[export] Instance stock_Empty_iff : Proper (eq ==> iff) Empty.
Proof.
  intros [rx wx] [ry wy] [Hreq Hweq].
  unfold RelationPairs.RelCompFun,Empty in *; simpl in *.
  rewrite Hreq, Hweq; split; auto.
Qed.

(** **** [eqDom] properties *)

#[export] Instance eqDom_iff : Proper (RC.eq ==> eq ==> iff) eqDom.
Proof.
  intros Rc Rc1 HeqRc W W1 HeqW; unfold eqDom; split; intros.
  - rewrite <- HeqRc; rewrite <- HeqW; auto.
  - rewrite HeqRc; rewrite HeqW; auto.
Qed.

Lemma eqDom_In (r: resource) (Rc: ℜ) (W: t) :
  eqDom Rc W -> (r ∈ Rc)%rc <-> In r W.
Proof. unfold eqDom; intro HeqDom; auto. Qed.

Lemma eqDom_Empty (Rc : ℜ) (W: t):
 eqDom Rc W -> (isEmpty(Rc))%rc <-> Empty W.
Proof.
  intro HeqDom; split; intro HEmp.
  - apply Empty_notin; intros r HIn.
    rewrite <- (eqDom_In r Rc) in HIn; auto.
    destruct HIn as [v HM].
    now apply (HEmp r v).
  - apply Empty_unfold in HEmp.
    intros x v HM. 
    apply HEmp.
    exists x.
    rewrite <- (eqDom_In x Rc); auto.
    now exists v.
Qed.

Lemma eqDom_is_empty (Rc : ℜ) (W: t):
  eqDom Rc W -> RC.Raw.is_empty Rc = is_empty W.
Proof.
  intro HeqDom.
  destruct (RC.Raw.is_empty Rc) eqn:HisEmp;
  destruct (is_empty W) eqn:HisEmp'; auto; exfalso.
  - apply RC.is_empty_2 in HisEmp.
    rewrite (eqDom_Empty _ W) in HisEmp; auto.
    now apply not_Empty_is_empty in HisEmp'.
  - apply Empty_is_empty in HisEmp'.
    rewrite <- eqDom_Empty in HisEmp'; eauto.
    apply RC.is_empty_1 in HisEmp'.
    rewrite HisEmp in *. inversion HisEmp'.
Qed.

Lemma eqDom_new_key (Rc : ℜ) (W: t):
  eqDom Rc W -> Rc⁺%rc = new_key W.
Proof.
  revert W; induction Rc using RC.map_induction; intros W HeqDom.
  - rewrite RC.Ext.new_key_Empty; auto.
    rewrite (eqDom_Empty Rc W HeqDom) in H.
    rewrite new_key_Empty; auto.
  - unfold RC.Add in H0; rewrite H0 in *; clear H0.
    rewrite RC.Ext.new_key_add_max.

    destruct W as [rW wW]; unfold eqDom,In, new_key in *.
    simpl in HeqDom.
    simpl (readers (rW, wW)⁺)%sr.
    simpl (writers (rW, wW)⁺)%rm.

    assert (HIn: (x ∈ ⌈ x ⤆ e ⌉ Rc1)%rc).
    { rewrite RC.add_in_iff; auto. }

    apply HeqDom in HIn as HIn'.
    destruct HIn' as [[v HM] | [v' HM']].
    -- apply SRE.find_1 in HM.
       apply SRE.add_id in HM; rewrite <- HM; clear HM.
       rewrite <- SRE.add_remove_1.
       rewrite SRE.Ext.new_key_add_max.

       destruct (RM.In_dec wW x) as [[v' HM'] | HnInw].
       + apply RM.find_1 in HM'.
         apply RM.add_id in HM'; rewrite <- HM'; clear HM'.
         rewrite <- RM.add_remove_1.
         rewrite RM.Ext.new_key_add_max.
         rewrite (IHRc1 (SRE.Raw.remove x rW, RM.Raw.remove x wW)).
         ++ simpl (readers (SRE.Raw.remove x rW, RM.Raw.remove x wW)).
            simpl (writers (SRE.Raw.remove x rW, RM.Raw.remove x wW)).
            lia.
         ++ intro r; split; simpl.
            * intro HInRc1.
              destruct (Resource.eq_dec r x); subst; try contradiction.
              rewrite SRE.remove_in_iff.
              rewrite RM.remove_in_iff.
              rewrite <- RC.add_neq_in_iff in HInRc1; eauto.
              apply HeqDom in HInRc1 as [|]; auto.
            * rewrite SRE.remove_in_iff.
              rewrite RM.remove_in_iff.
              intros [[Hneq HInr] | [HInw Hneq]].
              ** rewrite <- RC.add_neq_in_iff; eauto.
                 rewrite HeqDom; auto.
              ** rewrite <- RC.add_neq_in_iff; eauto.
                 rewrite HeqDom; auto.
       + rewrite (IHRc1 (SRE.Raw.remove x rW, wW)).
         ++ simpl (readers (SRE.Raw.remove x rW, wW)).
            simpl (writers (SRE.Raw.remove x rW, wW)).
            lia.
         ++ intro r; split; simpl.
            * intro HInRc1.
              destruct (Resource.eq_dec r x); subst; try contradiction.
              rewrite SRE.remove_in_iff.
              rewrite <- RC.add_neq_in_iff in HInRc1; eauto.
              apply HeqDom in HInRc1 as [|]; auto.
            * rewrite SRE.remove_in_iff.
              intros [[Hneq HInr] | HInw].
              ** rewrite <- RC.add_neq_in_iff; eauto.
                 rewrite HeqDom; auto.
              ** destruct (Resource.eq_dec r x); subst; try contradiction.
                 rewrite <- RC.add_neq_in_iff; eauto.
                 rewrite HeqDom; auto.
    -- apply RM.find_1 in HM'.
       apply RM.add_id in HM'; rewrite <- HM'; clear HM'.
       rewrite <- RM.add_remove_1.
       rewrite RM.Ext.new_key_add_max.

       destruct (SRE.In_dec rW x) as [HInr | HnInr].

       + destruct HInr as [v HM].
         apply SRE.find_1 in HM.
         apply SRE.add_id in HM; rewrite <- HM; clear HM.
         rewrite <- SRE.add_remove_1.
         rewrite SRE.Ext.new_key_add_max.
         rewrite (IHRc1 (SRE.Raw.remove x rW, RM.Raw.remove x wW)).
         ++ simpl (readers (SRE.Raw.remove x rW, RM.Raw.remove x wW)).
            simpl (writers (SRE.Raw.remove x rW, RM.Raw.remove x wW)).
            lia.
         ++ intro r; split; simpl.
            * intro HInRc1.
              destruct (Resource.eq_dec r x); subst; try contradiction.
              rewrite SRE.remove_in_iff.
              rewrite RM.remove_in_iff.
              rewrite <- RC.add_neq_in_iff in HInRc1; eauto.
              apply HeqDom in HInRc1 as [|]; auto.
            * rewrite SRE.remove_in_iff.
              rewrite RM.remove_in_iff.
              intros [[Hneq HInr] | [HInw Hneq]].
              ** rewrite <- RC.add_neq_in_iff; eauto.
                 rewrite HeqDom; auto.
              ** rewrite <- RC.add_neq_in_iff; eauto.
                 rewrite HeqDom; auto.
       + rewrite (IHRc1 (rW, RM.Raw.remove x wW)).
         ++ simpl (readers (rW, RM.Raw.remove x wW)).
            simpl (writers (rW, RM.Raw.remove x wW)).
            lia.
         ++ intro r; split; simpl.
            * intro HInRc1.
              destruct (Resource.eq_dec r x); subst; try contradiction.
              rewrite RM.remove_in_iff.
              rewrite <- RC.add_neq_in_iff in HInRc1; eauto.
              apply HeqDom in HInRc1 as [|]; auto.
            * rewrite RM.remove_in_iff.
              intros [HInr | [Hneq HInw]].
              ** destruct (Resource.eq_dec r x); subst; try contradiction.
                 rewrite <- RC.add_neq_in_iff; eauto.
                 rewrite HeqDom; auto.
              ** rewrite <- RC.add_neq_in_iff; eauto.
                 rewrite HeqDom; auto.
Qed.

End Stock.

(** ---- *)

(** ** Notation - Virtual Resource Environment *)

Module StockNotations.

(** *** Scope *)
Declare Scope stock_scope.
Delimit Scope stock_scope with sk.

(** *** Notations *)
Definition 𝐖 := Stock.t.

Infix "∈" := Stock.In (at level 60, no associativity) : stock_scope. 
Notation "r '∉' t" := (~ (Stock.In r t)) (at level 75, no associativity) : stock_scope. 
Notation "t '⁺'" := (Stock.new_key t) (at level 16) : stock_scope.
Notation "∅" := Stock.empty (at level 0, no associativity) : stock_scope. 
Notation "t '⌊' x '⌋'"  := (Stock.find x t) (at level 15, x constr) : stock_scope.
Notation "⌈ x '~' x1 ⤆ v '⌉' t"  := (Stock.add x x1 v t) 
                                     (at level 15, x constr, v constr) : stock_scope.
Notation "'[⧐' lb '–' k ']' t" := (Stock.shift lb k t) 
                                   (at level 65, right associativity) : stock_scope.

Infix "=" := Stock.eq : stock_scope.
Infix "∪" := Stock.union : stock_scope.
Infix "⊩" := Stock.Wf (at level 20, no associativity) : stock_scope.

(** *** Morphisms *)

Import Stock.

#[export] Instance stock_shift_eq : Proper (Resource.eq ==> Resource.eq ==> eq ==> eq) shift := _.

#[export] Instance stock_Wf_iff : Proper (Resource.eq ==> eq ==> iff) Wf := _.

#[export] Instance stock_halts_iff: Proper (Logic.eq ==> eq ==> iff) halts := _.

#[export] Instance stock_in_iff : Proper (Logic.eq ==> eq ==> iff) In := _.

#[export] Instance stock_find_eq : Proper (Logic.eq ==> eq ==> Logic.eq) find := _.

#[export] Instance stock_add_eq : 
  Proper (Resource.eq ==> Resource.eq ==> Term.eq ==> eq ==> eq) add := _.

#[export] Instance stock_new_key_eq : Proper (eq ==> Logic.eq) new_key := _.

#[export] Instance stock_Empty_iff : Proper (eq ==> iff) Empty := _.

#[export] Instance stock_eqDom_iff : Proper (RC.eq ==> eq ==> iff) eqDom := _.

End StockNotations.