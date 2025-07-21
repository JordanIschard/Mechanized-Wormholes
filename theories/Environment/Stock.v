From Coq Require Import Lia List Arith.
From Mecha Require Import Resource Term Triplet Evaluation_Transition REnvironment
                          Cell.
From DeBrLevel Require Import LevelInterface ListLevel.
From MMaps Require Import MMaps.
Import ResourceNotations TermNotations ListNotations REnvironmentNotations
       CellNotations.

Module Stock <: IsLvlET.

Include IsLvlListETWL Triplet.

Definition halts (m : lvl) (st : t) :=
 List.Forall (fun (tp: Triplet.t) =>  let (_,v) := tp 
                                      in Evaluation_Transition.halts m v) st.

Definition keys (st : t) :=
 fold_right (fun '((rg,rs),_) acc => rg :: rs :: acc) [] st.

Definition max_key (st : t) :=
  fold_right (fun '((rg,rs),_) acc => max (max rg rs) acc) 0 st.

Definition new_key (st : t) :=
  match st with
    | [] => 0
    | _  => (max_key st) + 1
  end.

Fixpoint init_locals (st : t) (V : 𝐕) : 𝐕 :=
  match st with
    | [] => V
    | (r,r',v) :: st' => (⌈r ⤆ ⩽ v … ⩾⌉(⌈r' ⤆ ⩽ unit … ⩾⌉ (init_locals st' V)))%re
  end.

Fixpoint update_locals (st : t) (V : 𝐕) : t :=
  match st with
    | [] => []
    | (r,r',v) :: st' =>  match (V⌊r'⌋)%re with
                            | Some (⩽ … v' ⩾) =>  (r,r',v') :: (update_locals st' V)
                            | _ => (r,r',v) :: (update_locals st' V)
                          end
  end.

Lemma halts_nil (m : lvl) : halts m [].
Proof. 
  unfold halts.
  constructor.
Qed.

Lemma halts_app (m : lvl) (st st' : t) :
  halts m (st ++ st') <-> halts m st /\ halts m st'.
Proof.
  unfold halts.
  apply Forall_app.
Qed.

Lemma halts_weakening (m n : lvl) (st : t) : 
  m <= n -> halts m st -> halts n (shift m (n - m) st).
Proof.
  intro Hle.
  induction st; intro Hlt.
  - simpl.
    constructor.
  - simpl in *.
    inversion Hlt; subst.
    destruct a as [[rg rs] v].
    constructor; simpl.
    -- now apply Evaluation_Transition.halts_weakening.
    -- now apply IHst.
Qed.


Lemma keys_in_app (r : resource) (st st' : t) :
  In r (keys (st ++ st')) <-> In r (keys st) \/ In r (keys st').
Proof.
  revert r st'; induction st; intros r st'.
  - simpl; split; auto.
    intros [|]; auto.
    inversion H.
  - destruct a as [[rg rs] v]; simpl; split.
    -- intros [|[|HIn]]; subst; auto.
       apply IHst in HIn; destruct HIn; auto.
    -- intros [[|[|]]|]; subst; auto.
       + do 2 right.
         apply IHst; auto.
       + do 2 right.
         apply IHst; auto.
Qed.

(* Lemma shift_in (m n : lvl) (tp : Triplet.t) (st : t) :
  In tp st <-> In (Triplet.shift m n tp) (shift m n st).
Proof.
  revert r; induction st; simpl; intro r.
  - split; auto.
  - destruct a as [[rg rs] v]; simpl; split.
    -- intros [|[|HIn]]; subst; auto.
       do 2 right.
       now apply IHst.
    -- intros [|[|HIn]].
       + apply Resource.shift_eq_iff in H; subst; auto.
       + apply Resource.shift_eq_iff in H; subst; auto.
       + apply IHst in HIn; auto.
Qed. *)


(* Lemma shift_in_e (m n : lvl) (tp : Triplet.t) (st : t) :
  In tp (shift m n st) -> exists tp', Logic.eq tp (Triplet.shift m n tp').
Proof.
  revert tp; induction st; simpl; intro tp.
  - intro Hc; inversion Hc.
  - destruct a as [[rg rs] v]; simpl. intros [| HIn]; subst.
    -- now exists (rg,rs,v).
    -- auto.
Qed. *)

Lemma keys_in_shift (m n : lvl) (r : resource) (st : t) :
  In r (keys st) <-> In ([⧐m – n] r)%r (keys (shift m n st)).
Proof.
  revert r; induction st; simpl; intro r.
  - split; auto.
  - destruct a as [[rg rs] v]; simpl; split.
    -- intros [|[|HIn]]; subst; auto.
       do 2 right.
       now apply IHst.
    -- intros [|[|HIn]].
       + apply Resource.shift_eq_iff in H; subst; auto.
       + apply Resource.shift_eq_iff in H; subst; auto.
       + apply IHst in HIn; auto.
Qed.

Lemma keys_in_shift_e (m n : lvl) (r : resource) (st : t) :
  In r (keys (shift m n st)) -> exists r', Logic.eq r ([⧐m – n] r')%r.
Proof.
  revert r; induction st; simpl; intro r.
  - intro Hc; inversion Hc.
  - destruct a as [[rg rs] v]; simpl; intros [|[| HIn]]; subst.
    -- now exists rg.
    -- now exists rs.
    -- auto.
Qed.

Lemma keys_in_new_key (r : resource) (st : t) :
  In r (keys st) -> r < (new_key st).
Proof.
  revert r; induction st; intro r.
  - simpl; lia.
  - destruct a as [[rg rs] v]; simpl.
    intros [|[|HIn]]; subst; try lia.
    apply IHst in HIn.
    destruct st.
    simpl in *; try lia.
    unfold new_key in HIn.
    lia.
Qed.


Lemma max_key_app (st st' : t) :
  max_key (st ++ st') = max (max_key st) (max_key st').
Proof.
  induction st.
  - now simpl.
  - destruct a as [[rg rs] v].
    simpl.
    rewrite IHst.
    lia.
Qed.

Lemma new_key_app (st st' : t) :
  new_key (st ++ st') = max (new_key st) (new_key st').
Proof.
  unfold new_key.
  destruct st.
  - now simpl.
  - destruct p as [[rg rs] v].
    simpl.
    rewrite max_key_app.
    destruct st'; simpl.
    -- lia.
    -- destruct p as [[rg' rs'] v'].
       lia.
Qed.

Lemma new_key_cons (r r' : resource) (v : Λ) (st : t) :
  new_key ((r,r',v) :: st) = max (r + 1) (max (r' + 1) (new_key st)).
Proof.
  destruct st.
  - simpl; lia.
  - destruct p as [[rg rs] v']; simpl; lia.
Qed. 

Lemma max_key_shift_refl (m n : lvl) (st : t) :
  m >= (new_key st) -> max_key (shift m n st) = max_key st.
Proof.
  induction st.
  - simpl; auto.
  - destruct a as [[rg rs] v]; simpl; intros.
    rewrite <- IHst.
    -- f_equal.
       rewrite Resource.shift_wf_refl.
       + rewrite Resource.shift_wf_refl; auto.
         unfold Resource.Wf; lia.
       + unfold Resource.Wf; lia.
    -- destruct st.
       + simpl; lia.
       + destruct p as [[rg' rs'] v']. simpl in *; lia.
Qed.

Lemma new_key_shift_refl (m n : lvl) (st : t) :
  m >= (new_key st) -> new_key (shift m n st) = new_key st.
Proof.
  destruct st.
  - now simpl.
  - destruct p as [[rg rs] v].
    simpl.
    intros.
    rewrite max_key_shift_refl; try lia.
    -- f_equal. f_equal.
       rewrite Resource.shift_wf_refl.
       + rewrite Resource.shift_wf_refl; auto.
         unfold Resource.Wf; lia.
       + unfold Resource.Wf; lia.
    -- destruct st; simpl; try lia.
       destruct p as [[rg' rs'] v'].
       simpl in *; lia.
Qed.

Lemma keys_in_shift_new_key (n : lvl) (r : resource) (st : t) :
  In r (keys (shift (new_key st) n st)) <-> In r (keys st).
Proof.
  split; intro HIn.
  - apply keys_in_shift_e in HIn as Heq.
    destruct Heq as [r' ]; subst.
    apply keys_in_shift in HIn.
    apply keys_in_new_key in HIn as Hlt.
    rewrite Resource.shift_wf_refl; auto.
  - apply keys_in_new_key in HIn as Hlt.
    rewrite <- (Resource.shift_wf_refl (new_key st) n r); auto.
    now rewrite <- keys_in_shift.
Qed.

Lemma NoDup_keys_app (st st' : t) :
  NoDup (keys st) -> NoDup (keys st') ->
  (forall r, In r (keys st') -> ~ In r (keys st)) ->
  NoDup (keys (st ++ st')).
Proof.
 revert st'; induction st; intros st' HNoD1 HNoD2 Hdisj.
 - now simpl.
 - destruct a as [[rg rs] v]; simpl in *.
   inversion HNoD1; subst. 
   simpl in *.
   inversion H2; subst.
   constructor.
   -- simpl; intros [| HIn]; subst.
      + apply H1; now left.
      + apply keys_in_app in HIn; destruct HIn as [HIn|HIn].
        ++ apply H1; auto.
        ++ apply Hdisj in HIn.
           apply HIn; auto.
   -- constructor.
      + intro HIn.
        apply keys_in_app in HIn; destruct HIn as [HIn|HIn].
        ++ auto.
        ++ apply Hdisj in HIn.
           apply HIn; auto.
      + apply IHst; auto.
        intros r HIn.
        apply Hdisj in HIn; auto.
Qed.

Lemma NoDup_keys_shift (m n : lvl) (st : t) :
  NoDup (keys st) -> NoDup (keys (shift m n st)).
Proof.
  induction st.
  - simpl; auto.
  - destruct a as [[rg rs] v]; simpl.
    intro HNoD.
    inversion HNoD; subst.
    inversion H2; subst.
    constructor.
    -- simpl; intros [|HIn].
       + apply Resource.shift_eq_iff in H; subst.
         apply H1.
         simpl; auto.
       + apply keys_in_shift in HIn.
         apply H1; simpl; auto.
    -- constructor; auto.
       simpl in *.
       now rewrite <- keys_in_shift.
Qed.

    


Lemma update_locals_max_key (V : 𝐕) (t : t) :
  max_key (update_locals t V) = max_key t.
Proof.
  induction t; simpl; auto.
  destruct a as [[rg rs] v]; subst.
  destruct (V⌊rs⌋)%re as [ov|]; try (destruct ov); 
  simpl; now rewrite IHt.
Qed.

Lemma update_locals_new_key (V : 𝐕) (t : t) :
  new_key (update_locals t V) = new_key t.
Proof.
  unfold new_key.
  destruct t; simpl; auto.
  destruct p as [[rg rs] v].
  destruct (V⌊rs⌋)%re as [ov|]; try (destruct ov); 
  simpl; now rewrite update_locals_max_key.
Qed.

Lemma update_locals_In r r' v (V : 𝐕) (t : t) :
  In (r,r',v) (update_locals t V) -> 
  (In (r,r',v) t /\ V⌊r'⌋ <> Some (Cell.out v))%re \/ 
  (exists v', In (r,r',v') t /\ V⌊r'⌋ = Some (Cell.out v))%re.
Proof.
  revert r; induction t; simpl; intros.
  - inversion H.
  - destruct a as [[rr rw] p].
    destruct (V⌊rw⌋)%re eqn:Hfi.
    -- destruct r0.
       + destruct H.
         ++ inversion H; subst.
            left; split; auto.
            intro.
            rewrite H0 in *; inversion Hfi.
         ++ apply IHt in H.
            destruct H as [[HIn Hneq]|[v' [HIn Heq]]]; auto.
            right.
            exists v'; auto.
       + destruct H.
         ++ inversion H; subst.
            right; exists p; split; auto.
         ++ apply IHt in H.
            destruct H as [[HIn Hneq]|[v' [HIn Heq]]]; auto.
            right.
            exists v'; auto.
    -- destruct H.
       + inversion H; subst.
         left; split; auto.
         intro; rewrite H0 in *; inversion Hfi.
       + apply IHt in H.
         destruct H as [[HIn Hneq]|[v' [HIn Heq]]]; auto.
         right.
         exists v'; auto.
Qed.

Lemma update_locals_keys_In r (V : 𝐕) (t : t) :
  In r (keys (update_locals t V)) <-> In r (keys t).
Proof.
  revert r; induction t; simpl; intro.
  - split; auto.
  - destruct a as [[rr rw] p].
    destruct (V⌊rw⌋)%re;
    try (destruct r0); simpl; 
    split; intros [|[|]]; auto;
    do 2 right;
    try (now rewrite <- IHt);
    try (now rewrite IHt).
Qed.


Lemma update_locals_NoDup_keys (st : t) V :
  NoDup (keys st) -> NoDup (keys (update_locals st V)).
Proof.
  induction st; simpl; auto.
  destruct a as [[rr rw] p]; intro HND.
  inversion HND; subst.
  inversion H2; subst.
  destruct (V⌊rw⌋)%re;
  try (destruct r); simpl.
  - constructor.
    -- simpl; intros [|]; subst.
       + apply H1; simpl; auto.
       + rewrite update_locals_keys_In in H.
         apply H1; simpl; auto.
    -- constructor; auto.
       rewrite update_locals_keys_In; auto.
  - constructor.
    -- simpl; intros [|]; subst.
       + apply H1; simpl; auto.
       + rewrite update_locals_keys_In in H.
         apply H1; simpl; auto.
    -- constructor; auto.
       rewrite update_locals_keys_In; auto.
 - constructor.
    -- simpl; intros [|]; subst.
       + apply H1; simpl; auto.
       + rewrite update_locals_keys_In in H.
         apply H1; simpl; auto.
    -- constructor; auto.
       rewrite update_locals_keys_In; auto.
Qed.


Lemma Wf_cons_1 (k : lvl) p (t : t) :
  Wf k (p :: t) -> Wf k t.
Proof.
  intros Hwf r HIn; apply Hwf; simpl; auto.
Qed.

Lemma update_locals_Wf (k: lvl) (V : 𝐕) (W: t) :
  Wf k W /\ (k ⊩ V)%re -> Wf k (update_locals W V).
Proof.
  induction W; simpl; intros [Hwf Hwf']; auto.
  destruct a as [[rg rs] v].
  apply Wf_cons in Hwf as [Hwf Hwf''].
  destruct (V⌊rs⌋)%re eqn:Hfi; try (destruct r); 
  intro r; simpl; intros [|HIn]; subst;
  try (apply IHW; auto; split; now auto);
  try (apply Hwf; simpl; now auto).
  destruct Hwf.
  eapply REnvironment.Wf_find in Hfi; eauto.
  simpl in *; destruct Hfi.
  unfold Cell.Wf in *; simpl in *.
  repeat split; auto.
Qed.

Lemma halts_init_locals (m : lvl) (st : t) (V : 𝐕) :
  halts m st -> REnvironment.halts m V -> 
  REnvironment.halts m (init_locals st V).
Proof.
  induction st.
  - simpl; intros.
    intros k v Hfi.
    now apply H0 in Hfi.
  - intros Hlt HltV.
    destruct a as [[rg rs] v'].
    simpl.
    inversion Hlt; subst.
    apply IHst in H2; auto.
    apply REnvironment.halts_add; split.
    -- now simpl.
    -- apply REnvironment.halts_add; split; auto.
       simpl.
       exists <[unit]>; split; auto.
       reflexivity.
Qed.

Lemma halts_update_locals (k : lvl) (W : t) (V : 𝐕) :
  REnvironment.halts k V -> halts k W -> halts k (update_locals W V).
Proof.
  induction W; intros HltV HltW.
  - now simpl.
  - destruct a as [[rg rs] v].
    inversion HltW; subst. 
    simpl in *.
    destruct (V⌊rs⌋)%re eqn:Hfi.
    -- destruct r.
       + constructor; auto.
         apply IHW; auto.
       + constructor.
         ++ apply HltV in Hfi.
            now simpl in *.
         ++ apply IHW; auto.
    -- constructor; auto.
       apply IHW; auto.
Qed.

Lemma update_locals_not_nil t V :
  update_locals t V <> [] <-> t <> [].
Proof.
  induction t; simpl; split; auto;
  destruct a as [[rr rw] p].
  - destruct (V⌊rw⌋)%re; try destruct r; 
    intros H c; inversion c.
  - intro H.
    destruct (V⌊rw⌋)%re; try destruct r; 
    intros c; inversion c.
Qed.

Lemma app_not_nil A (t1 t2 : list A) :
  t1 ++ t2 <> [] -> t1 <> [] \/ t2 <> [].
Proof.
  destruct t1; simpl; auto.
  intros. 
  left.
  intro c; inversion c.
Qed.

Lemma shift_not_nil m n t :
  (shift n m t) <> [] <-> t <> [].
Proof.
  destruct t; simpl; split; auto.
  - intros H c; inversion c.
  - intros H c; inversion c.
Qed.

(** **** [eqDom] properties *)
Definition eqDom' (V : 𝐕) (W: t) := forall (r : resource), (r ∈ V)%re <-> In r (keys W).

#[export] Instance eqDom'_iff : Proper (REnvironment.eq ==> eq ==> iff) eqDom'.
Proof.
  intros V V1 HeqV W W1 HeqW; unfold eqDom'; split; intros.
  - rewrite <- HeqV; rewrite <- HeqW; auto.
  - rewrite HeqV; rewrite HeqW; auto.
Qed.

Lemma eqDom'_In (r: resource) (V: 𝐕) (W: t) :
  eqDom' V W -> (r ∈ V)%re <-> In r (keys W).
Proof. unfold eqDom'; intro HeqDom'; auto. Qed.

Lemma eqDom'_Empty (V: 𝐕) (W: t):
 eqDom' V W -> (isEmpty(V))%re <-> W = [].
Proof.
  intro HeqDom'; split; intro HEmp.
  - destruct W; auto.
    destruct p as [[rg rs] v].
    assert (rg ∈ V)%re.
    { apply HeqDom'; simpl; auto. }
    destruct H as [v' HM].
    exfalso.
    now apply (HEmp rg v').
  - subst.
    intros x v HM.
    assert (HIn : (x ∈ V)%re).
    { now exists v. }
    rewrite (HeqDom' x) in HIn.
    simpl in *; auto. 
Qed.

Lemma eqDom'_new_key (V: 𝐕) (W: t):
  NoDup (keys W) ->
  eqDom' V W -> V⁺%re = new_key W.
Proof.
  revert V; induction W; intros V HNoD HeqDom'.
  - simpl.
    rewrite REnvironment.Ext.new_key_Empty; auto.
    rewrite eqDom'_Empty; auto.
  - destruct a as [[rg rs] v].
    rewrite new_key_cons.
    assert (HIn: (rg ∈ V)%re).
    { rewrite (HeqDom' rg); simpl; auto. }
    destruct HIn as [v' HM].
    apply REnvironment.find_1 in HM.
    apply REnvironment.add_id in HM.
    rewrite <- HM in *; clear HM.
    rewrite <- REnvironment.add_remove_1 in *.
    assert (HIn: (rs ∈ (⌈ rg ⤆ v' ⌉ REnvironment.Raw.remove rg V))%re).
    { rewrite (HeqDom' rs); simpl; auto. }
    destruct HIn as [v'' HM].
    apply REnvironment.find_1 in HM.
    apply REnvironment.add_id in HM.
    rewrite <- HM in *; clear HM.
    rewrite <- REnvironment.add_remove_1 in *.
    inversion HNoD; subst; simpl in *.
    inversion H2; subst; simpl in *.
    clear H2 HNoD; simpl in *.
    apply Classical_Prop.not_or_and in H1 as [Hneq HnIn].
    rewrite REnvironment.remove_add_2 in * by lia.
    do 2 rewrite REnvironment.Ext.new_key_add_max.
    rewrite IHW; try lia; auto.
    intros r; split; intro HIn.
    + assert (HIn': (r ∈ (⌈ rs ⤆ v'' ⌉ (⌈ rg ⤆ v' ⌉ REnvironment.Raw.remove rs (REnvironment.Raw.remove rg V))))%re).
      { do 2 rewrite REnvironment.add_in_iff; auto. }
      apply HeqDom' in HIn'.
      apply REnvironment.remove_in_iff in HIn as [Hneq' HIn].
      apply REnvironment.remove_in_iff in HIn as [Hneq'' HIn].
      simpl in HIn'; destruct HIn' as [Hc|[Hc|]]; auto;
      subst; try contradiction.
    + assert (In r (keys ((rg,rs,v):: W))).
      { simpl; auto. }
      apply HeqDom' in H.
      do 2 rewrite REnvironment.add_in_iff in H.
      destruct H as [Hc|[Hc|HIn']]; subst; try contradiction; auto.
Qed.


Lemma init_locals_in_iff (r : resource) (W : t) (V : 𝐕) :
  (r ∈ (init_locals W V))%re <-> In r (keys W) \/ (r ∈ V)%re.
Proof.
  revert r; induction W; simpl; intros r.
  - split; intros; auto.
    destruct H; auto.
    contradiction.
  - destruct a as [[rg rs] v]; split; intro HIn.
    -- do 2 rewrite REnvironment.add_in_iff in HIn.
       simpl.
       destruct HIn as [|[| HIn]]; subst; auto.
       apply IHW in HIn as [|]; auto.
    -- simpl in *.
       do 2 rewrite REnvironment.add_in_iff.
       rewrite IHW.
       destruct HIn as [[|[|]]|]; auto; subst.
Qed.

Lemma init_locals_new_key (V : 𝐕) (t : t) : ((init_locals t V)⁺)%re = max (new_key t) (V⁺)%re.
Proof.
  induction t; auto.
  destruct a as [[rg rs] v].
  rewrite new_key_cons.
  simpl.
  do 2 rewrite REnvironment.Ext.new_key_add_max.
  rewrite IHt; lia.
Qed.

Lemma init_locals_Wf (k : lvl) (V : 𝐕) (t : t) :
  Wf k t /\ (k ⊩ V)%re -> (k ⊩ init_locals t V)%re.
Proof.
  induction t; simpl; intros [Hwf Hwf']; auto.
  destruct a as [[rg rs] v].
  apply Wf_cons in Hwf as [Hwf Hwf''].
  destruct Hwf as [Hwfrg [Hwfrs Hwfv]].
  apply REnvironment.Wf_add; split; auto.
  split.
  - now unfold Cell.Wf; simpl.
  - apply REnvironment.Wf_add; repeat split; auto.
    constructor.
Qed.

Lemma init_locals_find_e r c  (V : 𝐕) (W : t) :
  (V⌊r⌋%re = Some c -> exists v, Logic.eq c (Cell.inp v)) ->
  (init_locals W V)⌊r⌋%re = Some c -> exists v, Logic.eq c (Cell.inp v).
Proof.
  revert r c; induction W; intros r c Hfi.
  - simpl; auto.
  - destruct a as [[rg rs] v].
    simpl.
    intro Hfi'.
    rewrite REnvironment.add_o in Hfi'.
    destruct (Resource.eq_dec rg r); subst.
    -- now inversion Hfi'; exists v.
    -- rewrite REnvironment.add_o in Hfi'.
       destruct (Resource.eq_dec rs r); subst.
       + inversion Hfi'; subst.
         now exists <[unit]>.
       + eapply IHW; eauto.
Qed.

Lemma init_locals_find_W r v V W :
  (r ∉ V)%re ->
  (init_locals W V)⌊r⌋%re = Some (Cell.inp v) -> 
  exists r', 
  (In (r,r',v) W \/ (exists v', In (r',r,v') W /\ v = Term.tm_unit)).
Proof.
  revert r v.
  induction W; intros r v HnIn Hfi; simpl in *.
  - exfalso; apply HnIn.
    exists (Cell.inp v); now apply REnvironment.find_2.
  - destruct a as [[rg rs] v'].
    destruct (Resource.eq_dec r rg); subst.
    -- rewrite REnvironment.add_eq_o in Hfi; auto.
       inversion Hfi; subst.
       exists rs; auto.
    -- rewrite REnvironment.add_neq_o in Hfi; auto.
       destruct (Resource.eq_dec r rs); subst.
       + rewrite REnvironment.add_eq_o in Hfi; auto.
         exists rg; right.
         exists v'; split; auto.
         inversion Hfi; reflexivity.
       + rewrite REnvironment.add_neq_o in Hfi; auto.
         apply IHW in Hfi; auto.
         destruct Hfi as [r' [HIn| [v'' [HIn Heq]]]].
         ++ exists r'; auto.
         ++ subst.
            exists r'; right.
            exists v''; auto.
Qed.

Lemma init_locals_find_V r c V W :
  ~(In r (keys W)) ->
  (init_locals W V)⌊r⌋%re = Some c -> 
  V⌊r⌋%re = Some c.
Proof.
  intros; induction W; simpl in *; auto.
  destruct a as [[rg rs] v'].
  apply IHW; auto.
  - intro; apply H; simpl; auto.
  - rewrite REnvironment.add_neq_o in H0.
    -- rewrite REnvironment.add_neq_o in H0; auto.
       intro; subst; apply H; simpl; auto.
    -- intro; subst; apply H; simpl; auto.
Qed.

End Stock.

Module StockNotations.
  (** *** Scope *)
Declare Scope stock_scope.
Delimit Scope stock_scope with sk.

(** *** Notations *)
Definition 𝐖 := Stock.t.

Infix "∈" := List.In (at level 60, no associativity) : stock_scope. 
Notation "r '∉' t" := (~ (List.In r t)) (at level 75, no associativity) : stock_scope. 
Notation "t '⁺'" := (Stock.new_key t) (at level 16) : stock_scope.
Notation "'[⧐' lb '–' k ']' t" := (Stock.shift lb k t) 
                                   (at level 65, right associativity) : stock_scope.

Infix "=" := Stock.eq : stock_scope.
Infix "⊩" := Stock.Wf (at level 20, no associativity) : stock_scope.
End StockNotations.