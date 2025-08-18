From Coq Require Import Lia List Arith.
From DeBrLevel Require Import LevelInterface ListLevel.
From MMaps Require Import MMaps.
From Mecha Require Import Resource Term Triplet REnvironment Cell
                          SyntaxNotation.
Import ListNotations.

(** * Environment - Stock

  In the functional transition, there is an environment that saves the local resources and their initial expression. We define it as a list of triplets where a triplet is already defined in [Triplet] module. 
*)

Module Stock <: IsLvlET.

Module RE := REnvironment.

(** ** Definitions *)

Include IsLvlListETWL Triplet.

(** *** Get all keys

  It gets all keys in the triplet list and gathers them in a list.
*)
Definition keys (st : t) :=
 fold_right (fun '((rg,rs),_) acc => rg :: rs :: acc) [] st.

(** *** Definition of [new_key]

  Acts the same that the [new_key] function from maps.
*)
Definition max_key (st : t) :=
  fold_right (fun '((rg,rs),_) acc => max (max rg rs) acc) 0 st.

Definition new_key (st : t) :=
  match st with
    | [] => 0
    | _  => (max_key st) + 1
  end.

(** *** Initialize locals 

  At the beginning of the temporal transition, the local resources are initialized thanks to the stock. For each triplet [(r,r',v)], [r] is initialized as unused with [v] and [r'] is initialized as unused with [unit]
*)
Fixpoint init_locals (st : t) (V : RE.t) : RE.t :=
  match st with
    | [] => V
    | (r,r',v) :: st' => RE.Raw.add r (Cell.inp v) 
                        (RE.Raw.add r' (Cell.inp <[unit]>) 
                        (init_locals st' V))
  end.

(** *** Update locals

  At the end of the temporal transition, each expression bound to local resources is updated regards of the resource environment. If the writing resource is used then the expression is replaced by the new one, otherwise nothing changes.
*)
Fixpoint update_locals (st : t) (V : RE.t) : t :=
  match st with
    | [] => []
    | (r,r',v) :: st' =>  match (RE.Raw.find r' V) with
                            | Some (⩽ … v' ⩾) =>  (r,r',v') :: (update_locals st' V)
                            | _ => (r,r',v) :: (update_locals st' V)
                          end
  end.

(** *** Domain equality between stock and resource environment *)

Definition eqDom' (V : RE.t) (W: t) := 
  forall (r : resource), (RE.Raw.In r V) <-> In r (keys W).

(** ** Properties *)

Lemma app_not_nil A (t1 t2 : list A) :
  t1 ++ t2 <> [] -> t1 <> [] \/ t2 <> [].
Proof.
  destruct t1; simpl; auto.
  intros. 
  left.
  intro c; inversion c.
Qed.

Lemma Wf_cons_1 (k : lvl) p (t : t) :
  Wf k (p :: t) -> Wf k t.
Proof.
  intros Hwf r HIn; apply Hwf; simpl; auto.
Qed.

Lemma shift_not_nil m n t :
  (shift n m t) <> [] <-> t <> [].
Proof.
  destruct t; simpl; split; auto.
  - intros H c; inversion c.
  - intros H c; inversion c.
Qed.

(** *** [keys] properties *)

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

(** *** [max_key] and [new_key] properties *)

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

(** *** [NoDup] properties *)

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
 
(** *** [update_locals] properties *)

Lemma update_locals_max_key (V : RE.t) (t : t) :
  max_key (update_locals t V) = max_key t.
Proof.
  induction t; simpl; auto.
  destruct a as [[rg rs] v]; subst.
  destruct (RE.Raw.find rs V) as [ov|]; try (destruct ov); 
  simpl; now rewrite IHt.
Qed.

Lemma update_locals_new_key (V : RE.t) (t : t) :
  new_key (update_locals t V) = new_key t.
Proof.
  unfold new_key.
  destruct t; simpl; auto.
  destruct p as [[rg rs] v].
  destruct (RE.Raw.find rs V) as [ov|]; try (destruct ov); 
  simpl; now rewrite update_locals_max_key.
Qed.

Lemma update_locals_In r r' v (V : RE.t) (t : t) :
  In (r,r',v) (update_locals t V) -> 
  (In (r,r',v) t /\ RE.Raw.find r' V <> Some (Cell.out v)) \/ 
  (exists v', In (r,r',v') t /\ 
              RE.Raw.find r' V = Some (Cell.out v)).
Proof.
  revert r; induction t; simpl; intros.
  - inversion H.
  - destruct a as [[rr rw] p].
    destruct (RE.Raw.find rw V) eqn:Hfi.
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

Lemma update_locals_keys_In r (V : RE.t) (t : t) :
  In r (keys (update_locals t V)) <-> In r (keys t).
Proof.
  revert r; induction t; simpl; intro.
  - split; auto.
  - destruct a as [[rr rw] p].
    destruct (RE.Raw.find rw V);
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
  destruct (RE.Raw.find rw V);
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


Lemma update_locals_Wf (k: lvl) (V : RE.t) (W: t) :
  Wf k W /\ (RE.Wf k V) -> Wf k (update_locals W V).
Proof.
  induction W; simpl; intros [Hwf Hwf']; auto.
  destruct a as [[rg rs] v].
  apply Wf_cons in Hwf as [Hwf Hwf''].
  destruct (RE.Raw.find rs V) eqn:Hfi; try (destruct r); 
  intro r; simpl; intros [|HIn]; subst;
  try (apply IHW; auto; split; now auto);
  try (apply Hwf; simpl; now auto).
  destruct Hwf.
  eapply REnvironment.Wf_find in Hfi; eauto.
  simpl in *; destruct Hfi.
  unfold Cell.Wf in *; simpl in *.
  repeat split; auto.
Qed.

Lemma update_locals_not_nil t V :
  update_locals t V <> [] <-> t <> [].
Proof.
  induction t; simpl; split; auto;
  destruct a as [[rr rw] p].
  - destruct (RE.Raw.find rw V); try destruct r; 
    intros H c; inversion c.
  - intro H.
    destruct (RE.Raw.find rw V); try destruct r; 
    intros c; inversion c.
Qed.

(** *** [eqDom'] properties *)

#[export] Instance eqDom'_iff : Proper (REnvironment.eq ==> eq ==> iff) eqDom'.
Proof.
  intros V V1 HeqV W W1 HeqW; unfold eqDom'; split; intros.
  - eapply RE.renvironment_in_iff in HeqV; auto.
    rewrite <- HeqV; rewrite <- HeqW; auto.
  - eapply RE.renvironment_in_iff in HeqV; auto.
    rewrite HeqV; rewrite HeqW; auto.
Qed.

Lemma eqDom'_In (r: resource) (V: RE.t) (W: t) :
  eqDom' V W -> (RE.Raw.In r V) <-> In r (keys W).
Proof. unfold eqDom'; intro HeqDom'; auto. Qed.

Lemma eqDom'_Empty (V: RE.t) (W: t):
 eqDom' V W -> (RE.Empty V) <-> W = [].
Proof.
  intro HeqDom'; split; intro HEmp.
  - destruct W; auto.
    destruct p as [[rg rs] v].
    assert (RE.Raw.In rg V).
    { apply HeqDom'; simpl; auto. }
    destruct H as [v' HM].
    exfalso.
    now apply (HEmp rg v').
  - subst.
    intros x v HM.
    assert (HIn : (RE.Raw.In x V)).
    { now exists v. }
    rewrite (HeqDom' x) in HIn.
    simpl in *; auto. 
Qed.

#[local] Instance re_in_iff : 
  Proper (Logic.eq ==> RE.eq ==> iff) RE.Raw.In := RE.renvironment_in_iff.

#[local] Instance re_new_eq : 
  Proper (RE.eq ==> Logic.eq) (RE.Ext.new_key) := RE.Ext.new_key_eq. 


Lemma eqDom'_new_key (V: RE.t) (W: t):
  NoDup (keys W) ->
  eqDom' V W -> RE.Ext.new_key V = new_key W.
Proof.
  revert V; induction W; intros V HNoD HeqDom'.
  - simpl.
    rewrite RE.Ext.new_key_Empty; auto.
    rewrite eqDom'_Empty; auto.
  - Import REnvironment.
    destruct a as [[rg rs] v].
    rewrite new_key_cons.
    assert (HIn: (RE.Raw.In rg V)).
    { rewrite (HeqDom' rg); simpl; auto. }
    destruct HIn as [v' HM].
    apply RE.find_1 in HM.
    apply RE.add_id in HM.
    rewrite <- HM in *; clear HM.
    rewrite <- RE.add_remove_1 in *.
    assert (HIn: RE.Raw.In rs (RE.Raw.add rg v' (RE.Raw.remove rg V))).
    { rewrite (HeqDom' rs); simpl; auto. }
    destruct HIn as [v'' HM].
    apply RE.find_1 in HM.
    apply RE.add_id in HM.
    rewrite <- HM in *; clear HM.
    rewrite <- RE.add_remove_1 in *.
    inversion HNoD; subst; simpl in *.
    inversion H2; subst; simpl in *.
    clear H2 HNoD; simpl in *.
    apply Classical_Prop.not_or_and in H1 as [Hneq HnIn].
    rewrite RE.remove_add_2 in * by lia.
    do 2 rewrite RE.Ext.new_key_add_max.
    rewrite IHW;try lia; auto.
    intros r; split; intro HIn.
    + assert (HIn': RE.Raw.In r  
                      (RE.Raw.add rs v'' 
                      (RE.Raw.add rg v' 
                      (RE.Raw.remove rs (RE.Raw.remove rg V))))).
      { do 2 rewrite RE.add_in_iff; auto. }
      apply HeqDom' in HIn'.
      apply RE.remove_in_iff in HIn as [Hneq' HIn].
      apply RE.remove_in_iff in HIn as [Hneq'' HIn].
      simpl in HIn'; destruct HIn' as [Hc|[Hc|]]; auto;
      subst; try contradiction.
    + assert (In r (keys ((rg,rs,v):: W))).
      { simpl; auto. }
      apply HeqDom' in H.
      do 2 rewrite RE.add_in_iff in H.
      destruct H as [Hc|[Hc|HIn']]; subst; try contradiction; auto.
Qed.

(** *** [init_locals] properties *)

Lemma init_locals_in_iff (r : resource) (W : Stock.t) (V : RE.t) :
  (RE.Raw.In r (init_locals W V)) <-> In r (keys W) \/ 
                                      (RE.Raw.In r V).
Proof.
  revert r; induction W; simpl; intros r.
  - split; intros; auto.
    destruct H; auto.
    contradiction.
  - destruct a as [[rg rs] v]; split; intro HIn.
    -- do 2 rewrite RE.add_in_iff in HIn.
       simpl.
       destruct HIn as [|[| HIn]]; subst; auto.
       apply IHW in HIn as [|]; auto.
    -- simpl in *.
       do 2 rewrite RE.add_in_iff.
       rewrite IHW.
       destruct HIn as [[|[|]]|]; auto; subst.
Qed.

Lemma init_locals_new_key (V : RE.t) (t : Stock.t) : 
  RE.Ext.new_key (init_locals t V) = max (new_key t) (RE.Ext.new_key V).
Proof.
  induction t; auto.
  destruct a as [[rg rs] v].
  rewrite new_key_cons.
  simpl.
  do 2 rewrite RE.Ext.new_key_add_max.
  rewrite IHt; lia.
Qed.

Lemma init_locals_Wf (k : lvl) (V : RE.t) (t : Stock.t) :
  Stock.Wf k t /\ (RE.Wf k V) -> RE.Wf k (init_locals t V).
Proof.
  induction t; simpl; intros [Hwf Hwf']; auto.
  destruct a as [[rg rs] v].
  apply Wf_cons in Hwf as [Hwf Hwf''].
  destruct Hwf as [Hwfrg [Hwfrs Hwfv]].
  apply RE.Wf_add; split; auto.
  split.
  - now unfold Cell.Wf; simpl.
  - apply RE.Wf_add; repeat split; auto.
    constructor.
Qed.

Lemma init_locals_find_e r c  (V : RE.t) (W : Stock.t) :
  (RE.Raw.find r V = Some c -> exists v, Logic.eq c (Cell.inp v)) ->
  RE.Raw.find r (init_locals W V) = Some c -> exists v, Logic.eq c (Cell.inp v).
Proof.
  revert r c; induction W; intros r c Hfi.
  - simpl; auto.
  - destruct a as [[rg rs] v].
    simpl.
    intro Hfi'.
    rewrite RE.add_o in Hfi'.
    destruct (Resource.eq_dec rg r); subst.
    -- now inversion Hfi'; exists v.
    -- rewrite RE.add_o in Hfi'.
       destruct (Resource.eq_dec rs r); subst.
       + inversion Hfi'; subst.
         now exists <[unit]>.
       + eapply IHW; eauto.
Qed.

Lemma init_locals_find_W r v V W :
  ~ RE.Raw.In r V ->
  RE.Raw.find r (init_locals W V) = Some (Cell.inp v) -> 
  exists r', 
  (In (r,r',v) W \/ (exists v', In (r',r,v') W /\ v = Term.tm_unit)).
Proof.
  revert r v.
  induction W; intros r v HnIn Hfi; simpl in *.
  - exfalso; apply HnIn.
    exists (Cell.inp v); now apply RE.find_2.
  - destruct a as [[rg rs] v'].
    destruct (Resource.eq_dec r rg); subst.
    -- rewrite RE.add_eq_o in Hfi; auto.
       inversion Hfi; subst.
       exists rs; auto.
    -- rewrite RE.add_neq_o in Hfi; auto.
       destruct (Resource.eq_dec r rs); subst.
       + rewrite RE.add_eq_o in Hfi; auto.
         exists rg; right.
         exists v'; split; auto.
         inversion Hfi; reflexivity.
       + rewrite RE.add_neq_o in Hfi; auto.
         apply IHW in Hfi; auto.
         destruct Hfi as [r' [HIn| [v'' [HIn Heq]]]].
         ++ exists r'; auto.
         ++ subst.
            exists r'; right.
            exists v''; auto.
Qed.

Lemma init_locals_find_V r c V W :
  ~(In r (keys W)) ->
  RE.Raw.find r (init_locals W V) = Some c -> 
  RE.Raw.find r V = Some c.
Proof.
  intros; induction W; simpl in *; auto.
  destruct a as [[rg rs] v'].
  apply IHW; auto.
  - intro; apply H; simpl; auto.
  - rewrite RE.add_neq_o in H0.
    -- rewrite RE.add_neq_o in H0; auto.
       intro; subst; apply H; simpl; auto.
    -- intro; subst; apply H; simpl; auto.
Qed.

Lemma init_locals_unused r W V:
  In r (keys W) ->
  unused r (init_locals W V).
Proof.
  revert V r; induction W; simpl; intros V r HIn.
  - contradiction.
  - destruct a as [[rg rs] v].
    simpl in *;
    destruct HIn as [Heq | [Heq | HIn]]; subst.
    -- unfold unused, Cell.opt_unused.
       rewrite RE.add_eq_o; auto.
       constructor.
    -- destruct (Resource.eq_dec r rg); subst.
       + unfold unused, Cell.opt_unused.
         rewrite RE.add_eq_o; auto.
         constructor.
       + unfold unused, Cell.opt_unused.
         rewrite RE.add_neq_o, RE.add_eq_o; auto.
         constructor.
    -- apply (IHW V) in HIn.
       destruct (Resource.eq_dec r rg); 
       destruct (Resource.eq_dec r rs); subst;
       try (unfold unused, Cell.opt_unused;
            rewrite RE.add_eq_o; auto; now constructor).
       + unfold unused, Cell.opt_unused.
         rewrite RE.add_neq_o, RE.add_eq_o; auto.
         constructor.
       + unfold unused, Cell.opt_unused.
         do 2 (rewrite RE.add_neq_o; auto).
Qed.

Lemma init_locals_unused_not r W V:
  ~ (In r (keys W)) ->
  unused r V ->
  unused r (init_locals W V).
Proof.
  revert r; induction W; simpl; intros r HnIn Hunsd; auto.
  destruct a as [[rr rw] v]; simpl in *.
  apply Classical_Prop.not_or_and in HnIn as [Hneq HnIn].
  apply Classical_Prop.not_or_and in HnIn as [Hneq' HnIn].
  apply unused_add_neq; auto.
  apply unused_add_neq; auto.
Qed. 

End Stock.