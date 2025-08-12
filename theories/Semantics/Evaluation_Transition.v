From Coq Require Import Relations.Relation_Operators Classes.Morphisms
                        Classes.RelationClasses Lia Program List.
From Mecha Require Import Var Resource Term Typ Cell Triplet VContext RContext Type_System
                          REnvironment Stock SREnvironment 
                          SyntaxNotation EnvNotation.
Import ListNotations.

Open Scope term_scope.

(** * Semantics - Evaluation

  Wormholes’s dynamic semantics is split in three sets of transition rules: the evaluation transition which extends standard B-reduction; the functional transition, defined in [Functional_Transition.v], which performs the logical instant, and the temporal transition, defined in [Temporal_Transition.v], which corresponds to the reactivity of the program: it initializes the resources values, performs the instant via the functional transition and updates the system. In this file, we focus on the evaluation transition.
*)

(** ** Definition - Evaluation *)

(** *** Substitution function

  The evaluation transition relies on the substitution function. This function, denoted [subst], takes four arguments, [x] the variable to substitute, [v] the term which substitutes [x], [lb], [k] two levels and [t] a term, and returns [t] where all occurences of [x] are replaced by [v]. In addition to the usual behavior of a substitution function, [lb] and [k] are arguments of the function. They keep consistent the resource names representation. Consider, as an illustrating example, the following expressions valid at [0]. 
<<
t1 = wormhole(unit; rsf[0] >>> x)
t2 = wormhole(unit; rsf[0])
>>
  With an usual substitution function, the result of substituting [x] by [t2] in [t1] is ill-formed, see below, because the resource [0] in [t2] is captured by the [t1]'s [wormhole] term. Another way to say it is that [0] in [t1] and [t2] represents two distinct resource names. In [[x := t2] t1], the resource name [0] represents the same resource name, we lost the information.
<<
[x := t2] wormhole(unit; rsf[0] >>> x) = wormhole([x := t2] unit; [x := t2] rsf[0] >>> x)
                                       = wormhole(unit; [x := t2] rsf[0] >>> x)
                                       = wormhole(unit; [x := t2] rsf[0] >>> [x := t2] x)
                                       = wormhole(unit; rsf[0] >>> wormhole(unit; rsf[0]))
>>
  Consequently, we carry two extra arguments [lb] and [k] which are respectively the well-formedness level of [v] and the the number of bound resources encountered. In the example below, we rename [wormhole] by [wh] and contract ([0 – k]) by [k] in the substitution notation in order to save space.
<<
[x := t2 ~ 0 – 0] wh(unit; rsf[0] >>> x) = wh([x := t2 ~ 0] unit; [x := t2 ~ 2] rsf[0] >>> x)
                                         = wh(unit; [x := t2 ~ 2] rsf[0] >>> x)
                                         = wh(unit; [x := t2 ~ 2] rsf[0] >>> [x := t2 ~ 2] x)
                                         = wh(unit; rsf[0] >>> [⧐ 0 – 2] wh(unit; rsf[0]))
                                         = wh(unit; rsf[0] >>> wh([⧐ 0 – 2] unit; [⧐ 0 – 2] rsf[0]))
                                         = wh(unit; rsf[0] >>> wh(unit; [⧐ 0 – 2] rsf[0]))
                                         = wh(unit; rsf[0] >>> wh(unit; rsf[2]))
>>
*)

Reserved Notation "'[' x ':=' v '~' lb '–' k ']' t" (in custom wh at level 66, right associativity).

Fixpoint subst (lb : lvl) (k : lvl) (x : variable) (v t : Λ) : Λ :=
  match t with
    | Term.tm_var y => if (x =? y)%v then <[[⧐ lb – k] v]> else t 
    | <[\y:C,t]>      => if (x =? y)%v then <[\y:C,t]> else <[\y:C,[x := v ~ lb – k] t]>

    | <[fst.t]>    => <[fst.([x := v ~ lb – k]t)]>
    | <[snd.t]>    => <[snd.([x := v ~ lb – k]t)]>
    | <[Fix t]>    => <[Fix ([x := v ~ lb – k]t)]>
    | <[arr(t)]>   => <[arr([x := v ~ lb – k]t)]>
    | <[first(C:t)]> => <[first(C:[x := v ~ lb – k]t)]>

    | <[t1 t2]>   => <[ ([x := v ~ lb – k]t1) ([x := v ~ lb – k]t2)]>
    | <[⟨t1,t2⟩]> => <[⟨([x := v ~ lb – k]t1),([x := v ~ lb – k]t2)⟩]>
    | <[t1 >>> t2]>       => <[([x := v ~ lb – k]t1) >>> ([x := v ~ lb – k]t2)]>
    | <[wormhole(t1;t2)]> => <[wormhole([x := v ~ lb – k] t1;[x := v ~ lb – {S (S k)}] t2)]>

    | _ => t
  end
where "'[' x ':=' v '~' lb '–' k ']' t" := (subst lb k x v t) (in custom wh).

Notation "'[' x ':=' v '~' lb ']' t" := (subst lb 0 x v t) 
                                        (in custom wh at level 66,  right associativity).



(** *** Evaluation transition

  The evaluation transition is a small-step semantics with a weak call-by-value strategy. The strategy bypasses variable capture issues as well as determine the reduction.  Modifications on the substitution affect the evaluation transition. [k] being the number of bound resources encountered, we set it to [0]. But, [lb] is the well-formedness level of [v], thus, it cannot be deduced. Consequently, we also need the well-formedness level, named [k] here, to be explicit in the evaluation transition.
*)

Reserved Notation "k '⊨' t '⟼' t1" (at level 57, t custom wh, t1 custom wh, no associativity).

Inductive evaluate : lvl -> Λ -> Λ -> Prop :=
  | eT_appv (k : lvl) (x : variable) (C : Τ) (t v : Λ) :

                         value(v) ->
      (* ------------------------------------- ET-Appv *)
           k ⊨ ((\x:C,t) v) ⟼ ([x:= v ~ k] t)

  | eT_app1 (k : lvl) (t1 t1' t2 : Λ) :

               k ⊨ t1 ⟼ t1' -> 
      (* --------------------------- ET-App1 *)
           k ⊨ (t1 t2) ⟼ (t1' t2)

  | eT_app2  (k : lvl) (v t t' : Λ) :
                    
           value(v) -> k ⊨ t ⟼ t' -> 
      (* ------------------------------- ET-App2 *)
              k ⊨ (v t) ⟼ (v t') 

  | eT_fixv (k : lvl) (f : variable) (C : Τ) (t : Λ) :

      (* --------------------------------------------------- ET-Fixv *)
          k ⊨ (Fix (\f:C,t)) ⟼ ([f := (Fix (\f:C,t)) ~ k] t)


  | eT_fix1 (k : lvl) (t t' : Λ) :

                k ⊨ t ⟼ t' ->
      (* --------------------------- ET-Fix1 *)
          k ⊨ (Fix t) ⟼ (Fix t')

  | eT_pair1 (k : lvl) (t1 t1' t2 : Λ) :

               k ⊨ t1 ⟼ t1' -> 
      (* --------------------------- ET-Pair1 *)
           k ⊨ ⟨t1,t2⟩ ⟼ ⟨t1',t2⟩

  | eT_pair2 (k : lvl) (v t t' : Λ) :

           value(v) -> k ⊨ t ⟼ t' -> 
      (* ------------------------------ ET-Pair2 *)
             k ⊨ ⟨v,t⟩ ⟼ ⟨v,t'⟩

  | eT_fst1 (k : lvl) (t t' : Λ) :

             k ⊨ t ⟼ t' -> 
      (* ----------------------- ET-Fst1 *)
           k ⊨ fst.t ⟼ fst.t'

  | eT_fstv (k : lvl) (v1 v2 : Λ) :

           value(v1) -> value(v2) -> 
      (* ----------------------------- ET-Fstv *)
            k ⊨ fst.⟨v1,v2⟩ ⟼ v1

  | eT_snd1 (k : lvl) (t t' : Λ) :

               k ⊨ t ⟼ t' -> 
      (* ----------------------- ET-Snd1 *)
           k ⊨ snd.t ⟼ snd.t'

  | eT_sndv (k : lvl) (v1 v2 : Λ) :

           value(v1) -> value(v2) -> 
      (* ----------------------------- ET-Sndv *)
            k ⊨ snd.⟨v1,v2⟩ ⟼ v2
                            
  | eT_comp1 (k : lvl) (t1 t1' t2 : Λ) :

                 k ⊨ t1 ⟼ t1' -> 
      (* ------------------------------- ET-Comp1 *)
           k ⊨ t1 >>> t2 ⟼ t1' >>> t2

  | eT_comp2 (k : lvl) (v t t' : Λ) :
                      
           value(v) -> k ⊨ t ⟼ t' -> 
      (* ------------------------------- ET-Comp2 *)
             k ⊨ v >>> t ⟼ v >>> t'

  (* | eT_arr (k : lvl) (t t' : Λ) :

               k ⊨ t ⟼ t' -> 
      (* ------------------------- ET-Arr *)
           k ⊨ arr(t) ⟼ arr(t') *)

  | eT_first (k : lvl) (C: Τ) (t t' : Λ) :
                
                 k ⊨ t ⟼ t' -> 
      (* ----------------------------- ET-First *)
           k ⊨ first(C:t) ⟼ first(C:t')

  | eT_wh1 (k : lvl) (t1 t1' t2 : Λ) :

                        k ⊨ t1 ⟼ t1' -> 
      (* ------------------------------------------- ET-Wh1 *)
           k ⊨ wormhole(t1;t2) ⟼ wormhole(t1';t2)

  | eT_wh2 (k : lvl) (v t t' : Λ) :

           value(v) -> (S (S k)) ⊨ t ⟼ t' -> 
      (* ----------------------------------------- ET-Wh2 *)
           k ⊨ wormhole(v;t) ⟼ wormhole(v;t')

where "k '⊨' t '⟼' t1" := (evaluate k t t1).



(** *** Multi transition step 

  We define the reflexive transitive closure of the evaluation transition.
*)
Definition multi (k : lvl) :=  clos_refl_trans_1n Λ (evaluate k).


Notation "k '⊨' t '⟼⋆' t1" := (multi k t t1) 
                                (at level 57, t custom wh, t1 custom wh, no associativity).

(** *** Halts 

  In the functional transition' proof of progress, we suppose the termination of successive application of (⟼) for some terms. Thus, we define [halts] which takes a level [k] and a term  [t], and states that [t] can be reduced into a value named [t'].  
*)
Definition halts (k : lvl)  (t : Λ) : Prop :=  exists t', k ⊨ t ⟼⋆ t' /\  value(t').


(** *** Halts for a resource environment

  In the functional transition proofs, we assume that all elements in the input resource environment halts. Thus, we define this property here with [For_all].
  An environment has the halting property if and only if each term in it halts. 
*)
Definition halts_re (k : lvl) := RE.Ext.For_all (fun _ d => halts k (Cell.extract d)).


(** *** Halts for a stock

  A stock holds the halting property if all terms in it halt.
*)
Definition halts_sk (m : lvl) (st : 𝐖) :=
 List.Forall (fun (tp: Triplet.t) =>  let (_,v) := tp 
                                      in halts m v) st.


(** **** Halts  for a simple environment

  An environment holds the halting property if and only if each term in it halts. 
*)
Definition halts_sre (k : lvl) := SRE.Ext.For_all (fun _ d => halts k d).

(** *** Value of a term

  We define a property [isvalueof] that takes a level [n] and two terms [t] and [v]. If it is satisfied then [v] is a value of [t] after several reduction regards of [n].
*)

Definition isvalueof (n : lvl) (t v : Λ) := n ⊨ t ⟼⋆ v /\ Term.value v.

#[export] Hint Constructors evaluate clos_refl_trans_1n : core.

(** ---- *)

(** ** Property - Evaluation *)

(** *** [subst] properties *)

Lemma subst_shift (lb k m n : lvl) (y : variable) (v t : Λ) :
  lb <= k ->
  <[[⧐ lb – m] ([y := v ~ k – n] t)]> = <[[y := ([⧐ lb – m] v) ~ {k + m} – n] ([⧐ lb – m] t)]>.
Proof.
  revert lb k m n; induction t; intros lb k m n Hle; simpl; f_equal; auto.
  - destruct (Var.eqb_spec y x); simpl; auto. 
    now apply Term.shift_permute_2.
  - destruct (Var.eqb_spec y x); simpl; f_equal; auto.
Qed.

Lemma subst_preserves_Wf (m n : lvl) (y : variable) (v t : Λ) :
  m >= n -> m ⊩ t -> n ⊩ v -> m ⊩ <[[y := v ~ n – {m - n}] t]>.
Proof.
  revert m n; induction t; intros m n Hle Hvt Hvv; auto;
  try (unfold Term.Wf in *; inversion Hvt; subst; constructor; now eauto).
  - simpl; destruct (Var.eqb_spec y x); subst; auto.
    now apply Term.shift_preserves_wf_2.
  - inversion Hvt; subst. 
    simpl; destruct (Var.eqb_spec y x); subst; auto.
    constructor; auto. 
    apply IHt; auto.
  - inversion Hvt; subst. 
    simpl; constructor; auto.
    -- now apply IHt1.
    -- replace (S (S (m - n))) with ((S (S m)) - n) by lia. 
       apply IHt2; auto.
Qed.

Lemma subst_preserves_wf_zero (k : lvl) (x : variable) (v t : Λ) :
  k ⊩ t ->  k ⊩ v -> k ⊩ <[[x := v ~ k] t]>.
Proof.
  replace 0 with (k - k) by lia. 
  apply subst_preserves_Wf; auto.
Qed.

(** *** [evaluate] properties *)

Lemma evaluate_not_value (k : lvl) (t t' : Λ) : k ⊨ t ⟼ t' -> ~ (value(t)).
Proof. intro HeT; induction HeT; intro Hvt; inversion Hvt; subst; auto. Qed.

Lemma evaluate_deterministic (k : lvl) (t t1 t2 : Λ) :
  k ⊨ t ⟼ t1 -> k ⊨ t ⟼ t2 -> t1 = t2.
Proof.
  intro eT; revert t2; induction eT; intros t3 HeT; 
  inversion HeT; subst; try (f_equal; now auto); clear HeT;
  try (exfalso; eapply (evaluate_not_value k v _); now eauto);
  try (now apply evaluate_not_value in eT; contradiction).
  - inversion eT; subst.
    -- apply evaluate_not_value in H5; contradiction. 
    -- apply evaluate_not_value in H6; contradiction. 
  - inversion H3; subst.
    -- apply evaluate_not_value in H6; contradiction. 
    -- apply evaluate_not_value in H7; contradiction.
  - inversion eT; subst.
    -- apply evaluate_not_value in H5; contradiction. 
    -- apply evaluate_not_value in H6; contradiction. 
  - inversion H3; subst.
    -- apply evaluate_not_value in H6; contradiction. 
    -- apply evaluate_not_value in H7; contradiction.
Qed.

Lemma evaluate_preserves_wf_term (k : lvl) (t t' : Λ) :
  k ⊩ t -> k ⊨ t ⟼ t' -> k ⊩ t'.
Proof.
  revert k t'; induction t; intros k t' Hvt HeT; inversion Hvt; subst; 
  inversion HeT; subst; try (constructor; auto); 
  try (now apply IHt); try (now apply IHt1); try (now apply IHt2).
  - apply subst_preserves_wf_zero; auto; now inversion H2.
  - apply subst_preserves_wf_zero; auto; now inversion H1.
  - now inversion Hvt; subst; inversion H4; subst.
  - now inversion Hvt; subst; inversion H4; subst.
Qed.

Lemma evaluate_subst_gen (lb k m n : lvl) (t t' : Λ) :
  lb <= k -> m <= lb -> n <= k -> m <= n -> k - lb = n - m ->
  lb ⊨ t ⟼ t' -> k ⊨ ([⧐ m – {n - m}] t) ⟼ ([⧐ m – {n - m}] t').
Proof.
  intros Hlelbk Hlemlb Hlenk Hlemn Heq eT.
  revert k m n Hlelbk Hlemlb Hlenk Hlemn Heq; induction eT; 
  intros; simpl; eauto; try (constructor; eauto; now apply Term.shift_value_iff).
  - rewrite subst_shift; auto; rewrite <- Heq at 4. 
    replace (k + (k0 - k)) with k0 by lia.
    constructor; now apply Term.shift_value_iff.
  - rewrite subst_shift; auto; rewrite <- Heq at 3. 
    replace (k + (k0 - k)) with k0 by lia.
    constructor; now apply Term.shift_value_iff.
  - constructor; try (now rewrite <- Term.shift_value_iff); apply IHeT; lia.
Qed.


Corollary evaluate_subst (m n : lvl) (t t' : Λ) :
  m <= n ->
  m ⊨ t ⟼ t' -> n ⊨ ([⧐ m – {n - m}] t) ⟼ ([⧐ m – {n - m}] t').
Proof. intros; now apply evaluate_subst_gen with (lb := m). Qed.

Lemma evaluate_shift_e_gen (lb k m n : lvl) (t t' : Λ) :
  lb <= k -> n <= lb -> m <= k -> n <= m -> k - lb = m - n ->
  k ⊨ ([⧐ n – {m - n}] t) ⟼ t' -> 
  exists t1, lb ⊨ t ⟼ t1 /\ t' = <[[⧐ n – {m - n}] t1]>.
Proof.
  revert lb k m n t'; induction t; 
  intros lb k m n t' Hle Hle1 Hle2 Hle3 Heq HeT;
  try (now inversion HeT).
  - simpl in *; inversion HeT; subst.
    -- destruct t1; try inversion H; subst.
       exists <[[x0 := t2 ~ lb] t1]>.
       split.
       + rewrite <- Term.shift_value_iff in H3.
         constructor; auto.
       + rewrite subst_shift; auto.
         replace (lb + (m - n)) with k by lia.
         reflexivity.
    -- apply IHt1 with (lb := lb) in H3  as [t1'' [HeT']]; auto; subst.
       exists <[t1'' t2]>; split.
       + now constructor.
       + simpl; auto.
    -- rewrite <- Term.shift_value_iff in H2.
       apply IHt2 with (lb := lb) in H4 as [t2'' [HeT']]; auto; subst.
       exists <[t1 t2'']>; split; auto.
  - simpl in *.
    inversion HeT; subst.
    -- apply IHt1 with (lb := lb) in H3 as [t1'' [HeT']]; auto; subst.
       exists <[⟨t1'',t2⟩]>; split; auto.
    -- rewrite <- Term.shift_value_iff in H2.
       apply IHt2 with (lb := lb) in H4 as [t2'' [HeT']]; auto; subst.
       exists <[⟨t1,t2''⟩]>; split; auto.
  - simpl in *.
    inversion HeT; subst.
    -- destruct t; try inversion H1; subst.
       exists <[[x := {Term.tm_fix <[\x:A, t ]>} ~ lb] t]>; split.
       + apply eT_fixv; auto.
       + rewrite subst_shift; auto.
         replace (lb + (m - n)) with k by lia.
         reflexivity.
    -- apply IHt with (lb := lb) in H1 as [t'' [HeT']]; auto; subst.
       exists (Term.tm_fix t''); split; auto.
  - inversion HeT; subst.
    -- apply IHt with (lb := lb) in H1 as [t'' [HeT']]; auto; subst.
       exists (Term.tm_fst t''); split; auto.
    -- destruct t; inversion H; subst.
       rewrite <- Term.shift_value_iff in H0,H2.
       exists t1; split; auto.       
  - inversion HeT; subst.
    -- apply IHt with (lb := lb) in H1 as [t'' [HeT']]; auto; subst.
       exists (Term.tm_snd t''); split; auto.
    -- destruct t; inversion H; subst.
       rewrite <- Term.shift_value_iff in H0,H2.
       exists t2; split; auto.
  - simpl in *; inversion HeT; subst.
    apply IHt with (lb := lb) in H3 as [t'' [HeT']]; auto; subst.
    exists <[first(A: t'')]>; split; auto.
  - simpl in *; inversion HeT; subst.
    -- apply IHt1 with (lb := lb) in H3 as [t1'' [HeT']]; auto; subst.
       exists <[t1'' >>> t2]>; split; auto.
    -- rewrite <- Term.shift_value_iff in H2.
       apply IHt2 with (lb := lb) in H4 as [t2'' [HeT']]; auto; subst.
       exists <[t1 >>> t2'']>; split; auto.
  - simpl in *; inversion HeT; subst.
    -- apply IHt1 with (lb := lb) in H3 as [t1'' [HeT']]; auto; subst.
       exists <[wormhole(t1'';t2)]>; split; auto.
    -- apply IHt2 with (lb := S (S lb)) in H4 as [t2'' [HeT']]; 
       auto; subst; try lia.
       rewrite <- Term.shift_value_iff in H2.
       exists <[wormhole(t1;t2'')]>; split; auto.
Qed.     

Corollary evaluate_shift_e (m n : lvl) (t t' : Λ) :
  n <= m ->
  m ⊨ ([⧐ n – {m - n}] t) ⟼ t' -> 
  exists t1, n ⊨ t ⟼ t1 /\ t' = <[[⧐ n – {m - n}] t1]>.
Proof.
  intros.
  now apply evaluate_shift_e_gen with (lb := n) (k := m).
Qed.

  
(** *** [multi] properties

  The reflexive transitive closure of the evaluation transition lifts [evaluate] rules. In addition, we have identity rules for variable, [unit] and [rsf] terms.
*)

#[export] Instance multi_refl (k : lvl) : Reflexive (multi k).
Proof. repeat red; intros; apply rt1n_refl. Qed. 

#[export] Instance multi_trans (k : lvl) : Transitive (multi k).
Proof.
  intros x y z HmeT HmeT'; induction HmeT; auto.
  eapply rt1n_trans; eauto. 
  now apply IHHmeT.
Qed.


Hint Constructors clos_refl_trans_1n : core.
Hint Resolve multi_refl multi_trans : core.


Lemma multi_var (k : lvl) (x : variable) : 

  (* ---------------- MET-Var *)
       k ⊨ {Term.tm_var x} ⟼⋆ {Term.tm_var x}.
Proof. reflexivity. Qed.

Lemma multi_rsf (k : lvl) (r : resource) : 

  (* -------------------------- MET-Rsf *)
       k ⊨ rsf[r] ⟼⋆ rsf[r].
Proof. reflexivity. Qed.

Lemma multi_unit (k : lvl) : 

  (* ---------------------- MET-Unit *)
       k ⊨ unit ⟼⋆ unit.
Proof. reflexivity. Qed.

Lemma multi_app1 (k : lvl) (t t' t2 : Λ) : 

            k ⊨ t ⟼⋆ t' -> 
  (* --------------------------- MET-App1 *)
       k ⊨ (t t2) ⟼⋆ (t' t2).
Proof. 
  intro HeT; induction HeT.
  - reflexivity.
  - apply rt1n_trans with <[y t2]>; auto.
Qed.

Lemma multi_app2 (k : lvl) (t t' t1 : Λ) : 

       value(t1) -> k ⊨ t ⟼⋆ t' ->   
  (* -------------------------------- MET-App2 *)
         k ⊨ (t1 t) ⟼⋆ (t1 t').
Proof. 
  intros Hvt HeT; induction HeT.
  - reflexivity.
  - apply rt1n_trans with <[t1 y]>; auto.
Qed.

Lemma multi_appv (k : lvl) (x : variable) (C : Τ) (v t : Λ) :

                    value(v) -> 
  (* ----------------------------------------- MET-Appv *)
       k ⊨ ((\x:C, t) v) ⟼⋆ ([x := v ~ k] t).
Proof. 
  intro Hv; apply rt1n_trans with (y := <[[x := v ~ k] t]>); auto.
Qed.

Lemma multi_fix1 (k : lvl) (t t' : Λ) : 

            k ⊨ t ⟼⋆ t' -> 
  (* ----------------------------- MET-Fix1 *)
       k ⊨ (Fix t) ⟼⋆ (Fix t').
Proof. 
  intro HeT; induction HeT.
  - reflexivity.
  - apply rt1n_trans with <[Fix y]>; auto.
Qed.

Lemma multi_fix (k : lvl) (x : variable) (C : Τ) (t : Λ) :

  (* ------------------------------------------------------- MET-Fix *)
       k ⊨ (Fix (\x:C, t)) ⟼⋆ ([x := (Fix (\x:C, t)) ~ k] t).
Proof. 
  apply rt1n_trans with (y := <[[x := (Fix (\x:C, t)) ~ k] t]>); auto.
Qed.

Lemma multi_pair1 (k : lvl) (t t' t2 : Λ) : 

          k ⊨ t ⟼⋆ t' -> 
  (* --------------------------- MET-Pair1 *)
       k ⊨ ⟨t,t2⟩ ⟼⋆ ⟨t',t2⟩.
Proof.
  intro eT; induction eT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[⟨y,t2⟩]>; auto. 
Qed.

Lemma multi_pair2 (k : lvl) (t t' t1 : Λ) : 

       value(t1) -> k ⊨ t ⟼⋆ t' -> 
  (* -------------------------------- MET-Pair2 *)
         k ⊨ ⟨t1,t⟩ ⟼⋆ ⟨t1,t'⟩.
Proof.
  intros Hvt eT; induction eT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[⟨t1,y⟩]>; auto. 
Qed.

Lemma multi_fstv (k : lvl) (t1 t2 : Λ) : 

       value(t1) -> value(t2) -> 
  (* ----------------------------- MET-Fstv *)
        k ⊨ fst.⟨t1,t2⟩ ⟼⋆ t1.
Proof. intros Hvt1 Hvt2; apply rt1n_trans with t1; auto. Qed.

Lemma multi_fst1 (k : lvl) (t t' : Λ) : 

           k ⊨ t ⟼⋆ t' -> 
  (* ------------------------- MET-Fst1 *)
       k ⊨ fst.t ⟼⋆ fst.t'.
Proof.
  intro eT; induction eT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[fst.y]>; auto. 
Qed.

Lemma multi_sndv (k : lvl) (t1 t2 : Λ) : 

       value(t1) -> value(t2) -> 
  (* ----------------------------- MET-Sndv *)
        k ⊨ snd.⟨t1,t2⟩ ⟼⋆ t2.
Proof. intros Hvt1 Hvt2; apply rt1n_trans with t2; auto. Qed.

Lemma multi_snd1 (k : lvl) (t t' : Λ) : 

           k ⊨ t ⟼⋆ t' -> 
  (* ------------------------- MET-Snd1 *)
       k ⊨ snd.t ⟼⋆ snd.t'.
Proof.
  intro eT; induction eT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[snd.y]>; auto. 
Qed.

Lemma multi_first (k : lvl) (C : Τ) (t t' : Λ) : 
 
              k ⊨ t ⟼⋆ t' -> 
  (* ------------------------------- MET-First *)
       k ⊨ first(C:t) ⟼⋆ first(C:t').
Proof.
  intros HeT; induction HeT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[first(C:y)]>; auto. 
Qed.

Lemma multi_comp1 (k : lvl) (t t' t2 : Λ) : 

              k ⊨ t ⟼⋆ t' -> 
  (* ------------------------------- MET-Comp1 *)
       k ⊨ t >>> t2 ⟼⋆ t' >>> t2.
Proof. 
  intros HeT; induction HeT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[y >>> t2]>; auto.
Qed.

Lemma multi_comp2 (k : lvl) (t t' t1 : Λ) : 
       
       value(t1) -> k ⊨ t ⟼⋆ t' -> 
  (* -------------------------------- MET-Comp2 *)
        k ⊨ t1 >>> t ⟼⋆ t1 >>> t'.
Proof. 
  intros Hvt HeT; induction HeT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[t1 >>> y]>; auto.
Qed.

Lemma multi_wh1 (k : lvl) (t t' t2 : Λ) : 

                    k ⊨ t ⟼⋆ t' -> 
  (* ------------------------------------------- MET-Wh1 *)
       k ⊨ wormhole(t;t2) ⟼⋆ wormhole(t';t2).
Proof. 
  intros HeT; induction HeT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[wormhole(y;t2)]>; auto.
Qed.

Lemma multi_wh2 (k : lvl) (t t' t1 : Λ) : 

        value(t1) -> (S (S k)) ⊨ t ⟼⋆ t' -> 
  (* ------------------------------------------- MET-Wh2 *)
       k ⊨ wormhole(t1;t) ⟼⋆ wormhole(t1;t').
Proof. 
  intros Hvt HeT; dependent induction HeT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[wormhole(t1;y)]>; auto.
    apply (IHHeT k); auto.
Qed.


Hint Resolve multi_appv multi_app1 multi_app2 multi_fix multi_fix1 
             multi_pair1 multi_pair2 multi_fst1 multi_fstv multi_snd1 
             multi_sndv multi_comp1 multi_comp2 multi_first multi_wh1 multi_wh2 : core.

Theorem multi_evaluate_subst_gen (lb k m n : lvl) (t t' : Λ) :
  lb <= k -> m <= lb -> n <= k -> m <= n -> k - lb = n - m ->
  lb ⊨ t ⟼⋆ t' -> k ⊨ ([⧐ m – {n - m}] t) ⟼⋆ ([⧐ m – {n - m}] t').
Proof.
  intros; induction H4; try now constructor.
  eapply rt1n_trans with (y := <[[⧐ m – {n - m}] y ]>); auto.
  eapply evaluate_subst_gen with (lb := lb); auto.
Qed.

Corollary multi_evaluate_subst (m n : lvl) (t t' : Λ) :
  m <= n ->
  m ⊨ t ⟼⋆ t' -> n ⊨ ([⧐ m – {n - m}] t) ⟼⋆ ([⧐ m – {n - m}] t').
Proof. intros; now apply multi_evaluate_subst_gen with (lb := m). Qed.

Lemma eT_to_MeT (k : lvl) (t t' : Λ) : 
  k ⊨ t ⟼ t' -> k ⊨ t ⟼⋆ t'.
Proof.
  intro eT; induction eT; auto.
Qed.  

Lemma multi_evaluate_shift_e (m n : lvl) (t t' : Λ) :
  n <= m ->
  m ⊨ ([⧐ n – {m - n}] t) ⟼⋆ t' -> 
  exists t1, n ⊨ t ⟼⋆ t1 /\ t' = <[[⧐ n – {m - n}] t1]>.
Proof.
  intros; revert H; dependent induction H0; intros.
  - exists t; split; auto.
    reflexivity.
  - apply evaluate_shift_e in H as [t1 [HeT]]; auto; subst.
    specialize (IHclos_refl_trans_1n n t1).
    destruct IHclos_refl_trans_1n; auto.
    destruct H as [HeT']; subst.
    exists x; split; auto.
    apply eT_to_MeT in HeT.
    transitivity t1; auto.
Qed.

(** *** [halts] property *)

Lemma evaluate_preserves_halting (k : lvl) (t t' : Λ) :
  k ⊨ t ⟼ t' -> (halts k t <-> halts k t').
Proof.
  intro HeT; unfold halts; split; intros [t'' [HmeT Hv]].
  - destruct HmeT.
    -- apply evaluate_not_value in HeT; contradiction.
    -- apply (evaluate_deterministic k t t' y HeT) in H as Heq; subst.
       now exists z.
  - exists t''; split; try assumption; now apply rt1n_trans with (y := t').     
Qed.

Corollary evaluate_preserves_halting' (k : lvl) (t t' : Λ) :
  halts k t -> k ⊨ t ⟼ t' -> halts k t'.
Proof.
  intros.
  rewrite evaluate_preserves_halting with (t' := t')in H; auto.
Qed.

Lemma multi_preserves_halting (k : lvl) (t t' : Λ) :
  k ⊨ t ⟼⋆ t' -> (halts k t <-> halts k t').
Proof.
  intros meT; induction meT; unfold halts; split; intros [t'' [meT' Hv]];
  try (exists t''; now split).
  - apply evaluate_preserves_halting in H as H'.
    assert (halts k x). { exists t''; now split. }
    rewrite H' in H0; now rewrite IHmeT in H0.
  - apply evaluate_preserves_halting in H as H'.
    assert (halts k z). { exists t''; now split. }
    rewrite <- IHmeT in H0. now rewrite <- H' in H0.
Qed.

Lemma halts_weakening (m n : lvl) (t : Λ) : 
  m <= n -> halts m t -> halts n <[[⧐ m – {n - m}] t]>.
Proof.
  unfold halts; intros. destruct H0 as [t' [HeT Hvt']].
  exists <[[⧐ m – {n - m}] t']>; split.
  - eapply multi_evaluate_subst_gen; eauto.
  - now apply Term.shift_value_iff.
Qed.

Lemma halts_weakening_1 (m n : lvl) (t : Λ) : 
  halts m t -> halts (m + n) <[[⧐ m – n] t]>.
Proof.
  intro Hlt. 
  replace <[[⧐ m – n] t]> with <[[⧐ m – {(m + n) - m}] t ]> by (f_equal; lia).
  apply halts_weakening; auto; lia.
Qed.

Lemma halts_pair (k : lvl) (t1 t2 : Λ) :
  halts k <[⟨t1,t2⟩]> <-> halts k t1 /\ halts k t2.
Proof.
  assert (Hpair : forall k t1 t2 t, k ⊨ ⟨t1,t2⟩ ⟼⋆ t -> exists t1' t2', t = <[⟨t1',t2'⟩]>).
  {
    intros k' t'1 t'2 t HeT; dependent induction HeT; subst.
    - exists t'1; now exists t'2.
    - inversion H; subst; eauto. 
  }
  split; intros HA.
  - destruct HA as [t [HmeT Hvt]]. apply Hpair in HmeT as Heq.
    destruct Heq as [t1' [t2' Heq]]; subst. dependent induction HmeT.
    -- inversion Hvt; subst; split.
       + exists t1; split; now auto.
       + exists t2; split; now auto.
    -- inversion H; subst.
       + eapply IHHmeT with (t1' := t1') (t2' := t2') in Hvt; auto.
         destruct Hvt; split; auto; clear H1.
         rewrite evaluate_preserves_halting; eauto.
       + eapply IHHmeT with (t1 := t1) (t2 := t') in Hvt; eauto.
         destruct Hvt; split; auto; clear H0.
         rewrite evaluate_preserves_halting; eauto.
  - destruct HA. destruct H as [t1' [HmeT1 Hvt1']];
    destruct H0 as [t2' [HmeT2 Hvt2']].
    exists <[⟨t1',t2'⟩]>; split.
    -- apply multi_trans with <[⟨t1',t2⟩]>.
       + now apply multi_pair1.
       + now apply multi_pair2.
    -- now constructor.
Qed.

Lemma halts_first (k : lvl) (C : Τ) (t : Λ) :
  halts k <[first(C:t)]> <-> halts k t.
Proof.
  split; intros HA.
  - destruct HA as [t' [HmeT Hvt]]; dependent induction HmeT.
    -- inversion Hvt; subst; exists t; split; auto.  apply rt1n_refl.
    -- inversion H; subst. 
       apply (IHHmeT C t') in Hvt; eauto.
       rewrite evaluate_preserves_halting; eauto.
  - destruct HA as [t' [HmeT Hvt']]; exists <[first(C:t')]>; split; auto.
Qed.

Lemma halts_comp (k : lvl) (t1 t2 : Λ) :
  halts k <[t1 >>> t2]> <-> halts k t1 /\ halts k t2.
Proof.
  assert (Hcomp : forall k t1 t2 t, k ⊨ t1 >>> t2 ⟼⋆ t ->
                             exists t1' t2', t = <[t1' >>> t2']>).
  {
    intros k' t'1 t'2 t HeT; dependent induction HeT; subst.
    - exists t'1; now exists t'2.
    - inversion H; subst; eauto. 
  }
  split; intros HA.
  - destruct HA as [t [HmeT Hvt]]. apply Hcomp in HmeT as Heq.
    destruct Heq as [t1' [t2' Heq]]; subst. dependent induction HmeT.
    -- inversion Hvt; subst; split.
       + exists t1; split; now auto.
       + exists t2; split; now auto.
    -- inversion H; subst.
       + eapply IHHmeT with (t1 := t1'0) (t2 := t2) in Hvt; eauto.
         destruct Hvt; split; auto; clear H1.
         rewrite evaluate_preserves_halting; eauto.
       + eapply IHHmeT with (t1 := t1) (t2 := t') in Hvt; eauto.
         destruct Hvt; split; auto; clear H0.
         rewrite evaluate_preserves_halting; eauto.
  - destruct HA. destruct H as [t1' [HmeT1 Hvt1']];
    destruct H0 as [t2' [HmeT2 Hvt2']].
    exists <[t1' >>> t2']>; split.
    -- apply multi_trans with <[t1' >>> t2]>.
       + now apply multi_comp1.
       + now apply multi_comp2.
    -- now constructor.
Qed.

Lemma halts_wh (k : lvl) (t1 t2 : Λ) :
  halts k <[wormhole(t1;t2)]> <-> halts k t1 /\ halts (S (S k)) t2.
Proof.
  assert (Hwh : forall k t1 t2 t, k ⊨ wormhole(t1;t2) ⟼⋆ t ->
                             exists t1' t2', t = <[wormhole(t1';t2')]>).
  {
    intros k' t'1 t'2 t HeT; dependent induction HeT; subst.
    - exists t'1; now exists t'2.
    - inversion H; subst; eauto. 
  }
  split; intros HA.
  - destruct HA as [t [HmeT Hvt]]. apply Hwh in HmeT as Heq.
    destruct Heq as [t1' [t2' Heq]]; subst. dependent induction HmeT.
    -- inversion Hvt; subst; split.
       + exists t1; split; now auto.
       + exists t2; split; now auto.
    -- inversion H; subst.
       + eapply IHHmeT with (t1 := t1'0) (t2 := t2) in Hvt; eauto.
         destruct Hvt; split; auto; clear H1.
         rewrite evaluate_preserves_halting; eauto.
       + eapply IHHmeT with (t1 := t1) (t2 := t') in Hvt; eauto.
         destruct Hvt; split; auto; clear H0.
         rewrite evaluate_preserves_halting; eauto.
  - destruct HA. destruct H as [t1' [HmeT1 Hvt1']];
    destruct H0 as [t2' [HmeT2 Hvt2']].
    exists <[wormhole(t1';t2')]>; split.
    -- apply multi_trans with <[wormhole(t1';t2)]>.
       + now apply multi_wh1.
       + now apply multi_wh2.
    -- now constructor.
Qed.


(** *** [halts_re] properties *)

Lemma halts_re_add (k : lvl) (r: resource) (v: 𝑣) (V: 𝐕) :
  (halts k (Cell.extract v)) /\ halts_re k V -> halts_re k (⌈r ⤆ v⌉ V)%re.
Proof.
  intros [Hltv Hltm] r' v' Hfi.
  destruct (Resource.eq_dec r r') as [| Hneq]; subst.
  - rewrite RE.add_eq_o in Hfi; auto.
    inversion Hfi; subst; auto.
  - rewrite RE.add_neq_o in Hfi; auto.
    now apply Hltm in Hfi.
Qed.

Lemma halts_re_weakening (m n : lvl) (V: 𝐕) : 
  m <= n -> halts_re m V -> halts_re n ([⧐ m – (n - m)] V)%re.
Proof.
  intros Hle Hlt r v Hfi. 
  apply RE.shift_find_e_1 in Hfi as HI.
  destruct HI as [[r' Heqr'] [v' Heqv']]; subst.
  rewrite <- RE.shift_find_iff in Hfi. 
  destruct v'; simpl in *; 
  apply halts_weakening; auto; apply Hlt in Hfi; now simpl in *.
Qed.

Lemma halts_re_weakening_1 (m n : lvl) (V: 𝐕) : 
  halts_re m V -> halts_re (m + n) ([⧐ m – n] V)%re.
Proof.
  intro Hlt; replace n with ((m + n) - m) at 2 by lia.
  apply halts_re_weakening; auto; lia.
Qed.

#[export] Instance halts_re_iff : 
  Proper (Logic.eq ==> RE.eq ==> iff) halts_re. 
Proof. 
  unfold halts_re; intros m n Heqm V V' HeqV; subst.
  now rewrite HeqV. 
Qed.

(** *** [halts_sk] properties *)

Lemma halts_sk_nil (m : lvl) : halts_sk m [].
Proof. 
  constructor.
Qed.

Lemma halts_sk_app (m : lvl) (st st' : 𝐖) :
  halts_sk m (st ++ st') <-> halts_sk m st /\ halts_sk m st'.
Proof.
  apply Forall_app.
Qed.

Lemma halts_sk_weakening (m n : lvl) (st : 𝐖) : 
  m <= n -> 
  halts_sk m st -> halts_sk n ([⧐ m – (n - m)] st)%sk.
Proof.
  intro Hle.
  induction st; intro Hlt.
  - simpl.
    constructor.
  - simpl in *.
    inversion Hlt; subst.
    destruct a as [[rg rs] v].
    constructor; simpl.
    -- now apply halts_weakening.
    -- now apply IHst.
Qed.

Lemma halts_sk_init_locals (m : lvl) (st : 𝐖) (V : 𝐕) :
  halts_sk m st -> halts_re m V -> 
  halts_re m (ST.init_locals st V).
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
    apply halts_re_add; split.
    -- now simpl.
    -- apply halts_re_add; split; auto.
       simpl.
       exists <[unit]>; split; auto.
       reflexivity.
Qed.

Lemma halts_sk_update_locals (k : lvl) (W : 𝐖) (V : 𝐕) :
  halts_re k V -> halts_sk k W -> 
  halts_sk k (ST.update_locals W V).
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


(** *** [halts_sre] properties *)

Lemma halts_sre_Empty (k: lvl) (t: 𝐄) :
  SRE.Empty t -> halts_sre k t.
Proof.
  intros HEmp k' v Hfi.
  exfalso.
  apply SRE.find_2 in Hfi.
  apply (HEmp k' v Hfi).
Qed.

Lemma halts_sre_union (k : lvl) (sr sr': 𝐄) :
  halts_sre k sr /\ halts_sre k sr' -> halts_sre k (sr ∪ sr')%sr.
Proof.
  unfold halts_sre; intros [HFa HFa'] r v Hfi.
  apply SRE.find_2 in Hfi. 
  apply SRE.extend_mapsto_iff in Hfi as [HM | [HM _]]; 
  apply SRE.find_1 in HM.
  - now apply (HFa' r).
  - now apply (HFa r).
Qed.

Lemma halts_sre_add (k : lvl) (r: resource) (v: Λ) (sr: 𝐄) :
  (halts k v) /\ halts_sre k sr -> 
  halts_sre k (SRE.Raw.add r v sr).
Proof.
  intros [Hltv Hlts] r' v' Hfi.
  rewrite SRE.add_o in Hfi; 
  destruct (Resource.eq_dec r r') as [| Hneq]; subst.
  - inversion Hfi; subst; auto.
  - apply Hlts in Hfi; auto.
Qed.

Lemma halts_sre_add_iff (k : lvl) (r: resource) (v: Λ) (sr: 𝐄) :
  (r ∉ sr)%sr -> 
  halts_sre k (SRE.Raw.add r v sr) <-> 
  (halts k v) /\ halts_sre k sr.
Proof.
  intros HIn; split.
  - unfold halts; intro HFa.
    apply SRE.For_all_add_notin in HFa; auto.
  - apply halts_sre_add.
Qed.

Lemma halts_sre_weakening (m n : lvl) (sr: 𝐄) : 
  m <= n -> 
  halts_sre m sr -> halts_sre n ([⧐ m – (n - m)] sr)%sr.
Proof.
  intros Hle Hlt r v Hfi. 
  apply SRE.shift_find_e_1 in Hfi as HI.
  destruct HI as [[r' Heqr'] [v' Heqv']]; subst.
  rewrite <- SRE.shift_find_iff in Hfi. 
  apply halts_weakening; auto; apply Hlt in Hfi; now simpl in *.
Qed.

Lemma halts_sre_weakening_1 (m n : lvl) (sr: 𝐄) : 
  halts_sre m sr -> halts_sre (m + n) ([⧐ m – n] sr)%sr.
Proof.
  intro Hlt; replace n with ((m + n) - m) at 2 by lia.
  apply halts_sre_weakening; auto; lia.
Qed.

#[export] Instance halts_sre_iff : 
  Proper (Logic.eq ==> SRE.eq ==> iff) halts_sre. 
Proof. 
  unfold halts_sre; 
  intros m n Heqm sr sr' Heqrs; subst.
  now rewrite Heqrs. 
Qed.

(** *** [isvalueof] properties *)

Lemma isvalueof_eT (n : lvl) (t t' : Λ) (v : Λ) :
  n ⊨ t ⟼ t' -> isvalueof n t v -> isvalueof n t' v.
Proof.
  intros HeT [HmeT Hv].
  split; auto.
  revert t' HeT Hv.
  induction HmeT; intros.
  - apply evaluate_not_value in HeT; contradiction.
  - eapply evaluate_deterministic in H; eauto; subst; auto.
Qed.

Lemma isvalueof_eT' (n : lvl) (t t' : Λ) (v : Λ) :
  n ⊨ t ⟼ t' -> isvalueof n t' v -> isvalueof n t v.
Proof.
  intros HeT [HmeT Hv].
  split; auto.
  transitivity t'; auto.
  now apply eT_to_MeT.
Qed.

Lemma isvalueof_first (n : lvl) (C : Τ) (t v : Λ) :
  isvalueof n <[first(C:t)]> <[first(C:v)]> -> isvalueof n t v.
Proof.
  intros [HmeT Hvt]; inversion Hvt; subst.
  split; auto.
  clear Hvt.
  dependent induction HmeT; subst; auto.
  - reflexivity.
  - inversion H; subst.
    transitivity t'; auto.
    -- now apply eT_to_MeT.
    -- apply (IHHmeT C); auto.
Qed.

Lemma isvalueof_first' (n : lvl) (C: Τ) (t v : Λ) :
  isvalueof n t v -> isvalueof n <[first(C:t)]> <[first(C:v)]>.
Proof.
  intros [HmeT Hvt]; split; auto.
Qed.

Lemma isvalueof_first_e (n : lvl) (C: Τ) (t v : Λ) :
  isvalueof n <[first(C:t)]> v -> exists v', (v = <[first(C:v')]>)%type.
Proof.
  intros [HmeT Hvt].
  revert Hvt.
  dependent induction HmeT; intro.
  - now exists t.
  - inversion H; subst. 
    eapply IHHmeT; eauto.
Qed.

Lemma isvalueof_compl (n : lvl) (t1 t2 v : Λ) :
  halts n t2 ->
  isvalueof n t1 v ->
  exists v', isvalueof n t2 v' /\ isvalueof n <[t1 >>> t2]> <[v >>> v']>.
Proof.
  intros [v' [HmeT' Hv']] [HmeT Hv].
  exists v'; split.
  - split; auto.
  - split; auto.
    transitivity <[v >>> t2]>.
    -- now apply multi_comp1.
    -- now apply multi_comp2.
Qed.

Lemma isvalueof_compr (n : lvl) (t1 t2 v : Λ) :
  halts n t1 ->
  isvalueof n t2 v ->
  exists v', isvalueof n t1 v' /\ isvalueof n <[t1 >>> t2]> <[v' >>> v]>.
Proof.
  intros [v' [HmeT' Hv']] [HmeT Hv].
  exists v'; split.
  - split; auto.
  - split; auto.
    transitivity <[v' >>> t2]>.
    -- now apply multi_comp1.
    -- now apply multi_comp2.
Qed.

Lemma isvalueof_comp_e (n : lvl) (t1 t2 v : Λ) :
  isvalueof n <[t1 >>> t2]> v -> 
  exists v1 v2, (v = <[v1 >>> v2]>)%type.
Proof.
  intros [HmeT Hv].
  revert Hv; dependent induction HmeT; intro.
  - exists t1, t2. 
    split; auto.
  - inversion H; subst. 
    -- apply (IHHmeT t1' t2) in Hv; auto.
    -- apply (IHHmeT t1 t') in Hv; auto.
Qed.

Lemma isvalueof_comp (n : lvl) (t1 t2 v1 v2 : Λ) :
  isvalueof n <[t1 >>> t2]> <[v1 >>> v2]> ->
  isvalueof n t1 v1 /\ isvalueof n t2 v2.
Proof.
  intros []; revert H0.
  dependent induction H; intro Hv; inversion Hv; subst.
  - split.
    -- split; auto; reflexivity.
    -- split; auto; reflexivity.
  - split.
    -- inversion H; subst.
       + apply (IHclos_refl_trans_1n t1' t2) in Hv as []; auto.
         destruct H1.
         apply eT_to_MeT in H7.
         split; auto.
         now transitivity t1'.
       + apply (IHclos_refl_trans_1n t1 t') in Hv as []; auto.
    -- inversion H; subst.
       + apply (IHclos_refl_trans_1n t1' t2) in Hv as []; auto.
       + apply (IHclos_refl_trans_1n t1 t') in Hv as []; auto.
         destruct H2.
         apply eT_to_MeT in H8.
         split; auto.
         now transitivity t'.
Qed.


Lemma isvalueof_wh (n : lvl) (i t v : Λ) :
  halts n i ->
  isvalueof (S (S n)) t v -> 
  exists v', isvalueof n i v' /\ isvalueof n <[wormhole(i;t)]> <[wormhole(v';v)]>.
Proof.
  intros [v' [HmeT' Hv']] [HmeT Hv].
  exists v'.
  split; split; auto.
  transitivity <[wormhole(v';t)]>.
  - now apply multi_wh1.
  - now apply multi_wh2.
Qed.

Lemma isvalueof_shift (n m : lvl) (t v : Λ) :
  n <= m ->
  isvalueof m  <[ [⧐ n – {m - n}] t]> v ->
  exists v', isvalueof n t v' /\ v =  <[[⧐ n – {m - n}] v']>.
Proof.
  intros Hle [HmeT Hv].
  apply multi_evaluate_shift_e in HmeT as [t' [HmeT]]; auto; subst.
  rewrite <- Term.shift_value_iff in Hv.
  exists t'; split; auto.
  split; auto.
Qed.

(** ---- *)

Open Scope rcontext_scope.

(** ** Preservation - Evaluation *)

Hint Constructors well_typed evaluate : core.

(** *** Substitution preserves typing 

  Suppose [y] a variable, [t] an expression well-typed by [A] under [Re] and [⌈y ⤆ B⌉ Γ] (2), [v] an expression typed as [B] under [Re1] and [Γ] (3). If [Re1] is included in [Re] (4) and well-formed under its own new key (1), then the resulting expression of substitute [y] by [v] in [t] is typed by [A] under [Re] and [Γ]. We can specify the proof by assuming that [Re1] is equals to [Re] (see the following corollary).
*)
Theorem subst_preserves_typing_gen (Γ : Γ) (Re Re1 : ℜ) (y : variable) (v t : Λ) (A B : Τ) :

       (* (1) *) (Re1⁺ ⊩ Re1)%rc -> (* (2) *) (⌈y ⤆ B⌉ Γ)%vc ⋅ Re ⊢ t ∈ A -> 
       (* (3) *) (∅)%vc ⋅ Re1 ⊢ v ∈ B -> (* (4) *) Re1 ⊆ Re ->
  (* -------------------------------------------------------------------------- *)
               Γ ⋅ Re ⊢ ([y := v ~  {Re1⁺} – {Re⁺ - Re1⁺}] t) ∈ A.
Proof.
  revert Γ Re Re1 v A B y. 
  induction t; intros Γ Re Re1 v' A' B' y HvRe Hwt Hwv Hsub; 
  simpl; inversion Hwt; subst; auto; (try econstructor; eauto).
  (* variable *)
  - (* clean *) rename H2 into HfΓ. (* clean *)

    destruct (Var.eqb_spec y x); subst.
    (* x = y *)
    -- rewrite VContext.add_eq_o in HfΓ; auto. 
       inversion HfΓ; subst; clear HfΓ. 
       apply weakening_Γ_empty.
       apply weakening_ℜ; auto.
    (* x <> y *)
    -- rewrite VContext.add_neq_o in HfΓ; auto. 
  (* abstraction *)
  - destruct (Var.eqb_spec y x); subst; constructor; auto.
    -- now rewrite VContext.add_shadow in H5.
    -- rewrite VContext.add_add_2 in H5; auto.
       apply (IHt _ _ _ _ _ B' y HvRe H5 Hwv Hsub).
  (* wormhole *)
  - apply RC.Ext.new_key_Submap in Hsub as Hle.
    replace (S (S (Re⁺ - Re1⁺))) with ((S (S (Re⁺))) - Re1⁺) by lia.
    eapply IHt2 in Hwv; eauto.
    + erewrite <- RC.new_key_wh; eauto.
    + now apply RC.Ext.new_key_Submap_add.
Qed.

Corollary subst_preserves_typing (Γ : Γ) (Re : ℜ) (y : variable) (v t : Λ) (A B : Τ) :

       (* (1) *) (Re⁺ ⊩ Re)%rc -> 
       (* (2) *) (⌈y ⤆ B⌉ Γ)%vc ⋅ Re ⊢ t ∈ A -> (* (3) *) (∅)%vc ⋅ Re ⊢ v ∈ B -> 
  (* ----------------------------------------------------------------------------- *)
                       Γ ⋅ Re ⊢ ([y := v ~ {Re⁺}] t) ∈ A.
Proof.
  intros HvRe Hwt Hwv; replace 0 with (Re⁺ - Re⁺) by lia. 
  apply (subst_preserves_typing_gen _ _ Re _ _ _ _ B HvRe Hwt Hwv); auto.
Qed.

(** *** Evaluate preserves typing.

  Suppose [t] an expression well-typed by [A] under [Re] (2) and [t'] the resulting expression of apply a transition rule on [t] (3). If [Re] is well-formed under its own new key (1), then [t'] is also typed by [A] under [Re].
*)
Theorem evaluate_preserves_typing (Re : ℜ) (t t' : Λ) (A : Τ) :

       (* (1) *) (Re⁺ ⊩ Re)%rc -> 
       (* (2) *) (∅)%vc ⋅ Re ⊢ t ∈ A -> (* (3) *) Re⁺ ⊨ t ⟼ t' -> 
  (* --------------------------------------------------------------- *)
                      (∅)%vc ⋅ Re ⊢ t' ∈ A.
Proof. 
  intros HvRe wt; revert t'; dependent induction wt; intros t' 
  HeT; inversion HeT; subst; eauto.
  (* abstraction *)
  - inversion wt1; subst. 
    eapply subst_preserves_typing; eauto.
  (* fst *)
  - inversion wt; subst; auto.
  (* snd *)
  - inversion wt; subst; auto.
  (* fix *)
  - inversion wt; subst.
    apply (subst_preserves_typing _ _ _ _ _ _ C); auto.
  - apply wt_wh with (R' := R') (C := C); auto.
    apply IHwt2; auto. 
    -- apply well_typed_implies_Wf in wt1 as [_ Hvτ]; auto.
       rewrite RC.new_key_wh; apply RC.Wf_wh; auto;
       repeat constructor; simpl; auto.
    -- now rewrite RC.new_key_wh.
Qed.

(** *** Multi-Evaluation preserves typing.

  Same as above but with the reflexive transitive closure of the evaluation transition.
*)
Theorem multi_preserves_typing (Re : ℜ) (t t' : Λ) (A : Τ) :

    (* (1) *) (Re⁺ ⊩ Re)%rc ->
    (* (2) *) (∅)%vc ⋅ Re ⊢ t ∈ A -> (* (3) *) Re⁺ ⊨ t ⟼⋆ t' -> 
(*-----------------------------------------------------------------*)
                        (∅)%vc ⋅ Re ⊢ t' ∈ A.
Proof.
  intros HvRe Hwt meT; dependent induction meT; subst; auto.
  apply IHmeT; auto. 
  apply (evaluate_preserves_typing Re x y A HvRe Hwt H).
Qed.

(** ---- *)

(** ** Progress - Evaluation 

  Suppose [t] an expression well-typed by [C] under [Re] (1). Either, [t] is a value (2) or it exists an evaluation of [t], named here [t'] (3).
*)
Theorem progress_of_evaluate (Re : ℜ) (t : Λ) (C : Τ) :
                  (* (1) *) (∅)%vc ⋅ Re ⊢ t ∈ C -> 
  (* ------------------------------------------------------------- *)
       (* (2) *) value(t) \/ (* (3) *) exists t', Re⁺ ⊨ t ⟼ t'.
Proof.
  revert Re C; induction t; intros Re C' Hwt; inversion Hwt; subst; try (now left);
  try (apply IHt1 in H3 as H3'; apply IHt2 in H5 as H5').
  - destruct H3',H5'; right. 
    -- inversion H; subst; inversion H3; subst. exists <[[x:= t2 ~ {Re⁺}] t]>.
      now constructor.
    -- destruct H0; exists <[t1 x]>; now constructor.
    -- destruct H; exists <[x t2]>; now constructor.
    -- destruct H; exists <[x t2]>; now constructor.
  - destruct H3',H5'; auto.
    -- right; destruct H0; exists <[⟨t1,x⟩]>; now constructor.
    -- right; destruct H; exists <[⟨x,t2⟩]>; now constructor.
    -- right; destruct H; exists <[⟨x,t2⟩]>; now constructor.
  - apply IHt in H2 as H2'; destruct H2'; right.
    -- inversion H2; subst; inversion H; subst.
       exists <[[x := (Fix (\x:C',t0)) ~ {Re⁺}] t0]>; now constructor.
    -- destruct H; exists (Term.tm_fix x); now constructor.
  - apply IHt in H2 as H2'; destruct H2'; right.
    -- inversion H; subst; inversion H2; subst; exists v1; now constructor. 
    -- destruct H; exists (Term.tm_fst x); now constructor.
  - apply IHt in H2 as H2'; destruct H2'; right.
    -- inversion H; subst; inversion H2; subst; exists v2; now constructor. 
    -- destruct H; exists (Term.tm_snd x); now constructor.
  - apply IHt in H3 as H0'; destruct H0' as [Hvt | [t' HeT']]; auto.
    right; exists <[first(A:t')]>; now constructor.
  - apply IHt1 in H1 as H1'; apply IHt2 in H5 as H5';
    destruct H1' as [Hvt1 | [t1' HeT1']]; destruct H5' as [Hvt2 | [t2' HeT2']];
    try (left; now constructor); right.
    -- exists <[t1 >>> t2']>; now constructor.
    -- exists <[t1' >>> t2]>; now constructor.
    -- exists <[t1' >>> t2]>; now constructor.
  - apply IHt1 in H6 as H6'; apply IHt2 in H8 as H8';
    destruct H6' as [Hvt1 | [t1' HeT1']]; destruct H8' as [Hvt2 | [t2' HeT2']];
    try (left; now constructor); right.
    -- exists <[wormhole(t1;t2')]>; constructor; auto.
       rewrite RC.new_key_wh in HeT2'; auto.
    -- exists <[wormhole(t1';t2)]>; now constructor.
    -- exists <[wormhole(t1';t2)]>; now constructor.
Qed.

Corollary progress_of_multi_evaluation (Re : ℜ) (t : Λ) (C : Τ) :
  (∅)%vc ⋅ Re ⊢ t ∈ C ->  exists t', Re⁺ ⊨ t ⟼⋆ t'.
Proof.
  intro Hwt.
  apply progress_of_evaluate in Hwt as [Hvt | [t' HeT]].
  - exists t.
    reflexivity.
  - exists t'.
    now apply eT_to_MeT.
Qed.