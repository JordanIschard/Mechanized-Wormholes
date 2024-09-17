From Coq Require Import Relations.Relation_Operators Classes.RelationClasses Lia Program.
From Mecha Require Import Var Resource Resources Term Typ VContext RContext Type_System.
Import VarNotations ResourceNotations ResourcesNotations SetNotations 
       TypNotations TermNotations VContextNotations RContextNotations.

Open Scope term_scope.

(** * Semantics - Evaluation

  Wormholes’s dynamic semantics is split in three sets of transition rules: the evaluation transition which extends standard β-reduction; the functional transition, defined in [Functional_Transition.v], which performs the logical instant, and the temporal transition, defined in [Temporal_Transition.v], which corresponds to the reactivity of the program: it initializes the resources values, performs the instant via the functional transition and updates the system. In this file, we focus on the evaluation transition.
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
    | <[\y,t]>      => if (x =? y)%v then <[\y,t]> else <[\y,[x := v ~ lb – k] t]>

    | <[fst.t]>    => <[fst.([x := v ~ lb – k]t)]>
    | <[snd.t]>    => <[snd.([x := v ~ lb – k]t)]>
    | <[Fix t]>    => <[Fix ([x := v ~ lb – k]t)]>
    | <[arr(t)]>   => <[arr([x := v ~ lb – k]t)]>
    | <[first(t)]> => <[first([x := v ~ lb – k]t)]>

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
  | eT_appv (k : lvl) (x : variable) (t v : Λ) :

                         value(v) ->
      (* ------------------------------------- ET-Appv *)
           k ⊨ ((\x,t) v) ⟼ ([x:= v ~ k] t)

  | eT_app1 (k : lvl) (t1 t1' t2 : Λ) :

               k ⊨ t1 ⟼ t1' -> 
      (* --------------------------- ET-App1 *)
           k ⊨ (t1 t2) ⟼ (t1' t2)

  | eT_app2  (k : lvl) (v t t' : Λ) :
                    
           value(v) -> k ⊨ t ⟼ t' -> 
      (* ------------------------------- ET-App2 *)
              k ⊨ (v t) ⟼ (v t') 

  | eT_fixv (k : lvl) (f : variable) (t : Λ) :

      (* --------------------------------------------------- ET-Fixv *)
          k ⊨ (Fix (\f,t)) ⟼ ([f := (Fix (\f,t)) ~ k] t)


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

  | eT_arr (k : lvl) (t t' : Λ) :

               k ⊨ t ⟼ t' -> 
      (* ------------------------- ET-Arr *)
           k ⊨ arr(t) ⟼ arr(t')

  | eT_first (k : lvl) (t t' : Λ) :
                
                 k ⊨ t ⟼ t' -> 
      (* ----------------------------- ET-First *)
           k ⊨ first(t) ⟼ first(t')

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


#[export] Hint Constructors evaluate clos_refl_trans_1n : core.

(** ---- *)

(** ** Property - Evaluation *)

(** *** [subst] property *)

Lemma subst_shift_spec (lb k m n : lvl) (y : variable) (v t : Λ) :
  lb <= k ->
  <[[⧐ lb – m] ([y := v ~ k – n] t)]> = <[[y := ([⧐ lb – m] v) ~ {k + m} – n] ([⧐ lb – m] t)]>.
Proof.
  revert lb k m n; induction t; intros lb k m n Hle; simpl; f_equal; eauto.
  - destruct (Var.eqb_spec y x); simpl; auto. 
    now apply Term.shift_permute_2.
  - destruct (Var.eqb_spec y x); simpl; f_equal; auto.
Qed.

Lemma subst_preserves_valid (m n : lvl) (y : variable) (v t : Λ) :
  m >= n -> m ⊩ t -> n ⊩ v -> m ⊩ <[[y := v ~ n – {m - n}] t]>.
Proof.
  revert m n; induction t; intros m n Hle Hvt Hvv; auto;
  try (unfold Term.valid in *; inversion Hvt; subst; constructor; now eauto).
  - simpl; destruct (Var.eqb_spec y x); subst; auto.
    now apply Term.shift_preserves_valid_2.
  - inversion Hvt; subst. 
    simpl; destruct (Var.eqb_spec y x); subst; auto.
    constructor; apply IHt; auto.
  - inversion Hvt; subst. 
    simpl; constructor; auto.
    -- now apply IHt1.
    -- replace (S (S (m - n))) with ((S (S m)) - n) by lia. 
       apply IHt2; auto.
Qed.

Lemma subst_preserves_valid_zero (k : lvl) (x : variable) (v t : Λ) :
  k ⊩ t ->  k ⊩ v -> k ⊩ <[[x := v ~ k] t]>.
Proof.
  replace 0 with (k - k) by lia. 
  apply subst_preserves_valid; auto.
Qed.

(** *** [evaluate] property *)

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

Lemma evaluate_preserves_valid_term (k : lvl) (t t' : Λ) :
  k ⊩ t -> k ⊨ t ⟼ t' -> k ⊩ t'.
Proof.
  revert k t'; induction t; intros k t' Hvt HeT; inversion Hvt; subst; 
  inversion HeT; subst; try (constructor; auto); 
  try (now apply IHt); try (now apply IHt1); try (now apply IHt2).
  - apply subst_preserves_valid_zero; auto; now inversion H2.
  - apply subst_preserves_valid_zero; auto; now inversion H1.
  - now inversion Hvt; subst; inversion H4; subst.
  - now inversion Hvt; subst; inversion H4; subst.
Qed.

Lemma evaluate_valid_weakening_gen (lb k m n : lvl) (t t' : Λ) :
  lb <= k -> m <= lb -> n <= k -> m <= n -> k - lb = n - m ->
  lb ⊨ t ⟼ t' -> k ⊨ ([⧐ m – {n - m}] t) ⟼ ([⧐ m – {n - m}] t').
Proof.
  intros Hlelbk Hlemlb Hlenk Hlemn Heq eT.
  revert k m n Hlelbk Hlemlb Hlenk Hlemn Heq; induction eT; 
  intros; simpl; eauto; try (constructor; eauto; now apply Term.shift_value_iff).
  - rewrite subst_shift_spec; auto; rewrite <- Heq at 3. 
    replace (k + (k0 - k)) with k0 by lia.
    constructor; now apply Term.shift_value_iff.
  - rewrite subst_shift_spec; auto; rewrite <- Heq at 2. 
    replace (k + (k0 - k)) with k0 by lia.
    constructor; now apply Term.shift_value_iff.
  - constructor; try (now rewrite <- Term.shift_value_iff); apply IHeT; lia.
Qed.

Corollary evaluate_valid_weakening (m n : lvl) (t t' : Λ) :
  m <= n ->
  m ⊨ t ⟼ t' -> n ⊨ ([⧐ m – {n - m}] t) ⟼ ([⧐ m – {n - m}] t').
Proof. intros; now apply evaluate_valid_weakening_gen with (lb := m). Qed.


(** *** [multi] property 

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
       k ⊨ x ⟼⋆ x.
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

Lemma multi_appv (k : lvl) (x : variable) (v t : Λ) :

                    value(v) -> 
  (* ----------------------------------------- MET-Appv *)
       k ⊨ ((\x, t) v) ⟼⋆ ([x := v ~ k] t).
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

Lemma multi_fix (k : lvl) (x : variable) (t : Λ) :

  (* ------------------------------------------------------- MET-Fix *)
       k ⊨ (Fix (\x, t)) ⟼⋆ ([x := (Fix (\x, t)) ~ k] t).
Proof. 
  apply rt1n_trans with (y := <[[x := (Fix (\x, t)) ~ k] t]>); auto.
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

Lemma multi_arr (k : lvl) (t t' : Λ) : 

            k ⊨ t ⟼⋆ t' -> 
  (* --------------------------- MET-Arr *)
       k ⊨ arr(t) ⟼⋆ arr(t').
Proof.
  intro HeT; induction HeT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[arr(y)]>; auto. 
Qed.

Lemma multi_first (k : lvl) (t t' : Λ) : 
 
              k ⊨ t ⟼⋆ t' -> 
  (* ------------------------------- MET-First *)
       k ⊨ first(t) ⟼⋆ first(t').
Proof.
  intros HeT; induction HeT; subst; auto.
  - reflexivity.
  - apply rt1n_trans with <[first(y)]>; auto. 
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

Theorem multi_evaluate_valid_weakening_gen (lb k m n : lvl) (t t' : Λ) :
  lb <= k -> m <= lb -> n <= k -> m <= n -> k - lb = n - m ->
  lb ⊨ t ⟼⋆ t' -> k ⊨ ([⧐ m – {n - m}] t) ⟼⋆ ([⧐ m – {n - m}] t').
Proof.
  intros; induction H4; try now constructor.
  eapply rt1n_trans with (y := <[[⧐ m – {n - m}] y ]>); auto.
  eapply evaluate_valid_weakening_gen with (lb := lb); auto.
Qed.

Corollary multi_evaluate_valid_weakening (m n : lvl) (t t' : Λ) :
  m <= n ->
  m ⊨ t ⟼⋆ t' -> n ⊨ ([⧐ m – {n - m}] t) ⟼⋆ ([⧐ m – {n - m}] t').
Proof. intros; now apply multi_evaluate_valid_weakening_gen with (lb := m). Qed.

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
  - eapply multi_evaluate_valid_weakening_gen; eauto.
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

Lemma halts_first (k : lvl) (t : Λ) :
  halts k <[first(t)]> <-> halts k t.
Proof.
  split; intros HA.
  - destruct HA as [t' [HmeT Hvt]]; dependent induction HmeT.
    -- inversion Hvt; subst; exists t; split; auto.  apply rt1n_refl.
    -- inversion H; subst. apply (IHHmeT t') in Hvt; eauto.
       rewrite evaluate_preserves_halting; eauto.
  - destruct HA as [t' [HmeT Hvt']]; exists <[first(t')]>; split; auto.
    -- now apply multi_first.
    -- now constructor.
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


(** ---- *)

Open Scope term_scope.
Open Scope rcontext_scope.

Module VC := VContext.
Module RC := RContext.

(** ** Preservation - Evaluation *)

Hint Resolve VC.valid_empty_spec : core.
Hint Constructors Term.value well_typed evaluate : core.

(** *** Substitution preserves typing 

  Suppose [y] a variable, [t] an expression well-typed by [α] under [Re] and [⌈y ⤆ β⌉ Γ] (2), [v] an expression typed as [β] under [Re1] and [Γ] (3). If [Re1] is included in [Re] (4) and well-formed under its own new key (1), then the resulting expression of substitute [y] by [v] in [t] is typed by [α] under [Re] and [Γ]. We can specify the proof by assuming that [Re1] is equals to [Re] (see the following corollary).
*)
Theorem subst_preserves_typing_gen (Γ : Γ) (Re Re1 : ℜ) (y : variable) (v t : Λ) (α β : Τ) :

       (* (1) *) (Re1⁺ ⊩ Re1)%rc -> (* (2) *) (⌈y ⤆ β⌉ Γ)%vc ⋅ Re ⊢ t ∈ α -> 
       (* (3) *) (∅)%vc ⋅ Re1 ⊢ v ∈ β -> (* (4) *) Re1 ⊆ Re ->
  (* -------------------------------------------------------------------------- *)
               Γ ⋅ Re ⊢ ([y := v ~  {Re1⁺} – {Re⁺ - Re1⁺}] t) ∈ α.
Proof.
  revert Γ Re Re1 v α β y. 
  induction t; intros Γ Re Re1 v' α β y HvRe Hwt Hwv Hsub; 
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
    -- now rewrite VContext.add_shadow in H3.
    -- rewrite VContext.add_add_2 in H3; auto.
       apply (IHt _ _ _ _ _ β y HvRe H3 Hwv Hsub).
  (* wormhole *)
  - apply RC.Ext.new_key_Submap_spec in Hsub as Hle.
    replace (S (S (Re⁺ - Re1⁺))) with ((S (S (Re⁺))) - Re1⁺) by lia.
    eapply IHt2 in Hwv; eauto.
    + erewrite <- RC.new_key_wh_spec; eauto.
    + now apply RC.Ext.new_key_Submap_add_spec.
Qed.

Corollary subst_preserves_typing (Γ : Γ) (Re : ℜ) (y : variable) (v t : Λ) (α β : Τ) :

       (* (1) *) (Re⁺ ⊩ Re)%rc -> 
       (* (2) *) (⌈y ⤆ β⌉ Γ)%vc ⋅ Re ⊢ t ∈ α -> (* (3) *) (∅)%vc ⋅ Re ⊢ v ∈ β -> 
  (* ----------------------------------------------------------------------------- *)
                       Γ ⋅ Re ⊢ ([y := v ~ {Re⁺}] t) ∈ α.
Proof.
  intros HvRe Hwt Hwv; replace 0 with (Re⁺ - Re⁺) by lia. 
  apply (subst_preserves_typing_gen _ _ Re _ _ _ _ β HvRe Hwt Hwv).
  apply RC.Submap_refl.
Qed.

(** *** Evaluate preserves typing.

  Suppose [t] an expression well-typed by [α] under [Re] (2) and [t'] the resulting expression of apply a transition rule on [t] (3). If [Re] is well-formed under its own new key (1), then [t'] is also typed by [α] under [Re].
*)
Theorem evaluate_preserves_typing (Re : ℜ) (t t' : Λ) (α : Τ) :

       (* (1) *) (Re⁺ ⊩ Re)%rc -> 
       (* (2) *) (∅)%vc ⋅ Re ⊢ t ∈ α -> (* (3) *) Re⁺ ⊨ t ⟼ t' -> 
  (* --------------------------------------------------------------- *)
                      (∅)%vc ⋅ Re ⊢ t' ∈ α.
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
    apply (subst_preserves_typing _ _ _ _ _ _ τ); auto.
  - apply wt_wh with (R' := R') (τ := τ); auto.
    apply IHwt2; auto. 
    -- apply well_typed_implies_valid in wt1 as [_ Hvτ]; auto.
       rewrite RC.new_key_wh_spec; apply RC.valid_wh_spec; auto;
       repeat constructor; simpl; auto.
    -- now rewrite RC.new_key_wh_spec.
Qed.

(** *** Multi-Evaluation preserves typing.

  Same as above but with the reflexive transitive closure of the evaluation transition.
*)
Theorem multi_preserves_typing (Re : ℜ) (t t' : Λ) (α : Τ) :

    (* (1) *) (Re⁺ ⊩ Re)%rc ->
    (* (2) *) (∅)%vc ⋅ Re ⊢ t ∈ α -> (* (3) *) Re⁺ ⊨ t ⟼⋆ t' -> 
(*-----------------------------------------------------------------*)
                        (∅)%vc ⋅ Re ⊢ t' ∈ α.
Proof.
  intros HvRe Hwt meT; dependent induction meT; subst; auto.
  apply IHmeT; auto. 
  apply (evaluate_preserves_typing Re x y α HvRe Hwt H).
Qed.

(** ---- *)

(** ** Progress - Evaluation 

  Suppose [t] an expression well-typed by [τ] under [Re] (1). Either, [t] is a value (2) or it exists an evaluation of [t], named here [t'] (3).
*)
Theorem progress_of_evaluate (Re : ℜ) (t : Λ) (τ : Τ) :
                  (* (1) *) (∅)%vc ⋅ Re ⊢ t ∈ τ -> 
  (* ------------------------------------------------------------- *)
       (* (2) *) value(t) \/ (* (3) *) exists t', Re⁺ ⊨ t ⟼ t'.
Proof.
  revert Re τ; induction t; intros Re τ' Hwt; inversion Hwt; subst; try (now left);
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
       exists <[[x := (Fix (\x,t0)) ~ {Re⁺}] t0]>; now constructor.
    -- destruct H; exists (Term.tm_fix x); now constructor.
  - apply IHt in H2 as H2'; destruct H2'; right.
    -- inversion H; subst; inversion H2; subst; exists v1; now constructor. 
    -- destruct H; exists (Term.tm_fst x); now constructor.
  - apply IHt in H2 as H2'; destruct H2'; right.
    -- inversion H; subst; inversion H2; subst; exists v2; now constructor. 
    -- destruct H; exists (Term.tm_snd x); now constructor.
  - apply IHt in H2 as H2'; destruct H2' as [Hvt | [t' HeT']]; 
    try (left; now constructor); right; exists <[arr(t')]>; now constructor.
  - apply IHt in H0 as H0'; destruct H0' as [Hvt | [t' HeT']]; 
    try (left; now constructor); right; exists <[first(t')]>; now constructor.
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
       rewrite RC.new_key_wh_spec in HeT2'; auto.
    -- exists <[wormhole(t1';t2)]>; now constructor.
    -- exists <[wormhole(t1';t2)]>; now constructor.
Qed.