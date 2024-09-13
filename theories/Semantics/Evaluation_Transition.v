From Coq Require Import Relations.Relation_Operators.
From Mecha Require Import Var Resource Term.
Import VarNotations ResourceNotations TermNotations.

Open Scope term_scope.

(** * Semantics - Evaluation

  Wormholes’s dynamic semantics is split in three sets of transition rules: the evaluation transition which extends standard β-reduction; the functional transition, defined in [Functional_Transition.v], which performs the logical instant, and the temporal transition, defined in [Temporal_Transition.v], which corresponds to the reactivity of the program: it initializes the resources values, performs the instant via the functional transition and updates the system. In this file, we focus on the evaluation transition.
*)

(** ** Definition - Evaluation *)

(** *** Substitution function 

  In addition to usual substitution parameters, the [subst] function carries
  two levels, [lb] and [k]. 
  Consider, as an illustrating example, the following expressions valid at [0].
<<
wh(unit; rsf[0] >>> x) (1)
wh(unit; rsf[0])       (2)
>>
  With a standard substitution, the result of substituting [x] by (2) in (1) is ill-
  formed because of the resource [0] in (2) is captured by the wh of (1).
<<
  [x := (2)] wh(unit; rsf[0] >>> x)
= wh([x := (2)] unit; [x := (2)] rsf[0] >>> x)
= wh(unit; [x := (2)] rsf[0] >>> x)
= wh(unit; [x := (2)] rsf[0] >>> [x := (2)] x)
= wh(unit; rsf[0] >>> wh(unit; rsf[0]))
>>
  With [lb] the validity level of (2), and [k] the number of bound resources encountered, we avoid
  this issue.
<<
  [x := (2) ~ 0 ≤ 0] wh(unit; rsf[0] >>> x)
= wh([x := (2) ~ 0 ≤ 0] unit; [x := (2) ~ 0 ≤ 2] rsf[0] >>> x)
= wh(unit; [x := (2) ~ 0 ≤ 2] rsf[0] >>> x)
= wh(unit; [x := (2) ~ 0 ≤ 2] rsf[0] >>> [x := (2) ~ 0 ≤ 2] x)
= wh(unit; rsf[0] >>> [⧐ₜₘ 0 ≤ 2] wh(unit; rsf[0]))
= wh(unit; rsf[0] >>> wh([⧐ₜₘ 0 ≤ 2] unit; [⧐ₜₘ 0 ≤ 2] rsf[0]))
= wh(unit; rsf[0] >>> wh(unit; [⧐ₜₘ 0 ≤ 2] rsf[0]))
= wh(unit; rsf[0] >>> wh(unit; rsf[2]))
>>
*)

Reserved Notation "'[' x ':=' v '~' lb '–' k ']' t" (in custom wh at level 66, right associativity).

Fixpoint subst (lb : lvl) (k : lvl) (x : variable) (v t : Λ) : Λ :=
  match t with
    | Term.tm_var y => if (x =? y)%v then <[[⧐ lb – k] v]> else t 
    | <[t1 t2]> => <[([x := v ~ lb – k]t1) ([x := v ~ lb – k]t2)]>
    | <[\y,t0]> => if (x =? y)%v then t else <[\y,[x := v ~ lb – k]t0]>

    | <[⟨t1,t2⟩]> => <[⟨([x := v ~ lb – k]t1),([x := v ~ lb – k]t2)⟩]>
    | <[t0.fst]> => <[([x := v ~ lb – k]t0).fst]>
    | <[t0.snd]> => <[([x := v ~ lb – k]t0).snd]>

    | <[arr(t0)]> => <[arr([x := v ~ lb – k]t0)]>
    | <[first(t0)]> => <[first([x := v ~ lb – k]t0)]>
    | <[t1 >>> t2]> => <[([x := v ~ lb – k]t1) >>> ([x := v ~ lb – k]t2)]>

    | <[wormhole(t1;t2)]> => <[wormhole([x := v ~ lb – k] t1;[x := v ~ lb – {S (S k)}] t2)]>

    | _ => t
  end
  where "'[' x ':=' v '~' lb '–' k ']' t" := (subst lb k x v t) (in custom wh)
.

Notation "'[' x ':=' v '~' lb ']' t" := (subst lb 0 x v t) 
                                        (in custom wh at level 66,  right associativity).



(** *** Evaluation transition

  The evaluation transition corresponds to a determinis-
  tic β-reduction. We choose a small step semantics with a call-by-value evaluation
  strategy (see Figure 6) in order to bypass capture issues for variables (in particular, 
  reduction does not act under λ’s). Modifications on the substitution
  affect the evaluation transition. [k] being the number of bound resources encountered, 
  we set it to [0]. But, [lb] is the level of validity of [v], thus, it cannot be deduced. 
  Consequently, we also need [lb] to be explicit in the evaluation transition.
*)

Reserved Notation "k '⊨' t '⟼' t1" (at level 57, t custom wh, t1 custom wh, no associativity).

Inductive evaluate : lvl -> Λ -> Λ -> Prop :=
  | eT_appv (k : lvl) (x : variable) (t v : Λ) :

                         value(v) ->
      (* ------------------------------------- ET-Appv *)
           k ⊨ ((\x,t) v) ⟼ ([x:= v ~ k] t)

  | eT_fix (k : lvl) (f : variable) (t : Λ) :

      (* --------------------------------------------------- ET-Fix *)
           k ⊨ (Fix (\f,t)) ⟼ ([f := (Fix (\f,t)) ~ k] t)

  | eT_app1 (k : lvl) (t1 t1' t2 : Λ) :

               k ⊨ t1 ⟼ t1' -> 
      (* --------------------------- ET-App1 *)
           k ⊨ (t1 t2) ⟼ (t1' t2)

  | eT_app2  (k : lvl) (v t t' : Λ) :
                    
           value(v) -> k ⊨ t ⟼ t' -> 
      (* ------------------------------- ET-App2 *)
              k ⊨ (v t) ⟼ (v t') 

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
           k ⊨ t.fst ⟼ t'.fst

  | eT_fstv (k : lvl) (v1 v2 : Λ) :

           value(v1) -> value(v2) -> 
      (* ----------------------------- ET-Fstv *)
            k ⊨ ⟨v1,v2⟩.fst ⟼ v1

  | eT_snd1 (k : lvl) (t t' : Λ) :

               k ⊨ t ⟼ t' -> 
      (* ----------------------- ET-Snd1 *)
           k ⊨ t.snd ⟼ t'.snd

  | eT_sndv (k : lvl) (v1 v2 : Λ) :

           value(v1) -> value(v2) -> 
      (* ----------------------------- ET-Sndv *)
            k ⊨ ⟨v1,v2⟩.snd ⟼ v2
                            
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

(** *** Multi transition step with fuel *)

Reserved Notation "k '⊨' t '⊢' st '⟶' t1" 
                  (at level 57, t custom wh, t1 custom wh, no associativity).

Inductive indexed : lvl -> nat -> Λ -> Λ -> Prop :=
  | index_refl (lb : lvl) (t : Λ) : 
  
      (* ------------------ *)
           lb ⊨ t ⊢ 0 ⟶ t

  | index_step (lb : lvl) (k : nat) (t t1 t' : Λ) : 
  
           lb ⊨ t ⟼ t1 -> lb ⊨ t1 ⊢ k ⟶ t' -> 
      (* -------------------------------------- *)
                   lb ⊨ t ⊢(S k)⟶ t'

where "k '⊨' t '⊢' st '⟶' t1" := (indexed k st t t1).

(** *** Multi transition step *)
Definition multi (k : lvl) :=  clos_refl_trans_1n Λ (evaluate k).


Notation "k '⊨' t '⟼⋆' t1" := (multi k t t1) 
                                (at level 57, t custom wh, t1 custom wh, no associativity).

(** *** Halts *)
Definition halts (k : lvl)  (t : Λ) : Prop :=  exists t', k ⊨ t ⟼⋆ t' /\  value(t').

(** *** Normal form *)
Definition normal_form (k : lvl) (t : Λ) : Prop := ~ (exists t', k ⊨ t ⟼ t').

#[export] Hint Constructors evaluate clos_refl_trans_1n indexed : core.

(** ---- *)

(** ** Property - Evaluation *)

(** *** [subst] property *)

(** *** [evaluate] property *)

(** *** [multi] property *)

(** *** [halts] property *)

(** ---- *)

(** ** Preservation - Evaluation *)

(** ---- *)

(** ** Progress - Evaluation *)
