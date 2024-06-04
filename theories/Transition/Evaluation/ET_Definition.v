From Mecha Require Import Var Resource Term.
Import ResourceNotations TermNotations.

(** * Transition - Evaluation - Definition

Wormholes’s semantics is given by three sets of transition rules: the evaluation
transition, which extends standard β-reduction; the functional transition which
performs the logical instant, and the temporal transition which corresponds to
the reactivity of the program: it initializes the resources values, performs the
instant via functional transition and updates the system.

In this file, we focus on the evaluation transition.
*)

(** ** Substitution *)

Reserved Notation "'[' x ':=' v '~' lb '≤' k ']' t" (in custom wh at level 66, 
                                                                  right associativity).

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
Fixpoint subst (lb : nat) (k : nat) (x : Var.t) (v t : Λ) : Λ :=
  match t with
    | Term.tm_var y => if (x =? y)%v then <[[⧐ₜₘ lb ≤ k] v]> else t 
    | <[t1 t2]> => <[([x := v ~ lb ≤ k]t1) ([x := v ~ lb ≤ k]t2)]>
    | <[\y:τ,t0]> => if (x =? y)%v then t else <[\y:τ,[x := v ~ lb ≤ k]t0]>

    | <[⟨t1,t2⟩]> => <[⟨([x := v ~ lb ≤ k]t1),([x := v ~ lb ≤ k]t2)⟩]>
    | <[t0.fst]> => <[([x := v ~ lb ≤ k]t0).fst]>
    | <[t0.snd]> => <[([x := v ~ lb ≤ k]t0).snd]>

    | <[arr(t0)]> => <[arr([x := v ~ lb ≤ k]t0)]>
    | <[first(τ:t0)]> => <[first(τ:[x := v ~ lb ≤ k]t0)]>
    | <[t1 >>> t2]> => <[([x := v ~ lb ≤ k]t1) >>> ([x := v ~ lb ≤ k]t2)]>

    | <[wormhole(t1;t2)]> => <[wormhole([x := v ~ lb ≤ k] t1;[x := v ~ lb ≤ {S (S k)}] t2)]>

    | _ => t
  end
  where "'[' x ':=' v '~' lb '≤' k ']' t" := (subst lb k x v t) (in custom wh)
.

Notation "'[' x ':=' v '~' lb ']' t" := (subst lb 0 x v t) (in custom wh at level 66, 
                                                                  right associativity).

(** ** Evaluation Transition *)

Reserved Notation "k '⊨' t '⟼' t1" (at level 57, t custom wh, 
                                                   t1 custom wh, no associativity).
Reserved Notation "k '⊨' t '⟼⋆' t1" (at level 57, t custom wh, 
                                                    t1 custom wh, no associativity).
Reserved Notation "k '⊨' t '⊢' st '⟶' t1" (at level 57, t custom wh, 
                                                         t1 custom wh, no associativity).

(** *** Small-step semantics

  The evaluation transition corresponds to a determinis-
  tic β-reduction. We choose a small step semantics with a call-by-value evaluation
  strategy (see Figure 6) in order to bypass capture issues for variables (in par-
  ticular, reduction does not act under λ’s). Modifications on the substitution
  affect the evaluation transition. [k] being the number of bound resources encountered, 
  we set it to [0]. But, [lb] is the level of validity of [v], thus, it cannot be deduced. 
  Consequently, we also need [lb] to be explicit in the evaluation transition.
*)
Inductive evaluate : nat -> Λ -> Λ -> Prop :=
  | eT_appv   : forall lb x τ t v,
                                  value(v) ->
                (*-------------------------------------------- ET-Appv *)
                    lb ⊨ ((\x:τ,t) v) ⟼ ([x:= v ~ lb] t)


  | eT_fix   : forall lb f τ t,
                (*------------------------------------------------------------ ET-Fix *)
                    lb ⊨ (Fix (\f:τ,t)) ⟼ ([f := (Fix (\f:τ,t)) ~ lb] t)

  | eT_app1   : forall lb t1 t1' t2,
                        lb ⊨ t1 ⟼ t1' -> 
                (*---------------------------- ET-App1 *)
                    lb ⊨ (t1 t2) ⟼ (t1' t2)

  | eT_app2   : forall lb v t t',
                    value(v) -> lb ⊨ t ⟼ t' -> 
                (*------------------------------- ET-App2 *)
                      lb ⊨ (v t) ⟼ (v t') 

  | eT_pair1  : forall lb t1 t1' t2,
                        lb ⊨ t1 ⟼ t1' -> 
                (*----------------------------- ET-Pair1 *)
                    lb ⊨ ⟨t1,t2⟩ ⟼ ⟨t1',t2⟩

  | eT_pair2  : forall lb v t t',
                    value(v) -> lb ⊨ t ⟼ t' -> 
                (*------------------------------- ET-Pair2 *)
                      lb ⊨ ⟨v,t⟩ ⟼ ⟨v,t'⟩ 

  | eT_fst1   : forall lb t t',
                      lb ⊨ t ⟼ t' -> 
                (*------------------------- ET-Fst1 *)
                    lb ⊨ t.fst ⟼ t'.fst

  | eT_fstv   : forall lb v1 v2,
                    value(v1) -> value(v2) -> 
                (*----------------------------- ET-Fstv *)
                    lb ⊨ ⟨v1,v2⟩.fst ⟼ v1

  | eT_snd1   : forall lb t t',
                        lb ⊨ t ⟼ t' -> 
                (*-------------------------- ET-Snd1 *)
                    lb ⊨ t.snd ⟼ t'.snd

  | eT_sndv   : forall lb v1 v2,
                    value(v1) -> value(v2) -> 
                (*----------------------------- ET-Sndv *)
                    lb ⊨ ⟨v1,v2⟩.snd ⟼ v2
                            
  | eT_comp1  : forall lb t1 t1' t2,
                            lb ⊨ t1 ⟼ t1' -> 
                (*--------------------------------- ET-Comp1 *)
                    lb ⊨ t1 >>> t2 ⟼ t1' >>> t2

  | eT_comp2  : forall lb v t t',
                      value(v) -> lb ⊨ t ⟼ t' -> 
                (*--------------------------------- ET-Comp2 *)
                      lb ⊨ v >>> t ⟼ v >>> t'

  | eT_arr  : forall lb t t',
                      lb ⊨ t ⟼ t' -> 
              (*------------------------- ET-Arr *)
                  lb ⊨ arr(t) ⟼ arr(t')

  | eT_first  : forall lb τ t t',
                            lb ⊨ t ⟼ t' -> 
                (*--------------------------------- ET-First *)
                    lb ⊨ first(τ:t) ⟼ first(τ:t')

  | eT_wh1   :  forall lb i i' t,
                                lb ⊨ i ⟼ i' -> 
                (*----------------------------------------- ET-Wh1 *)
                    lb ⊨ wormhole(i;t) ⟼ wormhole(i';t)

  | eT_wh2   :  forall lb i t t',
                    value(i) -> (S (S lb)) ⊨ t ⟼ t' -> 
                (*----------------------------------------- ET-Wh2 *)
                    lb ⊨ wormhole(i;t) ⟼ wormhole(i;t')

where "k '⊨' t '⟼' t1" := (evaluate k t t1)
.

(** *** Multi transition step with fuel *)
Inductive indexed : nat -> nat -> Λ -> Λ -> Prop :=
  | index_refl : forall lb x, lb ⊨ x ⊢ 0 ⟶ x
  | index_step : forall lb k x y z, lb ⊨ x ⟼ y -> lb ⊨ y ⊢ k ⟶ z -> lb ⊨ x ⊢(S k)⟶ z
where "k '⊨' t '⊢' st '⟶' t1" := (indexed k st t t1)
.

(** *** Multi transition step *)
Inductive multi : nat -> Λ -> Λ -> Prop :=
  | multi_refl : forall k x, k ⊨ x ⟼⋆ x
  | multi_step : forall k x y z, k ⊨ x ⟼ y -> k ⊨ y ⟼⋆ z -> k ⊨ x ⟼⋆ z
where "k '⊨' t '⟼⋆' t1" := (multi k t t1).

Definition halts (k : nat)  (t : Λ) : Prop :=  exists t', k ⊨ t ⟼⋆ t' /\  value(t').
Definition normal_form (k : nat) (t : Λ) : Prop := ~ (exists t', k ⊨ t ⟼ t').

#[export] Hint Constructors evaluate multi indexed : core.