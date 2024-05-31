From Mecha Require Import Var Resource Term.

(** * Transition - Evaluation - Definition

Wormholes's semantics are divided in three sub semantics:
- evaluation transition <--
- functional transition
- temporal transition

This file focuses on the evaluation transition which is a small step semantics with a call by value evaluation strategy.
*)

(** ** Substitution *)

Reserved Notation "'[' x ':=' v '~' lb '≤' k ']' t" (in custom wormholes at level 66, 
                                                                  right associativity).

(** *** Substitution function 

  The substitution function works as well as the classic one with extra information.
  Indeed, when we go through the term searching compatible variables, we can go through
  a [wormhole] term. However the wormhole term does not have the same level inside. In fact
  it has the level outside increment by 2. Then we add extra information:
  - the current level of the substitute [lb] and
  - the shift between the level of the substitute [v] and the current term.

  Thus, when we find a compatible variable we substitute it by the term [v] after
  having perfomed a shift.

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
  where "'[' x ':=' v '~' lb '≤' k ']' t" := (subst lb k x v t) (in custom wormholes)
.

Notation "'[' x ':=' v '~' lb ']' t" := (subst lb 0 x v t) (in custom wormholes at level 66, 
                                                                  right associativity).

(** *** Example

  Suppose the following Womhole's terms:
<<
(1) wormhole[rr,rw](i'; rsf[rr] >>> x)
(2) wormhole[rr1,rw1](i; rsf[rr1])
>>

  Translated in the De Bruijn level representation we have:
<<
(1) wormhole(i'; rsf[0] >>> x)
(2) wormhole(i; rsf[0])
>>

  If we substitute x by (2) in (1) with the classic substitution we have the following result:
<<
  [x := (2)] wormhole(i'; rsf[0] >>> x)
= wormhole([x := (2)] i'; [x := (2)] (rsf[0] >>> x))
= wormhole([x := (2)] i'; [x := (2)] rsf[0] >>> [x := (2)] x)
= wormhole([x := (2)] i'; rsf[0] >>> wormhole(i; rsf[0]))
>>

  If we do the opposite translation we expect:
<<
wormhole[rr,rw](i'; rsf[rr] >>> wormhole[rr1,rw1](i; rsf[rr1]))
>>

  but found:
<<
wormhole[rr,rw](i'; rsf[rr] >>> wormhole[rr1,rw1](i; rsf[rr]))
>>

  With our substitution the result is the expected one, as we can see below.

<<
  [x := (1) ~ 0 ≤ 0] wormhole(i'; rsf[0] >>> x)
= wormhole([x := (1) ~ 0 ≤ 0] i'; [x := (1) ~ 0 ≤ 2] (rsf[0] >>> x))
= wormhole([x := (1) ~ 0 ≤ 0] i'; [x := (1) ~ 0 ≤ 2] rsf[0] >>> [x := (1) ~ 0 ≤ 2] x)
= wormhole([x := (1) ~ 0 ≤ 0] i'; rsf[0] >>> [>> 0 ≤ 2] wormhole(i; rsf[0]))
= wormhole([x := (1) ~ 0 ≤ 0] i'; rsf[0] >>> wormhole([>> 0 ≤ 2] i; [>> 0 ≤ 2] rsf[0]))
= wormhole([x := (1) ~ 0 ≤ 0] i'; rsf[0] >>> wormhole([>> 0 ≤ 2] i; rsf[2]))
>>
*)

(** ** Evaluation Transition *)

Reserved Notation "k '⊨' t '⟼' t1" (at level 57, t custom wormholes, 
                                                   t1 custom wormholes, no associativity).
Reserved Notation "k '⊨' t '⟼⋆' t1" (at level 57, t custom wormholes, 
                                                    t1 custom wormholes, no associativity).
Reserved Notation "k '⊨' t '⊢' st '⟶' t1" (at level 57, t custom wormholes, 
                                                         t1 custom wormholes, no associativity).

(** *** Small-step semantics

  Evaluation transition is defined as we found in an stlc formalization with a slight difference. Indeed, we have an additional element
  [lb]. This is the current level that are valid. It is required because of the definition of validity of terms and for a well use of the 
  substitution in the [eT_appv] rule. 
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