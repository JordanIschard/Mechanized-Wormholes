From Coq Require Import Morphisms.
From DeBrLevel Require Import LevelInterface PairLevel.
From Mecha Require Import Resource Resources Term Typ VContext RContext 
                          Type_System Evaluation_Transition.
Import ResourceNotations ResourcesNotations TermNotations 
       TypNotations VContextNotations RContextNotations.

(** * Syntax - Sample *)

(** ** Module - Sample *)
Module Sample <: IsLvlETWL.

(** *** Definition *)

Include IsLvlPairETWL Term OptTerm.
Module ET := Evaluation_Transition.

(** **** Next function *)
Definition next : t -> Λ := @fst Term.t OptTerm.t.

(** **** Put function *)
Definition put (v : option Λ) (t : t) := (fst t,v).

(** **** Halts *)

Definition halts k (t : t) := 
  halts k (fst t) /\ OptTerm.prop_opt (halts k) (snd t).

(** **** Well-typed *)

Definition well_typed (Γ : Γ) (Re : ℜ) (t : t) (α β : Τ) :=
  Γ ⋅ Re ⊢ {fst t} ∈ α /\ OptTerm.prop_opt (fun v => Γ ⋅ Re ⊢ v ∈ β) (snd t).

(** *** Property *)

(** **** [put] property *)

#[export] Instance put_sap : Proper (OptTerm.eq ==> eq ==> eq) put.
Proof.
  intros ot ot' Heqot t t' Heqt; unfold put. 
  now rewrite Heqt, Heqot.
Qed.

(** **** [halts] property *)

#[export] Instance halts_eq : Proper (Logic.eq ==> eq ==> iff) halts.
Proof.
  intros k' k Heqk t t' Heqt; subst.
  destruct t,t'; unfold eq, RelationPairs.RelProd, halts in *.
  do 3 red in Heqt; unfold RelationPairs.RelCompFun in *; simpl in *.
  destruct Heqt as [Heq Heqo]; subst.
  destruct o, o0; subst; try contradiction; split; auto.
Qed.

Lemma halts_next (k : lvl) (t : t) : halts k t -> ET.halts k (next t).
Proof. unfold halts,next; now intros []. Qed.

Lemma halts_put_Some k t v :
  halts k t -> ET.halts k v -> halts k (put (Some v) t).
Proof. 
  unfold halts, put; destruct t as [i o]; simpl.
  intros [Hi _] Hv; auto.
Qed. 

Lemma halts_put_None (k : lvl) (t : t) :
  halts k t -> halts k (put None t).
Proof.
  unfold halts, put; destruct t as [i o]; simpl.
  intros [Hi _]; auto.
Qed. 

Lemma halts_weakening (m n : lvl) (t : t) : 
  m <= n -> halts m t -> halts n (shift m (n - m) t).
Proof.
  unfold halts, shift, OptTerm.prop_opt; destruct t as [i o]; simpl.
  intros Hle [Hi Ho]; split.
  - now apply ET.halts_weakening.
  - destruct o as [e |]; simpl; auto.
    now apply ET.halts_weakening.
Qed.

(** **** [well_typed] property *)

#[export] Instance wt_eq :
  Proper (VContext.eq ==> RContext.eq ==> eq ==> Typ.eq ==> Typ.eq ==> iff) well_typed.
Proof.
  intros G G' HeqG Re Re1 HeqRe t t' Heqt α α' Heqα β β' Heqβ.
  unfold well_typed; destruct t as [i o]; destruct t' as [i' o']. 
  repeat red in Heqt; unfold RelationPairs.RelCompFun in Heqt.
  simpl in *; destruct Heqt as [Heqi Heqo]; split; intros [Hwt Hwt'].
  - rewrite HeqG, HeqRe, Heqi, Heqα in Hwt; split; auto.
    destruct o,o'; simpl in *; auto; try contradiction.
    now rewrite HeqG, HeqRe, Heqo, Heqβ in Hwt'.
  - rewrite HeqG, HeqRe, Heqi, Heqα; split; auto.
    destruct o,o'; simpl in *; auto; try contradiction.
    now rewrite HeqG, HeqRe, Heqo, Heqβ.
Qed.

Lemma well_typed_next (Γ : Γ) (Re : ℜ) (t : t) (α β : Τ) :
  well_typed Γ Re t α β -> Γ ⋅ Re ⊢ {next t} ∈ α.
Proof.
  unfold well_typed; destruct t as [i o]; simpl; now intros [Hwt _].
Qed.

Lemma well_typed_None (Γ : Γ) (Re : ℜ) (t : t) (α β : Τ) :
  well_typed Γ Re t α β -> well_typed Γ Re (Sample.put None t) α β.
Proof. unfold well_typed; simpl; intros [Hwt _]; auto. Qed.

Lemma well_typed_Some (Γ : Γ) (Re : ℜ) (t : t) (v : Λ) (α β : Τ) :
  well_typed Γ Re t α β -> Γ ⋅ Re ⊢ v ∈ β ->
  well_typed Γ Re (Sample.put (Some v) t) α β.
Proof. unfold well_typed; simpl; intros [Hwt _] Hwt'; auto. Qed.

End Sample.

(** ---- *)

(** ** Notation - Sample *)
Module SampleNotations.

(** *** Scope *)
Declare Scope sample_scope.
Delimit Scope sample_scope with sp.

(** *** Notation *)
Definition σ := Sample.t.

Notation "'[⧐' lb '–' k ']' t" := (Sample.shift lb k t) 
                                   (at level 65, right associativity) : sample_scope.

Infix "=" := Sample.eq : sample_scope.
Infix "⊩" := Sample.valid (at level 20, no associativity) : sample_scope.

(** *** Morphism *)

Import Sample.

#[export] Instance equiv_sap : Equivalence Sample.eq := _.
#[export] Instance next_sap : Proper (eq ==> Term.eq) next := _.
#[export] Instance put_sap : Proper (OptTerm.eq ==> eq ==> eq) put := _.
#[export] Instance valid_sap : Proper (Logic.eq ==> eq ==> iff) valid := _.
#[export] Instance shift_sap : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.
#[export] Instance halts_sap : Proper (Logic.eq ==> eq ==> iff) halts := _. 
#[export] Instance wt_sap :
  Proper (VContext.eq ==> RContext.eq ==> eq ==> 
                                  Typ.eq ==> Typ.eq ==> iff) well_typed := _.

End SampleNotations.