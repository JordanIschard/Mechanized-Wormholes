From Coq Require Import Classes.Morphisms.
From Mecha Require Import Resource Var Typ Cell Term Triplet 
                          VContext RContext REnvironment 
                          Stock SREnvironment.


(** * Environment Notation *)

(** ** Scope *)
Declare Scope vcontext_scope.
Declare Scope rcontext_scope.
Declare Scope renvironment_scope.
Declare Scope stock_scope.
Declare Scope srenv_scope.

Delimit Scope vcontext_scope with vc.
Delimit Scope rcontext_scope with rc.
Delimit Scope renvironment_scope with re.
Delimit Scope stock_scope with sk.
Delimit Scope srenv_scope with sr.

(** ** Module *)

Module RC := RContext.
Module VC := VContext.
Module RE := REnvironment.
Module ST := Stock.
Module SRE := SREnvironment.

(** ** Notations *)
Definition Γ := VContext.t.
Definition ℜ := RContext.t.
Definition 𝐕 := REnvironment.t.
Definition 𝐖 := Stock.t.
Definition 𝐄 := SREnvironment.t.

Notation "r '∉' t" := (~ (VContext.Raw.In r t)) (at level 75, no associativity) : vcontext_scope. 
Notation "∅" := VContext.Raw.empty (at level 0, no associativity) : vcontext_scope. 
Notation "'isEmpty(' t ')'" := (VContext.Empty t) 
                                (at level 20, no associativity) : vcontext_scope. 
Notation "t '⌊' x '⌋'"  := (VContext.Raw.find x t) (at level 15, x constr) : vcontext_scope.
Notation "⌈ x ⤆ v '⌉' t"  := (VContext.Raw.add x v t) 
                             (at level 15, x constr, v constr) : vcontext_scope.
Notation "'[⧐' lb '–' k ']' t" := (VContext.shift lb k t) 
                                   (at level 65, right associativity) : vcontext_scope.

Infix "⊆" := VContext.Submap (at level 60, no associativity) : vcontext_scope. 
Infix "∈" := VContext.Raw.In (at level 60, no associativity) : vcontext_scope. 
Infix "=" := VContext.eq : vcontext_scope.
Infix "⊩" := VContext.Wf (at level 20, no associativity) : vcontext_scope.

Notation "∅" := RContext.Raw.empty (at level 0, no associativity) : rcontext_scope. 
Notation "t '⁺'" := (RContext.Ext.new_key t) (at level 16) : rcontext_scope.
Notation "r '∉' t" := (~ (RContext.Raw.In r t)) (at level 75, no associativity) : rcontext_scope. 
Notation "'isEmpty(' t ')'" := (RContext.Empty t) (at level 20, no associativity) : rcontext_scope. 
Notation "t '⌊' x '⌋'"  := (RContext.Raw.find x t) (at level 15, x constr) : rcontext_scope.
Notation "'max(' t ')'" := (RContext.Ext.max_key t) (at level 15) : rcontext_scope.
Notation "⌈ x ⤆ v '⌉' t" := (RContext.Raw.add x v t) 
                             (at level 15, x constr, v constr) : rcontext_scope.
Notation "'[⧐' lb '–' k ']' t" := (RContext.shift lb k t) 
                                   (at level 65, right associativity) : rcontext_scope.

Infix "⊆" := RContext.Submap (at level 60, no associativity) : rcontext_scope. 
Infix "∈" := RContext.Raw.In (at level 60, no associativity) : rcontext_scope. 
Infix "⊩" := RContext.Wf (at level 20, no associativity) : rcontext_scope.
Infix "=" := RContext.eq : rcontext_scope.

Notation "∅" := REnvironment.Raw.empty (at level 0, no associativity) : renvironment_scope. 
Notation "t '⁺'" := (REnvironment.Ext.new_key t) (at level 16) : renvironment_scope.
Notation "r '∉' t" := (~ (REnvironment.Raw.In r t)) 
                       (at level 75, no associativity) : renvironment_scope. 
Notation "'isEmpty(' t ')'" := (REnvironment.Empty t) (at level 20, no associativity) : renvironment_scope. 
Notation "t '⌊' x '⌋'"  := (REnvironment.Raw.find x t) (at level 15, x constr) : renvironment_scope.
Notation "'max(' t ')'"  := (REnvironment.Ext.max_key t) (at level 15) : renvironment_scope.
Notation "⌈ x ⤆ v '⌉' t"  := (REnvironment.Raw.add x v t) 
                              (at level 15, x constr, v constr) : renvironment_scope.
Notation "'[⧐' lb '–' k ']' t" := (REnvironment.shift lb k t) 
                                   (at level 65, right associativity) : renvironment_scope.

Infix "⊆" := REnvironment.Submap (at level 60, no associativity) : renvironment_scope. 
Infix "∈" := REnvironment.Raw.In (at level 60, no associativity) : renvironment_scope. 
Infix "=" := REnvironment.eq : renvironment_scope.
Infix "⊩" := REnvironment.Wf (at level 20, no associativity) : renvironment_scope.


Infix "∈" := List.In (at level 60, no associativity) : stock_scope. 
Notation "r '∉' t" := (~ (List.In r t)) (at level 75, no associativity) : stock_scope. 
Notation "t '⁺'" := (Stock.new_key t) (at level 16) : stock_scope.
Notation "'[⧐' lb '–' k ']' t" := (Stock.shift lb k t) 
                                   (at level 65, right associativity) : stock_scope.

Infix "=" := Stock.eq : stock_scope.
Infix "⊩" := Stock.Wf (at level 20, no associativity) : stock_scope.

Notation "t '⁺'" := (SREnvironment.Ext.new_key t) (at level 16) : srenv_scope.
Notation "∅" := SREnvironment.Raw.empty (at level 0, no associativity) : srenv_scope. 
Notation "r '∉' t" := (~ (SREnvironment.Raw.In r t)) (at level 75, no associativity) : srenv_scope. 
Notation "'isEmpty(' t ')'" := (SREnvironment.Empty t) (at level 20, no associativity) : srenv_scope. 
Notation "t '⌊' x '⌋'"  := (SREnvironment.Raw.find x t) (at level 15, x constr) : srenv_scope.
Notation "'max(' t ')'"  := (SREnvironment.Ext.max_key t) (at level 15) : srenv_scope.
Notation "⌈ x ⤆ v '⌉' t" := (SREnvironment.Raw.add x v t) 
                             (at level 15, x constr, v constr) : srenv_scope.
Notation "'[⧐' lb '–' k ']' t" := (SREnvironment.shift lb k t) 
                                   (at level 65, right associativity) : srenv_scope.

Infix "⊆" := SREnvironment.Submap (at level 60, no associativity) : srenv_scope. 
Infix "∈" := SREnvironment.Raw.In (at level 60, no associativity) : srenv_scope. 
Infix "=" := SREnvironment.eq : srenv_scope.
Infix "∪" := SREnvironment.extend (at level 50, left associativity) : srenv_scope.
Infix "⊩" := SREnvironment.Wf (at level 20, no associativity) : srenv_scope.

(** ** Morphism *)
#[export] Hint Resolve VC.Wf_empty RC.Wf_empty RE.Wf_empty
                       RC.Submap_wh RC.Wf_wh RE.Wf_wh
                       RC.Submap_refl VC.Submap_refl RE.Submap_refl 
                       SRE.Wf_empty SRE.Submap_refl : core.
#[export] Hint Rewrite RC.new_key_wh : core.

Section vcontext_instance.

Import VContext.

#[export] Instance vcontext_eq_equiv : Equivalence eq := _.

#[export] Instance vcontext_in_iff : 
  Proper (Logic.eq ==> VContext.eq ==> iff) (VContext.Raw.In) := _.

#[export] Instance vcontext_find_eq : 
  Proper (Logic.eq ==> VContext.eq ==> Logic.eq) (VContext.Raw.find) := _.

#[export] Instance vcontext_Empty_iff : 
  Proper (VContext.eq ==> iff) (VContext.Empty) := _.

#[export] Instance vcontext_Add_iff : 
  Proper (Var.eq ==> Typ.eq ==> VContext.eq ==> VContext.eq ==> iff) (@VContext.Add Typ.t) := _.

#[export] Instance vcontext_add_eq : 
  Proper (Var.eq ==> Typ.eq ==> VContext.eq ==> VContext.eq) (@VContext.Raw.add Typ.t) := _.

#[export] Instance vcontext_Submap_iff : 
  Proper (VContext.eq ==> VContext.eq ==> iff) VContext.Submap := _.

#[export] Instance vcontext_Wf_iff : 
  Proper (Logic.eq ==> VContext.eq ==> iff) VContext.Wf := _.

#[export] Instance vcontext_shift_eq : 
  Proper (Logic.eq ==> Logic.eq ==> VContext.eq ==> VContext.eq) VContext.shift := _.

#[export] Instance vcontext_Submap_po : 
  PreOrder VContext.Submap := _.

End vcontext_instance.

Section rcontext_instance.

Import RContext.

#[export] Instance rcontext_eq_equiv : Equivalence RContext.eq := Equal_equiv.

#[export] Instance rcontext_max_eq : Proper (eq ==> Logic.eq) (Ext.max_key) := Ext.max_key_eq.

#[export] Instance rcontext_new_eq : Proper (eq ==> Logic.eq) (Ext.new_key) := Ext.new_key_eq.

#[export] Instance rcontext_in_iff : Proper (Logic.eq ==> eq ==> iff) (Raw.In) := _.

#[export] Instance rcontext_find_eq : Proper (Logic.eq ==> eq ==> Logic.eq) (Raw.find) := _.

#[export] Instance rcontext_Empty_iff : Proper (eq ==> iff) (Empty) := _.

#[export] Instance rcontext_Add_iff : 
  Proper (Resource.eq ==> PairTyp.eq ==> eq ==> eq ==> iff) (@RContext.Add PairTyp.t) := _.

#[export] Instance rcontext_add_eq : 
  Proper (Resource.eq ==> PairTyp.eq ==> eq ==> eq) (@Raw.add PairTyp.t) := _.

#[export] Instance rcontext_Submap_iff : Proper (eq ==> eq ==> iff) Submap := _.

#[export] Instance rcontext_Submap_po : PreOrder Submap := Submap_po.

#[export] Instance rcontext_Wf_iff : Proper (Logic.eq ==> eq ==> iff) Wf := _.

#[export] Instance rcontext_shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.

End rcontext_instance.

Section renvironment_instance.

Import REnvironment.

#[export] Instance renvironment_equiv_eq : Equivalence REnvironment.eq := _.

#[export] Instance renvironment_max_eq : Proper (eq ==> Logic.eq) (Ext.max_key) := Ext.max_key_eq.

#[export] Instance renvironment_new_eq : Proper (eq ==> Logic.eq) (Ext.new_key) := Ext.new_key_eq. 

#[export] Instance renvironment_in_iff :  Proper (Logic.eq ==> eq ==> iff) (Raw.In) := _.

#[export] Instance renvironment_find_eq : Proper (Logic.eq ==> eq ==> Logic.eq) (Raw.find) := _.

#[export] Instance renvironment_Empty_iff : Proper (eq ==> iff) (Empty) := _.

#[export] Instance renvironment_Add_iff : 
  Proper (Resource.eq ==> Cell.eq ==> eq ==> eq ==> iff) (@REnvironment.Add Cell.t) := _.

#[export] Instance renvironment_add_eq : 
  Proper (Resource.eq ==> Cell.eq ==> REnvironment.eq ==> REnvironment.eq) (@Raw.add Cell.t) := _.

#[export] Instance renvironment_remove_eq : 
  Proper (Resource.eq ==> eq ==> eq) (@Raw.remove Cell.t) := _.

#[export] Instance renvironment_Submap_iff : Proper (eq ==> eq ==> iff) Submap := _.

#[export] Instance renvironment_Submap_po : PreOrder Submap := Submap_po.

#[export] Instance renvironment_Wf_iff : Proper (Logic.eq ==> eq ==> iff) Wf := _.

#[export] Instance renvironment_shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.


#[export] Instance renvironment_unused_iff : Proper (Logic.eq ==> eq ==> iff) unused := _.

#[export] Instance renvironment_used_iff : Proper (Logic.eq ==> eq ==> iff) used := _.

#[export] Instance renvironment_eqDom_iff : Proper (RC.eq ==> eq ==> iff) eqDom := _.

#[export] Instance renvironment_for_all_iff : Proper (Logic.eq ==> eq ==> iff) For_all := _.

End renvironment_instance.

Section stock_instance.

Import Stock.

#[export] Instance eqDom'_iff : Proper (RE.eq ==> eq ==> iff) eqDom' := _.

End stock_instance.

Section srenvironment_instance.

Import SREnvironment.

#[export] Instance srenvironment_equiv_eq : Equivalence SREnvironment.eq := _.

#[export] Instance srenvironment_max_eq : Proper (eq ==> Logic.eq) (Ext.max_key) := Ext.max_key_eq.

#[export] Instance srenvironment_new_eq : Proper (eq ==> Logic.eq) (Ext.new_key) := Ext.new_key_eq.

#[export] Instance srenvironment_in_iff : 
  Proper (Logic.eq ==> SREnvironment.eq ==> iff) (SREnvironment.Raw.In) := _.

#[export] Instance srenvironment_find_eq : Proper (Logic.eq ==> eq ==> Logic.eq) (Raw.find) := _.

#[export] Instance srenvironment_Empty_iff : 
  Proper (SREnvironment.eq ==> iff) (SREnvironment.Empty) := _.

#[export] Instance srenvironment_Add_iff : 
  Proper (Resource.eq ==> Term.eq ==> eq ==> eq ==> iff) (@SREnvironment.Add Term.t) := _.

#[export] Instance srenvironment_add_eq : 
  Proper (Resource.eq ==> Term.eq ==> eq ==> eq) (@Raw.add Term.t) := _.

#[export] Instance srenvironment_Submap_iff : Proper (eq ==> eq ==> iff) Submap := _.

#[export] Instance srenvironment_Submap_po : PreOrder SREnvironment.Submap := Submap_po.

#[export] Instance srenvironment_Wf_iff : 
  Proper (Logic.eq ==> SREnvironment.eq ==> iff) SREnvironment.Wf := _.

#[export] Instance srenvironment_shift_eq : Proper (Logic.eq ==> Logic.eq ==> eq ==> eq) shift := _.

#[export] Instance srenvironment_for_all_iff : Proper (Logic.eq ==> eq ==> iff) For_all := _.

End srenvironment_instance.