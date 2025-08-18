From Coq Require Import Structures.Orders Structures.OrdersEx.
From DeBrLevel Require Import LevelInterface Level.
From Mecha Require Import Var Resource Typ Term Triplet Cell.

(** * Notation - Syntax *)

(** ** Scope *)
Declare Custom Entry wh.

Declare Scope var_scope.
Declare Scope resource_scope.
Declare Scope typ_scope.
Declare Scope ptyp_scope.
Declare Scope set_scope.
Declare Scope resources_scope.
Declare Scope term_scope.
Declare Scope cell_scope.

Delimit Scope var_scope with v.
Delimit Scope resource_scope with r.
Delimit Scope typ_scope with ty.
Delimit Scope ptyp_scope with pty.
Delimit Scope set_scope with s.
Delimit Scope resources_scope with rs.
Delimit Scope term_scope with tm.
Delimit Scope cell_scope with cl.

(** Module *)

Module R := Resource.
Module RS := Resources.

(** ** Notations *)
Definition variable := Var.t.
Definition resource := Resource.t.
Definition resources := Resources.t.
Definition lvl := Level.t.
Definition Τ := Typ.t.
Definition πΤ := PairTyp.t.
Definition Λ := Term.t.
Definition 𝑣 := Cell.t.

Notation "<[ x ]>" := x (x custom wh at level 99).
Notation "( x )"   := x (in custom wh, x at level 99).
Notation "x"       := x (in custom wh at level 0, x constr at level 0).
Notation "{ x }"   := x (in custom wh at level 1, x constr).

Infix "<"  := Var.lt : var_scope.
Infix "="  := Var.eq : var_scope.
Infix "<?" := Var.ltb (at level 70) : var_scope.
Infix "=?" := Var.eqb (at level 70) : var_scope.

Infix "<"  := Resource.lt : resource_scope.
Infix "="  := Resource.eq : resource_scope.
Infix "⊩" := Resource.Wf (at level 20, no associativity) : resource_scope. 
Notation "'[⧐' lb '–' k ']' t" := (Resource.shift lb k t) 
                                   (at level 65, right associativity) : resource_scope.
Notation "'[⧐⧐' lb '–' k ']' t" := (Resource.multi_shift lb k t) 
                                    (at level 65, right associativity) : resource_scope.

Infix "⊩"  := Typ.Wf (at level 20, no associativity): typ_scope. 
Infix "⊩"  := PairTyp.Wf (at level 20, no associativity): ptyp_scope. 
Infix "="  := Typ.eq: typ_scope.
Notation "'𝟙'"       := Typ.ty_unit (in custom wh at level 0).
Notation "t1 '→' t2" := (Typ.ty_arrow t1 t2) (in custom wh at level 50, right associativity).
Notation "t1 '×' t2"   := (Typ.ty_prod t1 t2) 
                        (in custom wh at level 2, t1 custom wh, t2 custom wh at level 0).
Notation "t1 '⟿' t2 '∣' R" := (Typ.ty_reactive t1 t2 R)
                               (in custom wh at level 50, R constr, right associativity).
Notation "'[⧐' lb '–' k ']' t" := (Typ.shift lb k t) 
                                   (in custom wh at level 45, right associativity): typ_scope.
Notation "'[⧐⧐' lb '–' k ']' t" := (Typ.multi_shift lb k t) 
                                    (in custom wh at level 45, right associativity): typ_scope.
Notation "'[⧐' lb '–' k ']' t" := (PairTyp.shift lb k t) 
                                   (in custom wh at level 45, right associativity): ptyp_scope.

Notation "∅" := (Resources.St.empty) : set_scope.
Notation "'\{{' x '}}'" := (Resources.St.singleton x).
Notation "'\{{' x ';' y ';' .. ';' z '}}'" := (Resources.St.add x (Resources.St.add y .. (Resources.St.add z Resources.St.empty) .. )).
Infix "∉"  := (fun x s => ~ Resources.St.In x s) (at level 75) : set_scope.
Infix "∈"  := (Resources.St.In)  (at level 60, no associativity) : set_scope.
Infix "+:" := (Resources.St.add)  (at level 60, no associativity) : set_scope.
Infix "∪"  := (Resources.St.union) (at level 50, left associativity) : set_scope.
Infix "∩"  := (Resources.St.inter) (at level 50, left associativity) : set_scope.
Infix "\"  := (Resources.St.diff) (at level 50, left associativity) : set_scope.
Infix "⊆"  := Resources.St.Subset (at level 60, no associativity) : set_scope.
Infix "⊈"  := (fun s s' => ~ (Resources.St.Subset s s')) (at level 60, no associativity) : set_scope.
Infix "<"  := Resources.lt : set_scope.
Infix "<?" := Resources.St.ltb (at level 70) : set_scope.
Infix "="  := Resources.eq : set_scope.
Infix "=?" := Resources.St.equal (at level 70) : set_scope.

Infix "⊩" := Resources.Wf (at level 20, no associativity) : resources_scope. 
Notation "t '⁺'" := (Resources.new_key t) (at level 16) : resources_scope.
Notation "'[⧐' lb '–' k ']' t" := (Resources.shift lb k t) (at level 65, right associativity) : resources_scope.
Notation "'[⧐⧐' lb '–' k ']' t" := (Resources.multi_shift lb k t) (at level 65, right associativity) : resources_scope.

Coercion Term.tm_var: Var.t >-> Term.raw.
Notation "value( t )" := (Term.value t) (at level 20, no associativity).

Notation "t1 t2"     := (Term.tm_app t1 t2) (in custom wh at level 70, left associativity).
Notation "'\' x ':' A ',' t" := (Term.tm_abs x A t) 
                      (in custom wh at level 90, x at level 99, 
                                                 A custom wh at level 99,
                                                 t custom wh at level 99, 
                       left associativity).
Notation "'unit'" := (Term.tm_unit) (in custom wh at level 0).
Notation "⟨ t1 ',' t2 ⟩" := (Term.tm_pair t1 t2) 
                          (in custom wh at level 0, t1 custom wh at level 99, 
                           t2 custom wh at level 99).

Notation "'Fix' t"   := (Term.tm_fix t) (in custom wh at level 0).
Notation "'fst.' t"  := (Term.tm_fst t) (in custom wh at level 0).
Notation "'snd.' t"  := (Term.tm_snd t) (in custom wh at level 0).

Notation "'rsf[' r ']'" := (Term.tm_rsf r) (in custom wh at level 0, r constr, no associativity).

Notation "'arr(' t ')'"   := (Term.tm_arr t) 
                             (in custom wh at level 0, t custom wh at level 99, no associativity).
Notation "'first(' A ':' t ')'" := (Term.tm_first A t) (in custom wh at level 0).
Notation " t1 '>>>' t2 "  := (Term.tm_comp t1 t2) (in custom wh at level 60, left associativity).
Notation "'wormhole(' t1 ';' t2 ')'" := (Term.tm_wh t1 t2) 
                                        (in custom wh at level 23, t1 custom wh, t2 custom wh, 
                                         no associativity).

Notation "'[⧐' lb '–' k ']' t"   := (Term.shift lb k t) 
                                     (in custom wh at level 45, right associativity): term_scope.
Notation "'[⧐⧐' lb '–' k ']' t" := (Term.multi_shift lb k t) 
                                    (in custom wh at level 45, right associativity): term_scope.

Infix "⊩" := Term.Wf (at level 20, no associativity): term_scope.   
Infix "=" := Term.eq: term_scope.

Notation "⩽ v … ⩾" := (Cell.inp v) (at level 30, v custom wh, no associativity).
Notation "⩽ … v ⩾" := (Cell.out v) (at level 30, v custom wh, no associativity).
Notation "'[⧐' lb '–' k ']' t" := (Cell.shift lb k t) (at level 65, right associativity) : cell_scope.

Infix "⊩" := Cell.Wf (at level 20, no associativity) : cell_scope. 
Infix "=" := Cell.eq : cell_scope.

(** ** Morphisms *)

#[export] Hint Resolve Var.eq_refl Var.eq_sym Var.eq_trans : core.
#[export] Hint Constructors Term.value : core.

Section var_instance.

Import Var.

#[export] Instance var_eq_rr : RewriteRelation Var.eq := _.

#[export] Instance var_eq_equiv : Equivalence Var.eq := _.

#[export] Instance var_leibniz_eq : Proper Logic.eq Var.eq := _.

End var_instance.


Section resource_instance.

Import Resource. 

#[export] Instance resource_leibniz_eq : Proper Logic.eq Resource.eq := _.

#[export] Instance resource_Wf_iff : Proper (Level.eq ==> eq ==> iff) Wf := _.

#[export] Instance resource_shift_eq :
  Proper (Level.eq ==> Level.eq ==> eq ==> Logic.eq) shift := _.

#[export] Instance resource_multi_shift_eq : 
  Proper (Logic.eq ==> Logic.eq ==> eq ==> Logic.eq) multi_shift := _.

End resource_instance.


Section resources_instance.

Import Resources.

#[export] Instance resources_leibniz_eq : Proper Logic.eq Resources.eq := _.

#[export] Instance resources_Wf_iff :  Proper (Level.eq ==> eq ==> iff) Wf := _.

#[export] Instance resources_shift_eq :
  Proper (Level.eq ==> Level.eq ==> eq ==> eq) shift := shift_eq.

#[export] Instance resources_multi_shift_eq : 
  Proper (Logic.eq ==> Logic.eq ==> eq ==> Logic.eq) multi_shift := multi_shift_eq.

#[export] Instance resources_new_key_eq : Proper (eq ==> Logic.eq) new_key := new_key_eq.

End resources_instance.


Section typ_instance.

Import Typ.

#[export] Instance typ_leibniz_eq: Proper Logic.eq eq := _.

#[export] Instance typ_wf_iff:  Proper (Level.eq ==> eq ==> iff) Wf := _.

#[export] Instance typ_shift_eq: Proper (Level.eq ==> Level.eq ==> eq ==> eq) shift := shift_eq.

#[export] Instance typ_multi_shift_eq: 
  Proper (Logic.eq ==> Logic.eq ==> eq ==> Logic.eq) multi_shift := _.

End typ_instance.


Section term_instance.

Import Term.

#[export] Instance term_leibniz_eq: Proper Logic.eq eq := _.

#[export] Instance term_wf_iff:  Proper (Level.eq ==> eq ==> iff) Wf := _.

#[export] Instance term_shift_eq: 
  Proper (Level.eq ==> Level.eq ==> eq ==> eq) shift := shift_eq.

#[export] Instance term_multi_shift_eq: 
  Proper (Logic.eq ==> Logic.eq ==> eq ==> Logic.eq) multi_shift := _.

End term_instance.

Section cell_instance.

Import Cell.

#[export] Instance cell_leibniz_eq : Proper Logic.eq eq := _.

#[export] Instance cell_wf_iff :  Proper (Level.eq ==> eq ==> iff) Wf := _.

#[export] Instance cell_shift_eq : 
  Proper (Level.eq ==> Level.eq ==> eq ==> eq) shift := shift_eq.

End cell_instance.