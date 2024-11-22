From Coq Require Import Lia Arith.PeanoNat Classical_Prop Morphisms SetoidList.
From Mecha Require Import Resource Resources Term Cell REnvironment.
From Mecha Require Evaluation_Transition.
From DeBrLevel Require Import LevelInterface MapLevelInterface MapLevel MapExtInterface MapExt.
Import ResourceNotations TermNotations CellNotations
       ResourcesNotations SetNotations REnvironmentNotations.

(** * Environments - Inputs *)

(** ** Module - Inputs *)

Module Inputs <: IsLvlET.

(** *** Definition *)

Include MapLvlD.MakeLvlMapLVLD Term.
Import Raw Ext.

Module RE := REnvironment.
Open Scope renvironment_scope.

(** **** Initialize the resource environment *)

Definition init_globals_func (r : resource) (v : Λ) (V : 𝐕) := ⌈r ⤆ ⩽ v … ⩾⌉ V.

Definition init_globals (t : t) : 𝐕 := fold init_globals_func t ∅.



End Inputs.