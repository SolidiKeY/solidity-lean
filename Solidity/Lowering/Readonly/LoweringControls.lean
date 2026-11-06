import Solidity.Lowering.Readonly.PrimitiveInitialization
import Solidity.Lowering.Readonly.PrimitiveReads
import Solidity.Lowering.Readonly.PrimitiveLocals
import Solidity.Lowering.Readonly.JournalLeaves
import Solidity.Lowering.Readonly.Controls

/-! Nonempty typed lowering controls. Source/intrinsic storage and local APIs
are exercised directly; these are not EVM compiler/native adequacy claims. -/
namespace Solidity.Lowering.Readonly.LoweringControls
open Solidity.Source Solidity.Source.SemanticsExamples
open PrimitiveValues PrimitiveFields PrimitiveLocals
open Solidity.Lowering.Readonly.Controls

def layout : PrimitiveFields.Layout EB Cell where
  fields := .field "x" .uint dX (by rfl) rfl dX_ty rfl (by rfl) (by rfl) .nil
  persistent := rfl

theorem entry_related : Rel layout.fields thisC (sB.ex.world.accounts thisC).storage typedThree := by exact ⟨rfl, True.intro⟩

theorem constructed_exit : ∃ after : Solidity.Storage Cell,
    Rel layout.fields thisC (final.ex.world.accounts thisC).storage after ∧ after = typedThree :=
  caller_exit origin _ _ raw runtime layout typedThree entry_related

def typedZero : Solidity.Storage Cell := .cons (.prim ⟨0, by decide⟩) .nil

theorem unset_uses_source_default : Rel layout.fields thisC
    (Solidity.Source.Storage.empty : Solidity.Source.Storage EB.layout (EB.lay thisC)) typedZero := by exact ⟨rfl, True.intro⟩

theorem actual_source_read :
    (readAt FC dX.path (sourceTy .uint) : EM EB [] _).run (.nil, sB) =
      (.ok (toSource EB.layout .uint ⟨3, by decide⟩), (.nil, sB)) :=
  PrimitiveReads.read_head FC "x" .uint dX (by rfl) rfl dX_ty rfl (by rfl) (by rfl)
    .nil ⟨3, by decide⟩ .nil .nil sB entry_related

theorem actual_intrinsic_read : typedThree.find (SRef.ofRoot "x" rfl) =
    some (.prim (p := .uint) ⟨3, by decide⟩) := by rfl

def typedFour : Solidity.Storage Cell := .cons (.prim ⟨4, by decide⟩) .nil

theorem unrelated_storage_refused : ¬ Rel layout.fields thisC (sB.ex.world.accounts thisC).storage typedFour := by
  intro related
  have equal := PrimitiveFields.unique layout.fields thisC _ typedFour typedThree related entry_related
  cases equal

def parameters : Vals EB.layout ([PrimTy.uint, .int, .bool].map sourceTy) :=
  .cons (toSource EB.layout .uint ⟨11, by decide⟩)
    (.cons (toSource EB.layout .int ⟨-7, by decide⟩) (.cons (toSource EB.layout .bool true) .nil))

def sourceParameters := parameters.onto (Locals.nil : Locals EB.layout [])
def targetParameters : TEnv Cell [] (targetCtx [.bool, .int, .uint]) :=
  fromLocals EB.layout [.bool, .int, .uint] sourceParameters

/-- Existing Source.Vals.onto puts the last source parameter innermost. -/
theorem parameter_order : TEnv.get .here targetParameters = true ∧
    (TEnv.get (.there .here) targetParameters).val = -7 ∧
    (TEnv.get (.there (.there .here)) targetParameters).val = 11 := by exact ⟨rfl, rfl, rfl⟩

theorem parameter_permutation_refused :
    (TEnv.get (.there (.there .here)) targetParameters).val ≠ -7 := by decide +kernel

theorem static_write_leaf : StaticJournal.History sB.ex true
    ((setCell { FC with static := true } dX.path (some x3) : EM EB [] Unit).run (.nil, sB)).2.2.ex :=
  JournalLeaves.cell_history { FC with static := true } dX.path (some x3) .nil sB

theorem insufficient_debit_leaf :
    (debit thisC (word 1) : EM EB [] Bool).run (.nil, sB) = (.ok false, (.nil, sB)) := by rfl

theorem zero_debit_history : StaticJournal.History sB.ex true
    ((debit thisC (word 0) : EM EB [] Bool).run (.nil, sB)).2.2.ex :=
  JournalLeaves.debit_history _ _ _ _ _

/-- Nominal and aggregate source types cannot acquire this primitive certificate. -/
theorem enum_refused (name : DeclName) : ¬ ∃ p, sourceTy p = STy.enum name := by
  rintro ⟨p, same⟩
  cases p <;> cases same

theorem struct_refused (name : DeclName) : ¬ ∃ p, sourceTy p = STy.struct .storage name := by
  rintro ⟨p, same⟩
  cases p <;> cases same

def callLayout : CallLayout origin Cell where
  layout := layout
  owned := ⟨⟨"C", rfl, rfl⟩, True.intro⟩

theorem owned_constructed_exit : ∃ after : Solidity.Storage Cell,
    Rel callLayout.layout.fields thisC (final.ex.world.accounts thisC).storage after ∧ after = typedThree :=
  lowered_caller_exit origin _ _ raw runtime callLayout typedThree entry_related

theorem actual_return_slots :
    (zeroVals 1 ([PrimTy.int, .bool].map sourceTy) : EM EB [] _).run (.nil, sB) =
      (.ok (PrimitiveInitialization.defaults EB.layout [.int, .bool]), (.nil, sB)) := by
  rw [PrimitiveInitialization.zero_values]
  rfl

theorem exhausted_return_slots :
    (zeroVals 0 ([PrimTy.int, .bool].map sourceTy) : EM EB [] _).run (.nil, sB) =
      (.error .timeout, (.nil, sB)) := by
  rw [PrimitiveInitialization.exhausted_nonempty]
  rfl

theorem generic_intrinsic_read :
    ((SFields.cons (f := "x") (.prim (p := .uint) ⟨3, by decide⟩) SFields.nil).get
      (f := "x") (by rfl)).find .nil = some (.prim (p := .uint) ⟨3, by decide⟩) :=
  PrimitiveReads.target_read_head "x" .uint ⟨3, by decide⟩ .nil rfl

theorem actual_source_expression :
    (evalE (GB answerOnly) FC 1 (.state dX dX_ty) : EM EB [] _).run (.nil, sB) =
      (.ok (.val (toSource EB.layout .uint ⟨3, by decide⟩)), (.nil, sB)) :=
  PrimitiveReads.source_expression (GB answerOnly) FC 0 dX .uint dX_ty (by rfl) rfl (by rfl)
    .nil sB ⟨3, by decide⟩ (by rfl)

theorem actual_target_expression :
    (Solidity.Val.read (.root "x" rfl) : Solidity.Val Cell [] .uint).evalT
      (Solidity.State.ofStorage typedThree) = .ok ⟨3, by decide⟩ :=
  PrimitiveReads.target_expression _ "x" .uint rfl ⟨3, by decide⟩ actual_intrinsic_read

theorem exhausted_source_expression :
    (evalE (GB answerOnly) FC 0 (.state dX dX_ty) : EM EB [] _).run (.nil, sB) =
      (.error .timeout, (.nil, sB)) := by rfl

end Solidity.Lowering.Readonly.LoweringControls
