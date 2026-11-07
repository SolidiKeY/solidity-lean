import Solidity.Backend.Aggregates.IntegerArrays
import Solidity.Backend.Aggregates.ByteSliceControls

/-! Inhabited soundness boundary for selected uint8 reads versus eager copying.
These are native Source/client observations, never machine reverts. -/
namespace Solidity.Backend.Aggregates.IntegerReadBoundaryWitness
open Solidity ByteParameterControls

def data : Roadmap.Bytes := List.replicate 31 0 ++ [32] ++
  List.replicate 31 0 ++ [2] ++ List.replicate 31 0 ++ [255] ++
  List.replicate 30 0 ++ [1,0]

def frame : Source.Fr := { ByteParameterControls.frame with cd := selector ++ data }

def selected : Source.Val E.layout (.int Source.IntTy.u8) := .int 255 (by decide)

abbrev caller : Source.RCtx := [.bytes .memory,.bytes .memory]
abbrev locals : Source.RCtx := IntegerArrays.Expression.argumentTy Source.IntTy.u8 ::
  .int Source.IntTy.u256 :: caller

def before : Source.EMState E locals :=
  (.cons (.cdRef rfl 68 2) (.cons (.int 0 (by decide)) sourceLocals),sourceState)

theorem geometry : Source.cdWordAt frame 68 = 255 ∧ Source.cdWordAt frame 100 = 256 ∧
    Source.cdTail data 0 32 = .ok (68,2) := by
  refine ⟨by decide, by decide, ?_⟩
  have offset : Source.wordAt data 0 = 32 := by decide
  have count : Source.wordAt (data.drop 32) 0 = 2 := by decide
  have size : data.length = 128 := by rfl
  simp only [Source.cdTail, offset, count, size]
  rfl

theorem selected_decodes : Source.decodeWord E.layout 255 (.int Source.IntTy.u8) = .ok selected := rfl

theorem traversal_fails : (List.range 2).mapM (fun j => Source.decodeWord E.layout
    (Source.cdWordAt frame (68+32*j)) (.int Source.IntTy.u8)) = .error (.revert []) := rfl

/-- Inhabited native Source success versus eager Source-phase failure.
This refutes promotion of eager validation to general selected-read lowering;
it asserts no machine failure, profile exclusion or transaction rollback. -/
theorem inhabited_boundary :
    (Source.evalE ByteSliceControls.G frame 2 (IntegerArrays.CalldataRead.expr Source.IntTy.u8)).run before =
      (.ok (.val selected),before) ∧
    IntegerArrays.lowerEntry (E := E) aliasTarget Source.IntTy.u8 frame selector data rfl rfl 0 =
      .error (.revert []) := by
  have selected_ok : Source.decodeWord E.layout (Source.cdWordAt frame (68+32*0))
      (.int Source.IntTy.u8) = .ok selected := by
    rw [geometry.1]
    exact selected_decodes
  obtain ⟨typed,read,importError⟩ := IntegerArrays.CalldataRead.selected_success_import_error
    Source.IntTy.u8 ByteSliceControls.G frame 0 selector data rfl rfl geometry.2.2
    sourceLocals sourceState aliasTarget ⟨0,by decide⟩ selected (.revert []) selected_ok traversal_fails
  exact ⟨read,importError⟩

end Solidity.Backend.Aggregates.IntegerReadBoundaryWitness
