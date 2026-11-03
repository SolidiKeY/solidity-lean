import Solidity.Lowering.Readonly.LocationEffects
import Solidity.Lowering.Readonly.CopyControls

/-! Inhabited Source location controls. Static mode permits local/memory
mutation but retains storage/calldata guards and exact bounds/type failures.
These are helper runs, not native or deployment provenance. -/
namespace Solidity.Lowering.Readonly.LocationControls
open Solidity.Source
open Solidity.Source.SemanticsExamples
open SourceHistory
namespace C
abbrev E := CopyControls.E
abbrev frame := CopyControls.frame
abbrev checkpoint := CopyControls.checkpoint
abbrev memory := CopyControls.loaded.2.2
end C

def byteProgram : EM C.E [] (Solidity.Source.Val C.E.layout (.fixedBytes 1 (by decide))) := do
  writeLoc {C.frame with static := true} 12 (.memByte 0 0)
    (Solidity.Source.Val.fixedBytes (n := 1) (h := by decide) [99] rfl)
  readLoc {C.frame with static := true} (.memByte 0 0)
def byteResult := byteProgram.run (L0 C.E, C.memory)
def byteBounds := (writeLoc {C.frame with static := true} 12 (.memByte 0 2)
  (Solidity.Source.Val.fixedBytes (n := 1) (h := by decide) [5] rfl) :
  EM C.E [] Unit).run (L0 C.E, C.memory)
def byteLength := (lengthOf {C.frame with static := true}
  (Solidity.Source.Val.memRef (τ := .bytes .memory) rfl 0) : EM C.E [] Nat).run (L0 C.E, C.memory)

def arrayData : Solidity.Source.Data EB.layout (.array .memory .bool (some 1)) :=
  .array 1 (fun _ h => (Option.some.inj h).symm) (fun _ => .val (.bool false))
def arrayState : St EB := {sB with heap := ((Solidity.Source.Heap.empty).alloc ⟨_, arrayData⟩).1}
def arrayRef : Solidity.Source.Val EB.layout (.array .memory .bool (some 1)) := .memRef rfl 0
def arrayProgram : EM EB [] (Solidity.Source.Val EB.layout .bool) := do
  writeLoc {FC with static := true} 12 (.mem 0 0) (.bool true)
  readLoc {FC with static := true} (.mem 0 0)
def arrayResult := arrayProgram.run (L0 EB, arrayState)
def arrayWrong := (memSet 0 0 (Solidity.Source.Val.int (t := IntTy.u256) 1 (by decide)) :
  EM EB [] Unit).run (L0 EB, arrayState)
def indexGood := (indexLoc {FC with static := true} arrayRef 0 : EM EB [] _).run (L0 EB, arrayState)
def indexBad := (indexLoc {FC with static := true} arrayRef 1 : EM EB [] _).run (L0 EB, arrayState)

def localProgram : EM EB [.bool] (Solidity.Source.Val EB.layout .bool) := do
  writeLoc {FC with static := true} 12 (.local .here) (.bool true)
  readLoc {FC with static := true} (.local .here)
def localResult := localProgram.run (.cons (.bool false) .nil, sB)
def localDeleted := (deleteLoc {FC with static := true} 1
  (.local .here : Solidity.Source.Loc EB.layout [.bool] .bool) :
  EM EB [.bool] Unit).run (.cons (.bool true) .nil, sB)

def scalar (mode : Bool) := (writeLoc {FC with static := mode} 12
  (.stor dX.path) (Solidity.Source.Val.int (t := IntTy.u256) 4 (by decide)) :
  EM EB [] Unit).run (L0 EB, sB)
def scalarDeleted := (deleteLoc {FC with static := true} 12
  (.stor dX.path : Solidity.Source.Loc EB.layout [] uint) :
  EM EB [] Unit).run (L0 EB, sB)
def calldataWrite := (writeLoc {FC with static := true} 12
  (.cd 0) (Solidity.Source.Val.int (t := IntTy.u256) 4 (by decide)) :
  EM EB [] Unit).run (L0 EB, sB)
def deleteExhausted := (deleteLoc {FC with static := true} 0
  (.local .here : Solidity.Source.Loc EB.layout [.bool] .bool) :
  EM EB [.bool] Unit).run (.cons (.bool true) .nil, sB)


theorem observations : byteResult.1 = .ok (.fixedBytes [99] (by rfl)) ∧
 byteResult.2.2.heap.get 0 = some ⟨.bytes .memory, .bytes [99,9]⟩ ∧
 byteResult.2.2.ex = C.checkpoint.ex ∧
 byteBounds.1 = .error (.revert (Solidity.Source.panicData .index)) ∧
 byteBounds.2.2.heap.get 0 = some ⟨.bytes .memory, .bytes [7,9]⟩ ∧
 byteLength.1 = .ok 2 ∧
 arrayResult.1 = .ok (.bool true) ∧
 arrayResult.2.2.ex = sB.ex ∧
 arrayWrong.1 = .error (.stuck "element type") ∧
 arrayWrong.2.2.heap.get 0 = arrayState.heap.get 0 ∧
 indexGood.1 = .ok (.mem 0 0) ∧
 indexBad.1 = .error (.revert (Solidity.Source.panicData .index)) ∧
 localResult.1 = .ok (.bool true) ∧
 localResult.2.1 = .cons (.bool true) .nil ∧
 localResult.2.2.ex = sB.ex ∧
 localDeleted.1 = .ok () ∧
 localDeleted.2.1 = .cons (.bool false) .nil ∧
 (scalar false).1 = .ok () ∧
 readX (scalar false).2.2 = some 4 ∧
 (scalar true).1 = .error (.revert []) ∧
 readX (scalar true).2.2 = some 3 ∧
 scalarDeleted.1 = .error (.revert []) ∧
 calldataWrite.1 = .error (.stuck "calldata is read only") ∧
 deleteExhausted.1 = .error .timeout ∧
 deleteExhausted.2.1 = .cons (.bool true) .nil := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

theorem byte_effect : Solidity.Lowering.Readonly.SourceHistory.Effect true byteProgram := by
  unfold Solidity.Lowering.Readonly.LocationControls.byteProgram
  apply Solidity.Lowering.Readonly.SourceHistory.Effect.bind
  · exact Solidity.Lowering.Readonly.SourceHistory.writeLoc_effect {Solidity.Lowering.Readonly.LocationControls.C.frame with static := true} 12 _ _
  · intro done
    exact Solidity.Lowering.Readonly.SourceHistory.readLoc_effect true {Solidity.Lowering.Readonly.LocationControls.C.frame with static := true} _

theorem scalar_effect : ∀ mode n, Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.writeLoc (E := Solidity.Source.SemanticsExamples.EB) (Γ := []) {Solidity.Source.SemanticsExamples.FC with static := mode} n
 (Solidity.Source.Loc.stor Solidity.Source.SemanticsExamples.dX.path : Solidity.Source.Loc Solidity.Source.SemanticsExamples.EB.layout [] Solidity.Source.SemanticsExamples.uint)
 (Solidity.Source.Val.int (t := Solidity.Source.IntTy.u256) 4 (by decide))) := by
  intro mode n; exact Solidity.Lowering.Readonly.SourceHistory.writeLoc_effect {Solidity.Source.SemanticsExamples.FC with static := mode} n _ _

theorem ordinary_changes : Solidity.Source.SemanticsExamples.readX (scalar false).2.2 ≠ Solidity.Source.SemanticsExamples.readX Solidity.Source.SemanticsExamples.sB := by
  decide

end Solidity.Lowering.Readonly.LocationControls
