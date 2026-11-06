import SolidityBridge.Yul.JsonCompilation
import SolidityBridge.Yul.NestedSwitch
/-! Actual checked JSON to the recursive normal scope/switch compiler and
existing exact mathematical model selection. No Body dispatch/admission,
Source attachment/MemOK, open raw-local readback or native/G24 adequacy claim. -/
namespace SolidityBridge.Yul.StructuredJson
open Solidity Backend Scalar Selection
open Solidity.Yul Solidity.Yul.Compilation
open Solidity.Frontend.YulJson
abbrev Error := JsonCompilation.Error

structure Compiled {outside bound node} (checked : Words.Checked outside bound node) (fuel : Nat) where
  statement : NestedSwitch.Compiled fuel checked.program.code
  block : Backend.Block
  emitted : statement.emit = some block
  selected : OccurrenceControl.Selected block

def compile {outside bound node} (checked : Words.Checked outside bound node) (fuel : Nat) :
    Except Error (Compiled checked fuel) :=
  match NestedSwitch.compile fuel checked.program.code with
  | none => .error .statement
  | some statement =>
    match emitted : statement.emit with
    | none => .error .slots
    | some block =>
      match LoopSelection.selectBlock block with
      | none => .error .opcode
      | some selected => .ok ⟨statement,block,emitted,selected⟩

structure Packet (outside : List String) (bound fuel : Nat) (node : Lean.Json) where
  checked : Words.Checked outside bound node
  compiled : Compiled checked fuel

def checkCompile (outside : List String) (bound fuel : Nat) (node : Lean.Json) :
    Except Error (Packet outside bound fuel node) := do
  let checked ← (Words.check outside bound node).mapError JsonCompilation.Error.input
  let compiled ← compile checked fuel
  pure ⟨checked,compiled⟩

/-- Concrete checked-program execution; capacity/native/source attachment remain separate. -/
theorem Compiled.source {outside bound fuel node}
    {checked : Words.Checked outside bound node} (compiled : Compiled checked fuel) :
    checked.run fuel = some (⟨Fin.elim0,.normal⟩ : Closed.Outcome ClosedSyntax.rootControl 0) := by
  have law := compiled.statement.source (#v[] : Vector Solidity.Backend.Scalar.Word 0)
  have initial : Solidity.Yul.Compilation.ProducerExpressions.sourceLocals (#v[] : Vector Solidity.Backend.Scalar.Word 0) =
      (Fin.elim0 : Solidity.Yul.Closed.Values 0) := by
    funext i
    exact Fin.elim0 i
  have final : Solidity.Yul.Compilation.ProducerExpressions.sourceLocals (compiled.statement.update #v[]) =
      (Fin.elim0 : Solidity.Yul.Closed.Values 0) := by
    funext i
    exact Fin.elim0 i
  rw [initial,final] at law
  exact law

/-- Actual selected structured-model execution; capacity is separate. -/
theorem Compiled.model {outside bound fuel node}
    {checked : Words.Checked outside bound node} (compiled : Compiled checked fuel)
    (tail : Scalar.Stack) (m : Evm.Machine) (represented : m.stack = irStack tail) :
    Evm.run compiled.selected.realization.ir m = .ok m 0 := by
  have target := compiled.statement.structured compiled.block compiled.emitted #v[] tail
  have executed : Solidity.Backend.Selection.StructuredExec compiled.block tail tail := by
    simpa only [Vector.eq_empty,Vector.toList_empty,List.nil_append] using target
  have ran := (compiled.selected.lowering.success tail tail m represented).mpr executed
  rw [←represented] at ran
  exact ran

/-- info: 'SolidityBridge.Yul.StructuredJson.Compiled.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compiled.source
/-- info: 'SolidityBridge.Yul.StructuredJson.Compiled.model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compiled.model

/-- info: 'SolidityBridge.Yul.StructuredJson.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile

/-- info: 'SolidityBridge.Yul.StructuredJson.checkCompile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkCompile
end SolidityBridge.Yul.StructuredJson
