import Solidity.Frontend.SolcJson.YulWords
import Solidity.Yul.Compilation.ScopedStatements
import SolidityBridge.Yul.OccurrenceSelection
/-! Actual closed JSON word preparation to existing scoped compiler and exact
scalar instruction certificates. This is not Body dispatch/admission, Source
attachment/MemOK, open dirty-local readback or full Source/G24/native adequacy. -/
namespace SolidityBridge.Yul.JsonCompilation
open Solidity Backend Scalar Selection
open Solidity.Yul Solidity.Yul.Compilation
open Solidity.Frontend.YulJson

inductive Error where
  | input (reason : Words.Error)
  | statement
  | slots
  | opcode
  deriving Repr

/-- Certificates indexed by the actual checked JSON result and source horizon.
Every AST, local context and target instruction remains the existing type. -/
structure Compiled {outside bound node} (checked : Words.Checked outside bound node) (fuel : Nat) where
  statement : ProducerStatements.Compiled fuel checked.program.code
  code : Backend.Program
  emitted : statement.lowered.code 0 = some code
  selected : OccurrenceSelection.Slice code

def compile {outside bound node} (checked : Words.Checked outside bound node) (fuel : Nat) :
    Except Error (Compiled checked fuel) :=
  match ScopedStatements.compile fuel checked.program.code with
  | none => .error .statement
  | some statement =>
    match emitted : statement.lowered.code 0 with
    | none => .error .slots
    | some code =>
      match OccurrenceSelection.selectCode code with
      | none => .error .opcode
      | some selected => .ok ⟨statement,code,emitted,selected⟩

structure Packet (outside : List String) (bound fuel : Nat) (node : Lean.Json) where
  checked : Words.Checked outside bound node
  compiled : Compiled checked fuel

/-- Exact existing checker errors are retained; compiler-stage refusal is
separate from grammar/static/safety/policy failure. No dispatcher is widened. -/
def checkCompile (outside : List String) (bound fuel : Nat) (node : Lean.Json) :
    Except Error (Packet outside bound fuel node) := do
  let checked ← (Words.check outside bound node).mapError Error.input
  let compiled ← compile checked fuel
  pure ⟨checked,compiled⟩

/-- Actual prepared-program execution at the same source horizon. -/
theorem Compiled.source {outside bound node fuel}
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

/-- The emitted program executes successfully with every actual numeric caller
suffix and preserves the full existing machine. Capacity is separate. -/
theorem Compiled.model {outside bound node fuel}
    {checked : Words.Checked outside bound node} (compiled : Compiled checked fuel)
    (tail : Scalar.Stack) (m : Evm.Machine) (represented : m.stack = irStack tail) :
    Scalar.run compiled.code tail = some tail ∧ Evm.run compiled.selected.ir m = .ok m 0 := by
  have scalar := compiled.statement.lowered.correct 0 compiled.code compiled.emitted #v[] #v[] tail
  have executed : Solidity.Backend.Scalar.run compiled.code tail = some tail := by
    simpa only [Vector.eq_empty,Vector.toList_empty,List.nil_append] using scalar
  refine ⟨executed,?_⟩
  have ran := ((SolidityBridge.Yul.OccurrenceSelection.lowering compiled.code compiled.selected).success
    tail tail m represented).mpr (Solidity.Backend.Selection.StructuredExec.code executed)
  rw [←represented] at ran
  exact ran

/-- info: 'SolidityBridge.Yul.JsonCompilation.Compiled.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compiled.source
/-- info: 'SolidityBridge.Yul.JsonCompilation.Compiled.model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Compiled.model

end SolidityBridge.Yul.JsonCompilation
