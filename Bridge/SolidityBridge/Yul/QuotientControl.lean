import SolidityBridge.Yul.QuotientSelection
import SolidityBridge.Yul.ControlCompleteness
/-! Concrete arithmetic certificate table consumed by the existing structured
selector and its constructive classifier. No replacement compiler syntax,
evaluator, state, admission or native/source-G24 convention is introduced. -/
namespace SolidityBridge.Yul.QuotientControl
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation

def compileLeaf : (p : Backend.Program) → Option (ControlRealization.Slice p) :=
  ControlRealization.selectSliceWith QuotientSelection.select

def compileBlock : (block : Backend.Block) → Option (ControlRealization.Realization block) :=
  ControlRealization.selectBlockWith compileLeaf

/-- Full-word DIV condition; zero divisor produces false, not a source Panic. -/
def condition : Solidity.Yul.Expr [] [] 2 1 :=
  .builtin (.pure .div) (Fin.cases (.local 0) (fun _ => .local 1))
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 :=
  .if_ condition QuotientSelection.statement
def compiled := (NormalControl.compile 6 statement).get (by rfl)
def block := (compiled.emit 0).get (by rfl)
def selected := (compileBlock block).get (by rfl)
def lowering := ControlCompleteness.selected_lowering_with compileLeaf selected (by rfl)
abbrev source_model := ControlRealization.source_model compiled 0 block (by rfl) selected

def prefixedBlock := (compiled.emit 2).get (by rfl)
def prefixed := (compileBlock prefixedBlock).get (by rfl)
def prefixed_lowering := ControlCompleteness.selected_lowering_with compileLeaf prefixed (by rfl)
abbrev prefixed_source_model := ControlRealization.source_model compiled 2 prefixedBlock (by rfl) prefixed

end SolidityBridge.Yul.QuotientControl
