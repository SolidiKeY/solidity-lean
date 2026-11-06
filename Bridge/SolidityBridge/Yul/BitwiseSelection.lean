import SolidityBridge.Yul.QuotientSelection
import SolidityBridge.Yul.ControlCompleteness
import Solidity.Yul.EvmBitwise
/-! Concrete bitwise/shift instruction certificates using actual VY1 word
steps and original compiler bridges. No duplicated word semantics, AST/state,
selector algorithm or admission. Native/G24/resource closure remains open. -/
namespace SolidityBridge.Yul.BitwiseSelection
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation

def andFacts : QuotientSelection.BinaryEvidence .and BitExpressions.andBridge.selection :=
  ⟨rfl,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,
    QuotientSelection.bridge_step BitExpressions.andBridge .and Solidity.Yul.EvmBitwise.step_and⟩
def orFacts : QuotientSelection.BinaryEvidence .or BitExpressions.orBridge.selection :=
  ⟨rfl,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,
    QuotientSelection.bridge_step BitExpressions.orBridge .or Solidity.Yul.EvmBitwise.step_or⟩
def xorFacts : QuotientSelection.BinaryEvidence .xor BitExpressions.xorBridge.selection :=
  ⟨rfl,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,
    QuotientSelection.bridge_step BitExpressions.xorBridge .xor Solidity.Yul.EvmBitwise.step_xor⟩
def shlFacts : QuotientSelection.BinaryEvidence .shl BitExpressions.shlBridge.selection :=
  ⟨rfl,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,
    QuotientSelection.bridge_step BitExpressions.shlBridge .shl Solidity.Yul.EvmBitwise.step_shl⟩
def shrFacts : QuotientSelection.BinaryEvidence .shr BitExpressions.shrBridge.selection :=
  ⟨rfl,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,
    QuotientSelection.bridge_step BitExpressions.shrBridge .shr Solidity.Yul.EvmBitwise.step_shr⟩
def band : InstructionCertificate .and := QuotientSelection.certificate .and _ andFacts
def bor : InstructionCertificate .or := QuotientSelection.certificate .or _ orFacts
def bxor : InstructionCertificate .xor := QuotientSelection.certificate .xor _ xorFacts
def shl : InstructionCertificate .shl := QuotientSelection.certificate .shl _ shlFacts
def shr : InstructionCertificate .shr := QuotientSelection.certificate .shr _ shrFacts

/-- Separate extension table; earlier concrete tables and refusals are intact. -/
def select : (i : Evm.Instr) → Option (InstructionCertificate i)
  | .and => some band
  | .or => some bor
  | .xor => some bxor
  | .shl => some shl
  | .shr => some shr
  | i => QuotientSelection.select i

def compileLeaf : (p : Backend.Program) → Option (ControlRealization.Slice p) :=
  ControlRealization.selectSliceWith select
def compileBlock : (block : Backend.Block) → Option (ControlRealization.Realization block) :=
  ControlRealization.selectBlockWith compileLeaf

/-- Constructor helpers over the original intrinsic AST, with three locals:
count, value, mask. Shift counts are the left/top operands. -/
def expression (op : Solidity.Yul.Pure 2) (a b : Fin 3) : Solidity.Yul.Expr [] [] 3 1 :=
  .builtin (.pure op) (Fin.cases (.local a) (fun _ => .local b))
def assignment (target : Fin 3) (op : Solidity.Yul.Pure 2) (a b : Fin 3) :
    Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 :=
  .assign (fun _ : Fin 1 => .local target) (expression op a b)
def body : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 :=
  .seq (.seq (assignment 1 .and 1 2) (assignment 1 .xor 1 2))
    (.seq (assignment 2 .or 1 2) (.seq (assignment 1 .shl 0 1) (assignment 1 .shr 0 1)))
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 := .if_ (expression .and 1 2) body
def compiled := (NormalControl.compile 7 statement).get (by rfl)
def block := (compiled.emit 0).get (by rfl)
def selected := (compileBlock block).get (by rfl)
def lowering := ControlCompleteness.selected_lowering_with compileLeaf selected (by rfl)
abbrev source_model := ControlRealization.source_model compiled 0 block (by rfl) selected

def prefixedBlock := (compiled.emit 2).get (by rfl)
def prefixed := (compileBlock prefixedBlock).get (by rfl)
def prefixed_lowering := ControlCompleteness.selected_lowering_with compileLeaf prefixed (by rfl)
abbrev prefixed_source_model := ControlRealization.source_model compiled 2 prefixedBlock (by rfl) prefixed

end SolidityBridge.Yul.BitwiseSelection
