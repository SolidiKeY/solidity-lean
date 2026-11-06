import SolidityBridge.Yul.BitwiseSelection
import Solidity.Yul.EvmSigned
import Solidity.Yul.Compilation.SignedMachine
/-! Concrete signed instruction certificates and actual original source/control
consumption. Existing word semantics and candidate generator are reused;
source admission/native/charged/G24 closure are not inferred. -/
namespace SolidityBridge.Yul.SignedSelection
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation

def sdivFacts : QuotientSelection.BinaryEvidence .sdiv SignedExpressions.sdivBridge.selection :=
  ⟨rfl,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,
    QuotientSelection.bridge_step SignedExpressions.sdivBridge .sdiv Solidity.Yul.EvmSigned.step_sdiv⟩
def sdiv : InstructionCertificate .sdiv := QuotientSelection.certificate .sdiv _ sdivFacts
def smodFacts : QuotientSelection.BinaryEvidence .smod SignedExpressions.smodBridge.selection :=
  ⟨rfl,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,
    QuotientSelection.bridge_step SignedExpressions.smodBridge .smod Solidity.Yul.EvmSigned.step_smod⟩
def smod : InstructionCertificate .smod := QuotientSelection.certificate .smod _ smodFacts
def sltFacts : QuotientSelection.BinaryEvidence .slt SignedExpressions.sltBridge.selection :=
  ⟨rfl,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,
    QuotientSelection.bridge_step SignedExpressions.sltBridge .slt Solidity.Yul.EvmSigned.step_slt⟩
def slt : InstructionCertificate .slt := QuotientSelection.certificate .slt _ sltFacts
def sgtFacts : QuotientSelection.BinaryEvidence .sgt SignedExpressions.sgtBridge.selection :=
  ⟨rfl,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,
    QuotientSelection.bridge_step SignedExpressions.sgtBridge .sgt Solidity.Yul.EvmSigned.step_sgt⟩
def sgt : InstructionCertificate .sgt := QuotientSelection.certificate .sgt _ sgtFacts

def select : (i : Evm.Instr) → Option (InstructionCertificate i)
  | .sdiv => some sdiv
  | .smod => some smod
  | .slt => some slt
  | .sgt => some sgt
  | i => BitwiseSelection.select i

/-- Candidate generation is not assumed correct: real instruction certificates
and exact emitted-code identity still establish every successful Slice. -/
def compileLeaf : (p : Backend.Program) → Option (ControlRealization.Slice p) :=
  ControlRealization.selectSliceUsing SignedMachine.selectCode select
def compileBlock : (b : Backend.Block) → Option (ControlRealization.Realization b) :=
  ControlRealization.selectBlockWith compileLeaf

def expression (op : Solidity.Yul.Pure 2) (a b : Fin 3) : Solidity.Yul.Expr [] [] 3 1 :=
  .builtin (.pure op) (Fin.cases (.local a) (fun _ => .local b))
def assignment (target : Fin 3) (op : Solidity.Yul.Pure 2) (a b : Fin 3) :
    Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 :=
  .assign (fun _ : Fin 1 => .local target) (expression op a b)
def body : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 :=
  .seq (assignment 0 .sdiv 0 1) (.seq (assignment 1 .smod 0 1) (assignment 2 .sgt 0 1))
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 := .if_ (expression .slt 0 1) body
def compiled := (NormalControl.compile 6 statement).get (by rfl)
def block := (compiled.emit 0).get (by rfl)
def selected := (compileBlock block).get (by rfl)
def lowering := ControlCompleteness.selected_lowering_with compileLeaf selected (by rfl)
abbrev source_model := ControlRealization.source_model compiled 0 block (by rfl) selected

def prefixedBlock := (compiled.emit 2).get (by rfl)
def prefixed := (compileBlock prefixedBlock).get (by rfl)
def prefixed_lowering := ControlCompleteness.selected_lowering_with compileLeaf prefixed (by rfl)
abbrev prefixed_source_model := ControlRealization.source_model compiled 2 prefixedBlock (by rfl) prefixed

end SolidityBridge.Yul.SignedSelection
