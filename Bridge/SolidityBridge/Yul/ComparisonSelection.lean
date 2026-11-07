import SolidityBridge.Yul.SignedSelection
/-! Concrete unsigned LT/GT/EQ certificates and original-source structured
consumption. Existing word/compiler proofs are reused; native/G24/frontend
closure is not inferred. -/
namespace SolidityBridge.Yul.ComparisonSelection
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation

def ltFacts : QuotientSelection.BinaryEvidence .lt WordExpressions.ltBridge.selection :=
  ⟨rfl,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,
    QuotientSelection.bridge_step WordExpressions.ltBridge .lt Solidity.Yul.EvmBitwise.step_lt⟩
def lt : InstructionCertificate .lt := QuotientSelection.certificate .lt _ ltFacts

def gtFacts : QuotientSelection.BinaryEvidence .gt WordExpressions.gtBridge.selection :=
  ⟨rfl,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,
    QuotientSelection.bridge_step WordExpressions.gtBridge .gt Solidity.Yul.EvmBitwise.step_gt⟩
def gt : InstructionCertificate .gt := QuotientSelection.certificate .gt _ gtFacts

def eqFacts : QuotientSelection.BinaryEvidence .eq WordExpressions.eqBridge.selection :=
  ⟨rfl,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,
    QuotientSelection.bridge_step WordExpressions.eqBridge .eq Solidity.Yul.EvmBitwise.step_eq⟩
def eq : InstructionCertificate .eq := QuotientSelection.certificate .eq _ eqFacts

def select : (i : Evm.Instr) → Option (InstructionCertificate i)
  | .lt => some lt
  | .gt => some gt
  | .eq => some eq
  | i => SignedSelection.select i

def compileLeaf : (p : Backend.Program) → Option (ControlRealization.Slice p) :=
  ControlRealization.selectSliceUsing SignedMachine.selectCode select
def compileBlock : (b : Backend.Block) → Option (ControlRealization.Realization b) :=
  ControlRealization.selectBlockWith compileLeaf

def body : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 :=
  .seq (SignedSelection.assignment 0 .lt 0 1)
    (.seq (SignedSelection.assignment 1 .gt 1 0) (SignedSelection.assignment 2 .eq 0 1))
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 :=
  .if_ (SignedSelection.expression .eq 0 1) body
def compiled := (NormalControl.compile 6 statement).get (by rfl)
def block := (compiled.emit 0).get (by rfl)
def selected := (compileBlock block).get (by rfl)
def lowering := ControlCompleteness.selected_lowering_with compileLeaf selected (by rfl)
abbrev source_model := ControlRealization.source_model compiled 0 block (by rfl) selected

def prefixedBlock := (compiled.emit 2).get (by rfl)
def prefixed := (compileBlock prefixedBlock).get (by rfl)
def prefixed_lowering := ControlCompleteness.selected_lowering_with compileLeaf prefixed (by rfl)
abbrev prefixed_source_model := ControlRealization.source_model compiled 2 prefixedBlock (by rfl) prefixed
end SolidityBridge.Yul.ComparisonSelection
