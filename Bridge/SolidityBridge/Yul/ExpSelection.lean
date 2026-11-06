import SolidityBridge.Yul.UnarySelection
/-! Actual EXP instruction certificate from existing word/compiler semantics,
and original-source structured composition. Numeric model adequacy here does
not assert native fetched-byte/gas/G24/frontend correspondence. -/
namespace SolidityBridge.Yul.ExpSelection
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation

def expFacts : QuotientSelection.BinaryEvidence .exp RemainingWordBridges.expBridge.selection :=
  ⟨rfl,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,
    QuotientSelection.bridge_step RemainingWordBridges.expBridge .exp Solidity.Yul.EvmBitwise.step_exp⟩
def exp : InstructionCertificate .exp := QuotientSelection.certificate .exp _ expFacts

def select : (i : Evm.Instr) → Option (InstructionCertificate i)
  | .exp => some exp
  | i => UnarySelection.select i

def compileLeaf : (p : Backend.Program) → Option (ControlRealization.Slice p) :=
  ControlRealization.selectSliceUsing SignedMachine.selectCode select
def compileBlock : (b : Backend.Block) → Option (ControlRealization.Realization b) :=
  ControlRealization.selectBlockWith compileLeaf

def body : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 :=
  .seq (SignedSelection.assignment 0 .exp 0 1)
    (.seq (SignedSelection.assignment 1 .exp 0 1) (UnarySelection.assignment 2 .iszero 1))
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 :=
  .if_ (SignedSelection.expression .exp 0 1) body

def compiled := (NormalControl.compile 6 statement).get (by rfl)
def block := (compiled.emit 0).get (by rfl)
def selected := (compileBlock block).get (by rfl)
def lowering := ControlCompleteness.selected_lowering_with compileLeaf selected (by rfl)
abbrev source_model := ControlRealization.source_model compiled 0 block (by rfl) selected

def prefixedBlock := (compiled.emit 2).get (by rfl)
def prefixed := (compileBlock prefixedBlock).get (by rfl)
def prefixed_lowering := ControlCompleteness.selected_lowering_with compileLeaf prefixed (by rfl)
abbrev prefixed_source_model := ControlRealization.source_model compiled 2 prefixedBlock (by rfl) prefixed

/-- All instruction-boundary heights, separate from actual operand existence. -/
theorem exp_capacity (h : Int) :
    Scalar.stackBound [.op .EXP] h = (Scalar.safeHeight h && Scalar.safeHeight (h-1)) := by
  simp only [Scalar.stackBound,Scalar.heightTrace,Scalar.stackDelta,Scalar.numericDelta,
    Scalar.unary,Scalar.binary,Option.isSome_none,Option.isSome_some,Bool.false_eq_true,
    if_false,if_true,List.all_cons,List.all_nil,Bool.and_true,Int.sub_eq_add_neg]
end SolidityBridge.Yul.ExpSelection
