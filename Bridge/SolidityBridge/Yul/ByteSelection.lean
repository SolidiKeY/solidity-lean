import SolidityBridge.Yul.ExpSelection
/-! Exact compact literal certificates and the existing software BYTE compiler
expansion. No native BYTE instruction, source AST, word semantics, width-erased
byte identity or source admission is added. -/
namespace SolidityBridge.Yul.ByteSelection
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation MachineAdapter

/-- No truncation: PUSH1 is used only for a proved one-byte numerical value. -/
theorem compact_run :
∀ (n : Solidity.Yul.Word), n.val < 256 → ∀ input : Solidity.Backend.Scalar.Stack,
 Solidity.Backend.Scalar.run [Solidity.Backend.Scalar.pushByte (UInt8.ofNat n.val)] input =
 Solidity.Backend.Scalar.run [Solidity.Backend.Scalar.pushWord (BitVec.ofFin n)] input := by
  intro n small input
  have equal : BitVec.ofNat 256 (UInt8.ofNat n.val).toNat = BitVec.ofFin n := by
    apply BitVec.eq_of_toNat_eq
    change (UInt8.ofNat n.val).toNat % 2^256 = n.val
    rw [UInt8.toNat_ofNat',Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt n.isLt]
  simp only [Solidity.Backend.Scalar.run,Solidity.Backend.Scalar.step_pushByte,Solidity.Backend.Scalar.step_pushWord,equal,Option.bind_some]

def push :
∀ (n : Solidity.Yul.Word), n.val < 256 → Solidity.Backend.Selection.InstructionCertificate (.push (.val n)) := by
  intro n small
  refine ⟨[Solidity.Backend.Scalar.pushByte (UInt8.ofNat n.val)],?_,?_⟩
  · intro input output m represented
    rw [SolidityBridge.Yul.ByteSelection.compact_run n small input]
    exact SolidityBridge.Yul.LiteralSelection.push_success (BitVec.ofFin n) input output m represented
  · intro input m represented
    rw [SolidityBridge.Yul.ByteSelection.compact_run n small input]
    exact SolidityBridge.Yul.LiteralSelection.push_refusal (BitVec.ofFin n) input m represented

/-- Compact certificate table only; the earlier PUSH32 table is unchanged. -/
def select : (i : Evm.Instr) → Option (InstructionCertificate i)
  | .push (.val n) =>
      if small : n.val < 256 then some (push n small)
      else ExpSelection.select (.push (.val n))
  | i => ExpSelection.select i

/-- Retain the previous exact selection first. The compact alternative also
checks exact re-emission; mixed encodings are not silently normalized. -/
def compileLeaf (p : Backend.Program) : Option (ControlRealization.Slice p) :=
  (ExpSelection.compileLeaf p).orElse (fun _ =>
    ControlRealization.selectSliceUsing SignedMachine.selectCode select p)
def compileBlock : (b : Backend.Block) → Option (ControlRealization.Realization b) :=
  ControlRealization.selectBlockWith compileLeaf

def body : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 :=
  .seq (SignedSelection.assignment 0 .byte 0 1)
    (.seq (SignedSelection.assignment 1 .byte 0 1) (UnarySelection.assignment 2 .iszero 1))
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 :=
  .if_ (SignedSelection.expression .byte 0 1) body

def compiled := (NormalControl.compile 6 statement).get (by rfl)
def block := (compiled.emit 0).get (by rfl)
def selected := (compileBlock block).get (by rfl)
def lowering := ControlCompleteness.selected_lowering_with compileLeaf selected (by rfl)
abbrev source_model := ControlRealization.source_model compiled 0 block (by rfl) selected

def prefixedBlock := (compiled.emit 2).get (by rfl)
def prefixed := (compileBlock prefixedBlock).get (by rfl)
def prefixed_lowering := ControlCompleteness.selected_lowering_with compileLeaf prefixed (by rfl)
abbrev prefixed_source_model := ControlRealization.source_model compiled 2 prefixedBlock (by rfl) prefixed

/-- Actual PUSH1 needs one spare height; Scalar/model success is uncapped. -/
theorem compact_capacity (b : UInt8) (h : Int) :
    Scalar.stackBound [Scalar.pushByte b] h = (Scalar.safeHeight h && Scalar.safeHeight (h+1)) := by
  simp only [Scalar.stackBound,Scalar.heightTrace,Scalar.pushByte,Scalar.stackDelta,
    List.all_cons,List.all_nil,Bool.and_true]
end SolidityBridge.Yul.ByteSelection
