import Solidity.Backend.Selection.P20Consumer
import Solidity.Yul.Compilation.P20InterfaceV1Controls

/-! Nonempty controls for the published CLOSED producer's numeric fragment.
This is deliberately not an instance of PendingG24 or represented Source
success. The conditional adapter above remains ready for that future producer. -/
namespace Solidity.Backend.Selection.P20ConsumerControls
open LabelExec
open Solidity.Yul.Closed
open Solidity.Yul.Compilation.ProducerExpressions

abbrev dirty : Scalar.Word := Solidity.Yul.Compilation.P20.InterfaceV1.Controls.dirty
abbrev published : Solidity.Yul.Compilation.P20.InterfaceV1.ClosedProducer 2
    Solidity.Yul.Compilation.P20.InterfaceV1.Controls.statement :=
  Solidity.Yul.Compilation.P20.InterfaceV1.Controls.producer

def code : Code 3 3 where
  instructions := [Scalar.pushWord dirty, .op (.SWAP 1), .op .POP]
  shape := .cons (.mk 0 1 3 rfl rfl rfl)
    (.cons (.mk 3 3 1 rfl rfl rfl) (.cons (.mk 1 0 3 rfl rfl rfl) (.nil 3)))
  capacity := by decide

def ir : List Evm.Instr := [.push (.val (Evm.wmod dirty.toNat)), .swap 2, .pop]

theorem producer_code : published.lowered.code 0 = some code.instructions := rfl

theorem selected : compileScalar ir = some code.instructions := rfl

/-- Reuse the original statement evaluator theorem, not a copied producer. -/
theorem yul_source :
    evalStmt 2 .nil True.intro
      Solidity.Yul.Compilation.P20.InterfaceV1.Controls.statement published.profile
      (sourceLocals #v[9,0]) = some ⟨sourceLocals #v[9,dirty],.normal⟩ :=
  published.source #v[9,0]

/-- Exact published lowering, with a retained physical suffix. -/
theorem scalar_run : Scalar.run code.instructions [9,0,23] = some [9,dirty,23] :=
  published.lowered.correct 0 code.instructions producer_code #v[9,0] #v[] [23]

def artifact : CompositionCertificate ir (.code code.instructions) 3 3 :=
  scalarComposition ir code selected

theorem artifact_code : artifact.assembled.code = code.instructions :=
  scalarComposition_code ir code selected

theorem size_thirtyfive : size artifact.assembled.code = 35 := by rw [artifact_code]; rfl

theorem ir_run (caller : Evm.Machine) (stack : caller.stack = irStack [9,0,23]) :
    Evm.run ir caller = .ok { caller with stack := irStack [9,dirty,23] } 0 := by
  rw [compileScalar_equation ir code.instructions selected [9,0,23] caller stack, scalar_run]

/-- This inhabits the closed fragment, not the missing whole G24 link. -/
theorem inhabited : ∃ count, ExecutionTrace.Safe (encode artifact.assembled.code) count
    ⟨0,[9,0,23]⟩ ⟨35,[9,dirty,23]⟩ := by
  have actual : Evm.run ir { Evm.Machine.init with stack := irStack [9,0,23] } =
      .ok { Evm.Machine.init with stack := irStack [9,dirty,23] } 0 :=
    ir_run { Evm.Machine.init with stack := irStack [9,0,23] } rfl
  obtain ⟨count,trace⟩ := artifact.execute [9,0,23] [9,dirty,23]
    { Evm.Machine.init with stack := irStack [9,0,23] } rfl rfl actual
  rw [size_thirtyfive] at trace
  exact ⟨count,trace⟩

/-- Independent fetched-byte evaluation pins all three instructions. -/
theorem actual_bytes : advance 3 (encode artifact.assembled.code) ⟨0,[9,0,23]⟩ =
    some ⟨35,[9,dirty,23]⟩ := by rw [artifact_code]; decide

theorem no_cleaning : advance 3 (encode artifact.assembled.code) ⟨0,[9,0,23]⟩ ≠
    some ⟨35,[9,257,23]⟩ := by rw [actual_bytes]; decide

theorem corrupt_tail : advance 3 (encode artifact.assembled.code) ⟨0,[9,0,23]⟩ ≠
    some ⟨35,[9,dirty,24]⟩ := by rw [actual_bytes]; decide

def wrongSlot : Program := [Scalar.pushWord dirty, .op (.SWAP 0), .op .POP]

theorem wrong_slot_run : advance 3 (encode wrongSlot) ⟨0,[9,0,23]⟩ =
    some ⟨35,[dirty,0,23]⟩ := by decide

theorem wrong_slot_discriminates : advance 3 (encode wrongSlot) ⟨0,[9,0,23]⟩ ≠
    advance 3 (encode artifact.assembled.code) ⟨0,[9,0,23]⟩ := by
  rw [wrong_slot_run, actual_bytes]
  decide

#print axioms producer_code
#print axioms selected
#print axioms yul_source
#print axioms scalar_run
#print axioms artifact
#print axioms artifact_code
#print axioms ir_run
#print axioms inhabited
#print axioms actual_bytes
#print axioms no_cleaning
#print axioms corrupt_tail
#print axioms wrong_slot_run
#print axioms wrong_slot_discriminates

end Solidity.Backend.Selection.P20ConsumerControls
