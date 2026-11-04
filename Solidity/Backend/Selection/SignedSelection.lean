import Solidity.Backend.Selection.UnsignedSelection
import Solidity.Backend.Scalar.SignedMul

/-! Signed numeric selection reuses the published signed-reading and encoding
lemmas. Raw IR/EVM behavior is distinct from checked source guard behavior. -/
namespace Solidity.Backend.Selection

/-- Reuse the existing bounded integer-to-word bridge. -/
theorem ir_signed_result (value : Int)
    (range : -(Evm.W : Int) ≤ value ∧ value < Evm.W) :
    Evm.sword value = Evm.wmod (BitVec.ofInt 256 value).toNat := by
  unfold Evm.sword
  rw [Scalar.toWord_ofInt value range]

/-- Numeric IR SLT selects one Osaka SLT, including operand-underflow refusal. -/
def sltCertificate : InstructionCertificate .slt :=
  certificateOfStep .slt [.op .SLT] (by
    intro input m stack
    cases input with
    | nil => simp only [Evm.Instr.step, stack, irStack, List.map_nil,
        Scalar.run, Scalar.step, Scalar.numericStep, Scalar.unary,
        Scalar.binary, Scalar.applyBinary, Option.bind_none]
    | cons a rest =>
      cases rest with
      | nil => simp only [Evm.Instr.step, stack, irStack, List.map_cons,
          List.map_nil, Scalar.run, Scalar.step, Scalar.numericStep,
          Scalar.unary, Scalar.binary, Scalar.applyBinary, Option.bind_none]
      | cons b tail =>
        simp only [Evm.Instr.step, stack, irStack, List.map_cons,
          Evm.Machine.next, Scalar.run, Scalar.step, Scalar.numericStep,
          Scalar.unary, Scalar.binary, Scalar.applyBinary, Option.bind_some,
          ir_word_nat, Scalar.sgn_word, ir_flag_word])

/-- Numeric IR SGT selects one Osaka SGT, including operand-underflow refusal. -/
def sgtCertificate : InstructionCertificate .sgt :=
  certificateOfStep .sgt [.op .SGT] (by
    intro input m stack
    cases input with
    | nil => simp only [Evm.Instr.step, stack, irStack, List.map_nil,
        Scalar.run, Scalar.step, Scalar.numericStep, Scalar.unary,
        Scalar.binary, Scalar.applyBinary, Option.bind_none]
    | cons a rest =>
      cases rest with
      | nil => simp only [Evm.Instr.step, stack, irStack, List.map_cons,
          List.map_nil, Scalar.run, Scalar.step, Scalar.numericStep,
          Scalar.unary, Scalar.binary, Scalar.applyBinary, Option.bind_none]
      | cons b tail =>
        simp only [Evm.Instr.step, stack, irStack, List.map_cons,
          Evm.Machine.next, Scalar.run, Scalar.step, Scalar.numericStep,
          Scalar.unary, Scalar.binary, Scalar.applyBinary, Option.bind_some,
          ir_word_nat, Scalar.sgn_word, ir_flag_word])

theorem ir_sdiv_word (a b : Scalar.Word) :
    (if (Evm.wmod b.toNat).val = 0 then (⟨0, Evm.W_pos⟩ : Fin Evm.W)
      else Evm.sword ((Evm.sgn (Evm.wmod a.toNat).val).tdiv
        (Evm.sgn (Evm.wmod b.toNat).val))) =
      Evm.wmod (if b == 0 then (0 : Scalar.Word) else
        BitVec.ofInt 256 (a.toInt.tdiv b.toInt)).toNat := by
  simp only [ir_word_nat, Scalar.sgn_word, word_beq_nat]
  have zero_word : (0 : Scalar.Word).toNat = 0 := rfl
  rw [zero_word]
  simp only [decide_eq_true_eq]
  by_cases zero : b.toNat = 0
  · simp only [if_pos zero]
    rfl
  · simp only [if_neg zero]
    have range : -(Evm.W : Int) ≤ a.toInt.tdiv b.toInt ∧
        a.toInt.tdiv b.toInt < Evm.W := by
      simpa only [Scalar.sgn_word] using Evm.tdiv_sgn_range a.isLt b.toInt
    exact ir_signed_result _ range

/-- Numeric IR SDIV selects one Osaka SDIV, including operand-underflow refusal. -/
def sdivCertificate : InstructionCertificate .sdiv :=
  certificateOfStep .sdiv [.op .SDIV] (by
    intro input m stack
    cases input with
    | nil => simp only [Evm.Instr.step, stack, irStack, List.map_nil,
        Scalar.run, Scalar.step, Scalar.numericStep, Scalar.unary,
        Scalar.binary, Scalar.applyBinary, Option.bind_none]
    | cons a rest =>
      cases rest with
      | nil => simp only [Evm.Instr.step, stack, irStack, List.map_cons,
          List.map_nil, Scalar.run, Scalar.step, Scalar.numericStep,
          Scalar.unary, Scalar.binary, Scalar.applyBinary, Option.bind_none]
      | cons b tail =>
        simp only [Evm.Instr.step, stack, irStack, List.map_cons,
          Evm.Machine.next, Scalar.run, Scalar.step, Scalar.numericStep,
          Scalar.unary, Scalar.binary, Scalar.applyBinary, Option.bind_some,
          ir_sdiv_word])

theorem ir_smod_word (a b : Scalar.Word) :
    (if (Evm.wmod b.toNat).val = 0 then (⟨0, Evm.W_pos⟩ : Fin Evm.W)
      else Evm.sword ((Evm.sgn (Evm.wmod a.toNat).val).tmod
        (Evm.sgn (Evm.wmod b.toNat).val))) =
      Evm.wmod (if b == 0 then (0 : Scalar.Word) else
        BitVec.ofInt 256 (a.toInt.tmod b.toInt)).toNat := by
  simp only [ir_word_nat, Scalar.sgn_word, word_beq_nat]
  have zero_word : (0 : Scalar.Word).toNat = 0 := rfl
  rw [zero_word]
  simp only [decide_eq_true_eq]
  by_cases zero : b.toNat = 0
  · simp only [if_pos zero]
    rfl
  · simp only [if_neg zero]
    have nonzero : b.toInt ≠ 0 := by
      intro same
      have word_zero : b = 0 := BitVec.eq_of_toInt_eq same
      exact zero (congrArg BitVec.toNat word_zero)
    have divisor_range : -(Evm.H : Int) ≤ b.toInt ∧ b.toInt < Evm.H := by
      simpa only [Scalar.sgn_word] using Evm.sgn_range b.isLt
    have narrow : -(Evm.H : Int) ≤ a.toInt.tmod b.toInt ∧
        a.toInt.tmod b.toInt < Evm.H := Evm.tmod_range divisor_range nonzero
    have width : Evm.W = 2 * Evm.H := Evm.W_eq
    have positive : 0 < Evm.H := Evm.H_pos
    have range : -(Evm.W : Int) ≤ a.toInt.tmod b.toInt ∧
        a.toInt.tmod b.toInt < Evm.W := by constructor <;> omega
    exact ir_signed_result _ range

/-- Numeric IR SMOD selects one Osaka SMOD, including operand-underflow refusal. -/
def smodCertificate : InstructionCertificate .smod :=
  certificateOfStep .smod [.op .SMOD] (by
    intro input m stack
    cases input with
    | nil => simp only [Evm.Instr.step, stack, irStack, List.map_nil,
        Scalar.run, Scalar.step, Scalar.numericStep, Scalar.unary,
        Scalar.binary, Scalar.applyBinary, Option.bind_none]
    | cons a rest =>
      cases rest with
      | nil => simp only [Evm.Instr.step, stack, irStack, List.map_cons,
          List.map_nil, Scalar.run, Scalar.step, Scalar.numericStep,
          Scalar.unary, Scalar.binary, Scalar.applyBinary, Option.bind_none]
      | cons b tail =>
        simp only [Evm.Instr.step, stack, irStack, List.map_cons,
          Evm.Machine.next, Scalar.run, Scalar.step, Scalar.numericStep,
          Scalar.unary, Scalar.binary, Scalar.applyBinary, Option.bind_some,
          ir_smod_word])

/-- Component selection only, without a whole-compiler refusal verdict. -/
def selectSigned : (instruction : Evm.Instr) → Option (InstructionCertificate instruction)
  | .slt => some sltCertificate
  | .sgt => some sgtCertificate
  | .sdiv => some sdivCertificate
  | .smod => some smodCertificate
  | _ => none

namespace SignedControls

def negativeOne : Scalar.Word := BitVec.ofInt 256 (-1)
def negativeTwo : Scalar.Word := BitVec.ofInt 256 (-2)
def negativeThree : Scalar.Word := BitVec.ofInt 256 (-3)
def negativeSeven : Scalar.Word := BitVec.ofInt 256 (-7)
def minimum : Scalar.Word := BitVec.ofNat 256 (2 ^ 255)

theorem slt_run (tail : Scalar.Stack) :
    Scalar.run sltCertificate.code (negativeOne :: 0 :: tail) = some (1 :: tail) := by
  have actual : Scalar.run sltCertificate.code [negativeOne, 0] = some [1] := by decide
  exact Scalar.run_frame actual tail

theorem slt_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.slt.step { m with stack := irStack (negativeOne :: 0 :: tail) } =
      .ok { m with stack := irStack (1 :: tail) } 0 := by
  exact (sltCertificate.success _ _ _ rfl).mpr (slt_run tail)

theorem slt_underflow : Scalar.run sltCertificate.code [] = none ∧
    Scalar.run sltCertificate.code [7] = none := by exact ⟨rfl, rfl⟩

theorem slt_wrong_result :
    Scalar.run sltCertificate.code [negativeOne, 0, 23] ≠ some [0, 23] := by decide

theorem sgt_run (tail : Scalar.Stack) :
    Scalar.run sgtCertificate.code (0 :: negativeOne :: tail) = some (1 :: tail) := by
  have actual : Scalar.run sgtCertificate.code [0, negativeOne] = some [1] := by decide
  exact Scalar.run_frame actual tail

theorem sgt_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.sgt.step { m with stack := irStack (0 :: negativeOne :: tail) } =
      .ok { m with stack := irStack (1 :: tail) } 0 := by
  exact (sgtCertificate.success _ _ _ rfl).mpr (sgt_run tail)

theorem sgt_underflow : Scalar.run sgtCertificate.code [] = none ∧
    Scalar.run sgtCertificate.code [7] = none := by exact ⟨rfl, rfl⟩

theorem sgt_wrong_result :
    Scalar.run sgtCertificate.code [0, negativeOne, 23] ≠ some [0, 23] := by decide

theorem sdiv_run (tail : Scalar.Stack) :
    Scalar.run sdivCertificate.code (negativeSeven :: 3 :: tail) = some (negativeTwo :: tail) := by
  have actual : Scalar.run sdivCertificate.code [negativeSeven, 3] = some [negativeTwo] := by decide
  exact Scalar.run_frame actual tail

theorem sdiv_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.sdiv.step { m with stack := irStack (negativeSeven :: 3 :: tail) } =
      .ok { m with stack := irStack (negativeTwo :: tail) } 0 := by
  exact (sdivCertificate.success _ _ _ rfl).mpr (sdiv_run tail)

theorem sdiv_underflow : Scalar.run sdivCertificate.code [] = none ∧
    Scalar.run sdivCertificate.code [7] = none := by exact ⟨rfl, rfl⟩

theorem sdiv_wrong_result :
    Scalar.run sdivCertificate.code [negativeSeven, 3, 23] ≠ some [0, 23] := by decide

theorem smod_run (tail : Scalar.Stack) :
    Scalar.run smodCertificate.code (negativeSeven :: 3 :: tail) = some (negativeOne :: tail) := by
  have actual : Scalar.run smodCertificate.code [negativeSeven, 3] = some [negativeOne] := by decide
  exact Scalar.run_frame actual tail

theorem smod_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.smod.step { m with stack := irStack (negativeSeven :: 3 :: tail) } =
      .ok { m with stack := irStack (negativeOne :: tail) } 0 := by
  exact (smodCertificate.success _ _ _ rfl).mpr (smod_run tail)

theorem smod_underflow : Scalar.run smodCertificate.code [] = none ∧
    Scalar.run smodCertificate.code [7] = none := by exact ⟨rfl, rfl⟩

theorem smod_wrong_result :
    Scalar.run smodCertificate.code [negativeSeven, 3, 23] ≠ some [3, 23] := by decide

/-- Signed comparisons distinguish full-width negative encodings. -/
theorem comparison_boundaries :
    Scalar.run sltCertificate.code [0, negativeOne] = some [0] ∧
    Scalar.run sgtCertificate.code [negativeOne, 0] = some [0] ∧
    Scalar.run sltCertificate.code [minimum, negativeOne] = some [1] ∧
    Scalar.run sgtCertificate.code [minimum, minimum] = some [0] := by decide

/-- Raw EVM division truncates toward zero, and remainder follows dividend sign. -/
theorem division_signs :
    Scalar.run sdivCertificate.code [negativeSeven, negativeThree] = some [2] ∧
    Scalar.run sdivCertificate.code [7, negativeThree] = some [negativeTwo] ∧
    Scalar.run smodCertificate.code [negativeSeven, negativeThree] = some [negativeOne] ∧
    Scalar.run smodCertificate.code [7, negativeThree] = some [1] ∧
    Scalar.run sdivCertificate.code [negativeSeven, 3] ≠ some [negativeThree] ∧
    Scalar.run smodCertificate.code [negativeSeven, 3] ≠ some [2] := by decide

/-- No minimum divided by -1 exclusion: raw SDIV wraps and SMOD returns zero. -/
theorem exceptional_words :
    Scalar.run sdivCertificate.code [minimum, negativeOne] = some [minimum] ∧
    Scalar.run smodCertificate.code [minimum, negativeOne] = some [0] ∧
    Scalar.run sdivCertificate.code [minimum, 1] = some [minimum] ∧
    Scalar.run sdivCertificate.code [minimum, minimum] = some [1] ∧
    Scalar.run sdivCertificate.code [negativeSeven, 0] = some [0] ∧
    Scalar.run smodCertificate.code [negativeSeven, 0] = some [0] ∧
    Scalar.run sdivCertificate.code [0, 0] = some [0] ∧
    Scalar.run smodCertificate.code [0, 0] = some [0] := by decide

theorem overflow_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.sdiv.step { m with stack := irStack (minimum :: negativeOne :: tail) } =
      .ok { m with stack := irStack (minimum :: tail) } 0 := by
  have actual : Scalar.run sdivCertificate.code [minimum, negativeOne] = some [minimum] := by decide
  exact (sdivCertificate.success _ _ _ rfl).mpr (Scalar.run_frame actual tail)

theorem zero_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.smod.step { m with stack := irStack (negativeSeven :: 0 :: tail) } =
      .ok { m with stack := irStack (0 :: tail) } 0 := by
  have actual : Scalar.run smodCertificate.code [negativeSeven, 0] = some [0] := by decide
  exact (smodCertificate.success _ _ _ rfl).mpr (Scalar.run_frame actual tail)

theorem corrupt_tail :
    Scalar.run sdivCertificate.code [negativeSeven, 3, 23] ≠ some [negativeTwo, 24] := by decide

theorem emitted_opcodes : encode sltCertificate.code = [0x12] ∧
    encode sgtCertificate.code = [0x13] ∧ encode sdivCertificate.code = [0x05] ∧
    encode smodCertificate.code = [0x07] := by decide

theorem outside_component : selectSigned .div = none ∧
    selectUnsigned .div = some divCertificate := by exact ⟨rfl, rfl⟩

end SignedControls

#print axioms SignedControls.slt_run
#print axioms SignedControls.slt_complete_frame
#print axioms SignedControls.slt_underflow
#print axioms SignedControls.slt_wrong_result
#print axioms SignedControls.sgt_run
#print axioms SignedControls.sgt_complete_frame
#print axioms SignedControls.sgt_underflow
#print axioms SignedControls.sgt_wrong_result
#print axioms SignedControls.sdiv_run
#print axioms SignedControls.sdiv_complete_frame
#print axioms SignedControls.sdiv_underflow
#print axioms SignedControls.sdiv_wrong_result
#print axioms SignedControls.smod_run
#print axioms SignedControls.smod_complete_frame
#print axioms SignedControls.smod_underflow
#print axioms SignedControls.smod_wrong_result
#print axioms SignedControls.comparison_boundaries
#print axioms SignedControls.division_signs
#print axioms SignedControls.exceptional_words
#print axioms SignedControls.overflow_complete_frame
#print axioms SignedControls.zero_complete_frame
#print axioms SignedControls.corrupt_tail
#print axioms SignedControls.emitted_opcodes
#print axioms SignedControls.outside_component
#print axioms ir_signed_result
#print axioms ir_sdiv_word
#print axioms ir_smod_word
#print axioms sltCertificate
#print axioms sgtCertificate
#print axioms sdivCertificate
#print axioms smodCertificate

end Solidity.Backend.Selection
