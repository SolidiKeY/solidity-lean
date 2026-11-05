import Solidity.Backend.Selection.ArithmeticSelection

/-! Numeric bitwise and unsigned comparison components over the existing IR.
Physical capacity and checked source arithmetic remain separate obligations. -/
namespace Solidity.Backend.Selection

/-- IR flags and physical flags have identical numeric representations. -/
theorem ir_flag_word (bit : Bool) :
    Evm.bword bit = Evm.wmod (Scalar.flag bit).toNat := by
  cases bit <;> rfl

/-- Word equality compares precisely the unsigned values used by the IR. -/
theorem word_beq_nat (a b : Scalar.Word) :
    (a == b) = decide (a.toNat = b.toNat) := by
  exact Bool.eq_iff_iff.mpr (by
    simp only [beq_iff_eq, decide_eq_true_eq, BitVec.toNat_inj])

theorem ir_and_word (a b : Scalar.Word) :
    (⟨(Evm.wmod a.toNat).val &&& (Evm.wmod b.toNat).val,
      Nat.and_lt_two_pow _ (Evm.wmod b.toNat).isLt⟩ : Fin Evm.W) =
      Evm.wmod (a &&& b).toNat := by
  apply Fin.ext
  rw [ir_word_nat (a &&& b)]
  simp only [ir_word_nat, BitVec.toNat_and]

/-- Numeric IR AND selects one Osaka AND, including operand-underflow refusal. -/
def andCertificate : InstructionCertificate .and :=
  certificateOfStep .and [.op .AND] (by
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
          ir_and_word])

theorem ir_or_word (a b : Scalar.Word) :
    (⟨(Evm.wmod a.toNat).val ||| (Evm.wmod b.toNat).val,
      Nat.or_lt_two_pow (Evm.wmod a.toNat).isLt (Evm.wmod b.toNat).isLt⟩ : Fin Evm.W) =
      Evm.wmod (a ||| b).toNat := by
  apply Fin.ext
  rw [ir_word_nat (a ||| b)]
  simp only [ir_word_nat, BitVec.toNat_or]

/-- Numeric IR OR selects one Osaka OR, including operand-underflow refusal. -/
def orCertificate : InstructionCertificate .or :=
  certificateOfStep .or [.op .OR] (by
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
          ir_or_word])

theorem ir_xor_word (a b : Scalar.Word) :
    (⟨(Evm.wmod a.toNat).val ^^^ (Evm.wmod b.toNat).val,
      Nat.xor_lt_two_pow (Evm.wmod a.toNat).isLt (Evm.wmod b.toNat).isLt⟩ : Fin Evm.W) =
      Evm.wmod (a ^^^ b).toNat := by
  apply Fin.ext
  rw [ir_word_nat (a ^^^ b)]
  simp only [ir_word_nat, BitVec.toNat_xor]

/-- Numeric IR XOR selects one Osaka XOR, including operand-underflow refusal. -/
def xorCertificate : InstructionCertificate .xor :=
  certificateOfStep .xor [.op .XOR] (by
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
          ir_xor_word])

/-- Numeric IR LT selects one Osaka LT, including operand-underflow refusal. -/
def ltCertificate : InstructionCertificate .lt :=
  certificateOfStep .lt [.op .LT] (by
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
          ir_word_nat, ir_flag_word])

/-- Numeric IR GT selects one Osaka GT, including operand-underflow refusal. -/
def gtCertificate : InstructionCertificate .gt :=
  certificateOfStep .gt [.op .GT] (by
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
          ir_word_nat, ir_flag_word])

/-- Numeric IR EQ selects one Osaka EQ, including operand-underflow refusal. -/
def eqCertificate : InstructionCertificate .eq :=
  certificateOfStep .eq [.op .EQ] (by
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
          ir_word_nat, ir_flag_word, word_beq_nat])

theorem ir_not_word (a : Scalar.Word) :
    (⟨Evm.W - 1 - (Evm.wmod a.toNat).val,
      by omega⟩ : Fin Evm.W) =
      Evm.wmod (~~~a).toNat := by
  apply Fin.ext
  rw [ir_word_nat (~~~a)]
  simp only [ir_word_nat, BitVec.toNat_not, Evm.W]

/-- Actual numeric IR NOT selection, including operand shortage. -/
def notCertificate : InstructionCertificate .not :=
  certificateOfStep .not [.op .NOT] (by
    intro input m stack
    cases input with
    | nil => simp only [Evm.Instr.step, stack, irStack, List.map_nil,
        Scalar.run, Scalar.step, Scalar.numericStep, Scalar.unary,
        Scalar.applyUnary, Option.bind_none]
    | cons a tail =>
      simp only [Evm.Instr.step, stack, irStack, List.map_cons,
        Evm.Machine.next, Scalar.run, Scalar.step, Scalar.numericStep,
        Scalar.unary, Scalar.applyUnary, Option.bind_some, ir_not_word])

/-- Actual numeric IR ISZERO selection, including operand shortage. -/
def iszeroCertificate : InstructionCertificate .iszero :=
  certificateOfStep .iszero [.op .ISZERO] (by
    intro input m stack
    cases input with
    | nil => simp only [Evm.Instr.step, stack, irStack, List.map_nil,
        Scalar.run, Scalar.step, Scalar.numericStep, Scalar.unary,
        Scalar.applyUnary, Option.bind_none]
    | cons a tail =>
      simp only [Evm.Instr.step, stack, irStack, List.map_cons,
        Evm.Machine.next, Scalar.run, Scalar.step, Scalar.numericStep,
        Scalar.unary, Scalar.applyUnary, Option.bind_some, ir_word_nat, ir_flag_word, word_beq_nat]
      rfl)

/-- Component selection only, with no whole-compiler refusal verdict. -/
def selectBitwiseComparison :
    (instruction : Evm.Instr) → Option (InstructionCertificate instruction)
  | .and => some andCertificate
  | .or => some orCertificate
  | .xor => some xorCertificate
  | .not => some notCertificate
  | .lt => some ltCertificate
  | .gt => some gtCertificate
  | .eq => some eqCertificate
  | .iszero => some iszeroCertificate
  | _ => none

namespace BitwiseControls

theorem and_run (tail : Scalar.Stack) :
    Scalar.run andCertificate.code (0xf0 :: 0x3c :: tail) = some (0x30 :: tail) := by
  have actual : Scalar.run andCertificate.code [0xf0, 0x3c] = some [0x30] := by decide
  exact Scalar.run_frame actual tail

theorem and_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.and.step { m with stack := irStack (0xf0 :: 0x3c :: tail) } =
      .ok { m with stack := irStack (0x30 :: tail) } 0 := by
  exact (andCertificate.success _ _ _ rfl).mpr (and_run tail)

theorem and_underflow : Scalar.run andCertificate.code [] = none ∧
    Scalar.run andCertificate.code [7] = none := by exact ⟨rfl, rfl⟩

theorem and_wrong_result :
    Scalar.run andCertificate.code [0xf0, 0x3c, 23] ≠ some [0xfc, 23] := by decide

theorem or_run (tail : Scalar.Stack) :
    Scalar.run orCertificate.code (0xf0 :: 0x3c :: tail) = some (0xfc :: tail) := by
  have actual : Scalar.run orCertificate.code [0xf0, 0x3c] = some [0xfc] := by decide
  exact Scalar.run_frame actual tail

theorem or_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.or.step { m with stack := irStack (0xf0 :: 0x3c :: tail) } =
      .ok { m with stack := irStack (0xfc :: tail) } 0 := by
  exact (orCertificate.success _ _ _ rfl).mpr (or_run tail)

theorem or_underflow : Scalar.run orCertificate.code [] = none ∧
    Scalar.run orCertificate.code [7] = none := by exact ⟨rfl, rfl⟩

theorem or_wrong_result :
    Scalar.run orCertificate.code [0xf0, 0x3c, 23] ≠ some [0x30, 23] := by decide

theorem xor_run (tail : Scalar.Stack) :
    Scalar.run xorCertificate.code (0xf0 :: 0x3c :: tail) = some (0xcc :: tail) := by
  have actual : Scalar.run xorCertificate.code [0xf0, 0x3c] = some [0xcc] := by decide
  exact Scalar.run_frame actual tail

theorem xor_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.xor.step { m with stack := irStack (0xf0 :: 0x3c :: tail) } =
      .ok { m with stack := irStack (0xcc :: tail) } 0 := by
  exact (xorCertificate.success _ _ _ rfl).mpr (xor_run tail)

theorem xor_underflow : Scalar.run xorCertificate.code [] = none ∧
    Scalar.run xorCertificate.code [7] = none := by exact ⟨rfl, rfl⟩

theorem xor_wrong_result :
    Scalar.run xorCertificate.code [0xf0, 0x3c, 23] ≠ some [0xfc, 23] := by decide

theorem not_run (tail : Scalar.Stack) :
    Scalar.run notCertificate.code (0 :: tail) = some (ArithmeticControls.maximum :: tail) := by
  have actual : Scalar.run notCertificate.code [0] = some [ArithmeticControls.maximum] := by decide
  exact Scalar.run_frame actual tail

theorem not_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.not.step { m with stack := irStack (0 :: tail) } =
      .ok { m with stack := irStack (ArithmeticControls.maximum :: tail) } 0 := by
  exact (notCertificate.success _ _ _ rfl).mpr (not_run tail)

theorem not_underflow : Scalar.run notCertificate.code [] = none := rfl

theorem not_wrong_result :
    Scalar.run notCertificate.code [0, 23] ≠ some [255, 23] := by decide

theorem lt_run (tail : Scalar.Stack) :
    Scalar.run ltCertificate.code (ArithmeticControls.maximum :: 0 :: tail) = some (0 :: tail) := by
  have actual : Scalar.run ltCertificate.code [ArithmeticControls.maximum, 0] = some [0] := by decide
  exact Scalar.run_frame actual tail

theorem lt_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.lt.step { m with stack := irStack (ArithmeticControls.maximum :: 0 :: tail) } =
      .ok { m with stack := irStack (0 :: tail) } 0 := by
  exact (ltCertificate.success _ _ _ rfl).mpr (lt_run tail)

theorem lt_underflow : Scalar.run ltCertificate.code [] = none ∧
    Scalar.run ltCertificate.code [7] = none := by exact ⟨rfl, rfl⟩

theorem lt_wrong_result :
    Scalar.run ltCertificate.code [ArithmeticControls.maximum, 0, 23] ≠ some [1, 23] := by decide

theorem gt_run (tail : Scalar.Stack) :
    Scalar.run gtCertificate.code (ArithmeticControls.maximum :: 0 :: tail) = some (1 :: tail) := by
  have actual : Scalar.run gtCertificate.code [ArithmeticControls.maximum, 0] = some [1] := by decide
  exact Scalar.run_frame actual tail

theorem gt_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.gt.step { m with stack := irStack (ArithmeticControls.maximum :: 0 :: tail) } =
      .ok { m with stack := irStack (1 :: tail) } 0 := by
  exact (gtCertificate.success _ _ _ rfl).mpr (gt_run tail)

theorem gt_underflow : Scalar.run gtCertificate.code [] = none ∧
    Scalar.run gtCertificate.code [7] = none := by exact ⟨rfl, rfl⟩

theorem gt_wrong_result :
    Scalar.run gtCertificate.code [ArithmeticControls.maximum, 0, 23] ≠ some [0, 23] := by decide

theorem eq_run (tail : Scalar.Stack) :
    Scalar.run eqCertificate.code (7 :: 7 :: tail) = some (1 :: tail) := by
  have actual : Scalar.run eqCertificate.code [7, 7] = some [1] := by decide
  exact Scalar.run_frame actual tail

theorem eq_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.eq.step { m with stack := irStack (7 :: 7 :: tail) } =
      .ok { m with stack := irStack (1 :: tail) } 0 := by
  exact (eqCertificate.success _ _ _ rfl).mpr (eq_run tail)

theorem eq_underflow : Scalar.run eqCertificate.code [] = none ∧
    Scalar.run eqCertificate.code [7] = none := by exact ⟨rfl, rfl⟩

theorem eq_wrong_result :
    Scalar.run eqCertificate.code [7, 7, 23] ≠ some [0, 23] := by decide

theorem iszero_run (tail : Scalar.Stack) :
    Scalar.run iszeroCertificate.code (0 :: tail) = some (1 :: tail) := by
  have actual : Scalar.run iszeroCertificate.code [0] = some [1] := by decide
  exact Scalar.run_frame actual tail

theorem iszero_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.iszero.step { m with stack := irStack (0 :: tail) } =
      .ok { m with stack := irStack (1 :: tail) } 0 := by
  exact (iszeroCertificate.success _ _ _ rfl).mpr (iszero_run tail)

theorem iszero_underflow : Scalar.run iszeroCertificate.code [] = none := rfl

theorem iszero_wrong_result :
    Scalar.run iszeroCertificate.code [0, 23] ≠ some [0, 23] := by decide

/-- Both flag branches and the full-width complement boundary are executed. -/
theorem alternate_cases :
    Scalar.run ltCertificate.code [3, 5] = some [1] ∧
    Scalar.run gtCertificate.code [3, 5] = some [0] ∧
    Scalar.run eqCertificate.code [7, 8] = some [0] ∧
    Scalar.run iszeroCertificate.code [ArithmeticControls.maximum] = some [0] ∧
    Scalar.run notCertificate.code [ArithmeticControls.maximum] = some [0] := by decide

theorem binary_corrupt_tail :
    Scalar.run andCertificate.code [0xf0, 0x3c, 23] ≠ some [0x30, 24] := by decide
theorem unary_corrupt_tail :
    Scalar.run iszeroCertificate.code [0, 23] ≠ some [1, 24] := by decide

theorem emitted_opcodes : encode andCertificate.code = [0x16] ∧
    encode orCertificate.code = [0x17] ∧ encode xorCertificate.code = [0x18] ∧
    encode notCertificate.code = [0x19] ∧ encode ltCertificate.code = [0x10] ∧
    encode gtCertificate.code = [0x11] ∧ encode eqCertificate.code = [0x14] ∧
    encode iszeroCertificate.code = [0x15] := by decide

/-- An absent component case can still be supported by another component. -/
theorem outside_component : selectBitwiseComparison .add = none ∧
    selectArithmetic .add = some addCertificate := by exact ⟨rfl, rfl⟩

end BitwiseControls

#print axioms BitwiseControls.and_run
#print axioms BitwiseControls.and_complete_frame
#print axioms BitwiseControls.and_underflow
#print axioms BitwiseControls.and_wrong_result
#print axioms BitwiseControls.or_run
#print axioms BitwiseControls.or_complete_frame
#print axioms BitwiseControls.or_underflow
#print axioms BitwiseControls.or_wrong_result
#print axioms BitwiseControls.xor_run
#print axioms BitwiseControls.xor_complete_frame
#print axioms BitwiseControls.xor_underflow
#print axioms BitwiseControls.xor_wrong_result
#print axioms BitwiseControls.not_run
#print axioms BitwiseControls.not_complete_frame
#print axioms BitwiseControls.not_underflow
#print axioms BitwiseControls.not_wrong_result
#print axioms BitwiseControls.lt_run
#print axioms BitwiseControls.lt_complete_frame
#print axioms BitwiseControls.lt_underflow
#print axioms BitwiseControls.lt_wrong_result
#print axioms BitwiseControls.gt_run
#print axioms BitwiseControls.gt_complete_frame
#print axioms BitwiseControls.gt_underflow
#print axioms BitwiseControls.gt_wrong_result
#print axioms BitwiseControls.eq_run
#print axioms BitwiseControls.eq_complete_frame
#print axioms BitwiseControls.eq_underflow
#print axioms BitwiseControls.eq_wrong_result
#print axioms BitwiseControls.iszero_run
#print axioms BitwiseControls.iszero_complete_frame
#print axioms BitwiseControls.iszero_underflow
#print axioms BitwiseControls.iszero_wrong_result
#print axioms BitwiseControls.alternate_cases
#print axioms BitwiseControls.binary_corrupt_tail
#print axioms BitwiseControls.unary_corrupt_tail
#print axioms BitwiseControls.emitted_opcodes
#print axioms BitwiseControls.outside_component
#print axioms ir_flag_word
#print axioms word_beq_nat
#print axioms ir_and_word
#print axioms ir_or_word
#print axioms ir_xor_word
#print axioms ir_not_word
#print axioms andCertificate
#print axioms orCertificate
#print axioms xorCertificate
#print axioms notCertificate
#print axioms ltCertificate
#print axioms gtCertificate
#print axioms eqCertificate
#print axioms iszeroCertificate

end Solidity.Backend.Selection
