import Solidity.Backend.Selection.BitwiseSelection

/-! Actual unsigned division/remainder and logical shift selection over numeric
IR words. Checked source guards and physical capacity remain separate. -/
namespace Solidity.Backend.Selection

theorem ir_div_word (a b : Scalar.Word) :
    (⟨if (Evm.wmod b.toNat).val = 0 then 0 else
      (Evm.wmod a.toNat).val / (Evm.wmod b.toNat).val, by
        split
        · exact Evm.W_pos
        · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Evm.wmod a.toNat).isLt⟩ : Fin Evm.W) =
      Evm.wmod (if b == 0 then (0 : Scalar.Word) else
        BitVec.ofNat 256 (a.toNat / b.toNat)).toNat := by
  apply Fin.ext
  rw [ir_word_nat (if b == 0 then (0 : Scalar.Word) else
    BitVec.ofNat 256 (a.toNat / b.toNat))]
  simp only [ir_word_nat, word_beq_nat]
  have zero_word : (0 : Scalar.Word).toNat = 0 := rfl
  rw [zero_word]
  simp only [decide_eq_true_eq]
  by_cases zero : b.toNat = 0
  · simp only [if_pos zero]
    rfl
  · have room : a.toNat / b.toNat < 2 ^ 256 :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt
    simp only [if_neg zero,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt room]

/-- Numeric IR DIV selects one Osaka DIV, including operand-underflow refusal. -/
def divCertificate : InstructionCertificate .div :=
  certificateOfStep .div [.op .DIV] (by
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
          ir_div_word])

theorem ir_mod_word (a b : Scalar.Word) :
    (⟨if (Evm.wmod b.toNat).val = 0 then 0 else
      (Evm.wmod a.toNat).val % (Evm.wmod b.toNat).val, by
        split
        · exact Evm.W_pos
        · exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Evm.wmod a.toNat).isLt⟩ : Fin Evm.W) =
      Evm.wmod (if b == 0 then (0 : Scalar.Word) else
        BitVec.ofNat 256 (a.toNat % b.toNat)).toNat := by
  apply Fin.ext
  rw [ir_word_nat (if b == 0 then (0 : Scalar.Word) else
    BitVec.ofNat 256 (a.toNat % b.toNat))]
  simp only [ir_word_nat, word_beq_nat]
  have zero_word : (0 : Scalar.Word).toNat = 0 := rfl
  rw [zero_word]
  simp only [decide_eq_true_eq]
  by_cases zero : b.toNat = 0
  · simp only [if_pos zero]
    rfl
  · have room : a.toNat % b.toNat < 2 ^ 256 :=
      Nat.lt_of_le_of_lt (Nat.mod_le _ _) a.isLt
    simp only [if_neg zero,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt room]

/-- Numeric IR MOD selects one Osaka MOD, including operand-underflow refusal. -/
def modCertificate : InstructionCertificate .mod :=
  certificateOfStep .mod [.op .MOD] (by
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
          ir_mod_word])


/-- SHL keeps the full numeric count and discards shifted-out high bits. -/
theorem ir_shl_word (a b : Scalar.Word) :
    (if (Evm.wmod a.toNat).val < 256 then
      Evm.wmod ((Evm.wmod b.toNat).val * 2 ^ (Evm.wmod a.toNat).val)
      else ⟨0, Evm.W_pos⟩) =
      Evm.wmod (if a.toNat < 256 then b <<< a.toNat else (0 : Scalar.Word)).toNat := by
  apply Fin.ext
  rw [ir_word_nat (if a.toNat < 256 then b <<< a.toNat else (0 : Scalar.Word))]
  simp only [ir_word_nat]
  by_cases small : a.toNat < 256
  · simp only [if_pos small, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Evm.wmod, Evm.W]
  · simp only [if_neg small]
    rfl

/-- Numeric IR SHL selects one Osaka SHL, including operand-underflow refusal. -/
def shlCertificate : InstructionCertificate .shl :=
  certificateOfStep .shl [.op .SHL] (by
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
          ir_shl_word])

/-- SHR is logical unsigned division, with an explicit out-of-width zero. -/
theorem ir_shr_word (a b : Scalar.Word) :
    (if (Evm.wmod a.toNat).val < 256 then
      (⟨(Evm.wmod b.toNat).val / 2 ^ (Evm.wmod a.toNat).val,
        Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Evm.wmod b.toNat).isLt⟩ : Fin Evm.W)
      else ⟨0, Evm.W_pos⟩) =
      Evm.wmod (if a.toNat < 256 then b >>> a.toNat else (0 : Scalar.Word)).toNat := by
  apply Fin.ext
  rw [ir_word_nat (if a.toNat < 256 then b >>> a.toNat else (0 : Scalar.Word))]
  simp only [ir_word_nat]
  by_cases small : a.toNat < 256
  · simp only [if_pos small, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · simp only [if_neg small]
    rfl

/-- Numeric IR SHR selects one Osaka SHR, including operand-underflow refusal. -/
def shrCertificate : InstructionCertificate .shr :=
  certificateOfStep .shr [.op .SHR] (by
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
          ir_shr_word])

/-- Component selection only; absence does not classify source execution. -/
def selectUnsigned : (instruction : Evm.Instr) → Option (InstructionCertificate instruction)
  | .div => some divCertificate
  | .mod => some modCertificate
  | .shl => some shlCertificate
  | .shr => some shrCertificate
  | _ => none

namespace UnsignedControls

theorem div_run (tail : Scalar.Stack) :
    Scalar.run divCertificate.code (17 :: 5 :: tail) = some (3 :: tail) := by
  have actual : Scalar.run divCertificate.code [17, 5] = some [3] := by decide
  exact Scalar.run_frame actual tail

theorem div_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.div.step { m with stack := irStack (17 :: 5 :: tail) } =
      .ok { m with stack := irStack (3 :: tail) } 0 := by
  exact (divCertificate.success _ _ _ rfl).mpr (div_run tail)

theorem div_underflow : Scalar.run divCertificate.code [] = none ∧
    Scalar.run divCertificate.code [7] = none := by exact ⟨rfl, rfl⟩

theorem div_wrong_order :
    Scalar.run divCertificate.code [17, 5, 23] ≠ some [0, 23] := by decide

theorem mod_run (tail : Scalar.Stack) :
    Scalar.run modCertificate.code (17 :: 5 :: tail) = some (2 :: tail) := by
  have actual : Scalar.run modCertificate.code [17, 5] = some [2] := by decide
  exact Scalar.run_frame actual tail

theorem mod_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.mod.step { m with stack := irStack (17 :: 5 :: tail) } =
      .ok { m with stack := irStack (2 :: tail) } 0 := by
  exact (modCertificate.success _ _ _ rfl).mpr (mod_run tail)

theorem mod_underflow : Scalar.run modCertificate.code [] = none ∧
    Scalar.run modCertificate.code [7] = none := by exact ⟨rfl, rfl⟩

theorem mod_wrong_order :
    Scalar.run modCertificate.code [17, 5, 23] ≠ some [5, 23] := by decide

theorem shl_run (tail : Scalar.Stack) :
    Scalar.run shlCertificate.code (1 :: 3 :: tail) = some (6 :: tail) := by
  have actual : Scalar.run shlCertificate.code [1, 3] = some [6] := by decide
  exact Scalar.run_frame actual tail

theorem shl_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.shl.step { m with stack := irStack (1 :: 3 :: tail) } =
      .ok { m with stack := irStack (6 :: tail) } 0 := by
  exact (shlCertificate.success _ _ _ rfl).mpr (shl_run tail)

theorem shl_underflow : Scalar.run shlCertificate.code [] = none ∧
    Scalar.run shlCertificate.code [7] = none := by exact ⟨rfl, rfl⟩

theorem shl_wrong_order :
    Scalar.run shlCertificate.code [1, 3, 23] ≠ some [8, 23] := by decide

theorem shr_run (tail : Scalar.Stack) :
    Scalar.run shrCertificate.code (1 :: 6 :: tail) = some (3 :: tail) := by
  have actual : Scalar.run shrCertificate.code [1, 6] = some [3] := by decide
  exact Scalar.run_frame actual tail

theorem shr_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.shr.step { m with stack := irStack (1 :: 6 :: tail) } =
      .ok { m with stack := irStack (3 :: tail) } 0 := by
  exact (shrCertificate.success _ _ _ rfl).mpr (shr_run tail)

theorem shr_underflow : Scalar.run shrCertificate.code [] = none ∧
    Scalar.run shrCertificate.code [7] = none := by exact ⟨rfl, rfl⟩

theorem shr_wrong_order :
    Scalar.run shrCertificate.code [1, 6, 23] ≠ some [0, 23] := by decide

theorem div_zero_run (tail : Scalar.Stack) :
    Scalar.run divCertificate.code (17 :: 0 :: tail) = some (0 :: tail) := by
  have actual : Scalar.run divCertificate.code [17, 0] = some [0] := by decide
  exact Scalar.run_frame actual tail

theorem div_zero_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.div.step { m with stack := irStack (17 :: 0 :: tail) } =
      .ok { m with stack := irStack (0 :: tail) } 0 := by
  exact (divCertificate.success _ _ _ rfl).mpr (div_zero_run tail)

theorem mod_zero_run (tail : Scalar.Stack) :
    Scalar.run modCertificate.code (17 :: 0 :: tail) = some (0 :: tail) := by
  have actual : Scalar.run modCertificate.code [17, 0] = some [0] := by decide
  exact Scalar.run_frame actual tail

theorem mod_zero_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.mod.step { m with stack := irStack (17 :: 0 :: tail) } =
      .ok { m with stack := irStack (0 :: tail) } 0 := by
  exact (modCertificate.success _ _ _ rfl).mpr (mod_zero_run tail)

def highBit : Scalar.Word := BitVec.ofNat 256 (2 ^ 255)
def halfMaximum : Scalar.Word := BitVec.ofNat 256 (2 ^ 255 - 1)

/-- Full-width values distinguish unsigned division/remainder from signed ones. -/
theorem unsigned_boundaries :
    Scalar.run divCertificate.code [ArithmeticControls.maximum, 2] = some [halfMaximum] ∧
    Scalar.run modCertificate.code [ArithmeticControls.maximum, 2] = some [1] ∧
    Scalar.run divCertificate.code [0, 17] = some [0] ∧
    Scalar.run modCertificate.code [0, 17] = some [0] ∧
    Scalar.run divCertificate.code [0, 0] = some [0] ∧
    Scalar.run modCertificate.code [0, 0] = some [0] := by decide

/-- Counts are never truncated modulo256; SHR never sign-extends. -/
theorem shift_boundaries :
    Scalar.run shlCertificate.code [0, ArithmeticControls.maximum] = some [ArithmeticControls.maximum] ∧
    Scalar.run shrCertificate.code [0, ArithmeticControls.maximum] = some [ArithmeticControls.maximum] ∧
    Scalar.run shlCertificate.code [255, 1] = some [highBit] ∧
    Scalar.run shrCertificate.code [255, highBit] = some [1] ∧
    Scalar.run shlCertificate.code [256, 1] = some [0] ∧
    Scalar.run shrCertificate.code [256, ArithmeticControls.maximum] = some [0] ∧
    Scalar.run shlCertificate.code [ArithmeticControls.maximum, 1] = some [0] ∧
    Scalar.run shrCertificate.code [ArithmeticControls.maximum, ArithmeticControls.maximum] = some [0] ∧
    Scalar.run shlCertificate.code [1, ArithmeticControls.maximum] = some [ArithmeticControls.doubled] ∧
    Scalar.run shrCertificate.code [1, ArithmeticControls.maximum] = some [halfMaximum] := by decide

theorem zero_divisor_not_failure :
    Scalar.run divCertificate.code [17, 0] ≠ none ∧
    Scalar.run modCertificate.code [17, 0] ≠ none := by decide

theorem div_corrupt_tail :
    Scalar.run divCertificate.code [17, 5, 23] ≠ some [3, 24] := by decide
theorem shr_corrupt_tail :
    Scalar.run shrCertificate.code [1, 6, 23] ≠ some [3, 24] := by decide

theorem emitted_opcodes : encode divCertificate.code = [0x04] ∧
    encode modCertificate.code = [0x06] ∧ encode shlCertificate.code = [0x1b] ∧
    encode shrCertificate.code = [0x1c] := by decide

/-- Local absence does not imply another component lacks selection. -/
theorem outside_component : selectUnsigned .and = none ∧
    selectBitwiseComparison .and = some andCertificate := by exact ⟨rfl, rfl⟩

end UnsignedControls

#print axioms UnsignedControls.div_run
#print axioms UnsignedControls.div_complete_frame
#print axioms UnsignedControls.div_underflow
#print axioms UnsignedControls.div_wrong_order
#print axioms UnsignedControls.mod_run
#print axioms UnsignedControls.mod_complete_frame
#print axioms UnsignedControls.mod_underflow
#print axioms UnsignedControls.mod_wrong_order
#print axioms UnsignedControls.shl_run
#print axioms UnsignedControls.shl_complete_frame
#print axioms UnsignedControls.shl_underflow
#print axioms UnsignedControls.shl_wrong_order
#print axioms UnsignedControls.shr_run
#print axioms UnsignedControls.shr_complete_frame
#print axioms UnsignedControls.shr_underflow
#print axioms UnsignedControls.shr_wrong_order
#print axioms UnsignedControls.div_zero_run
#print axioms UnsignedControls.div_zero_complete_frame
#print axioms UnsignedControls.mod_zero_run
#print axioms UnsignedControls.mod_zero_complete_frame
#print axioms UnsignedControls.unsigned_boundaries
#print axioms UnsignedControls.shift_boundaries
#print axioms UnsignedControls.zero_divisor_not_failure
#print axioms UnsignedControls.div_corrupt_tail
#print axioms UnsignedControls.shr_corrupt_tail
#print axioms UnsignedControls.emitted_opcodes
#print axioms UnsignedControls.outside_component
#print axioms ir_div_word
#print axioms ir_mod_word
#print axioms ir_shl_word
#print axioms ir_shr_word
#print axioms divCertificate
#print axioms modCertificate
#print axioms shlCertificate
#print axioms shrCertificate

end Solidity.Backend.Selection
