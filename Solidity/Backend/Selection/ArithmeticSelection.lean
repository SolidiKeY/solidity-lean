import Solidity.Backend.Selection.LiteralSelection

/-! Numeric opcode selection uses the existing IR step and Scalar interpreter.
Physical admission remains a separate V2 frame obligation. -/
namespace Solidity.Backend.Selection

/-- Construct the existing certificate from an equation of the actual runners. -/
def certificateOfStep (instruction : Evm.Instr) (code : Program)
    (equation : ∀ (input : Scalar.Stack) (m : Evm.Machine),
      m.stack = irStack input → instruction.step m =
        match Scalar.run code input with
        | none => .fault
        | some output => .ok { m with stack := irStack output } 0) :
    InstructionCertificate instruction where
  code := code
  success := by
    intro input output m stack
    rw [equation input m stack]
    cases result : Scalar.run code input with
    | none => simp only [reduceCtorEq]
    | some reached =>
      simpa only [Evm.Out.ok.injEq, and_true, Option.some.injEq] using
        stack_update_eq m reached output
  refusal := by
    intro input m stack
    rw [equation input m stack]
    cases result : Scalar.run code input with
    | none => simp only
    | some reached => simp only [reduceCtorEq]

/-- Intrinsic physical words already satisfy the IR numeric bound. -/
theorem ir_word_nat (word : Scalar.Word) :
    (Evm.wmod word.toNat).val = word.toNat := by
  exact Nat.mod_eq_of_lt word.isLt

/-- The actual ADD operations agree at the shared 256-bit boundary. -/
theorem ir_add_word (a b : Scalar.Word) :
    Evm.wmod ((Evm.wmod a.toNat).val + (Evm.wmod b.toNat).val) =
      Evm.wmod (a + b).toNat := by
  apply Fin.ext
  simp only [ir_word_nat, BitVec.toNat_add, Evm.wmod, Evm.W, Nat.mod_mod,
    Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt]

/-- Numeric IR ADD selects one Osaka ADD, including operand-underflow refusal. -/
def addCertificate : InstructionCertificate .add :=
  certificateOfStep .add [.op .ADD] (by
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
          ir_add_word])

/-- The actual MUL operations agree at the shared 256-bit boundary. -/
theorem ir_mul_word (a b : Scalar.Word) :
    Evm.wmod ((Evm.wmod a.toNat).val * (Evm.wmod b.toNat).val) =
      Evm.wmod (a * b).toNat := by
  apply Fin.ext
  simp only [ir_word_nat, BitVec.toNat_mul, Evm.wmod, Evm.W, Nat.mod_mod,
    Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt]

/-- Numeric IR MUL selects one Osaka MUL, including operand-underflow refusal. -/
def mulCertificate : InstructionCertificate .mul :=
  certificateOfStep .mul [.op .MUL] (by
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
          ir_mul_word])

/-- Component selection only: other instructions are outside this component. -/
def selectArithmetic : (instruction : Evm.Instr) → Option (InstructionCertificate instruction)
  | .add => some addCertificate
  | .mul => some mulCertificate
  | _ => none

namespace ArithmeticControls

/-- Largest intrinsic physical word. -/
def maximum : Scalar.Word := BitVec.ofNat 256 (2 ^ 256 - 1)
def doubled : Scalar.Word := BitVec.ofNat 256 (2 ^ 256 - 2)

theorem add_wrap_word : maximum + 1 = 0 := by decide
theorem mul_wrap_word : maximum * 2 = doubled := by decide

/-- Actual target execution preserves an arbitrary physical suffix. -/
theorem add_wrap (tail : Scalar.Stack) :
    Scalar.run addCertificate.code (maximum :: 1 :: tail) = some (0 :: tail) := by
  change some ((maximum + 1) :: tail) = some (0 :: tail)
  rw [add_wrap_word]

theorem mul_wrap (tail : Scalar.Stack) :
    Scalar.run mulCertificate.code (maximum :: 2 :: tail) = some (doubled :: tail) := by
  change some ((maximum * 2) :: tail) = some (doubled :: tail)
  rw [mul_wrap_word]

/-- The actual IR result retains the entire arbitrary nonstack caller frame. -/
theorem add_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.add.step { m with stack := irStack (maximum :: 1 :: tail) } =
      .ok { m with stack := irStack (0 :: tail) } 0 := by
  exact (addCertificate.success _ _ _ rfl).mpr (add_wrap tail)

theorem mul_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.mul.step { m with stack := irStack (maximum :: 2 :: tail) } =
      .ok { m with stack := irStack (doubled :: tail) } 0 := by
  exact (mulCertificate.success _ _ _ rfl).mpr (mul_wrap tail)

/-- Both physical operand shortages are refused by each actual selected opcode. -/
theorem add_underflow : Scalar.run addCertificate.code [] = none ∧
    Scalar.run addCertificate.code [7] = none := by exact ⟨rfl, rfl⟩
theorem mul_underflow : Scalar.run mulCertificate.code [] = none ∧
    Scalar.run mulCertificate.code [7] = none := by exact ⟨rfl, rfl⟩

theorem add_wrong_result :
    Scalar.run addCertificate.code [maximum, 1, 23] ≠ some [1, 23] := by decide
theorem mul_wrong_result :
    Scalar.run mulCertificate.code [maximum, 2, 23] ≠ some [maximum, 23] := by decide
theorem add_corrupt_tail :
    Scalar.run addCertificate.code [maximum, 1, 23] ≠ some [0, 24] := by decide
theorem mul_corrupt_tail :
    Scalar.run mulCertificate.code [maximum, 2, 23] ≠ some [doubled, 24] := by decide

theorem emitted_opcodes : encode addCertificate.code = [0x01] ∧
    encode mulCertificate.code = [0x02] := by exact ⟨rfl, rfl⟩

/-- This component's absence is not a verdict about source SUB execution. -/
theorem outside_component : selectArithmetic .sub = none := rfl

end ArithmeticControls

#print axioms ArithmeticControls.add_wrap
#print axioms ArithmeticControls.mul_wrap
#print axioms ArithmeticControls.add_complete_frame
#print axioms ArithmeticControls.mul_complete_frame
#print axioms ArithmeticControls.add_underflow
#print axioms ArithmeticControls.mul_underflow
#print axioms ArithmeticControls.add_wrong_result
#print axioms ArithmeticControls.mul_wrong_result
#print axioms ArithmeticControls.add_corrupt_tail
#print axioms ArithmeticControls.mul_corrupt_tail
#print axioms ArithmeticControls.emitted_opcodes
#print axioms ArithmeticControls.outside_component
#print axioms ir_mul_word
#print axioms mulCertificate
#print axioms certificateOfStep
#print axioms ir_add_word
#print axioms addCertificate

end Solidity.Backend.Selection
