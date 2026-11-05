import Solidity.Backend.Selection.Interface

/-! Numeric literal selection from the existing compiler IR to Osaka PUSH32.
The certificate compares actual IR steps with Scalar.run and preserves every
nonstack machine field. Symbolic slots are not coerced to numeric words.
This is the literal component, not a claim of complete IR opcode coverage. -/
namespace Solidity.Backend.Selection

/-- The existing numeric stack representation loses no physical word. -/
theorem irStack_injective {input output : Scalar.Stack}
    (same : irStack input = irStack output) : input = output := by
  induction input generalizing output with
  | nil =>
    cases output with
    | nil => rfl
    | cons b bs => cases same
  | cons a rest ih =>
    cases output with
    | nil => cases same
    | cons b bs =>
      have parts : Evm.Word.val (Evm.wmod a.toNat) =
          Evm.Word.val (Evm.wmod b.toNat) ∧ irStack rest = irStack bs :=
        List.cons.inj same
      have values : Evm.wmod a.toNat = Evm.wmod b.toNat := Evm.Word.val.inj parts.1
      have residues : a.toNat % Evm.W = b.toNat % Evm.W := congrArg Fin.val values
      have numbers : a.toNat = b.toNat := by
        simpa only [Evm.W, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using residues
      have words : a = b := BitVec.eq_of_toNat_eq numbers
      have tails : rest = bs := ih parts.2
      cases words
      cases tails
      rfl

/-- Equality of the complete unchanged frame reduces to numeric stack equality. -/
theorem stack_update_eq (m : Evm.Machine) (input output : Scalar.Stack) :
    { m with stack := irStack input } = { m with stack := irStack output } ↔
      input = output := by
  constructor
  · intro same
    exact irStack_injective (congrArg Evm.Machine.stack same)
  · rintro rfl
    rfl

/-- Every existing numeric IR literal is restored exactly, not modulo a
second, independently chosen bound. -/
theorem literal_word_restore (value : Fin Evm.W) :
    Evm.wmod (BitVec.ofNat 256 value.val).toNat = value := by
  have number : (BitVec.ofNat 256 value.val).toNat = value.val := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt value.isLt
  rw [number]
  exact Evm.wmod_of_lt value.isLt

/-- Actual one-instruction IR selection, uniform in the entire caller frame.
Physical stack admission is a separate V2 obligation, not inferred from this
gasless instruction certificate. -/
def literalCertificate (value : Fin Evm.W) :
    InstructionCertificate (.push (.val value)) where
  code := [Scalar.pushWord (BitVec.ofNat 256 value.val)]
  success := by
    intro input output m stack
    have source : (Evm.Instr.push (.val value)).step m =
        .ok { m with stack := irStack (BitVec.ofNat 256 value.val :: input) } 0 := by
      simp only [Evm.Instr.step, Evm.Machine.next, stack, irStack,
        List.map_cons, literal_word_restore]
    have target : Scalar.run [Scalar.pushWord (BitVec.ofNat 256 value.val)] input =
        some (BitVec.ofNat 256 value.val :: input) := by
      simp only [Scalar.run, Scalar.step_pushWord, Option.bind_some]
    rw [source, target]
    simpa only [Evm.Out.ok.injEq, and_true, Option.some.injEq] using
      stack_update_eq m (BitVec.ofNat 256 value.val :: input) output
  refusal := by
    intro input m _
    simp only [Evm.Instr.step, Evm.Machine.next, Scalar.run,
      Scalar.step_pushWord, Option.bind_some, reduceCtorEq]

/-- Literal component of selection over the actual IR datatype. Other IR
constructors are outside this component; no whole-selector refusal is implied. -/
def selectLiteral : (instruction : Evm.Instr) → Option (InstructionCertificate instruction)
  | .push (.val value) => some (literalCertificate value)
  | _ => none

#print axioms irStack_injective
#print axioms stack_update_eq
#print axioms literal_word_restore
#print axioms literalCertificate

end Solidity.Backend.Selection
