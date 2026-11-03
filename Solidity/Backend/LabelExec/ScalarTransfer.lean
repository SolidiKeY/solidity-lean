import Solidity.Backend.LabelExec.Fetch

/-! Lifts `Scalar.step` results to `effect`: successful numeric effects are the
same effects in byte-PC control execution. Unsupported numeric/control
instructions are not admitted by a fabricated effect supplier. -/
namespace Solidity.Backend.LabelExec

/-- The existing numeric step's actual result determines the control-layer
stack and next PC; this is not a new arithmetic or source evaluator. -/
theorem effect_of_scalar (code : List UInt8) (pc : Nat) (i : Instr)
    (stack next : Scalar.Stack) (h : Scalar.step i stack = some next) :
    effect code i ⟨pc,stack⟩ = some ⟨pc+i.size,next⟩ := by
  cases i with
  | push n imm => simp only [effect, h, Option.map_some]
  | op o =>
    cases o <;> first
    | exact (by cases h)
    | simp only [effect, h, Option.map_some]

end Solidity.Backend.LabelExec
