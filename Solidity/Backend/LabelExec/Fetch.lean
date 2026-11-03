import Solidity.Backend.LabelExec.Step

/-! Actual instruction fetch behind an arbitrary byte prefix. The whole code
is retained for jump validity; no instruction-boundary claim is inferred for
an arbitrary prefix. Assembler consumers supply legitimate labelled layouts. -/
namespace Solidity.Backend.LabelExec

theorem fetch_prefix (pre : List UInt8) (i : Instr) (post : List UInt8) :
    Creation.fetch ((pre ++ (i.encode ++ post)).drop pre.length) = some (i,post) := by
  simp only [List.drop_left, Creation.fetch_encode]

/-- The fetched instruction, not a supplied successful step, determines its effect. -/
theorem step_prefix (pre : List UInt8) (i : Instr) (post : List UInt8)
    (stack : Scalar.Stack) :
    step (pre ++ (i.encode ++ post)) ⟨pre.length,stack⟩ =
      effect (pre ++ (i.encode ++ post)) i ⟨pre.length,stack⟩ := by
  simp only [step, fetch_prefix, Option.bind_some]

/-- Actual PUSH transport, including instruction width and physical tail. -/
theorem push_prefix (pre : List UInt8) (n : Fin 33) (imm : Vector UInt8 n)
    (post : List UInt8) (tail : Scalar.Stack) :
    step (pre ++ ((Instr.push n imm).encode ++ post)) ⟨pre.length,tail⟩ =
      some ⟨pre.length + (Instr.push n imm).size, Scalar.immediate imm.toList :: tail⟩ := by
  simp only [step, fetch_prefix, Option.bind_some, effect, Scalar.step, Option.map_some]

end Solidity.Backend.LabelExec
