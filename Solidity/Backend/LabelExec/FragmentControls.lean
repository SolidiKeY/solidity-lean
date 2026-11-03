import Solidity.Backend.LabelExec.FragmentSound

/-! Kernel controls for static underflow, capacity, and value-frame boundaries.
These are constructed IR controls, not source/native fixtures or EVM faults. -/
namespace Solidity.Backend.LabelExec

/-- DUP16 cannot read a nonexistent sixteenth input word. -/
theorem dup16_underflow : ¬ InstrShape (.op (.DUP 15)) 15 16 := by
  rintro ⟨a,b,suffix,row,hin,hout⟩
  simp only [arity, Option.some.injEq, Prod.mk.injEq] at row
  rcases row with ⟨rfl,rfl⟩
  omega

/-- SWAP16 needs seventeen physical input words, not sixteen. -/
theorem swap16_underflow : ¬ InstrShape (.op (.SWAP 15)) 16 16 := by
  rintro ⟨a,b,suffix,row,hin,hout⟩
  simp only [arity, Option.some.injEq, Prod.mk.injEq] at row
  rcases row with ⟨rfl,rfl⟩
  omega

/-- A nonempty admitted condition: its height is right while its lower word changes. -/
def overwritingCondition : Code 1 2 where
  instructions := [.op .POP, Scalar.pushByte 99, .push 0 #v[]]
  shape := .cons (.mk 1 0 0 rfl rfl rfl)
    (.cons (.mk 0 1 0 rfl rfl rfl) (.cons (.mk 0 1 1 rfl rfl rfl) (.nil 2)))
  capacity := by decide

/-- Height/capacity alone cannot supply a value-frame invariant. -/
theorem condition_changes_lower_word :
    Scalar.run overwritingCondition.instructions [42] = some [0,99] := by rfl

/-- The condition alone is within 1024, before the generated target PUSH. -/
def boundaryCondition : Code 1023 1024 where
  instructions := [.push 0 #v[]]
  shape := .cons (.mk 0 1 1023 rfl rfl rfl) (.nil 1024)
  capacity := by decide

/-- Structured control must reserve its second temporary word. -/
theorem control_capacity_boundary : (1022+2 ≤ (1024 : Nat)) ∧ ¬ (1023+2 ≤ (1024 : Nat)) := by
  decide

/-- A legitimate condition cannot waive the subsequent control-header peak.
This is rejection of a static shape, not an observed EVM fault. -/
theorem loop_header_overflow (cond : Code 1023 1024) (body : Block) :
    ¬ BlockShape (.loop cond.instructions body) 1023 1023 := by
  intro shape
  have hp : 1023+2 ≤ 1024 := shape.control_capacity
  omega

end Solidity.Backend.LabelExec
