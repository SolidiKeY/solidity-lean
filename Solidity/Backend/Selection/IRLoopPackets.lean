import Solidity.Backend.Selection.IRBranchPackets

/-! Clients of the actual compiler-IR loop semantics. Finite success is recovered
from loopRun itself; no termination or successful-turn premise is postulated. -/
namespace Solidity.Backend.Selection.IRLoop

theorem out_bind_self (out : Evm.Out) : out.bind (fun machine pending => .ok machine pending) = out := by
  cases out <;> rfl

theorem single_run (condition body : List Evm.Instr) (initial : Evm.Machine) :
    Evm.run [.loop condition body] initial = Evm.loopRun (Evm.run condition) (Evm.run body) initial := by
  simp only [Evm.run, Evm.exec_cons_zero, Evm.Instr.step, Evm.exec_nil, out_bind_self]
  rfl

theorem finite_success (rc rb : Evm.Machine → Evm.Out) (initial final : Evm.Machine) (skip : Nat)
    (actual : Evm.loopRun rc rb initial = .ok final skip) :
    ∃ count, Evm.loopIterN rc rb count initial = .inr (.ok final skip) := by
  classical
  by_cases finished : ∃ result count, Evm.loopIterN rc rb count initial = .inr result
  · have chosen : Classical.choose finished = Evm.Out.ok final skip := by
      simpa only [Evm.loopRun, finished, dif_pos] using actual
    obtain ⟨count,trace⟩ := Classical.choose_spec finished
    rw [chosen] at trace
    exact ⟨count,trace⟩
  · simp only [Evm.loopRun, finished, dif_neg, not_false_eq_true, reduceCtorEq] at actual

theorem turn_word (rc rb : Evm.Machine → Evm.Out) (initial : Evm.Machine)
    (word : Scalar.Word) (tail : Scalar.Stack)
    (actual : rc initial = .ok { initial with stack := irStack (word :: tail) } 0) :
    Evm.loopTurn rc rb initial =
      if word == 0 then .inr (.ok { initial with stack := irStack tail } 0)
      else match rb { initial with stack := irStack tail } with
        | .ok next 0 => .inl next
        | .ok _ (_ + 1) => .inr .fault
        | result => .inr result := by
  simp only [Evm.loopTurn, actual, irStack, List.map_cons, ir_word_nat]
  by_cases zero : word = 0
  · subst word
    rfl
  · have number : word.toNat ≠ 0 := fun equal => zero (BitVec.eq_of_toNat_eq equal)
    have flag : (word == 0) = false := Bool.eq_false_iff.mpr (fun equal => zero (beq_iff_eq.mp equal))
    simp only [if_neg number, flag, Bool.false_eq_true, if_false]
    rfl

theorem turn_empty (rc rb : Evm.Machine → Evm.Out) (initial : Evm.Machine)
    (actual : rc initial = .ok { initial with stack := irStack [] } 0) :
    Evm.loopTurn rc rb initial = .inr .fault := by
  rw [Evm.loopTurn, actual]
  rfl

theorem turn_continue (rc rb : Evm.Machine → Evm.Out) (initial final : Evm.Machine)
    (word : Scalar.Word) (tail : Scalar.Stack) (nonzero : word ≠ 0)
    (condition : rc initial = .ok { initial with stack := irStack (word :: tail) } 0)
    (body : rb { initial with stack := irStack tail } = .ok final 0) :
    Evm.loopTurn rc rb initial = .inl final := by
  rw [turn_word rc rb initial word tail condition]
  have flag : (word == 0) = false := Bool.eq_false_iff.mpr (fun equal => nonzero (beq_iff_eq.mp equal))
  simp only [flag, Bool.false_eq_true, if_false, body]

theorem turn_done (rc rb : Evm.Machine → Evm.Out) (initial : Evm.Machine) (tail : Scalar.Stack)
    (condition : rc initial = .ok { initial with stack := irStack (0 :: tail) } 0) :
    Evm.loopTurn rc rb initial = .inr (.ok { initial with stack := irStack tail } 0) := by
  rw [turn_word rc rb initial 0 tail condition]
  rfl

theorem iter_three (rc rb : Evm.Machine → Evm.Out) (initial first second : Evm.Machine) (result : Evm.Out)
    (one : Evm.loopTurn rc rb initial = .inl first)
    (two : Evm.loopTurn rc rb first = .inl second)
    (three : Evm.loopTurn rc rb second = .inr result) :
    Evm.loopIterN rc rb 3 initial = .inr result := by
  simp only [Evm.loopIterN, one, two, three]

theorem iter_two (rc rb : Evm.Machine → Evm.Out) (initial next : Evm.Machine) (result : Evm.Out)
    (one : Evm.loopTurn rc rb initial = .inl next)
    (two : Evm.loopTurn rc rb next = .inr result) :
    Evm.loopIterN rc rb 2 initial = .inr result := by
  simp only [Evm.loopIterN, one, two]

/-- info: 'Solidity.Backend.Selection.IRLoop.turn_continue' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms turn_continue
/-- info: 'Solidity.Backend.Selection.IRLoop.turn_done' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms turn_done
/-- info: 'Solidity.Backend.Selection.IRLoop.iter_three' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms iter_three
/-- info: 'Solidity.Backend.Selection.IRLoop.iter_two' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms iter_two

/-- info: 'Solidity.Backend.Selection.IRLoop.out_bind_self' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms out_bind_self
/-- info: 'Solidity.Backend.Selection.IRLoop.single_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms single_run
/-- info: 'Solidity.Backend.Selection.IRLoop.finite_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finite_success
/-- info: 'Solidity.Backend.Selection.IRLoop.turn_word' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms turn_word
/-- info: 'Solidity.Backend.Selection.IRLoop.turn_empty' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms turn_empty

end Solidity.Backend.Selection.IRLoop
