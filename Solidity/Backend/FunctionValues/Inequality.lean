import Solidity.Backend.FunctionValues.Controls

/-! External-function inequality uses actual EQ/ISZERO and the same source key.
No ordering or dynamic external call coverage is inferred. -/
namespace Solidity.Backend.FunctionValues
open Solidity.Source Solidity.Roadmap Evm

theorem source_inequality (a b : ExternalValue D ps rs m) :
    Source.cmpVal .ne a.source b.source = .ok (decide (a.number ≠ b.number)) := by
  simp only [Source.cmpVal, source_key]
  change Except.ok (decide ((a.number : Int) ≠ (b.number : Int))) = _
  simp only [ne_eq, Int.ofNat_inj]

theorem inequality (a b : ExternalValue D ps rs m) (machine : Machine) :
    run (construct b.source ++ construct a.source ++ [.eq, .iszero]) machine =
      .ok { machine with stack := .val (bword (decide (a.number ≠ b.number))) :: machine.stack } 0 := by
  have keyA : (encode a.source).val = a.number := rfl
  have keyB : (encode b.source).val = b.number := rfl
  simp only [construct, List.cons_append, List.nil_append, run, exec, Instr.step,
    Machine.next, Out.bind, keyA, keyB]
  by_cases equal : a.number = b.number
  · simp only [ne_eq, equal, eq_self, decide_true, not_true_eq_false, not_false_eq_true, decide_false, bword, Bool.false_eq_true, if_true, if_false]
    rfl
  · simp only [ne_eq, equal, eq_self, decide_false, not_false_eq_true, not_true_eq_false, decide_true, bword, Bool.false_eq_true, if_true, if_false]

namespace Controls

theorem inequality_flags : decide (sample.number ≠ changedSelector.number) = true ∧
    decide (sample.number ≠ sample.number) = false := by decide

theorem source_inequality_positive : Source.cmpVal .ne sample.source changedSelector.source = .ok true := by
  rw [source_inequality, inequality_flags.1]

theorem compiled_inequality_positive :
    run (construct changedSelector.source ++ construct sample.source ++ [.eq, .iszero]) Machine.init =
      .ok { Machine.init with stack := [.val (bword true)] } 0 := by
  rw [inequality, inequality_flags.1]
  rfl

theorem compiled_inequality_negative :
    run (construct sample.source ++ construct sample.source ++ [.eq, .iszero]) Machine.init =
      .ok { Machine.init with stack := [.val (bword false)] } 0 := by
  rw [inequality, inequality_flags.2]
  rfl

end Controls
end Solidity.Backend.FunctionValues
