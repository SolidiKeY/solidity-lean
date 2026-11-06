import Solidity.Yul.Compilation.ControlLowering

namespace Solidity.Yul.Compilation
open Backend Scalar

def branchCondition : LoweredExpr 1 (fun l => l[0]) := lowerLocal ⟨0, by decide⟩
def branchYes : LoweredStmt 1 (fun l => l.set 0 7 (by decide)) :=
  lowerAssign ⟨0, by decide⟩ (lowerLiteral 7)
def branchNo : LoweredStmt 1 (fun l => l.set 0 9 (by decide)) :=
  lowerAssign ⟨0, by decide⟩ (lowerLiteral 9)
def branchTarget : Backend.Block := .ite [readSlot ⟨0, by decide⟩]
  (.code ([pushWord 7] ++ writeSlot ⟨0, by decide⟩))
  (.code ([pushWord 9] ++ writeSlot ⟨0, by decide⟩))
example : lowerBranch branchCondition branchYes branchNo 0 = some branchTarget := rfl
example (value : Word) (tail : Stack) :
    ∃ cc aa bb, branchTarget = .ite cc (.code aa) (.code bb) ∧
      run cc (value :: tail) = some (value :: value :: tail) ∧
      run (if value = 0 then bb else aa) (value :: tail) =
        some ((if value = 0 then [9] else [7]) ++ tail) :=
  by simpa only [apply_ite] using
    lowerBranch_slices branchCondition branchYes branchNo 0 branchTarget rfl #v[value] #v[] tail
example : (assemble 0 (fun x : Empty => nomatch x) (branchTarget.expand 0).1).isSome :=
  by
    apply emittedControl_assembles branchTarget 0 0
    intro l hl
    have h : l = 0 ∨ l = 1 := by
      simpa only [branchTarget, Backend.Block.refs_expand, List.append_nil, List.nil_append,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Nat.reduceAdd] using hl
    rcases h with h | h <;> subst l <;> decide +kernel
example : lowerBranch (lowerLocal (n := 16) ⟨15, by decide⟩)
    (lowerSkip 16) (lowerSkip 16) 1 = none := rfl
example : lowerBranch (lowerLiteral (n := 16) 0)
    (lowerAssign ⟨15, by decide⟩ (lowerLiteral 7)) (lowerSkip 16) 1 = none := rfl

def decrement : LoweredStmt 1 (fun l => l.set 0 (l[0] - 1) (by decide)) :=
  lowerAssign ⟨0, by decide⟩ (lowerBinary selectSub (lowerLocal ⟨0, by decide⟩) (lowerLiteral 1))
def whileTarget : Backend.Block := .loop [readSlot ⟨0, by decide⟩]
  (.code ([pushWord 1, readSlot ⟨1, by decide⟩, .op .SUB] ++ writeSlot ⟨0, by decide⟩))
example : lowerWhile branchCondition decrement 0 = some whileTarget := rfl
example : (assemble 0 (fun x : Empty => nomatch x) (whileTarget.expand 0).1).isSome :=
  by
    apply emittedControl_assembles whileTarget 0 0
    intro l hl
    have h : l = 1 ∨ l = 0 := by
      simpa only [whileTarget, Backend.Block.refs_expand, List.append_nil, List.nil_append,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Nat.reduceAdd] using hl
    rcases h with h | h <;> subst l <;> decide +kernel
example : ∃ p, (lowerFixedRepeat decrement 3).code 2 = some p ∧
    run p [100, 101, 3, 77, 88] = some [100, 101, 0, 77, 88] :=
  ⟨_, rfl, (lowerFixedRepeat decrement 3).correct 2 _ rfl #v[3] #v[100, 101] [77, 88]⟩
end Solidity.Yul.Compilation
