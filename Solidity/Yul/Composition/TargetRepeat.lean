import Solidity.Yul.Composition.Concrete

/-! Finite target repetitions with concrete arithmetic, not a Yul loop AST
or a proof of source for/while admission, fuel adequacy or compiled jumps. -/
namespace Solidity.Yul.Composition
open Solidity.Backend Scalar

def incrementCode : Program := [pushByte 1, .op .ADD]
def repeatIncrement : Nat → Program
  | 0 => []
  | n + 1 => incrementCode ++ repeatIncrement n

def incremented : Nat → Word → Word
  | 0, a => a
  | n + 1, a => incremented n (1 + a)

theorem increment_run (a : Word) (tail : Stack) :
    run incrementCode (a :: tail) = some ((1 + a) :: tail) := by
  simp only [incrementCode, run, step_pushByte, Option.bind_some]
  rfl

/-- Every finite repetition executes actual ADD code and preserves the tail.
There is no source-execution or compiler-correctness premise. -/
theorem repeat_increment_run (n : Nat) (a : Word) (tail : Stack) :
    run (repeatIncrement n) (a :: tail) = some (incremented n a :: tail) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => exact run_comp (increment_run a tail) (ih (1 + a))

example : run (repeatIncrement 3) [250,99] = some [253,99] := by decide +kernel
example : run (repeatIncrement 1) [BitVec.ofNat 256 (2^256-1),99] = some [0,99] := by decide +kernel
example : run incrementCode [] = none := rfl
#print axioms increment_run
#print axioms repeat_increment_run
end Solidity.Yul.Composition
