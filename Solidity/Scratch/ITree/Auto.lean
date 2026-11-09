import Solidity.Scratch.ITree.Payments
import Solidity.Examples.ScopedRuns

/-!
# Scratch (itree-inspection, Experiment D): does the tree still compute?

The kernel and the compiler on the tree reading (`Prog.tree`, read by
`Tree.runDet`) against today's run (`Prog.run`), on `CallbackRuns.lean`'s
`paysCore` and `ScopedRuns.lean`'s `guardLowCore`.  Not for merge.
-/

namespace Solidity.Scratch.ITree.AutoTest

open Solidity Solidity.Scratch.ITree

def paysCore := (sol[StandardExample]{
  uint to = 9; to.transfer(2); } : Prog StandardExample [] _)

def σ₀ : State StandardExample [] := State.ofStorage Storage.standardExample

/-- A funded start, so that the transfer is booked. -/
def σ₁ : State StandardExample [] := { σ₀ with selfBalance := ⟨5, by decide⟩ }

-- today's run, by the kernel
set_option profiler true in
set_option profiler.threshold 0 in
example : (Prog.run σ₀ guardLowCore).halt? = some .revert := by decide +kernel
set_option profiler true in
set_option profiler.threshold 0 in
example : (Prog.run σ₁ paysCore).isOk = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 0 in
example : (Prog.run σ₀ paysCore).halt? = some .revert := by decide +kernel

-- the tree reading, by the kernel
set_option profiler true in
set_option profiler.threshold 0 in
example : (Prog.tree guardLowCore σ₀).runDet.halt? = some .revert := by decide +kernel
set_option profiler true in
set_option profiler.threshold 0 in
example : (Prog.tree paysCore σ₁).runDet.isOk = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 0 in
example : (Prog.tree paysCore σ₀).runDet.halt? = some .revert := by decide +kernel

-- the tree is a `vis` node exactly when the transfer is booked
set_option profiler true in
set_option profiler.threshold 0 in
example : (match Prog.tree paysCore σ₁ with | .vis .. => true | .ret _ => false) = true := by
  decide +kernel

/-- 32 payments in a row. -/
def pays32 := (sol[StandardExample]{
  uint to = 9; to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); to.transfer(1); } : Prog StandardExample [] _)

def σ₂ : State StandardExample [] := { σ₀ with selfBalance := ⟨40, by decide⟩ }

set_option profiler true in
set_option profiler.threshold 0 in
example : (Prog.run σ₂ pays32).isOk = true := by decide +kernel
set_option profiler true in
set_option profiler.threshold 0 in
example : (Prog.tree pays32 σ₂).runDet.isOk = true := by decide +kernel

/-- Compiled evaluation, `reps` times each (ns). -/
def bench (reps : Nat) : IO (Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let mut a := 0
  for i in [0:reps] do
    let σ : State StandardExample [] := { σ₀ with selfBalance := (PrimTy.ofInt? .uint (40 + (i % 2 : Nat))).getD ⟨40, rfl⟩ }
    if (Prog.run σ pays32).isOk then a := a + 1
  let t1 ← IO.monoNanosNow
  for i in [0:reps] do
    let σ : State StandardExample [] := { σ₀ with selfBalance := (PrimTy.ofInt? .uint (40 + (i % 2 : Nat))).getD ⟨40, rfl⟩ }
    if (Prog.tree pays32 σ).runDet.isOk then a := a + 1
  let t2 ← IO.monoNanosNow
  return (t1 - t0, t2 - t1)

#eval bench 2000

end Solidity.Scratch.ITree.AutoTest
