import tests.«internal-flow».FragileReturnCalls
import Solidity.Backend.InternalFlow.LocalStoreTarget
namespace Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias
open Evm Evm.Memory
/-- Actual published finite compiler admission, not a supplied target certificate. -/
def cert : Calls.Program 1 producer.frag program :=
  (Calls.compile 1 producer.frag program).get (by decide +kernel)
attribute [irreducible] cert
theorem metrics : (cert.need,cert.cost final.st,cert.frag.get (.here : Idx Final (.alias R))) =
    (8,2,.fragile) := by decide +kernel
theorem cost : cert.cost final.st = 2 := congrArg (fun p => p.2.1) metrics
theorem need : cert.need = 8 := congrArg (fun p => p.1) metrics
theorem flag : cert.frag.get (.here : Idx Final (.alias R)) = .fragile := congrArg (fun p => p.2.2) metrics

def stmt : Calls.Statement 1 producer.frag (.block program) := Calls.block cert
def checked : Compiler.Compilation 1 producer.frag program := .memoryCalls cert (by decide +kernel)
attribute [irreducible] checked

theorem checked_need : checked.requiredFrame = stmt.need := by
  unfold checked stmt
  rfl
theorem checked_cost : checked.allocationCost final.st = stmt.cost final.st := by
  unfold checked stmt
  rfl

theorem stmt_run : (Stmt.block program).run final.st = .ok reached := by
  change (program.run final.st).map _ = _
  rw [source_run]
  rfl

theorem prefix_cost : prefixProducer.cost stored.st = 5 := by
  have h := congrArg (fun xs : List Nat => xs[5]!) exact_cost
  exact h
theorem old_cost : producer.cost caller.st = 3 := by
  have h := congrArg (fun xs : List Nat => xs[7]!) exact_cost
  exact h
theorem old_need : producer.need = 10 := by
  have h := congrArg (fun xs : List Nat => xs[4]!) exact_cost
  exact h
theorem stmt_cost : stmt.cost final.st = 2 := cost

/-- Reuse the actual old call/suffix result as one checked typed Out. -/
def previous : Solidity.Out C caller.st.H Final :=
  ⟨final.st,exported.ext.trans final.ext⟩
theorem previous_run : Solidity.Backend.InternalFlow.FragileReturnChecks.program.run caller.st = .ok previous :=
  actual_program

theorem total_room : 256 + (prefixProducer.cost stored.st +
    (producer.cost caller.st + stmt.cost final.st)) < W := by
  rw [prefix_cost,old_cost,stmt_cost]
  decide +kernel

end Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias

#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.metrics
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.cost
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.need
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.flag
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.checked_need
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.checked_cost
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.stmt_run
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.prefix_cost
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.old_cost
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.old_need
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.stmt_cost
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.previous_run
#print axioms Solidity.Backend.InternalFlow.FragileReturnChecks.ScopedAlias.total_room
