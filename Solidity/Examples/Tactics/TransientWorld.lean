import Solidity.Semantics.TransientWorld
import Solidity.Syntax.Splice

/-! Explicit typed owner and delegate contexts, not general source-world admission. -/
namespace Solidity.Examples.Tactics.TransientWorld
open Solidity.ContractWorld

def Cell : Contract := contract!{ uint saved; uint transient scratch; }
def Empty : Contract := contract!{}
def contracts : Bool → Contract | false => Cell | true => Empty
private def roles : Bool → Role | false => .contractCode | true => .libraryCode
private def sender : Address := ⟨⟨1, by decide +kernel⟩, by decide +kernel⟩
private def first : Address := ⟨⟨2, by decide +kernel⟩, by decide +kernel⟩
private def second : Address := ⟨⟨3, by decide +kernel⟩, by decide +kernel⟩
private def link : Address := ⟨⟨4, by decide +kernel⟩, by decide +kernel⟩
private def ctx : Context := { sender }
private def initial : World contracts :=
  World.empty contracts (fun _ => ⟨0, by decide +kernel⟩) roles
private def setup : TRes (World contracts) := do
  let (w, _) ← initial.create false first .nil ctx
  let (w, _) ← w.create false second .nil ctx
  let (w, _) ← w.deployLibrary true link ctx
  pure w
private def mutation : Library contracts false Unit :=
  ⟨true, link, Entry.unit (sol[Cell]{ scratch = 9; saved = 3; })⟩
private def observe (w : World contracts) (a : Address) : Option (Int × Int) := do
  let st ← w.storage? (⟨a⟩ : Handle false)
  let .prim scratch ← st.find (SRef.ofRoot "scratch" rfl)
  let .prim saved ← st.find (SRef.ofRoot "saved" rfl)
  pure (scratch.1, saved.1)
private def delegated : Operation contracts := .libraryCall false ⟨first⟩ mutation ctx

private def sharedFrame : TRes (Option (Int × Int) × Option (Int × Int)) := do
  let w ← setup
  let (next, _) ← w.libraryCall (⟨first⟩ : Handle false) mutation ctx
  pure (observe next first, observe next second)

/-- Delegation writes the caller's transient region, not another owning instance. -/
theorem delegate_owner : sharedFrame.toOption = some (some (9, 3), some (0, 0)) := by decide +kernel
/-- Reject the false interpretation that owners share transient cells. -/
example : sharedFrame.toOption ≠ some (some (9, 3), some (9, 3)) := by decide +kernel

private def completed : TRes (Bool × Option (Int × Int) × Option (Int × Int)) := do
  let w ← setup
  let (next, status) := delegated.transact w
  pure (status.isOk, observe next first, observe next second)
/-- A successful delegated transaction commits persistent state but discards cells. -/
theorem delegate_reset : completed.toOption = some (true, some (0, 3), some (0, 0)) := by decide +kernel

private def failed : TRes (Bool × Option (Int × Int)) := do
  let w ← setup
  let failure : Operation contracts := .seq delegated
    (.call false ⟨first⟩ (Entry.unit (sol[Cell]{ revert(); })) ctx)
  let (next, status) := failure.transact w
  pure ((match status with | .error .revert => true | _ => false), observe next first)
/-- A later ancestor failure loses a successful delegate's writes to both regions. -/
theorem delegate_rollback : failed.toOption = some (true, some (0, 0)) := by decide +kernel

#print axioms delegate_owner
#print axioms delegate_reset
#print axioms delegate_rollback
#print axioms Solidity.ContractWorld.Operation.transact_ok
#print axioms Solidity.ContractWorld.Operation.transact_failure
end Solidity.Examples.Tactics.TransientWorld
