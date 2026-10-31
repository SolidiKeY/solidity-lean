import SolidityBridge.RoadmapV15.PublishedWorldTransport
import Solidity.Examples.Tactics.ContractWorld
import Solidity.Examples.Tactics.TransientWorld

/-! New consumer combinations over published actual world fixtures, read only.
No production source admission, nonce/log or pinned-EVM result is claimed. -/
namespace SolidityBridge.RoadmapV15.PublishedWorldControls
open Solidity Solidity.ContractWorld

private abbrev catalog := Solidity.Examples.Tactics.ContractWorld.contracts
private abbrev start := Solidity.Examples.Tactics.ContractWorld.initial
private abbrev built := Solidity.Examples.Tactics.ContractWorld.factoryWorld
private abbrev factory := Solidity.Examples.Tactics.ContractWorld.factoryOperation
private def alice : Address := ⟨⟨1, by decide +kernel⟩, by decide +kernel⟩
private def child : Address := ⟨⟨3, by decide +kernel⟩, by decide +kernel⟩
private def ctx : Context := { sender := alice }

private theorem start_reset : start.resetTransient = start := rfl
private theorem factory_ready : factory.run start.resetTransient = .ok built := by
  rw [start_reset]
  exact Solidity.Examples.Tactics.ContractWorld.factory_run

-- This published prefix actually installs code and changes funds; it is not an
-- identity operation or a local Journal pretending to be an account world.
example : (built.accounts child).isSome = true := by decide +kernel
example : (start.accounts child).isSome = false := rfl
example : (built.balance alice).val ≠ (start.balance alice).val := by decide +kernel

example : (Operation.seq factory (.guard false)).run start = .error .revert :=
  world_sequence_failure start built factory (.guard false) .revert
    Solidity.Examples.Tactics.ContractWorld.factory_run rfl
example : (Operation.seq factory (.guard false)).transact start =
    (start.resetTransient, .error .revert) :=
  world_operation_transaction_failure start built factory (.guard false) .revert factory_ready rfl

private def failedFrame (w : World catalog) : TRes (World catalog × List UInt8) :=
  (factory.run w).bind (fun _ => .error (.revertWith [0, 255]))
private theorem failed_frame : failedFrame start.resetTransient = .error (.revertWith [0, 255]) := by
  unfold failedFrame
  rw [factory_ready]
  rfl

example : start.transact failedFrame = (start.resetTransient, .error (.revertWith [0, 255])) :=
  world_transaction_prefix_failure start built factory (fun _ => .error (.revertWith [0, 255]))
    (.revertWith [0, 255]) factory_ready rfl
example : start.transact (fun before => (factory.run before).bind (fun next => .ok (next, [1, 255]))) =
    (built.resetTransient, .ok ([1, 255] : List UInt8)) :=
  world_transaction_prefix_success start built built factory (fun next => .ok (next, [1, 255]))
    [1, 255] factory_ready rfl

example : (Backend.toBytesBE 32
    (Backend.Scalar.encodeValue .uint ((start.transact failedFrame).1.balance alice)).toNat).toList =
      (Backend.toBytesBE 32 (Backend.Scalar.encodeValue .uint (start.balance alice)).toNat).toList :=
  world_failure_balance_bytes start failedFrame (.revertWith [0, 255]) failed_frame alice
example : (start.transact failedFrame).1.accounts child =
    (start.accounts child).map (fun ⟨k, st⟩ => ⟨k, Storage.resetTransient st⟩) :=
  world_failure_accounts start failedFrame (.revertWith [0, 255]) failed_frame child

private def abortFrame (w : World catalog) : TRes (World catalog × Unit) :=
  ((Operation.guard false : Operation catalog).run w).map (fun next => (next, ()))
private def enabledPath : SRef (catalog .cell) (.prim .bool) := SRef.ofRoot "enabled" rfl
example : enabledPath.root ∉ (catalog .cell).transientRoots := by decide
example : ((built.transact abortFrame).1.storage? (⟨child⟩ : Handle .cell)).bind
      (fun st => st.find enabledPath) =
    (built.storage? (⟨child⟩ : Handle .cell)).bind (fun st => st.find enabledPath) :=
  world_failure_persistent built abortFrame .revert rfl ⟨child⟩ enabledPath (by decide)

-- The persistent-path premise is not available for a declared transient cell.
example : ("scratch" : Name) ∈ Solidity.Examples.Tactics.TransientWorld.Cell.transientRoots := by decide
example : catchable .exhausted = false := rfl
example : catchable .diverge = false := rfl

-- Creation collision at an actually installed account inhabits the catch law.
private theorem revert_of_test {α : Type} (run : TRes α)
    (h : (match run with | .error .revert => true | _ => false) = true) : run = .error .revert := by
  cases run with
  | ok value => cases h
  | error e => cases e <;> first | rfl | cases h
private theorem collision : built.create .cell child .nil ctx = .error .revert :=
  revert_of_test _ (by decide +kernel)
example :
    (Operation.seq (.tryCreate (.ok ()) .cell (fun _ => child) (fun _ => .nil) (fun _ => ctx))
      (.guard true)).run built = .ok built :=
  world_caught_creation_tail built () .cell (fun _ => child) (fun _ => .nil) (fun _ => ctx)
    .revert rfl collision rfl (.guard true)

example :
    (Operation.seq (.tryCreate (.error (.revertWith [0, 255]) : TRes Unit) .cell
      (fun _ => child) (fun _ => .nil) (fun _ => ctx)) (.guard true)).run built =
      .error (.revertWith [0, 255]) :=
  world_argument_failure_tail built (.revertWith [0, 255]) .cell
    (fun _ : Unit => child) (fun _ => .nil) (fun _ => ctx) (.guard true)
example :
    (Operation.seq (.tryCreate (.error .exhausted : TRes Unit) .cell
      (fun _ => child) (fun _ => .nil) (fun _ => ctx)) (.guard true)).run built = .error .exhausted :=
  world_argument_failure_tail built .exhausted .cell
    (fun _ : Unit => child) (fun _ => .nil) (fun _ => ctx) (.guard true)

-- A real intrinsic call writes a declared transient root and a persistent root.
-- Comparison uses the published typed SVal.beq fold; no indexed-family matcher
-- or replacement storage interpreter is introduced in this control.
private abbrev transientCell := Solidity.Examples.Tactics.TransientWorld.Cell
private def transientCatalog (_ : Unit) : Contract := transientCell
private def vacant : World transientCatalog := World.empty transientCatalog (fun _ => ⟨0, by decide +kernel⟩)
private def installation := vacant.create () child .nil ctx
private def resident : World transientCatalog := (installation.toOption.map Prod.fst).getD vacant
private def scratchPath : SRef (transientCatalog ()) (.prim .uint) := SRef.ofRoot "scratch" rfl
private def savedPath : SRef (transientCatalog ()) (.prim .uint) := SRef.ofRoot "saved" rfl
private def writes : Entry transientCell Unit := Entry.unit (sol[transientCell]{ scratch = 17; saved = 23; })
private def writeOp : Operation transientCatalog := .call () ⟨child⟩ writes ctx
private def mid : World transientCatalog := (writeOp.run resident.resetTransient).toOption.getD resident
private theorem result_ok {α : Type} (run : TRes α) (fallback : α) (h : run.isOk = true) :
    run = .ok (run.toOption.getD fallback) := by
  cases run with
  | ok value => rfl
  | error e => cases h
private theorem write_ready : writeOp.run resident.resetTransient = .ok mid :=
  result_ok _ _ (by decide +kernel)
private def scratch17 (w : World transientCatalog) : Bool :=
  ((w.storage? (⟨child⟩ : Handle ())).bind (fun st => st.find scratchPath)).any
    (fun value => value.beq (.prim ⟨17, by decide +kernel⟩))
private def saved23 (w : World transientCatalog) : Bool :=
  ((w.storage? (⟨child⟩ : Handle ())).bind (fun st => st.find savedPath)).any
    (fun value => value.beq (.prim ⟨23, by decide +kernel⟩))
private theorem mid_scratch : scratch17 mid = true := by decide +kernel
private theorem mid_scratch_reset : scratch17 mid.resetTransient = false := by decide +kernel
private theorem mid_saved_reset : saved23 mid.resetTransient = true := by decide +kernel
example : installation.isOk = true := by decide +kernel
example : (mid.accounts child).isSome = true := by decide +kernel
example : saved23 mid = true := by decide +kernel
example : scratch17 mid ≠ scratch17 mid.resetTransient := by
  rw [mid_scratch, mid_scratch_reset]
  decide

private def observeTail (w : World transientCatalog) : TRes (World transientCatalog × Bool) :=
  .ok (w, scratch17 w)
private theorem observed_tail : observeTail mid = .ok (mid, true) := by
  unfold observeTail
  rw [mid_scratch]
private theorem successful_boundary :
    resident.transact (fun before => (writeOp.run before).bind observeTail) =
      (mid.resetTransient, .ok true) :=
  world_transaction_prefix_success resident mid mid writeOp observeTail true write_ready observed_tail
example : (resident.transact (fun before => (writeOp.run before).bind observeTail)).2 = .ok true := by
  rw [successful_boundary]
example : scratch17 (resident.transact (fun before => (writeOp.run before).bind observeTail)).1 = false := by
  rw [successful_boundary]
  exact mid_scratch_reset
example : saved23 (resident.transact (fun before => (writeOp.run before).bind observeTail)).1 = true := by
  rw [successful_boundary]
  exact mid_saved_reset

-- This condition observes storage, never whether a callee accepts payment.
-- A premature sibling reset would select success instead of this exact error.
private def failIfObserved (w : World transientCatalog) : TRes (World transientCatalog × Unit) :=
  if scratch17 w then .error (.revertWith [17]) else .ok (w, ())
private theorem observed_failure : failIfObserved mid = .error (.revertWith [17]) := by
  simp only [failIfObserved, mid_scratch, ↓reduceIte]
private theorem failed_boundary :
    resident.transact (fun before => (writeOp.run before).bind failIfObserved) =
      (resident.resetTransient, .error (.revertWith [17])) :=
  world_transaction_prefix_failure resident mid writeOp failIfObserved (.revertWith [17])
    write_ready observed_failure
example : scratch17 (resident.transact (fun before => (writeOp.run before).bind failIfObserved)).1 = false := by
  rw [failed_boundary]
  decide +kernel
example : saved23 (resident.transact (fun before => (writeOp.run before).bind failIfObserved)).1 = false := by
  rw [failed_boundary]
  decide +kernel

private def abortTransient (w : World transientCatalog) : TRes (World transientCatalog × Unit) :=
  ((Operation.guard false : Operation transientCatalog).run w).map (fun next => (next, ()))
-- Occupied, non-normalized input: 17 is cleared while persistent 23 survives.
example : (mid.transact abortTransient).1.accounts child =
    (mid.accounts child).map (fun ⟨k, st⟩ => ⟨k, Storage.resetTransient st⟩) :=
  world_failure_accounts mid abortTransient .revert rfl child
private theorem account_reset_differs : mid.resetTransient.accounts child ≠ mid.accounts child := by
  intro h
  have observed : scratch17 mid.resetTransient = scratch17 mid := by
    unfold scratch17 World.storage?
    rw [h]
  rw [mid_scratch_reset, mid_scratch] at observed
  cases observed
example : (mid.transact abortTransient).1.accounts child ≠ mid.accounts child := by
  rw [World.transact_failure mid abortTransient .revert rfl]
  exact account_reset_differs
example : scratch17 (mid.transact abortTransient).1 = false := by
  rw [World.transact_failure mid abortTransient .revert rfl]
  exact mid_scratch_reset
example : saved23 (mid.transact abortTransient).1 = true := by
  rw [World.transact_failure mid abortTransient .revert rfl]
  exact mid_saved_reset

#print axioms world_failure_balance_bytes
#print axioms world_failure_accounts
#print axioms world_sequence_failure
#print axioms world_transaction_prefix_failure
#print axioms world_transaction_prefix_success
#print axioms world_operation_transaction_failure
#print axioms world_failure_persistent
#print axioms world_caught_creation_tail
#print axioms world_argument_failure_tail
end SolidityBridge.RoadmapV15.PublishedWorldControls
