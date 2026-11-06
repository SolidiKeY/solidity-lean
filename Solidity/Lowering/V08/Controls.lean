import Solidity.Lowering.V08.Callable
import Solidity.Lowering.V08.Transactions
import Solidity.Syntax.Splice

/-! Inhabited controls for the adapter laws. These are intrinsic executions,
not independent source-execution or compiler/EVM certificates. -/
namespace Solidity.Lowering.V08.Controls
open Solidity.ContractWorld

def Cell : Contract := contract!{ uint saved; uint transient scratch; }
def catalog : Unit → Contract := fun _ => Cell
def sender : Address := ⟨⟨1, by decide +kernel⟩, by decide +kernel⟩
def self : Address := ⟨⟨2, by decide +kernel⟩, by decide +kernel⟩
def ctx : Context := { sender }
def paidCtx : Context := { sender, mode := .ordinary ⟨7, by decide +kernel⟩ }
def initial : World catalog := World.empty catalog
  (fun address => if address = sender then ⟨100, by decide +kernel⟩ else ⟨0, by decide +kernel⟩)
def setup : TRes (World catalog) := do
  let (world, _) ← initial.create () self .nil ctx
  pure world

def entry : Entry Cell (List UInt8) :=
  { locals := [], body := sol[Cell]{ saved = 3; scratch = 9; },
    result := fun _ => .ok [0xab, 0xcd], payable := true }

def observe (world : World catalog) : Option (Int × Int × Int × Int) := do
  let store ← world.storage? (⟨self⟩ : Handle ())
  let .prim saved ← store.find (SRef.ofRoot "saved" rfl)
  let .prim scratch ← store.find (SRef.ofRoot "scratch" rfl)
  pure ((world.balance sender).1, (world.balance self).1, saved.1, scratch.1)

def paidObservation : TRes (Option (Int × Int × Int × Int) × List UInt8) := do
  let world ← setup
  let (next, bytes) ← world.call (⟨self⟩ : Handle ()) entry paidCtx
  pure (observe next, bytes)

/-- Actual creation then nonzero paid call changes balances and both regions. -/
theorem funded_call : paidObservation.toOption =
    some (some (93, 7, 3, 9), [0xab, 0xcd]) := by decide +kernel

/-- An ABI observation cannot replace the exact return bytes. -/
theorem wrong_payload : paidObservation.toOption ≠
    some (some (93, 7, 3, 9), [0xab, 0xce]) := by decide +kernel

def failedOuter : TRes (Option (Int × Int × Int × Int) × Option (List UInt8)) := do
  let world ← setup
  let (next, result) := world.transact (fun before => do
    let _ ← before.call (⟨self⟩ : Handle ()) entry paidCtx
    (.error (.revertWith [0xde, 0xad]) : TRes (World catalog × Unit)))
  pure (observe next, match result with | .error (.revertWith bytes) => some bytes | _ => none)

/-- A later ancestor failure rolls back the paid successful descendant. -/
theorem funded_rollback : failedOuter.toOption =
    some (some (100, 0, 0, 0), some [0xde, 0xad]) := by decide +kernel

/-- The descendant's paid snapshot is the wrong rollback frame. -/
theorem wrong_frame : failedOuter.toOption ≠
    some (some (93, 7, 3, 0), some [0xde, 0xad]) := by decide +kernel

def repeated : TRes (Option (Int × Int × Int × Int) × List UInt8) := do
  let world ← setup
  let (middle, result) := world.transact (fun before => before.call (⟨self⟩ : Handle ()) entry paidCtx)
  let _ ← result
  let (next, status) := middle.transact (fun before => before.call (⟨self⟩ : Handle ())
    ({ locals := [], body := .nil, result := fun _ => .ok [0xab, 0xcd] } : Entry Cell (List UInt8)) ctx)
  let bytes ← status
  pure (observe next, bytes)

/-- A second observation sees persistent writes and cleared transient cells. -/
theorem repeated_reset : repeated.toOption =
    some (some (93, 7, 3, 0), [0xab, 0xcd]) := by decide +kernel

def extendedObservation : TRes (Option (Int × Int × Int × Int) × Nat) := do
  let world ← setup
  let (next, length) ← world.call (⟨self⟩ : Handle ()) (observeEntry entry List.length) paidCtx
  pure (observe next, length)

/-- A nonidentity result adapter keeps the actual nonzero-paid world. -/
theorem extension_funded : extendedObservation.toOption = some (some (93, 7, 3, 9), 2) := by decide +kernel

def failedDecoder : TRes (Option (List UInt8)) := do
  let world ← setup
  let result := world.call (⟨self⟩ : Handle ())
    (observeEntry ({ entry with result := fun _ => .error (.revertWith [0xba, 0xd0]) } : Entry Cell (List UInt8)) List.length) paidCtx
  pure (match result with | .error (.revertWith bytes) => some bytes | _ => none)

/-- Extending a failing caller-side decoder retains its exact payload. -/
theorem decoder_failure : failedDecoder.toOption = some (some [0xba, 0xd0]) := by decide +kernel

/-- A wrong failure payload is rejected after the paid descendant rolls back. -/
theorem wrong_failure_payload : failedOuter.toOption ≠
    some (some (100, 0, 0, 0), some [0xde, 0xae]) := by decide +kernel

def third : Address := ⟨⟨3, by decide +kernel⟩, by decide +kernel⟩
def creationCatch : TRes (Option (Int × Int × Int × Int) × Bool × Bool) := do
  let world ← setup
  let (next, status) := world.transact (fun before => do
    let (paid, _) ← before.call (⟨self⟩ : Handle ()) entry paidCtx
    paid.tryCreate (.ok ()) () (fun _ => third)
      (fun _ => sol[Cell]{ saved = 8; scratch = 12; revert(); }) (fun _ => ctx)
      (fun after _ => .ok (after, false)) (fun snapshot _ => .ok (snapshot, true)))
  let caught ← status
  pure (observe next, caught, (next.accounts third).isSome)

/-- A failing nonempty constructor is caught at the post-payment snapshot. -/
theorem constructor_caught : creationCatch.toOption = some (some (93, 7, 3, 0), true, false) := by decide +kernel

/-- Catching construction does not refund the outer successful call's payment. -/
theorem constructor_wrong_snapshot : creationCatch.toOption ≠
    some (some (100, 0, 0, 0), true, false) := by decide +kernel

#print axioms extension_funded
#print axioms decoder_failure
#print axioms wrong_failure_payload
#print axioms constructor_caught
#print axioms constructor_wrong_snapshot
#print axioms funded_call
#print axioms wrong_payload
#print axioms funded_rollback
#print axioms wrong_frame
#print axioms repeated_reset
#print axioms Solidity.Lowering.V08.call_observeEntry
#print axioms Solidity.Lowering.V08.transact_descendant_failure
#print axioms Solidity.Lowering.V08.transact_repeat
end Solidity.Lowering.V08.Controls
