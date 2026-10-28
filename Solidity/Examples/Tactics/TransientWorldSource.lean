import Solidity.Frontend.WorldImport
import Solidity.Semantics.TransientWorld

/-! Compositions of imported source frames with one outer transaction boundary.
The complete composition is explicit Lean code, not a new general source-call
lowering. Both compiler pipelines retain the same actual source programs. -/
namespace Solidity.Examples.Tactics.TransientWorldSource
open Solidity.ContractWorld

namespace Legacy
noncomputable section
solc_world_factory "../../../tests/solc/TransientFactory.ast.json" hash 0xd1b660dd56e1e5f3
  contract "TransientFactory" function "make" as Direct
solc_world_factory "../../../tests/solc/TransientFactory.ast.json" hash 0xd1b660dd56e1e5f3
  contract "TransientFactory" function "caught" as Caught
solc_world_factory "../../../tests/solc/TransientFactory.ast.json" hash 0xd1b660dd56e1e5f3
  contract "TransientFactory" function "failMake" as Failed
/-- error: solidity.worldFactory.owner: transient state needs the shared world transaction interface -/
#guard_msgs in
solc_world_factory "../../../tests/solc/TransientFactory.ast.json" hash 0xd1b660dd56e1e5f3
  contract "TransientProduct" function "write" as RefusedOwner

private def alice : Address := ⟨⟨1, by decide +kernel⟩, by decide +kernel⟩
private def factory : Address := ⟨⟨2, by decide +kernel⟩, by decide +kernel⟩
private def first : Address := ⟨⟨3, by decide +kernel⟩, by decide +kernel⟩
private def second : Address := ⟨⟨4, by decide +kernel⟩, by decide +kernel⟩
private def ctx : Context := { sender := alice }
private def childCtx : Context := { sender := factory }
private def boot : TRes (World Direct.contracts) := do
  let (w, _) ← Direct.deploy (World.empty Direct.contracts (fun _ => ⟨0, by decide +kernel⟩)) factory ctx
  pure w
private def make (w : World Direct.contracts) (address : Address) (context : Context := ctx) :=
  if h : Direct.assumptions w context = true then Direct.run w ⟨factory⟩ context address h
  else .error .exhausted
private def observe (w : World Direct.contracts) (address : Address) : Option (Int × Int) := do
  let st ← w.storage? (⟨address⟩ : Handle Direct.Code.target)
  let .prim scratch ← st.find (SRef.ofRoot "scratch" rfl)
  let .prim saved ← st.find (SRef.ofRoot "saved" rfl)
  pure (scratch.1, saved.1)

/-- Two owners share a transaction, but not their logical transient cells. -/
private def composed (w : World Direct.contracts) : TRes (World Direct.contracts × Bool) := do
  let (w, a) ← make w first
  let (w, _) ← w.call a (Entry.unit Direct.Source.TransientProduct.checkFrame) ctx
  let (w, _) ← make w second
  let (w, _) ← w.call a (Entry.unit Direct.Source.TransientProduct.write) ctx
  let (w, _) ← w.call a (Entry.unit Direct.Source.TransientProduct.checkWritten) ctx
  pure (w, decide (observe w first = some (7, 11) ∧ observe w second = some (9, 9)))

private def successive : TRes (Bool × Option (Int × Int) × Option (Int × Int) × Bool) := do
  let w ← boot
  let (next, status) := w.transact composed
  let (later, read) := next.transact fun entry =>
    entry.call (⟨first⟩ : Handle Direct.Code.target) (Entry.unit Direct.Source.TransientProduct.checkLater) ctx
  pure (status.toOption == some true, observe next first, observe later second, read.isOk)

/-- Constructor and sibling calls share cells; each outer boundary resets both
owners, retains persistent writes, and supports the next actual source call. -/
theorem source_transactions : successive.toOption = some (true, some (0, 11), some (0, 9), true) := by
  decide +kernel
/-- Reject the interpretation that transaction-local writes persist. -/
theorem false_persistent_cells : successive.toOption ≠ some (true, some (7, 11), some (9, 9), true) := by
  decide +kernel

private def badCtor : Prog (Direct.contracts .target) [] [] :=
  sol[Direct.Source.TransientProduct]{ constructor(true); }

private def caughtFrame (w : World Direct.contracts) : TRes (World Direct.contracts × Bool) := do
  let (w, a) ← make w first
  let (w, _) ← w.call a (Entry.unit Direct.Source.TransientProduct.write) ctx
  w.tryCreate (.ok ()) .target (fun _ => second) (fun _ => badCtor)
    (fun _ => childCtx) (fun next _ => .ok (next, false))
    (fun restored _ => .ok (restored, decide (observe restored first = some (7, 11) ∧
      (restored.accounts second).isNone)))
private def caughtSnapshot : TRes (Bool × Option (Int × Int) × Bool) := do
  let w ← boot
  let (next, result) := w.transact caughtFrame
  pure (result.toOption == some true, observe next first, (next.accounts second).isNone)
/-- A caught constructor revert preserves prior sibling writes and removes the
failed instance; only outer exit discards the successful owner's cells. -/
theorem caught_rollback : caughtSnapshot.toOption = some (true, some (0, 11), true) := by decide +kernel

private def failedFrame (w : World Direct.contracts) : TRes (World Direct.contracts × Unit) := do
  let (w, a) ← make w first
  let (w, _) ← w.call a (Entry.unit Direct.Source.TransientProduct.write) ctx
  let _ ← w.create .target second badCtor childCtx
  pure (w, ())
private def uncaughtSnapshot : TRes (Bool × Bool × Bool) := do
  let w ← boot
  let (next, result) := w.transact failedFrame
  pure ((match result with | .error .revert => true | _ => false),
    (next.accounts first).isNone, (next.accounts second).isNone)
/-- Uncaught failure rolls back the successful creations and their descendants. -/
theorem uncaught_rollback : uncaughtSnapshot.toOption = some (true, true, true) := by decide +kernel

private def staticSnapshot : TRes (Bool × Bool) := do
  let w ← boot
  let (next, result) := w.transact fun entry => make entry first { sender := alice, mode := .readOnly }
  pure ((match result with | .error .revert => true | _ => false), (next.accounts first).isNone)
/-- Source factory creation remains forbidden in a static context. -/
theorem static_creation : staticSnapshot.toOption = some (true, true) := by decide +kernel

private def falseSource : TRes Bool := do
  let w ← boot
  let (next, _) := w.transact composed
  pure (match next.call (⟨first⟩ : Handle Direct.Code.target)
      (Entry.unit Direct.Source.TransientProduct.falseShared) ctx with
    | .error .panic => true | _ => false)
/-- A false assertion in the actual imported source panics after reset. -/
theorem source_false_control : falseSource.toOption = some true := by decide +kernel

private def ancestorSnapshot : TRes (Bool × Bool × Bool) := do
  let w ← boot
  let (next, result) := w.transact fun entry => do
    let (changed, _) ← composed entry
    changed.call (⟨first⟩ : Handle Direct.Code.target)
      (Entry.unit Direct.Source.TransientProduct.fail) ctx
  pure ((match result with | .error .revert => true | _ => false),
    (next.accounts first).isNone, (next.accounts second).isNone)
/-- An imported source revert after successful sibling creations loses all code
and both owners' persistent/transient writes. -/
theorem ancestor_rollback : ancestorSnapshot.toOption = some (true, true, true) := by decide +kernel

private def dirtyEntry : TRes Bool := do
  let w ← boot
  let (dirty, _) ← composed w
  let (_, result) := dirty.transact fun entry =>
    .ok (entry, decide (observe entry first = some (0, 11) ∧ observe entry second = some (0, 9)))
  pure (result.toOption == some true)
/-- Deliberately dirty raw frames cannot leak either owner's transient cells
into a new outer transaction. -/
theorem entry_reset : dirtyEntry.toOption = some true := by decide +kernel

private def laterRollback : TRes (Bool × Option (Int × Int)) := do
  let w ← boot
  let (next, _) := w.transact composed
  let (restored, result) := next.transact fun entry =>
    entry.call (⟨first⟩ : Handle Direct.Code.target)
      (Entry.unit Direct.Source.TransientProduct.fail) ctx
  pure ((match result with | .error .revert => true | _ => false), observe restored first)
/-- A later transaction's source revert preserves an already installed owner's
persistent state while discarding that transaction's failed transient writes. -/
theorem later_rollback : laterRollback.toOption = some (true, some (0, 11)) := by decide +kernel

private def sourceCatch : TRes Bool := do
  let (w, f) ← Caught.deploy (World.empty Caught.contracts (fun _ => ⟨0, by decide +kernel⟩)) factory ctx
  let (next, result) := w.transact fun entry =>
    if h : Caught.assumptions entry ctx = true then Caught.run entry f ctx first h
    else .error .exhausted
  pure (result.toOption == some false && (next.accounts first).isNone)
/-- The generated source bare-catch wrapper observes the actual failed creation. -/
theorem source_catch : sourceCatch.toOption = some true := by decide +kernel

private def sourceUncaught : TRes Bool := do
  let (w, f) ← Failed.deploy (World.empty Failed.contracts (fun _ => ⟨0, by decide +kernel⟩)) factory ctx
  let (next, result) := w.transact fun entry =>
    if h : Failed.assumptions entry ctx = true then Failed.run entry f ctx first h
    else .error .exhausted
  pure ((match result with | .error .revert => true | _ => false) && (next.accounts first).isNone)
/-- The generated source direct creation propagates the constructor revert. -/
theorem source_uncaught : sourceUncaught.toOption = some true := by decide +kernel

/-- Resource halts are never converted to caught or committed success. -/
example (w : World Direct.contracts) :
    w.transact (fun _ => (.error .exhausted : TRes (World Direct.contracts × Unit))) =
      (w.resetTransient, .error .exhausted) := rfl
example (w : World Direct.contracts) :
    w.transact (fun _ => (.error .diverge : TRes (World Direct.contracts × Unit))) =
      (w.resetTransient, .error .diverge) := rfl

#print axioms entry_reset
#print axioms later_rollback
#print axioms source_false_control
#print axioms ancestor_rollback
#print axioms source_catch
#print axioms source_uncaught
#print axioms source_transactions
#print axioms caught_rollback
#print axioms uncaught_rollback
#print axioms static_creation
#print axioms World.resetTransient_storage?
#print axioms World.resetTransient_persistent
#print axioms World.transact_ok
#print axioms World.transact_commit
#print axioms World.transact_failure
end
end Legacy

namespace ViaIR
noncomputable section
solc_world_factory "../../../tests/solc/TransientFactory.viaIR.ast.json" hash 0xfc47fbb30573dd6e
  contract "TransientFactory" function "make" as Direct
solc_world_factory "../../../tests/solc/TransientFactory.viaIR.ast.json" hash 0xfc47fbb30573dd6e
  contract "TransientFactory" function "caught" as Caught
solc_world_factory "../../../tests/solc/TransientFactory.viaIR.ast.json" hash 0xfc47fbb30573dd6e
  contract "TransientFactory" function "failMake" as Failed
/-- error: solidity.worldFactory.owner: transient state needs the shared world transaction interface -/
#guard_msgs in
solc_world_factory "../../../tests/solc/TransientFactory.viaIR.ast.json" hash 0xfc47fbb30573dd6e
  contract "TransientProduct" function "write" as RefusedOwner

private def alice : Address := ⟨⟨1, by decide +kernel⟩, by decide +kernel⟩
private def factory : Address := ⟨⟨2, by decide +kernel⟩, by decide +kernel⟩
private def first : Address := ⟨⟨3, by decide +kernel⟩, by decide +kernel⟩
private def second : Address := ⟨⟨4, by decide +kernel⟩, by decide +kernel⟩
private def ctx : Context := { sender := alice }
private def childCtx : Context := { sender := factory }
private def boot : TRes (World Direct.contracts) := do
  let (w, _) ← Direct.deploy (World.empty Direct.contracts (fun _ => ⟨0, by decide +kernel⟩)) factory ctx
  pure w
private def make (w : World Direct.contracts) (address : Address) (context : Context := ctx) :=
  if h : Direct.assumptions w context = true then Direct.run w ⟨factory⟩ context address h
  else .error .exhausted
private def observe (w : World Direct.contracts) (address : Address) : Option (Int × Int) := do
  let st ← w.storage? (⟨address⟩ : Handle Direct.Code.target)
  let .prim scratch ← st.find (SRef.ofRoot "scratch" rfl)
  let .prim saved ← st.find (SRef.ofRoot "saved" rfl)
  pure (scratch.1, saved.1)

/-- Two owners share a transaction, but not their logical transient cells. -/
private def composed (w : World Direct.contracts) : TRes (World Direct.contracts × Bool) := do
  let (w, a) ← make w first
  let (w, _) ← w.call a (Entry.unit Direct.Source.TransientProduct.checkFrame) ctx
  let (w, _) ← make w second
  let (w, _) ← w.call a (Entry.unit Direct.Source.TransientProduct.write) ctx
  let (w, _) ← w.call a (Entry.unit Direct.Source.TransientProduct.checkWritten) ctx
  pure (w, decide (observe w first = some (7, 11) ∧ observe w second = some (9, 9)))

private def successive : TRes (Bool × Option (Int × Int) × Option (Int × Int) × Bool) := do
  let w ← boot
  let (next, status) := w.transact composed
  let (later, read) := next.transact fun entry =>
    entry.call (⟨first⟩ : Handle Direct.Code.target) (Entry.unit Direct.Source.TransientProduct.checkLater) ctx
  pure (status.toOption == some true, observe next first, observe later second, read.isOk)

/-- Constructor and sibling calls share cells; each outer boundary resets both
owners, retains persistent writes, and supports the next actual source call. -/
theorem source_transactions : successive.toOption = some (true, some (0, 11), some (0, 9), true) := by
  decide +kernel
/-- Reject the interpretation that transaction-local writes persist. -/
theorem false_persistent_cells : successive.toOption ≠ some (true, some (7, 11), some (9, 9), true) := by
  decide +kernel

private def badCtor : Prog (Direct.contracts .target) [] [] :=
  sol[Direct.Source.TransientProduct]{ constructor(true); }

private def caughtFrame (w : World Direct.contracts) : TRes (World Direct.contracts × Bool) := do
  let (w, a) ← make w first
  let (w, _) ← w.call a (Entry.unit Direct.Source.TransientProduct.write) ctx
  w.tryCreate (.ok ()) .target (fun _ => second) (fun _ => badCtor)
    (fun _ => childCtx) (fun next _ => .ok (next, false))
    (fun restored _ => .ok (restored, decide (observe restored first = some (7, 11) ∧
      (restored.accounts second).isNone)))
private def caughtSnapshot : TRes (Bool × Option (Int × Int) × Bool) := do
  let w ← boot
  let (next, result) := w.transact caughtFrame
  pure (result.toOption == some true, observe next first, (next.accounts second).isNone)
/-- A caught constructor revert preserves prior sibling writes and removes the
failed instance; only outer exit discards the successful owner's cells. -/
theorem caught_rollback : caughtSnapshot.toOption = some (true, some (0, 11), true) := by decide +kernel

private def failedFrame (w : World Direct.contracts) : TRes (World Direct.contracts × Unit) := do
  let (w, a) ← make w first
  let (w, _) ← w.call a (Entry.unit Direct.Source.TransientProduct.write) ctx
  let _ ← w.create .target second badCtor childCtx
  pure (w, ())
private def uncaughtSnapshot : TRes (Bool × Bool × Bool) := do
  let w ← boot
  let (next, result) := w.transact failedFrame
  pure ((match result with | .error .revert => true | _ => false),
    (next.accounts first).isNone, (next.accounts second).isNone)
/-- Uncaught failure rolls back the successful creations and their descendants. -/
theorem uncaught_rollback : uncaughtSnapshot.toOption = some (true, true, true) := by decide +kernel

private def staticSnapshot : TRes (Bool × Bool) := do
  let w ← boot
  let (next, result) := w.transact fun entry => make entry first { sender := alice, mode := .readOnly }
  pure ((match result with | .error .revert => true | _ => false), (next.accounts first).isNone)
/-- Source factory creation remains forbidden in a static context. -/
theorem static_creation : staticSnapshot.toOption = some (true, true) := by decide +kernel

private def falseSource : TRes Bool := do
  let w ← boot
  let (next, _) := w.transact composed
  pure (match next.call (⟨first⟩ : Handle Direct.Code.target)
      (Entry.unit Direct.Source.TransientProduct.falseShared) ctx with
    | .error .panic => true | _ => false)
/-- A false assertion in the actual imported source panics after reset. -/
theorem source_false_control : falseSource.toOption = some true := by decide +kernel

private def ancestorSnapshot : TRes (Bool × Bool × Bool) := do
  let w ← boot
  let (next, result) := w.transact fun entry => do
    let (changed, _) ← composed entry
    changed.call (⟨first⟩ : Handle Direct.Code.target)
      (Entry.unit Direct.Source.TransientProduct.fail) ctx
  pure ((match result with | .error .revert => true | _ => false),
    (next.accounts first).isNone, (next.accounts second).isNone)
/-- An imported source revert after successful sibling creations loses all code
and both owners' persistent/transient writes. -/
theorem ancestor_rollback : ancestorSnapshot.toOption = some (true, true, true) := by decide +kernel

private def dirtyEntry : TRes Bool := do
  let w ← boot
  let (dirty, _) ← composed w
  let (_, result) := dirty.transact fun entry =>
    .ok (entry, decide (observe entry first = some (0, 11) ∧ observe entry second = some (0, 9)))
  pure (result.toOption == some true)
/-- Deliberately dirty raw frames cannot leak either owner's transient cells
into a new outer transaction. -/
theorem entry_reset : dirtyEntry.toOption = some true := by decide +kernel

private def laterRollback : TRes (Bool × Option (Int × Int)) := do
  let w ← boot
  let (next, _) := w.transact composed
  let (restored, result) := next.transact fun entry =>
    entry.call (⟨first⟩ : Handle Direct.Code.target)
      (Entry.unit Direct.Source.TransientProduct.fail) ctx
  pure ((match result with | .error .revert => true | _ => false), observe restored first)
/-- A later transaction's source revert preserves an already installed owner's
persistent state while discarding that transaction's failed transient writes. -/
theorem later_rollback : laterRollback.toOption = some (true, some (0, 11)) := by decide +kernel

private def sourceCatch : TRes Bool := do
  let (w, f) ← Caught.deploy (World.empty Caught.contracts (fun _ => ⟨0, by decide +kernel⟩)) factory ctx
  let (next, result) := w.transact fun entry =>
    if h : Caught.assumptions entry ctx = true then Caught.run entry f ctx first h
    else .error .exhausted
  pure (result.toOption == some false && (next.accounts first).isNone)
/-- The generated source bare-catch wrapper observes the actual failed creation. -/
theorem source_catch : sourceCatch.toOption = some true := by decide +kernel

private def sourceUncaught : TRes Bool := do
  let (w, f) ← Failed.deploy (World.empty Failed.contracts (fun _ => ⟨0, by decide +kernel⟩)) factory ctx
  let (next, result) := w.transact fun entry =>
    if h : Failed.assumptions entry ctx = true then Failed.run entry f ctx first h
    else .error .exhausted
  pure ((match result with | .error .revert => true | _ => false) && (next.accounts first).isNone)
/-- The generated source direct creation propagates the constructor revert. -/
theorem source_uncaught : sourceUncaught.toOption = some true := by decide +kernel

/-- Resource halts are never converted to caught or committed success. -/
example (w : World Direct.contracts) :
    w.transact (fun _ => (.error .exhausted : TRes (World Direct.contracts × Unit))) =
      (w.resetTransient, .error .exhausted) := rfl
example (w : World Direct.contracts) :
    w.transact (fun _ => (.error .diverge : TRes (World Direct.contracts × Unit))) =
      (w.resetTransient, .error .diverge) := rfl

#print axioms entry_reset
#print axioms later_rollback
#print axioms source_false_control
#print axioms ancestor_rollback
#print axioms source_catch
#print axioms source_uncaught
#print axioms source_transactions
#print axioms caught_rollback
#print axioms uncaught_rollback
#print axioms static_creation
#print axioms World.resetTransient_storage?
#print axioms World.resetTransient_persistent
#print axioms World.transact_ok
#print axioms World.transact_commit
#print axioms World.transact_failure
end
end ViaIR
end Solidity.Examples.Tactics.TransientWorldSource
