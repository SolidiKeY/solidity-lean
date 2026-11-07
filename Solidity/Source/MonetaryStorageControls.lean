import Solidity.Source.MonetaryStorage
import Solidity.Source.FailureRuntimeControls

/-! Selected direct Source storage operations, not a dispatched contract call.
The registered example layout supplies real persistent/transient paths. -/
namespace Solidity.Source.MonetaryStorage.Controls
open SemanticsExamples
open FailureExecution.RuntimeControls (caller priorEvent)

def seed : St EB := { St.init EB with
  ex := (St.init EB).ex.apply (.account thisC (fun account => account.withBalance 17))
  heap := (Heap.empty.alloc ⟨.bytes .memory,Data.bytes [0xDE,0xAD]⟩).1
  events := [priorEvent]
  logs := [(user,[0xAA,0xBB])]
  fnLocals := ⟨[.bytes .memory,.bool],caller⟩ }
def nine : Val EB.layout (EB.cellTy dX.path) := .int 9 (by decide)
def seven : Val EB.layout (EB.cellTy dT.path) := .int 7 (by decide)

theorem seed_fit : seed.ex.BalancesFit := by
  have initial : (St.init EB).ex.BalancesFit := by
    refine ⟨?_, ?_⟩
    · intro address
      exact (by decide : Monetary.Fits 0)
    · intro entry member
      cases member
  exact (St.init EB).ex.apply_balanceFits thisC 17 initial (by decide)

def persistentExpected : St EB := { seed with ex := (seed.ex.apply
  (.account thisC (fun account => { account with storage := account.storage.set dX.path (some nine) }))) }
def transientExpected : St EB := { seed with ex := (seed.ex.apply
  (.transient thisC (fun storage => storage.set dT.path (some seven)))) }

theorem persistent_full :
    (setCell FC dX.path (some nine) : EM EB [.bytes .memory,.bool] Unit).run (caller,seed) =
      (.ok (),(caller,persistentExpected)) := by rfl

theorem transient_full :
    (setCell FC dT.path (some seven) : EM EB [.bytes .memory,.bool] Unit).run (caller,seed) =
      (.ok (),(caller,transientExpected)) := by rfl

theorem persistent_values : readX persistentExpected = some 9 ∧
    (persistentExpected.ex.world.accounts thisC).balance = 17 ∧
    persistentExpected.ex.journal.length = 2 := by decide

theorem transient_values : readT transientExpected = some 7 ∧
    (transientExpected.ex.world.accounts thisC).balance = 17 ∧
    transientExpected.ex.journal.length = 2 := by decide

theorem persistent_fit : persistentExpected.ex.BalancesFit :=
  seed.ex.storage_balancesFit thisC (fun storage => storage.set dX.path (some nine)) seed_fit

theorem transient_fit : transientExpected.ex.BalancesFit :=
  seed.ex.transient_balancesFit thisC (fun storage => storage.set dT.path (some seven)) seed_fit

theorem static_refused :
    (setCell { FC with static := true } dX.path (some nine) :
      EM EB [.bytes .memory,.bool] Unit).run (caller,seed) =
      (.error (.revert []),(caller,seed)) := by rfl

theorem wrong_type_stuck :
    (writeAt FC dX.path (.bool false) : EM EB [.bytes .memory,.bool] Unit).run (caller,seed) =
      (.error (.stuck "storage cell type"),(caller,seed)) := by rfl

/-- The real account journal restores both the overwritten cell and old money. -/
theorem persistent_undo : persistentExpected.ex.undo = seed.ex := by
  simp only [persistentExpected, ExecState.undo_apply]

theorem transient_undo : transientExpected.ex.undo = seed.ex := by
  simp only [transientExpected, ExecState.undo_apply]

end Solidity.Source.MonetaryStorage.Controls

/-- info: 'Solidity.Source.MonetaryStorage.Controls.seed_fit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryStorage.Controls.seed_fit
/-- info: 'Solidity.Source.MonetaryStorage.Controls.persistent_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryStorage.Controls.persistent_full
/-- info: 'Solidity.Source.MonetaryStorage.Controls.transient_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryStorage.Controls.transient_full
/-- info: 'Solidity.Source.MonetaryStorage.Controls.persistent_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryStorage.Controls.persistent_values
/-- info: 'Solidity.Source.MonetaryStorage.Controls.transient_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryStorage.Controls.transient_values
/-- info: 'Solidity.Source.MonetaryStorage.Controls.persistent_fit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryStorage.Controls.persistent_fit
/-- info: 'Solidity.Source.MonetaryStorage.Controls.transient_fit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryStorage.Controls.transient_fit
/-- info: 'Solidity.Source.MonetaryStorage.Controls.static_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryStorage.Controls.static_refused
/-- info: 'Solidity.Source.MonetaryStorage.Controls.wrong_type_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryStorage.Controls.wrong_type_stuck
/-- info: 'Solidity.Source.MonetaryStorage.Controls.persistent_undo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryStorage.Controls.persistent_undo
/-- info: 'Solidity.Source.MonetaryStorage.Controls.transient_undo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Source.MonetaryStorage.Controls.transient_undo
