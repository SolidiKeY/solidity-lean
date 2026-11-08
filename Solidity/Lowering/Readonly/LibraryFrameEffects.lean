import Solidity.Lowering.Readonly.HistoryRollback
import Solidity.Lowering.Readonly.EffectRules

/-! Generic delegated-memory frame journal proof. Regression purpose: the
new library try computation restores caller memory on every outcome and rolls
back a revert only to its actual live mark, retaining journal ancestry.
No pointer ABI, physical linkage, or whole-world equality is asserted. -/
namespace Solidity.Lowering.Readonly.SourceHistory
open Solidity.Source
open Solidity.Roadmap (Bytes)
variable {E : Env} {α : Type}

/-- Proof-time factoring of the existing delegated wrapper around an action. -/
def libraryFrame (action : EM E [] α) : EM E [] (Except Bytes α) := do
  let saved ← mark
  EM.modSt fun state => { state with heap := Heap.empty }
  let result ← EM.attempt action
  EM.modSt fun state => { state with heap := saved.2.2 }
  match result with
  | .ok value => pure (.ok value)
  | .error (.revert data) => do
    rollbackTo saved
    pure (.error data)
  | .error other => EM.halt other

private theorem frame_run (action : EM E [] α) (locals : Locals E.layout [])
    (state : St E) :
    (libraryFrame action).run (locals,state) =
      (let (result, updated, dirty) := action.run (locals,{state with heap := Heap.empty})
       match result with
       | .ok value => (.ok (.ok value),(updated,{dirty with heap := state.heap}))
       | .error (.revert data) =>
         (.ok (.error data),(updated,{dirty with
           heap := state.heap,
           ex := dirty.ex.undoN (dirty.ex.journal.length - state.ex.journal.length),
           logs := dirty.logs.drop (dirty.logs.length - state.logs.length)}))
       | .error other => (.error other,(updated,{dirty with heap := state.heap}))) := by
  simp only [libraryFrame, mark, EM.st, EM.modSt, EM.attempt, rollbackTo,
    bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.run,
    ExceptT.mk, StateT.bind, StateT.pure, StateT.get, StateT.modifyGet,
    modify, modifyGet, get, getThe, MonadStateOf.get, MonadStateOf.modifyGet,
    liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map]
  rcases execution : action.run (locals,{state with heap := Heap.empty}) with ⟨result, updated, dirty⟩
  change action (locals,{state with heap := Heap.empty}) = (result,(updated,dirty)) at execution
  rw [execution]
  cases result with
  | ok value => rfl
  | error halt => cases halt <;> rfl

/-- A real action history supplies the live ancestry needed for a revert.
The conclusion includes successful, reverting, stuck and timed-out actions. -/
theorem libraryFrame_effect (mode : Bool) (action : EM E [] α)
    (history : Effect mode action) : Effect mode (libraryFrame action) := by
  intro locals state
  have body := history locals {state with heap := Heap.empty}
  rcases execution : action.run (locals,{state with heap := Heap.empty}) with ⟨result, updated, dirty⟩
  rw [execution] at body
  rw [frame_run, execution]
  cases result with
  | ok value => exact body
  | error halt =>
    cases halt with
    | revert data =>
      change StaticJournal.History state.ex mode
        (dirty.ex.undoN (dirty.ex.journal.length - state.ex.journal.length))
      rw [HistoryRollback.rewind body]
      exact .start _ _
    | stuck why => exact body
    | timeout => exact body

macro "library_frame_factor" : tactic =>
 `(tactic| (
  simp only [libraryFrame, bind_assoc]
  congr 1
  funext saved
  congr 1
  funext cleared
  congr 1
  funext result
  congr 1
  funext restored
  cases result with
  | ok value => simp only [pure_bind]
  | error halt =>
    cases halt <;> simp only [bind_assoc, pure_bind, EM.halt] <;> rfl))

/-- Factoring preserves the actual continuation, including any conversion halt. -/
theorem libraryFrame_then {β : Type} (action : EM E [] α)
    (finish : α → EM E [] (Except Bytes β)) :
    (do
      let saved ← mark
      EM.modSt fun state => { state with heap := Heap.empty }
      let result ← EM.attempt action
      EM.modSt fun state => { state with heap := saved.2.2 }
      match result with
      | .ok value => finish value
      | .error (.revert data) => do
        rollbackTo saved
        pure (.error data)
      | .error other => EM.halt other) =
    (do
      let result ← libraryFrame action
      match result with
      | .ok value => finish value
      | .error data => pure (.error data)) := by
  library_frame_factor

end Solidity.Lowering.Readonly.SourceHistory

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.libraryFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.libraryFrame

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.libraryFrame_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.libraryFrame_effect

/-- info: 'Solidity.Lowering.Readonly.SourceHistory.libraryFrame_then' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Solidity.Lowering.Readonly.SourceHistory.libraryFrame_then
