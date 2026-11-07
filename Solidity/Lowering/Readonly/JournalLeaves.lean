import Solidity.Lowering.Readonly.StaticJournal

/-! Source primitive producers for P1 histories. These execute the existing
source operations, with their real mode/refusal branches, not endpoint frames. -/
namespace Solidity.Lowering.Readonly.JournalLeaves
open Solidity.Source StaticJournal
open Solidity.Roadmap (Address Word)
variable {E : Env} {Γ : RCtx}

theorem debit_history (a : Address) (v : Word) (locals : Locals E.layout Γ)
    (state : St E) (mode : Bool) :
    History state.ex mode ((debit a v : EM E Γ Bool).run (locals, state)).2.2.ex := by
  by_cases fits : v.val ≤ (state.ex.world.accounts a).balance
  · simp only [debit, EM.st, EM.modSt, bind, pure, ExceptT.bind,
      ExceptT.pure, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind,
      StateT.pure, StateT.get, StateT.modifyGet, modify, modifyGet, get,
      getThe, MonadStateOf.get, MonadStateOf.modifyGet, liftM, monadLift,
      MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map, fits, dif_pos]
    exact .balance (.start _ _) a _
  · simp only [debit, EM.st, EM.modSt, bind, pure, ExceptT.bind,
      ExceptT.pure, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind,
      StateT.pure, StateT.get, modify, modifyGet, get,
      getThe, MonadStateOf.get, MonadStateOf.modifyGet, liftM, monadLift,
      MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map, fits]
    exact .start _ _

/-- Guarded application produces an ordinary write or a refused static write,
using the actual source frame's static flag as the history index. -/
theorem operation_history (frame : Fr) (op : Op E.layout E.lay E.lay)
    (locals : Locals E.layout Γ) (state : St E) :
    History state.ex frame.static ((applyOp frame op : EM E Γ Unit).run (locals, state)).2.2.ex := by
  cases h : frame.static with
  | false =>
    simp only [applyOp, h, Bool.false_eq_true, ↓reduceIte]
    change History state.ex false (state.ex.apply op)
    exact .write (.start _ _) rfl op
  | true =>
    simp only [applyOp, h, ↓reduceIte]
    change History state.ex true state.ex
    exact .start _ _

/-- Both persistent and transient writes use the same real dynamic guard. -/
theorem cell_history (frame : Fr) (path : SPath)
    (value : Option (Val E.layout (E.cellTy path)))
    (locals : Locals E.layout Γ) (state : St E) :
    History state.ex frame.static ((setCell frame path value : EM E Γ Unit).run (locals, state)).2.2.ex := by
  unfold setCell
  split <;> exact operation_history frame _ locals state

/-- Sequential journal histories compose without assuming endpoint frames. -/
theorem chain {D : Solidity.Source.Layout} {L T : Address → Solidity.Source.SPath → STy}
    {middle final : ExecState D L T} {mode : Bool} (second : History middle mode final) :
    ∀ entry : ExecState D L T, History entry mode middle → History entry mode final := by
  induction second with
  | start => intro entry first; exact first
  | balance prior a b ih => intro entry first; exact .balance (ih entry first) a b
  | write prior ordinary op ih => intro entry first; exact .write (ih entry first) ordinary op
  | child prior requested nested ih _ => intro entry first; exact .child (ih entry first) requested nested
  | rollback prior requested ops nested a sender v input ih _ =>
    intro entry first
    exact .rollback (ih entry first) requested ops nested a sender v input

private theorem run_bind {α β : Type} (m : EM E Γ α) (k : α → EM E Γ β)
    (x : Locals E.layout Γ × St E) :
    (m >>= k).run x = match m.run x with
      | (.ok a, y) => (k a).run y
      | (.error h, y) => (.error h, y) := by
  rw [ExceptT.run_bind]
  show StateT.bind (ExceptT.run m) _ x = _
  simp only [StateT.bind]
  rcases m.run x with ⟨r, y⟩
  cases r <;> rfl

/-- Actual source bind transports histories at its LIVE intermediate state;
errors do not invoke the continuation. -/
theorem bind_history {α β : Type} (m : EM E Γ α) (k : α → EM E Γ β)
    (locals : Locals E.layout Γ) (state : St E) (mode : Bool)
    (first : History state.ex mode (m.run (locals, state)).2.2.ex)
    (next : ∀ value locals' state', m.run (locals, state) = (.ok value, (locals', state')) →
      History state'.ex mode ((k value).run (locals', state')).2.2.ex) :
    History state.ex mode ((m >>= k).run (locals, state)).2.2.ex := by
  rw [run_bind]
  rcases execution : m.run (locals, state) with ⟨result, locals', state'⟩
  rw [execution] at first
  cases result with
  | error halt => exact first
  | ok value => exact chain (next value locals' state' execution) _ first

/-- Actual source subframes keep caller locals while transporting the child's
world history; an error retains its actual dirty state, without fake rollback. -/
theorem sub_history {Γ' : RCtx} {α : Type} (inner : Locals E.layout Γ') (m : EM E Γ' α)
    (locals : Locals E.layout Γ) (state : St E) (mode : Bool)
    (history : History state.ex mode (m.run (inner, state)).2.2.ex) :
    History state.ex mode ((EM.sub inner m).run (locals, state)).2.2.ex := by
  rcases execution : m.run (inner, state) with ⟨result, locals', state'⟩
  rw [execution] at history
  change m (inner, state) = (result, (locals', state')) at execution
  cases result <;> simpa only [EM.sub, ExceptT.run, ExceptT.mk, execution] using history

end Solidity.Lowering.Readonly.JournalLeaves
