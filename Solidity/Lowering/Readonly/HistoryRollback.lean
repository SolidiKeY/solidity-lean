import Solidity.Lowering.Readonly.JournalLeaves

/-! Journal ancestry extracted from a guarded history. This is an algebraic
producer lemma for real source rollback, not an assumed storage frame. -/
namespace Solidity.Lowering.Readonly.HistoryRollback
open Solidity.Source StaticJournal
variable {D : Layout} {L T : Solidity.Roadmap.Address → SPath → STy}

/-- A history's final journal really extends its entry by actual operations.
Nested rollback discards only child operations, retaining its live ancestor. -/
theorem operations {entry final : ExecState D L T} {mode : Bool}
    (history : History entry mode final) : ∃ ops : List (Op D L T), final = entry.run ops := by
  induction history with
  | start => exact ⟨[], rfl⟩
  | balance prior a b ih =>
    obtain ⟨ops, execution⟩ := ih
    refine ⟨ops ++ [.account a (fun old => old.withBalance b)], ?_⟩
    rw [run_append, ← execution]
    rfl
  | write prior ordinary op ih =>
    obtain ⟨ops, execution⟩ := ih
    refine ⟨ops ++ [op], ?_⟩
    rw [run_append, ← execution]
    rfl
  | child prior requested nested first second =>
    obtain ⟨before, reached⟩ := first
    obtain ⟨after, executed⟩ := second
    exact ⟨before ++ after, by rw [run_append, ← reached]; exact executed⟩
  | rollback prior requested ops nested a sender value input first _ =>
    rw [rollback_run]
    exact first

/-- Undo exactly the descendant entries, preserving the live ancestor. -/
theorem rewind {entry final : ExecState D L T} {mode : Bool}
    (history : History entry mode final) :
    final.undoN (final.journal.length - entry.journal.length) = entry := by
  obtain ⟨ops, rfl⟩ := operations history
  simpa only [ExecState.journal_run, Nat.add_sub_cancel_left] using ExecState.undoN_run entry ops

/-- Projection of the actual rollbackTo operation at the live Source mark. -/
theorem checkpoint {E : Env} {Γ : RCtx} (entry dirty : St E) (mode : Bool)
    (locals : Locals E.layout Γ) (history : History entry.ex mode dirty.ex) :
    ((rollbackTo (entry.ex.journal.length, entry.logs.length, entry.heap) : EM E Γ Unit).run
      (locals, dirty)).2.2.ex = entry.ex := rewind history

end Solidity.Lowering.Readonly.HistoryRollback
