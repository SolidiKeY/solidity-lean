import Solidity.Yul.Views.ScalarWorld

/-! A typed companion to the actual source journal, for complete unowned slots.
Ownership is a fixed input domain, NOT a proved enumeration of all source paths.
Keys require nonownership intrinsically. Source updates remain actual Source.Op;
this module adds no Yul AST, owner-state rewrite or whole-view adequacy premise.
Owned-slot padding/dirty bits and dynamic ownership changes remain integration
obligations. Transaction reset clears transient residual cells and both journals.
All recursive families here are parameter-only (Gate G0). -/
namespace Solidity.Yul.Views

abbrev ResidualOwnership := Bool → Roadmap.Address → Roadmap.Word → Prop

structure ResidualKey (Own : ResidualOwnership) where
  transient : Bool
  address : Roadmap.Address
  slot : Roadmap.Word
  unowned : ¬Own transient address slot
  deriving DecidableEq

structure ResidualJournal (Own : ResidualOwnership) where
  cells : ResidualKey Own → Roadmap.Word
  journal : List (ResidualKey Own × Roadmap.Word)

def residualSave {Own : ResidualOwnership} (m : ResidualKey Own → Roadmap.Word)
    (k : ResidualKey Own) (v : Roadmap.Word) : ResidualKey Own → Roadmap.Word :=
  fun q => if q = k then v else m q

theorem residualSave_get {Own : ResidualOwnership} (m : ResidualKey Own → Roadmap.Word)
    (k : ResidualKey Own) (v : Roadmap.Word) : residualSave m k v k = v := by
  simp only [residualSave, ↓reduceIte]

theorem residualSave_other {Own : ResidualOwnership} (m : ResidualKey Own → Roadmap.Word)
    (k q : ResidualKey Own) (v : Roadmap.Word) (h : q ≠ k) : residualSave m k v q = m q := by
  simp only [residualSave, if_neg h]

theorem residualSave_restore {Own : ResidualOwnership} (m : ResidualKey Own → Roadmap.Word)
    (k : ResidualKey Own) (v : Roadmap.Word) : residualSave (residualSave m k v) k (m k) = m := by
  funext q
  by_cases h : q = k
  · subst q; exact residualSave_get _ _ _
  · simp only [residualSave_other _ _ _ _ h]

def residualWrite {Own : ResidualOwnership} (s : ResidualJournal Own)
    (w : ResidualKey Own × Roadmap.Word) : ResidualJournal Own :=
  ⟨residualSave s.cells w.1 w.2, (w.1, s.cells w.1) :: s.journal⟩

def residualRun {Own : ResidualOwnership} (s : ResidualJournal Own) :
    List (ResidualKey Own × Roadmap.Word) → ResidualJournal Own
  | [] => s
  | w :: ws => residualRun (residualWrite s w) ws

theorem residualRun_other {Own : ResidualOwnership} (s : ResidualJournal Own)
    (ws : List (ResidualKey Own × Roadmap.Word)) (q : ResidualKey Own)
    (h : ∀ w ∈ ws, q ≠ w.1) : (residualRun s ws).cells q = s.cells q := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    have tail : ∀ x ∈ ws, q ≠ x.1 := fun x hx => h x (List.mem_cons_of_mem w hx)
    rw [residualRun, ih _ tail]
    exact residualSave_other _ _ _ _ (h w (List.mem_cons_self))

def residualUndo {Own : ResidualOwnership} (s : ResidualJournal Own) : ResidualJournal Own :=
  match s.journal with
  | [] => s
  | (k, old) :: j => ⟨residualSave s.cells k old, j⟩

def residualUndoN {Own : ResidualOwnership} : Nat → ResidualJournal Own → ResidualJournal Own
  | 0, s => s
  | n + 1, s => residualUndoN n (residualUndo s)

theorem residualUndo_write {Own : ResidualOwnership} (s : ResidualJournal Own)
    (w : ResidualKey Own × Roadmap.Word) : residualUndo (residualWrite s w) = s := by
  cases s
  simp only [residualWrite, residualUndo, residualSave_restore]

theorem residual_journal_run {Own : ResidualOwnership} (s : ResidualJournal Own)
    (ws : List (ResidualKey Own × Roadmap.Word)) :
    (residualRun s ws).journal.length = s.journal.length + ws.length := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    simp only [residualRun, ih, residualWrite, List.length_cons]
    omega

theorem residualUndoN_succ {Own : ResidualOwnership} (n : Nat) (s : ResidualJournal Own) :
    residualUndoN (n + 1) s = residualUndo (residualUndoN n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih (residualUndo s)

theorem residualUndoN_run {Own : ResidualOwnership} (s : ResidualJournal Own)
    (ws : List (ResidualKey Own × Roadmap.Word)) : residualUndoN ws.length (residualRun s ws) = s := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    simp only [residualRun, List.length_cons, residualUndoN_succ, ih, residualUndo_write]

def residualRollback {Own : ResidualOwnership} (mark : Nat) (s : ResidualJournal Own) : ResidualJournal Own :=
  residualUndoN (s.journal.length - mark) s

theorem residualRollback_run {Own : ResidualOwnership} (s : ResidualJournal Own)
    (ws : List (ResidualKey Own × Roadmap.Word)) :
    residualRollback s.journal.length (residualRun s ws) = s := by
  simp only [residualRollback, residual_journal_run, Nat.add_sub_cancel_left, residualUndoN_run]

theorem residualRun_append {Own : ResidualOwnership} (s : ResidualJournal Own)
    (xs ys : List (ResidualKey Own × Roadmap.Word)) :
    residualRun s (xs ++ ys) = residualRun (residualRun s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons w ws ih => simp only [List.cons_append, residualRun, ih]

def residualEndTx {Own : ResidualOwnership} (s : ResidualJournal Own) : ResidualJournal Own :=
  ⟨fun k => if k.transient then ⟨0, by decide⟩ else s.cells k, []⟩

theorem residualEndTx_persistent {Own : ResidualOwnership} (s : ResidualJournal Own)
    (k : ResidualKey Own) (h : k.transient = false) : (residualEndTx s).cells k = s.cells k := by
  simp only [residualEndTx, h, Bool.false_eq_true, ↓reduceIte]

theorem residualEndTx_transient {Own : ResidualOwnership} (s : ResidualJournal Own)
    (k : ResidualKey Own) (h : k.transient = true) : (residualEndTx s).cells k = ⟨0, by decide⟩ := by
  simp only [residualEndTx, h, ↓reduceIte]

/-- Actual typed source state plus the new ownership-indexed residual journal. -/
structure ResidualCompanion (D : Source.Layout)
    (L T : Roadmap.Address → Source.SPath → Source.STy) (Own : ResidualOwnership) where
  source : Source.ExecState D L T
  residual : ResidualJournal Own

structure ResidualFrame where
  source : Source.CallFrame
  mark : Nat

def companionRunSource {D L T Own} (s : ResidualCompanion D L T Own)
    (os : List (Source.Op D L T)) : ResidualCompanion D L T Own :=
  ⟨s.source.run os, s.residual⟩

def companionRunResidual {D L T Own} (s : ResidualCompanion D L T Own)
    (ws : List (ResidualKey Own × Roadmap.Word)) : ResidualCompanion D L T Own :=
  ⟨s.source, residualRun s.residual ws⟩

theorem companion_independent_runs {D L T Own} (s : ResidualCompanion D L T Own)
    (os : List (Source.Op D L T)) (ws : List (ResidualKey Own × Roadmap.Word)) :
    companionRunResidual (companionRunSource s os) ws =
      companionRunSource (companionRunResidual s ws) os := rfl

def companionEnter {D L T Own} (s : ResidualCompanion D L T Own)
    (a c : Roadmap.Address) (v : Roadmap.Word) (i : Roadmap.Bytes) (st : Bool) : ResidualFrame :=
  ⟨s.source.enter a c v i st, s.residual.journal.length⟩

def companionRollback {D L T Own} (f : ResidualFrame) (s : ResidualCompanion D L T Own) :
    ResidualCompanion D L T Own := ⟨f.source.rollback s.source, residualRollback f.mark s.residual⟩

def companionCommit {D L T Own} (f : ResidualFrame) (s : ResidualCompanion D L T Own) :
    ResidualCompanion D L T Own := ⟨f.source.commit s.source, s.residual⟩

theorem companionRollback_run {D L T Own} (s : ResidualCompanion D L T Own)
    (os : List (Source.Op D L T)) (ws : List (ResidualKey Own × Roadmap.Word))
    (a c : Roadmap.Address) (v : Roadmap.Word) (i : Roadmap.Bytes) (st : Bool) :
    companionRollback (companionEnter s a c v i st)
      (companionRunResidual (companionRunSource s os) ws) = s := by
  cases s
  simp only [companionRollback, companionEnter, companionRunResidual, companionRunSource,
    Source.rollback_run, residualRollback_run]

theorem companionRollback_inner {D L T Own} (s : ResidualCompanion D L T Own)
    (os xs : List (Source.Op D L T)) (ws ys : List (ResidualKey Own × Roadmap.Word))
    (a c : Roadmap.Address) (v : Roadmap.Word) (i : Roadmap.Bytes) (st : Bool) :
    let callerState := companionRunResidual (companionRunSource s os) ws
    companionRollback (companionEnter callerState a c v i st)
      (companionRunResidual (companionRunSource callerState xs) ys) = callerState ∧
    companionRollback (companionEnter s a c v i st)
      (companionRollback (companionEnter callerState a c v i st)
        (companionRunResidual (companionRunSource callerState xs) ys)) = s := by
  dsimp only
  rw [companionRollback_run]
  exact ⟨rfl, companionRollback_run s os ws a c v i st⟩

theorem companionRollback_outer_commit {D L T Own} (s : ResidualCompanion D L T Own)
    (os xs : List (Source.Op D L T)) (ws ys : List (ResidualKey Own × Roadmap.Word))
    (a c : Roadmap.Address) (v : Roadmap.Word) (i : Roadmap.Bytes) (st : Bool) :
    let callerState := companionRunResidual (companionRunSource s os) ws
    companionRollback (companionEnter s a c v i st)
      (companionCommit (companionEnter callerState a c v i st)
        (companionRunResidual (companionRunSource callerState xs) ys)) = s := by
  cases s
  simp only [companionRollback, companionCommit, companionEnter, companionRunSource,
    companionRunResidual, Source.CallFrame.commit, ← Source.run_append, ← residualRun_append,
    Source.rollback_run, residualRollback_run]

def companionEndTx {D L T Own} (s : ResidualCompanion D L T Own) : ResidualCompanion D L T Own :=
  ⟨s.source.endTx, residualEndTx s.residual⟩

theorem companionEndTx_source {D L T Own} (s : ResidualCompanion D L T Own) :
    (companionEndTx s).source = s.source.endTx := rfl

theorem companionEndTx_persistent {D L T Own} (s : ResidualCompanion D L T Own)
    (k : ResidualKey Own) (h : k.transient = false) :
    (companionEndTx s).source.world = s.source.world ∧
    (companionEndTx s).residual.cells k = s.residual.cells k :=
  ⟨rfl, residualEndTx_persistent s.residual k h⟩

theorem companionEndTx_transient {D L T Own} (s : ResidualCompanion D L T Own)
    (k : ResidualKey Own) (h : k.transient = true)
    (a : Roadmap.Address) (p : Source.SPath) :
    ((companionEndTx s).source.transient.cells a).read p = Source.Val.default D (T a p) ∧
    (companionEndTx s).residual.cells k = ⟨0, by decide⟩ ∧
    (companionEndTx s).source.journal = [] ∧ (companionEndTx s).residual.journal = [] :=
  ⟨rfl, residualEndTx_transient s.residual k h, rfl, rfl⟩

end Solidity.Yul.Views
