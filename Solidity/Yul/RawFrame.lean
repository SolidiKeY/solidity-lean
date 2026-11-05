import Solidity.Yul.LocalBlock

/-! H11 raw LOCAL frame beside unchanged Source.Val/Locals.
Optional cells are overlays, not an exact write-set. A completed assembly
block captures its full logical word snapshot. No physical/world layout or
existing Source evaluator is changed. Ordinary Solidity reads require an
explicit operation-specific boundary, never implicit cleaning on write. -/
namespace Solidity.Yul.RawFrame

structure State (ctx : Solidity.Source.Ctx) where
  clean : Solidity.Source.Locals ctx.env.layout ctx.tys
  raw : WordCell (localExternalTypes ctx) → Option Word
  world : Solidity.Source.St ctx.env

def ofClean {ctx} (locals : Solidity.Source.Locals ctx.env.layout ctx.tys)
    (world : Solidity.Source.St ctx.env) : State ctx := ⟨locals, fun _ => none, world⟩

def view {ctx} (state : State ctx) : WordCells (localExternalTypes ctx) :=
  fun cell => (state.raw cell).getD (localWordCells ctx (LocalValues.ofClean state.clean) cell)

def write {ctx} (state : State ctx) (cell : WordCell (localExternalTypes ctx))
    (value : Word) : State ctx :=
  ⟨state.clean, fun other => if other.key = cell.key then some value else state.raw other,
    state.world⟩

theorem write_clean {ctx} (state : State ctx) (cell) (value) :
    (write state cell value).clean = state.clean := rfl

theorem write_world {ctx} (state : State ctx) (cell) (value) :
    (write state cell value).world = state.world := rfl

theorem view_write {ctx} (state : State ctx) (cell) (value) :
    view (write state cell value) = (view state).write cell value := by
  funext other
  by_cases same : other.key = cell.key
  · simp only [view, write, WordCells.write, if_pos same, Option.getD_some]
  · simp only [view, write, WordCells.write, if_neg same]

theorem read_write {ctx} (state : State ctx) (cell) (value) :
    view (write state cell value) cell = value := by
  rw [view_write, WordCells.write_same]

/-- Actual typed local writeback, used only as a proved bridge. The Source
clean values remain stored separately in the raw frame. -/
def materialize {ctx} (state : State ctx) : LocalState ctx.env ctx.tys :=
  (writebackLocalWords ctx (LocalValues.ofClean state.clean) (view state), state.world)

theorem materialize_view {ctx} (state : State ctx) :
    localWordCells ctx (materialize state).1 = view state :=
  writebackLocalWords_view ctx (LocalValues.ofClean state.clean) (view state)

def capture {ctx} (state : State ctx) (cells : WordCells (localExternalTypes ctx)) : State ctx :=
  ⟨state.clean, fun cell => some (cells cell), state.world⟩

theorem view_capture {ctx} (state : State ctx) (cells) :
    view (capture state cells) = cells := rfl

structure Outcome (ctx : Solidity.Source.Ctx) (control : Control) where
  state : State ctx
  flow : Closed.Flow control

def Outcome.project {ctx control} (result : Outcome ctx control) :
    WordAdapter.Outcome (localExternalTypes ctx) control 0 :=
  ⟨⟨Fin.elim0, view result.state⟩, result.flow⟩

def Outcome.ofWord {ctx control} (state : State ctx)
    (result : WordAdapter.Outcome (localExternalTypes ctx) control 0) : Outcome ctx control :=
  ⟨capture state result.state.cells, result.flow⟩

theorem Outcome.project_ofWord {ctx control} (state : State ctx)
    (result : WordAdapter.Outcome (localExternalTypes ctx) control 0) :
    (ofWord state result).project = result := by
  cases result with
  | mk state flow =>
    cases state with
    | mk locals cells =>
      have empty : locals = Fin.elim0 := by funext index; exact Fin.elim0 index
      cases empty
      rfl

def run {ctx control} (code : Stmt [] (localExternalTypes ctx) control 0)
    (policy : Policy.StmtP .A code) (fuel : Nat) (state : State ctx) :
    Option (Outcome ctx control) :=
  (WordAdapter.run code policy fuel ⟨Fin.elim0, view state⟩).map (Outcome.ofWord state)

theorem projection {ctx control} (code : Stmt [] (localExternalTypes ctx) control 0)
    (policy : Policy.StmtP .A code) (fuel : Nat) (state : State ctx) :
    (run code policy fuel state).map Outcome.project =
      WordAdapter.run code policy fuel ⟨Fin.elim0, view state⟩ := by
  unfold run
  cases actual : WordAdapter.run code policy fuel ⟨Fin.elim0, view state⟩ with
  | none => rfl
  | some result => exact congrArg some (Outcome.project_ofWord state result)

theorem local_projection {ctx control} (code : Stmt [] (localExternalTypes ctx) control 0)
    (policy : Policy.StmtP .A code) (fuel : Nat) (state : State ctx) :
    (run code policy fuel state).map Outcome.project =
      (runLocalBlock ctx code policy fuel (materialize state)).map LocalBlockOutcome.project := by
  rw [projection, runLocalBlock_projection, materialize_view]

theorem preserves {ctx control} (code : Stmt [] (localExternalTypes ctx) control 0)
    (policy : Policy.StmtP .A code) (fuel : Nat) (state : State ctx) {result}
    (done : run code policy fuel state = some result) :
    result.state.clean = state.clean ∧ result.state.world = state.world := by
  unfold run at done
  cases actual : WordAdapter.run code policy fuel ⟨Fin.elim0, view state⟩ with
  | none => rw [actual] at done; cases done
  | some wordResult =>
    rw [actual] at done
    cases done
    exact ⟨rfl, rfl⟩

end Solidity.Yul.RawFrame
