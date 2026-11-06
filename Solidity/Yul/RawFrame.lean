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


/-- A completed admitted execution retains its exact raw frame and control at every larger horizon. -/
theorem run_stable : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code) (state : Solidity.Yul.RawFrame.State ctx) (lo hi : Nat), lo ≤ hi →
 ∀ (result : Solidity.Yul.RawFrame.Outcome ctx control),
 Solidity.Yul.RawFrame.run code policy lo state = some result →
 Solidity.Yul.RawFrame.run code policy hi state = some result := by
  intro ctx control code policy state lo hi increasing result done
  unfold run at done ⊢
  cases actual : WordAdapter.run code policy lo ⟨Fin.elim0, view state⟩ with
  | none => rw [actual] at done; cases done
  | some raw =>
    rw [WordAdapter.run_stable code policy _ increasing actual]
    rw [actual] at done
    exact done

/-- Completed horizons determine the same whole outcome, without any coherence premise. -/
theorem run_completed_unique : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code) (state : Solidity.Yul.RawFrame.State ctx) (lo hi : Nat),
 ∀ (first second : Solidity.Yul.RawFrame.Outcome ctx control),
 Solidity.Yul.RawFrame.run code policy lo state = some first →
 Solidity.Yul.RawFrame.run code policy hi state = some second → first = second := by
  intro ctx control code policy state lo hi first second one two
  rcases Nat.le_total lo hi with lower | higher
  · exact Option.some.inj ((run_stable ctx control code policy state lo hi lower first one).symm.trans two)
  · exact Option.some.inj (one.symm.trans (run_stable ctx control code policy state hi lo higher second two))


/-- Exact reflection of actual word-interpreter some results through raw-frame capture. -/
theorem run_some_iff : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code) (fuel : Nat)
 (state : Solidity.Yul.RawFrame.State ctx), ∀ (result : Solidity.Yul.RawFrame.Outcome ctx control),
 Solidity.Yul.RawFrame.run code policy fuel state = some result ↔
 ∃ wordResult, Solidity.Yul.WordAdapter.run code policy fuel ⟨Fin.elim0, Solidity.Yul.RawFrame.view state⟩ = some wordResult ∧
 Solidity.Yul.RawFrame.Outcome.ofWord state wordResult = result := by
  intro ctx control code policy fuel state result
  simp only [run, Option.map_eq_some_iff]

/-- Exact reflection of actual word-interpreter none results through raw-frame capture. -/
theorem run_none_iff : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code) (fuel : Nat)
 (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.run code policy fuel state = none ↔
 Solidity.Yul.WordAdapter.run code policy fuel ⟨Fin.elim0, Solidity.Yul.RawFrame.view state⟩ = none := by
  intro ctx control code policy fuel state
  simp only [run, Option.map_eq_none_iff]

/-- Pre-capturing the current view preserves every exact later run, including
timeouts and full captured outcomes. Sparse overlay metadata need not agree. -/
theorem run_snapshot : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code) (fuel : Nat)
 (state : Solidity.Yul.RawFrame.State ctx),
 Solidity.Yul.RawFrame.run code policy fuel
 (Solidity.Yul.RawFrame.capture state (Solidity.Yul.RawFrame.view state)) =
 Solidity.Yul.RawFrame.run code policy fuel state := by
  intro ctx control code policy fuel state
  rfl

/-- Equal authoritative words, clean backups and worlds determine every exact raw run.
Overlay metadata may differ. All three equalities are explicit. -/
theorem run_agrees : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code) (fuel : Nat)
 (first second : Solidity.Yul.RawFrame.State ctx),
 first.clean = second.clean → first.world = second.world →
 Solidity.Yul.RawFrame.view first = Solidity.Yul.RawFrame.view second →
 Solidity.Yul.RawFrame.run code policy fuel first = Solidity.Yul.RawFrame.run code policy fuel second := by
  intro ctx control code policy fuel first second cleanEq worldEq viewEq
  cases first
  cases second
  cases cleanEq
  cases worldEq
  unfold run
  rw [viewEq]
  rfl

/-- Every actual completed raw outcome is fixed by full snapshot capture.
The completion premise is retained; arbitrary input overlays need not be fixed. -/
theorem run_captured : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code) (fuel : Nat)
 (state : Solidity.Yul.RawFrame.State ctx) (result : Solidity.Yul.RawFrame.Outcome ctx control),
 Solidity.Yul.RawFrame.run code policy fuel state = some result →
 Solidity.Yul.RawFrame.capture result.state (Solidity.Yul.RawFrame.view result.state) = result.state := by
  intro ctx control code policy fuel state result done
  obtain ⟨wordResult,_finished,captured⟩ :=
    (run_some_iff ctx control code policy fuel state result).mp done
  cases captured
  rfl

/-- An alleged result with an absent raw cell cannot be a completed outcome.
This refuses that result, not execution or completion in general. -/
theorem run_not_sparse : ∀ (ctx : Solidity.Source.Ctx) (control : Solidity.Yul.Control)
 (code : Solidity.Yul.Stmt [] (Solidity.Yul.localExternalTypes ctx) control 0)
 (policy : Solidity.Yul.Policy.StmtP .A code) (fuel : Nat)
 (state : Solidity.Yul.RawFrame.State ctx) (result : Solidity.Yul.RawFrame.Outcome ctx control)
 (cell : Solidity.Yul.WordCell (Solidity.Yul.localExternalTypes ctx)),
 result.state.raw cell = none →
 Solidity.Yul.RawFrame.run code policy fuel state ≠ some result := by
  intro ctx control code policy fuel state result cell missing done
  have same : (capture result.state (view result.state)).raw cell = result.state.raw cell :=
    congrArg (fun frame : State ctx => frame.raw cell)
      (run_captured ctx control code policy fuel state result done)
  change some (view result.state cell) = result.state.raw cell at same
  rw [missing] at same
  cases same

end Solidity.Yul.RawFrame
