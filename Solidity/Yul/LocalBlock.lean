import Solidity.Yul.LocalWriteback
import Solidity.Yul.LocalState
import Solidity.Yul.WordAdapterLogic

/-! Concrete pure Yul block execution over the actual LOCAL Source extension.
The old Source.St is retained entirely; all pure words are read/written through
the actual typed local view. This does not install a Source.RStmt/JSON dispatcher
or model dirty ordinary Source expressions, function frames or sessions. -/
namespace Solidity.Yul

structure LocalBlockOutcome (ctx : Solidity.Source.Ctx) (control : Control) where
  state : LocalState ctx.env ctx.tys
  flow : Closed.Flow control

namespace LocalBlockOutcome

def ofWord {ctx control} (initial : LocalState ctx.env ctx.tys)
    (result : WordAdapter.Outcome (localExternalTypes ctx) control 0) :
    LocalBlockOutcome ctx control :=
  ⟨(writebackLocalWords ctx initial.1 result.state.cells,initial.2),result.flow⟩

def project {ctx control} (result : LocalBlockOutcome ctx control) :
    WordAdapter.Outcome (localExternalTypes ctx) control 0 :=
  ⟨⟨Fin.elim0,localWordCells ctx result.state.1⟩,result.flow⟩

theorem project_ofWord {ctx control} (initial : LocalState ctx.env ctx.tys)
    (result : WordAdapter.Outcome (localExternalTypes ctx) control 0) :
    (ofWord initial result).project = result := by
  cases result with
  | mk state flow =>
      cases state with
      | mk locals cells =>
          have empty : locals = Fin.elim0 := by funext index; exact Fin.elim0 index
          cases empty
          change WordAdapter.Outcome.mk
            ⟨Fin.elim0,localWordCells ctx (writebackLocalWords ctx initial.1 cells)⟩ flow = _
          rw [writebackLocalWords_view]

end LocalBlockOutcome

def runLocalBlock (ctx : Solidity.Source.Ctx) {control}
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (fuel : Nat) (state : LocalState ctx.env ctx.tys) : Option (LocalBlockOutcome ctx control) :=
  (WordAdapter.run code policy fuel ⟨Fin.elim0,localWordCells ctx state.1⟩).map
    (LocalBlockOutcome.ofWord state)

/-- Actual complete result correspondence at EVERY horizon, preserving control
and the entire pure word state. This is not a Source.RStmt/session theorem. -/
theorem runLocalBlock_projection (ctx : Solidity.Source.Ctx) {control}
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (fuel : Nat) (state : LocalState ctx.env ctx.tys) :
    (runLocalBlock ctx code policy fuel state).map LocalBlockOutcome.project =
      WordAdapter.run code policy fuel ⟨Fin.elim0,localWordCells ctx state.1⟩ := by
  unfold runLocalBlock
  cases actual : WordAdapter.run code policy fuel ⟨Fin.elim0,localWordCells ctx state.1⟩ with
  | none => rfl
  | some result =>
      change some ((LocalBlockOutcome.ofWord state result).project) = some result
      rw [LocalBlockOutcome.project_ofWord]

theorem runLocalBlock_world (ctx : Solidity.Source.Ctx) {control}
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (fuel : Nat) (state : LocalState ctx.env ctx.tys) {result}
    (done : runLocalBlock ctx code policy fuel state = some result) :
    result.state.2 = state.2 := by
  unfold runLocalBlock at done
  cases actual : WordAdapter.run code policy fuel ⟨Fin.elim0,localWordCells ctx state.1⟩ with
  | none => rw [actual] at done; cases done
  | some raw =>
      rw [actual] at done
      cases done
      rfl

theorem runLocalBlock_nonword (ctx : Solidity.Source.Ctx) {control}
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (fuel : Nat) (state : LocalState ctx.env ctx.tys) {result}
    (done : runLocalBlock ctx code policy fuel state = some result)
    (ref : SourceLocalRef ctx) {kind} (shape : DeclaredSourceTypeD ctx.env ref.ty kind)
    (zero : wordCellWidth kind = 0) :
    result.state.1.get ref.index = state.1.get ref.index := by
  unfold runLocalBlock at done
  cases actual : WordAdapter.run code policy fuel ⟨Fin.elim0,localWordCells ctx state.1⟩ with
  | none => rw [actual] at done; cases done
  | some raw =>
      rw [actual] at done
      cases done
      exact writebackLocalWords_zero ctx state.1 raw.state.cells ref shape zero

theorem runLocalBlock_stable (ctx : Solidity.Source.Ctx) {control}
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (state : LocalState ctx.env ctx.tys) {lo hi} (increasing : lo ≤ hi) {result}
    (done : runLocalBlock ctx code policy lo state = some result) :
    runLocalBlock ctx code policy hi state = some result := by
  unfold runLocalBlock at done ⊢
  cases actual : WordAdapter.run code policy lo ⟨Fin.elim0,localWordCells ctx state.1⟩ with
  | none => rw [actual] at done; cases done
  | some raw =>
      rw [WordAdapter.run_stable code policy _ increasing actual]
      rw [actual] at done
      exact done

theorem runLocalBlock_zero (ctx : Solidity.Source.Ctx) {control}
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (state : LocalState ctx.env ctx.tys) : runLocalBlock ctx code policy 0 state = none := rfl

end Solidity.Yul
