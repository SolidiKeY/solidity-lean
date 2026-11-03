import Solidity.Yul.OpenComposition
import Solidity.Yul.LocalBlock

/-! Concrete independent Yul execution over the existing typed LOCAL Source
extension. Complete word writeback/world preservation are inherited by proved
equality. No old Source.RStmt or frontend dispatcher is installed here. -/
namespace Solidity.Yul.OpenRun
def localBlock (ctx : Solidity.Source.Ctx) {control}
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (fuel : Nat) (state : LocalState ctx.env ctx.tys) : Option (LocalBlockOutcome ctx control) :=
  (OpenRun.statement fuel .nil code policy ⟨Fin.elim0,localWordCells ctx state.1⟩).map
    (LocalBlockOutcome.ofWord state)

theorem localBlock_eq (ctx : Solidity.Source.Ctx) {control}
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (fuel : Nat) (state : LocalState ctx.env ctx.tys) :
    localBlock ctx code policy fuel state = runLocalBlock ctx code policy fuel state := by
  unfold localBlock runLocalBlock
  rw [OpenRun.run_agrees]

theorem localBlock_projection (ctx : Solidity.Source.Ctx) {control}
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (fuel : Nat) (state : LocalState ctx.env ctx.tys) :
    (localBlock ctx code policy fuel state).map LocalBlockOutcome.project =
      OpenRun.statement fuel .nil code policy ⟨Fin.elim0,localWordCells ctx state.1⟩ := by
  rw [localBlock_eq,runLocalBlock_projection,OpenRun.run_agrees]

theorem localBlock_world (ctx : Solidity.Source.Ctx) {control}
    (code : Stmt [] (localExternalTypes ctx) control 0) (policy : Policy.StmtP .A code)
    (fuel : Nat) (state : LocalState ctx.env ctx.tys) {result}
    (done : localBlock ctx code policy fuel state = some result) : result.state.2 = state.2 := by
  rw [localBlock_eq] at done
  exact runLocalBlock_world ctx code policy fuel state done
end Solidity.Yul.OpenRun
