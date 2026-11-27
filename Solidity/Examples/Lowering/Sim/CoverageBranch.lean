import Solidity.Correctness.Lowering.Sim.CoverageBranch

/-! A nonempty branch executes two effectful callbacks and chains their
statements. Temporary locals disappear, but fresh indices and memo entries
survive. This tests composition, not Source acceptance or EVM execution. -/
namespace Solidity.Examples.Lowering.Sim.CoverageBranch

open Solidity
open Solidity.Correctness.Lowering.Sim.CoverageBranch

local instance : FreshNames := .ofPrefixes "se" "sp" "ie" "mv"

private def C0 : Contract := { vars := [] }
private def sc : ElabScope := { funs := [], top := true, unchecked := true }
private def Γtmp : ECtx := [("temporary", .val .uint)]
private def memo0 : CallMemo := { starts := [("entry", 3)] }
private def memo1 : CallMemo := { starts := [("child", 7), ("entry", 3)] }
private def memo2 : CallMemo := { starts := [("child", 8), ("child", 7), ("entry", 3)] }
private def p : SStmt C0 := .of [] .revert

/-- Refuses top-level execution; also observes a reader field preserved by
branch entry. Each child changes both state layers. -/
private def child (_ : RawStmt) : ElabM (SProg C0) := do
  let scope ← read
  if scope.top || !scope.unchecked then throw "wrong branch reader"
  let (_, k) ← get
  set (Γtmp, k + 1)
  modifyThe CallMemo fun m => { m with starts := ("child", k) :: m.starts }
  pure [p]

private theorem children :
    Children child { sc with top := false } [.revert, .revert]
      ([], 7) memo0 [p, p] (Γtmp, 9) memo2 := by
  refine .cons (P := [p]) (Q := [p]) (mid := (Γtmp, 8)) (memo₁ := memo1) ?_ ?_
  · rfl
  · exact .cons (P := [p]) (Q := []) (by rfl) (.nil _ _)

/-- Both children execute; entry locals return, counter and memo do not roll back. -/
example : Runs (elabBranchWith C0 child [.revert, .revert]) sc
    ([], 7) memo0 [p, p] ([], 9) memo2 :=
  branch_run children

private theorem chain : SProg.chain [] [] [p, p] =
    .ok ⟨[], .cons .revert (.cons .revert .nil)⟩ := by
  apply chain_cons (s := .revert)
  · rfl
  · apply chain_cons (s := .revert)
    · rfl
    · exact chain_nil [] []

/-- The same execution produces a typed block through the unchanged scope helper. -/
example : Runs (elabScopeWith C0 (elabBranchWith C0 child) [] [.revert, .revert])
    sc ([], 7) memo0 ⟨[], .cons .revert (.cons .revert .nil)⟩ ([], 9) memo2 :=
  scope_run (branch_run children) chain

/-- The callback really rejects the original top-level reader. -/
example : ((child .revert).run sc |>.run ([], 7)).run memo0 =
    .error "wrong branch reader" := rfl

end Solidity.Examples.Lowering.Sim.CoverageBranch
