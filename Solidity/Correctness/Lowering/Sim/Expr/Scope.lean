import Solidity.Syntax.Elab.Arms

/-!
# The arithmetic scopes (ls2-expressions)

What `elabStmt1With` returns, at an arbitrary callback record, on
`unchecked { … }` and `checked { … }`: `rc.elabBranch` on the block, under the
changed scope. `elabBranch` is not one of the five callbacks the case
interface constrains, and `uncheckStmts` is `partial` with no equation in
`elabKernelTotal`, so nothing more is said of the output here.
-/
namespace Solidity.Correctness.Lowering.Sim

variable [FreshNames] (C : Contract) (rc : ElabRec C)

theorem stmt1_unchecked (ss : List RawStmt) :
    elabStmt1With C rc (.unchecked ss) = (do
      withReader (fun sc => { sc with unchecked := true })
        (rc.elabBranch (← ElabM.lift (uncheckStmts ss)))) := rfl

theorem stmt1_checked (o : OFMode) (ss : List RawStmt) :
    elabStmt1With C rc (.checked o ss) = (do
      match (← read).overflow with
      | some o' =>
        if o' == o then rc.elabBranch ss
        else throw "`checked { … }` and `ignoringOverflow { … }` do not nest in each other"
      | none =>
        let P ← withReader (fun sc => { sc with overflow := some o }) (rc.elabBranch ss)
        let sc ← read
        let sf := sc.selfFrame || sc.retainFailureData
        pure (P.flatMap (SStmt.withOF o sf))) := rfl

end Solidity.Correctness.Lowering.Sim
