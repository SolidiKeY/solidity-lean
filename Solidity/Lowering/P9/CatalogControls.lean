import Solidity.Lowering.P9.FunctionCatalog
import Solidity.Lowering.P9.GraphControls
import Solidity.Lowering.P9.RecursiveControls

/-! Nonempty complete function catalogues, computed from actual source units. -/
namespace Solidity.Lowering.P9.CatalogControls
open Source

theorem graph_catalog : WholeProgram.functions GraphControls.resolution =
    [GraphControls.leafDecl, GraphControls.entryDecl] := rfl

theorem graph_checked (fixed : Roadmap.Fixed) : WholeProgram.checkFunctions
    GraphControls.resolution (GraphControls.glob fixed) "P9" = true := by
  unfold WholeProgram.checkFunctions
  rw [graph_catalog]
  exact GraphControls.checker_accepts fixed

theorem graph_calls (fixed : Roadmap.Fixed) : CallsOK
    (fun d => d ∈ WholeProgram.functions GraphControls.resolution)
    (GraphControls.glob fixed) "P9" :=
  WholeProgram.functions_from_elaborate _ GraphControls.actual_elaboration _ rfl _ (graph_checked fixed)

theorem recursive_catalog : WholeProgram.functions RecursiveControls.resolution =
    [RecursiveControls.declaration] := rfl

theorem recursive_checked (fixed : Roadmap.Fixed) : WholeProgram.checkFunctions
    RecursiveControls.resolution (RecursiveControls.glob fixed) "P9" = true := by
  unfold WholeProgram.checkFunctions
  rw [recursive_catalog]
  exact RecursiveControls.checker_accepts fixed

#print axioms graph_calls
#print axioms recursive_checked
end Solidity.Lowering.P9.CatalogControls
