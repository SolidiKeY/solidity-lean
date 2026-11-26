import Solidity.Correctness.Lowering.Total.Versions.CalleeBinding.Frame

/-! Checks of the request-level callee binding contract (P2, statement level):
the exact frame renaming of one call `f(a)` of `function f(uint x) returns (uint y)`,
its parameter and return slots, the ordinary and recursive endpoints, and that
the e2b producer instance of `Publishes` is well typed. Nothing is proved
against the proposed relation. -/
namespace Solidity.Examples.Lowering.Total.CalleeBinding

open Solidity.Correctness.Lowering.Total
open Solidity.Correctness.Lowering.Total.Version.CalleeBinding

/-- `function f(uint x) returns (uint y)`, body omitted. -/
def decl : FunDecl := { params := [("x", .prim .uint)], rets := [("y", .prim .uint)], body := [] }

/-- The call site's request: `ρ` returns first, each newest first. -/
def callee : CalleeRequest :=
  { declaration := decl, names := [("y", "se2"), ("x", "se1")], constructor := false,
    selfFrame := false, locals := [("se2", .val .uint), ("se1", .val .uint)], scope := [],
    start := 1 }

/-! Slots in declaration order are the frame's locals, oldest first. -/
#guard paramSlots callee == ["se1"]
#guard returnSlots callee == ["se2"]
#guard paramSlots callee ++ returnSlots callee == (callee.locals.map Prod.fst).reverse

example : Renaming callee := by unfold Renaming; decide

/-- Parameters listed before returns are not the elaborator's renaming. -/
example : ¬ Renaming { callee with names := [("x", "se1"), ("y", "se2")] } := by
  unfold Renaming; decide

/-! The e2b producer instance of the statement to prove is well typed. -/
example : Prop :=
  Publishes fun σ r => fromFunctions σ.tables σ.registry σ.settings σ.scope σ.leadingParts
    r.contract.funs σ.index

/-! A recursive callee scope is never the ordinary one, and starts an empty memo. -/
example {r : Request} {o : ProductionOutput} {rf : RecFrame} (h : r.callee = some callee) :
    recursiveScope r o rf ≠ r.elabScope o := recursiveScope_ne h

example {o : ProductionOutput} : (recursiveState callee o).memo = {} := recursiveState_memo

end Solidity.Examples.Lowering.Total.CalleeBinding
