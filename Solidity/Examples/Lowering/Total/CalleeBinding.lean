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

/-! First-match alias resolution: with alias `f` twice, only position 0 is the
first match; the shadowed duplicate at position 1 is not. -/
def dupFuns : List (Name × FunDecl) := [("f", decl), ("f", { decl with params := [] })]

#guard CalleeAliases.firstIndex "f" dupFuns == some 0

example : ∃ i, CalleeAliases.firstIndex "f" dupFuns = some i ∧ dupFuns[i]? = some ("f", decl) :=
  index_of_lookup rfl

example {σ : Site} {r : Request} {s : Output} (b : AliasBound σ r callee s "f") :
    Semantics.lookupBy "f" r.contract.funs = some decl := b.lookup

example : Prop :=
  PublishesAlias fun σ r => fromFunctions σ.tables σ.registry σ.settings σ.scope
    σ.leadingParts r.contract.funs σ.index

example {produce : Site → Request → Option Output} (h : Publishes produce) :
    PublishesAlias produce := publishesAlias h

/-! A recursive callee scope is never the ordinary one, and starts an empty memo. -/
example {r : Request} {o : ProductionOutput} {rf : RecFrame} (h : r.callee = some callee) :
    recursiveScope r o rf ≠ r.elabScope o := recursiveScope_ne h

example {o : ProductionOutput} : (recursiveState callee o).memo = {} := recursiveState_memo

/-! Ordinary threading: the callee's context, the producer's memo, and the
spelled input under a binding. -/
example {r : Request} (h : r.callee = some callee) :
    r.context = @ECtx.toNCtx r.input.names callee.locals := context_callee h

example {r : Request} {o : ProductionOutput} : (r.elabState o).memo = o.after.memo :=
  elabState_memo

example {σ : Site} {r : Request} {o : ProductionOutput} {s : Output}
    (b : Bound σ r callee s) (hs : r.success o) :
    Decode.Tables.WithExpr.items σ.tables (Decode.Calls.expr σ.tables σ.registry) .body
      r.input.raw = some s.frame.body ∧ Declared (fun _ => some s.declaration) r callee s :=
  ⟨b.spelledInput hs, b.declared hs⟩

/-! The recursive endpoint is its own scope and state over the same locals. -/
example {r : Request} {o : ProductionOutput} {rf : RecFrame} (h : r.callee = some callee) :
    recursiveScope r o rf = { r.elabScope o with recs := rf :: (r.elabScope o).recs } ∧
      (recursiveState callee o).locals = (r.elabState o).locals :=
  ⟨recursiveScope_eq h, recursiveState_locals h⟩

example {r : Request} {o : ProductionOutput} {rf : RecFrame} {after : Solidity.Correctness.Lowering.Checker.Snapshot}
    {parts : SProg r.contract} {names : List Var} {F : Ctx} {p : Blk r.contract F}
    (h : Recursive r callee o rf after parts names F p) : r.success o :=
  (recursive_iff.mp h).2.1

/-! The proved slot statement at the sample. -/
example : paramSlots callee ++ returnSlots callee = (callee.locals.map Prod.fst).reverse :=
  slots callee (by unfold Renaming; decide) (by decide)

end Solidity.Examples.Lowering.Total.CalleeBinding
