import Solidity.Correctness.Lowering.Sim.Match

/-!
# The lowering diagram on one standalone loop (plan step `ls1-sim-diagrams`)

A coverage smoke for `Sim.diagram`: for the standalone loop `while (i = a) break;`
in a contract without state, every emitted program placed in the caller's
context has a body with the same production input that the diagram associates
with it (`coverage`: `Diagram.Total` at this input), and every Source state of
that body has a related model state (`matching`). The run itself is a
hypothesis: the elaborator is `partial`, so a closed production run has no
kernel proof; `Assoc` does not need one. The placement hypothesis is what
`Production` does not give (`u.output.names` is free there).

The remaining examples use each declaration of `Sim/Match.lean` and
`Sim/Match/Relations.lean` that nothing else uses.
-/
namespace Solidity.Examples.Lowering.Sim.Match

open Solidity.Goals.Shrink.Lowering
open Solidity.Correctness.Lowering
open Solidity.Correctness.Lowering.Sim

/-- A contract without state variables or functions. -/
def C : Contract := { vars := [] }

/-- The caller's locals, on both sides. -/
def locals : ECtx := [("i", .val .bool), ("a", .val .bool)]
def names : List (String × Source.STy) := [("i", .bool), ("a", .bool)]

/-- The raw standalone loop `while (i = a) break;`. -/
def raw : List RawStmt := [.whileLoop {} (.assign (.name "i") (.name "a")) [.brk]]

/-- The canonical Source unit of `C`, as the landed decoder gives it. -/
def unit : Source.Syn .unit :=
  .unit (.cons (.contract false Total.Decode.contractName .none .nil .nil) .nil)

theorem unit_decoded : Total.Decode.unit C = some unit := rfl

/-- The Source typing context of the request (`Total.Decode.context`). -/
def context : Source.Ctx :=
  { env := unit.env, scope := some Total.Decode.contractName, locals := [], rets := [] }

def condition : Source.Typed (context.at names) (.assign .assign (.ident "i") (.ident "a")) .bool :=
  .assign (.loc (i := 0) rfl rfl) (.loc (i := 1) rfl rfl) rfl rfl

/-- A Source typing derivation of the loop from the caller's locals. -/
def typing : Source.StmtD context (k := .body) names
    (.whileStmt (.assign .assign (.ident "i") (.ident "a")) .breakStmt) names :=
  .whileLoop condition rfl .brk

/-- The body: the resolved loop with its production input at a loop site. -/
def body : Body where
  E := unit.env
  returns := []
  modifier := false
  control := .body
  ctx := [.bool, .bool]
  input :=
    { raw, resolved := typing.toR, returnSlots := none, scope := { funs := [] },
      before := ⟨(locals, 0), {}⟩ }
  site := .loop

/-- The raw loop spells the Source loop. -/
theorem spelled : Total.Spells.Items .body raw
    (.cons (.stmtItem (.whileStmt (.assign .assign (.ident "i") (.ident "a")) .breakStmt)) .nil) :=
  .stmt (.whileLoop {} (.assign (.name "i") (.name "a")) (.stmt .brk .nil)) .nil

/-- An emitted program of `C` in the caller's context. -/
abbrev emitted (out : Checker.Output C [.val .bool, .val .bool]) : Emitted := ⟨C, _, out⟩

/-- **Coverage smoke** (`Diagram.Total` at this input): every production run
on `body`'s input whose program is placed under the caller's names has a body
with the same input and a context map that the diagram associates with it. -/
theorem coverage (out : Checker.Output C [.val .bool, .val .bool])
    (_ : @Production productionNames body (emitted out)) (_ : Accepted (emitted out))
    (placed : out.names = (request body (emitted out)).context.names) :
    ∃ b' : Body, b'.SameInput body ∧ ∃ m, diagram.Assoc b' (emitted out) m :=
  ⟨body, ⟨rfl, rfl, rfl, rfl, rfl⟩, Total.Simulation.primitiveMap [.bool, .bool], rfl, placed,
    aligned_primitiveMap _, _,
    ⟨rfl, context, names, _, names, .stmt typing .nil, rfl, rfl, spelled, rfl⟩, rfl⟩

/-- Total initial matching at the smoke: every Source state of the body has a
related model state, so the diagram's relations are not empty there. -/
theorem matching (out : Checker.Output C [.val .bool, .val .bool])
    (m : Solidity.Lowering.V07.ContextMap body.ctx (emitted out).Γ)
    (h : diagram.Assoc body (emitted out) m) (src : Source.EMState body.E body.ctx) :
    ∃ tgt : State C [.val .bool, .val .bool],
      m.Related (fun τ v => diagram.valRel τ v) src.1 tgt.env ∧ diagram.globRel src.2 tgt :=
  initial_matching body (emitted out) m h src

/-- The smoke's map is the positional map of the landed boundary. -/
example : Total.Simulation.Positional (Total.Simulation.primitiveMap [.bool, .bool]) :=
  (aligned_primitiveMap _).positional

/-- The callers are bound under the production fresh-name policy. -/
example : @CallerBound productionNames := @caller_bound productionNames

/-- The transport is monotone. -/
example : diagram.fuel 3 ≤ diagram.fuel 5 := diagram_relations.2.2 3 5 (by decide)

/-- The landed boundary relates `false` to `false`; so does the diagram. -/
example (E : Source.Env) (C : Contract) (H : HTy) :
    diagram.valRel (D := E.layout) (C := C) (H := H) .bool (.val .bool) (.bool false) false :=
  valRel_of_boundary (E := E) (show Total.Relation.val E C H .bool (.val .bool) (.bool false) false
    from Total.loopRel_false E C H)

/-- With the frame relation, the diagram's globals give the landed boundary's:
here, the transaction value. -/
example {E : Source.Env} {C : Contract} {Γ : Ctx} {st : Source.St E} {σ : State C Γ}
    (h : diagram.globRel st σ) {G : Source.Glob E} {F : Source.Fr} (frame : frameRel G F σ)
    (persistent : ∀ p, E.transientRoot p = false) : σ.tx.msgValue.1 = (F.value.val : Int) :=
  (globRel.boundary h frame persistent).2.1

end Solidity.Examples.Lowering.Sim.Match

#print axioms Solidity.Correctness.Lowering.Sim.diagram_relations
#print axioms Solidity.Correctness.Lowering.Sim.initial_matching
#print axioms Solidity.Correctness.Lowering.Sim.caller_bound
#print axioms Solidity.Correctness.Lowering.Sim.globRel.boundary
#print axioms Solidity.Examples.Lowering.Sim.Match.coverage
#print axioms Solidity.Examples.Lowering.Sim.Match.matching
