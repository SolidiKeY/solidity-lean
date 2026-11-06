import Solidity.Source.Agreement.Primitive
import Solidity.Source.Machine

/-!
# Primitive local-state correspondence

This is the value/local-state interface of SS-AGREE, not a simulation.
Contexts are intrinsic on both sides. Recursion is on the list of primitive
types; no source local is erased. Heap, storage, events, calldata and execution
resources have no correspondence theorem here.
-/
namespace Solidity.Source.Agreement

/-- Source context of the supported primitive locals. -/
def sourceContext (ps : List PrimTy) : RCtx := ps.map sourceTy

/-- Model context of the same primitive locals. -/
def modelContext (ps : List PrimTy) : Solidity.Ctx := ps.map LTy.val

/-- Each pair of locals retains its typed primitive value correspondence. -/
inductive LocalsRel (D : Layout) (C : Contract) (H : HTy) :
    (ps : List PrimTy) → Locals D (sourceContext ps) →
      TEnv C H (modelContext ps) → Prop where
  | nil : LocalsRel D C H [] .nil ()
  | cons {p : PrimTy} {ps : List PrimTy}
      {v : Source.Val D (sourceTy p)} {w : p.Denote}
      {vs : Locals D (sourceContext ps)} {ws : TEnv C H (modelContext ps)}
      (head : PrimitiveRel D p v w) (tail : LocalsRel D C H ps vs ws) :
      LocalsRel D C H (p :: ps) (.cons v vs) (w, ws)

/-- Total producer, including range evidence, for every model environment. -/
def localsOfModel (D : Layout) (C : Contract) (H : HTy) :
    (ps : List PrimTy) → TEnv C H (modelContext ps) → Locals D (sourceContext ps)
  | [], _ => .nil
  | p :: ps, ws => .cons (ofModel D p ws.1) (localsOfModel D C H ps ws.2)

/-- Nonvacuity: every model local environment has a related source value. -/
theorem localsOfModel_related (D : Layout) (C : Contract) (H : HTy)
    (ps : List PrimTy) (ws : TEnv C H (modelContext ps)) :
    LocalsRel D C H ps (localsOfModel D C H ps ws) ws := by
  induction ps with
  | nil => exact .nil
  | cons p ps ih => exact .cons (ofModel_related D p ws.1) (ih ws.2)

/-- The state projection concerns only locals. It does not compare stores,
heaps, ledgers, source journals, or calldata. -/
def StateLocalsRel (E : Env) (C : Contract) (ps : List PrimTy)
    (ls : Locals E.layout (sourceContext ps)) (model : Solidity.State C (modelContext ps)) :
    Prop := LocalsRel E.layout C model.H ps ls model.env

/-- This partial state projection is inhabited for every actual model state;
there is no false supported-fragment premise. -/
theorem stateLocals_total (E : Env) (C : Contract) (ps : List PrimTy)
    (model : Solidity.State C (modelContext ps)) :
    StateLocalsRel E C ps
      (localsOfModel E.layout C model.H ps model.env) model :=
  localsOfModel_related E.layout C model.H ps model.env

/-- A two-local client preserves order and distinguishes false from true. -/
theorem bool_pair_client (D : Layout) (C : Contract) (H : HTy) :
    LocalsRel D C H [.bool, .bool]
      (.cons (.bool false) (.cons (.bool true) .nil)) (false, true, ()) :=
  .cons (.bool false) (.cons (.bool true) .nil)

end Solidity.Source.Agreement
