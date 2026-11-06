import Solidity.Source.Agreement.NormalStatement

/-! Explicit per-statement producer premise for normal primitive-local results.
This is a proposition about the existing two evaluators, not a new execution
judgment/default, axiom, producer instance, or assumption of whole-program
agreement. Non-normal source outcomes and complete-state correspondence remain
outside this normal-only contract. Stateful statements may require a stronger
initial relation before any producer can inhabit this particular contract. -/
namespace Solidity.Source.Agreement

/-- A separately associated single statement, with all initial worlds and
actual source journal outputs explicit. This lane must discharge each such
fact using the Source owner API and the real statement association. -/
def NormalStmtObligation {E : Env} {C : Contract}
    {R : List STy} {M : Bool} {k : SCtx} (ps qs : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (s : RStmt E R M k (sourceContext ps) (sourceContext qs))
    (S : Solidity.Stmt C (modelContext ps) (modelContext qs)) : Prop :=
  ∀ (ls : Locals E.layout (sourceContext ps)) (st : St E)
    (model : Solidity.State C (modelContext ps)),
    StateLocalsRel E C ps ls model →
    ∀ (n : Nat) (ls' : Locals E.layout (sourceContext qs))
      (journal : Locals E.layout [] × St E),
      (execS G F n nps ph s ls).run (.nil, st) = (.ok (.normal ls'), journal) →
      ∃ out, Solidity.Stmt.runC S model = .ok out ∧ StateLocalsRel E C qs ls' out.st

end Solidity.Source.Agreement
