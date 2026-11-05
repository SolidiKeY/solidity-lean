import Solidity.Source.Agreement.Locals
import Solidity.Source.Eval

/-!
# The normal-result locals obligation (not a simulation theorem)

This proposition names the real source and model computations. It is not
inhabited here for any general source/model program pair. In particular,
source horizons, errors and return/break/continue tags are not collapsed into
model outcomes. Only normal-result primitive locals are specified; complete
state and execution agreement remain separate obligations.
-/
namespace Solidity.Source.Agreement

/-- The normal-result clause to be proved for an explicitly associated pair
of programs. There is no arbitrary observer, supported-fragment predicate,
or assumed execution field. Source initial/final journal states remain
explicit and are not identified with the model heap or storage.

This is one direction and one outcome clause only. A proof would not establish
source/model program association, error agreement, termination completeness,
or full-state agreement. No such proof or default instance is supplied here. -/
def NormalLocalsObligation {E : Env} {C : Contract}
    {R : List STy} {M : Bool} {k : SCtx} (ps qs : List PrimTy)
    (G : Glob E) (F : Fr) (nps : Nat) (ph : Option (Ph E))
    (b : RItems E R M k (sourceContext ps) (sourceContext qs))
    (P : Prog C (modelContext ps) (modelContext qs)) : Prop :=
  ∀ (ls : Locals E.layout (sourceContext ps)) (s : St E)
    (model : Solidity.State C (modelContext ps)),
    StateLocalsRel E C ps ls model →
    ∀ (n : Nat) (ls' : Locals E.layout (sourceContext qs))
      (journal : Locals E.layout [] × St E),
      (execItems G F n nps ph b ls).run (.nil, s) = (.ok (.normal ls'), journal) →
      ∃ out, Prog.runC P model = .ok out ∧ StateLocalsRel E C qs ls' out.st

end Solidity.Source.Agreement
