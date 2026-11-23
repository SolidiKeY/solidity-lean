import Solidity.Tools.SourceCounterexample

/-! # Executable goal binding

Relates imported and executable candidates by typed storage and call-data
identities. Each formula failure is proved independently at its candidate;
matching evaluation results alone do not establish formula equivalence.
-/
namespace Solidity.Tools

structure GoalPair where
  importedContract : Contract
  executableContract : Contract
  importedFormula : Fml importedContract []
  executableFormula : Fml executableContract []

/-- Strong typed correspondence, not an assumption licensed by matching JSON.
Every field must be proved for the actual retained and executable candidates. -/
structure SameCandidate (g : GoalPair) where
  imported : Cand g.importedContract
  executable : Cand g.executableContract
  storage : HEq imported.st executable.st
  arguments : imported.args = executable.args
  transaction : imported.tx = executable.tx
  ledger : imported.net = executable.net
  balance : imported.bal = executable.bal

/-- Reuse an existing candidate under an explicitly proved storage-layout
identity. No storage defaults, argument conversion or candidate search occurs.
This transports data only; it does not transport any formula or failure proof. -/
def Cand.rebindLayout {C D : Contract} (candidate : Cand C)
    (layout : C.vars = D.vars) : Cand D :=
  { st := cast (congrArg SFields layout) candidate.st,
    args := candidate.args, tx := candidate.tx, net := candidate.net, bal := candidate.bal }

theorem Cand.rebindLayout_storage {C D : Contract} (candidate : Cand C)
    (layout : C.vars = D.vars) : HEq candidate.st (candidate.rebindLayout layout).st :=
  (cast_heq (congrArg SFields layout) candidate.st).symm

theorem Cand.rebindLayout_argInts {C D : Contract} (candidate : Cand C)
    (layout : C.vars = D.vars) : (candidate.rebindLayout layout).argInts = candidate.argInts := rfl

theorem Cand.rebindLayout_vals [FreshNames] {C D : Contract} (candidate : Cand C)
    (layout : C.vars = D.vars) : (candidate.rebindLayout layout).vals = candidate.vals := rfl

/-- Build a typed same-candidate relation from the retained candidate
and a kernel proof of the actual layouts. Source/import/request authentication
and an independent exact executable failure proof remain frontend obligations. -/
def SameCandidate.ofLayout (g : GoalPair) (candidate : Cand g.importedContract)
    (layout : g.importedContract.vars = g.executableContract.vars) : SameCandidate g :=
  { imported := candidate, executable := candidate.rebindLayout layout,
    storage := candidate.rebindLayout_storage layout,
    arguments := rfl, transaction := rfl, ledger := rfl, balance := rfl }

theorem SameCandidate.ofLayout_imported (g : GoalPair) (candidate : Cand g.importedContract)
    (layout : g.importedContract.vars = g.executableContract.vars) :
    (ofLayout g candidate layout).imported = candidate := rfl

/-- The retained source-values equation is not a `Cand.vals` equation. Both are required
before rewriting a retained failure to the candidate-derived values here. -/
structure RetainedValuesBinding (C : Contract) (candidate : Cand C)
    (retained : List (Var × Semantics.CallValue)) : Prop where
  sourceValues : retained = candidate.sourceValuesV1
  candidateValues : retained = candidate.vals

/-- Reuse the retained failure, rewriting only by the separately proved
candidate-values equation. This performs no evaluation or candidate search. -/
theorem RetainedValuesBinding.failure {C : Contract} {candidate : Cand C}
    {retained : List (Var × Semantics.CallValue)} {formula : Fml C []}
    (binding : RetainedValuesBinding C candidate retained)
    (failure : Fml.eval3Peel (poolDom candidate.argInts) retained
      (candidate.tstate C) formula = .ff) :
    Fml.eval3Peel (poolDom candidate.argInts) candidate.vals
      (candidate.tstate C) formula = .ff := by
  simpa only [binding.candidateValues] using failure

structure SelectedFailure (g : GoalPair) where
  candidate : SameCandidate g
  importedFailure :
    Fml.eval3Peel (poolDom candidate.imported.argInts)
      candidate.imported.vals (candidate.imported.tstate g.importedContract)
      g.importedFormula = .ff
  executableFailure :
    Fml.eval3Peel (poolDom candidate.executable.argInts)
      candidate.executable.vals (candidate.executable.tstate g.executableContract)
      g.executableFormula = .ff

/-- Only the exact executable failure proves this negation. The imported
failure alone cannot refute a different goal. No equivalence is asserted. -/
theorem SelectedFailure.refuted {g : GoalPair}
    (w : SelectedFailure g) : ¬ Fml.Valid g.executableFormula :=
  Fml.not_valid_of_eval3Peel w.candidate.executable.vals
    (w.candidate.executable.tstate g.executableContract) w.executableFailure

end Solidity.Tools
