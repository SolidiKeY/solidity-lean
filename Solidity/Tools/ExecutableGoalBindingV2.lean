import Solidity.Tools.SourceCounterexample

/-! # Exact executable failure at a retained candidate, V2

Guards the regression where two failed evaluations are reported as a theorem
transporting an importer proof. These records certify the exact executable
formula only. Actual source/request authentication belongs to the opt-in
frontend ingress; a public record does not authenticate a caller's goal pair.
No source search, primitive admission guard, statement or budget is changed.
-/
namespace Solidity.Tools

structure GoalPairV2 where
  importedContract : Contract
  executableContract : Contract
  importedFormula : Fml importedContract []
  executableFormula : Fml executableContract []

/-- Strong typed correspondence, not an assumption licensed by matching JSON.
Every field must be proved for the actual retained and executable candidates. -/
structure SameCandidateV2 (g : GoalPairV2) where
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
def Cand.rebindLayoutV2 {C D : Contract} (candidate : Cand C)
    (layout : C.vars = D.vars) : Cand D :=
  { st := cast (congrArg SFields layout) candidate.st,
    args := candidate.args, tx := candidate.tx, net := candidate.net, bal := candidate.bal }

theorem Cand.rebindLayoutV2_storage {C D : Contract} (candidate : Cand C)
    (layout : C.vars = D.vars) : HEq candidate.st (candidate.rebindLayoutV2 layout).st :=
  (cast_heq (congrArg SFields layout) candidate.st).symm

theorem Cand.rebindLayoutV2_argInts {C D : Contract} (candidate : Cand C)
    (layout : C.vars = D.vars) : (candidate.rebindLayoutV2 layout).argInts = candidate.argInts := rfl

theorem Cand.rebindLayoutV2_vals [FreshNames] {C D : Contract} (candidate : Cand C)
    (layout : C.vars = D.vars) : (candidate.rebindLayoutV2 layout).vals = candidate.vals := rfl

/-- Build the approved typed same-candidate relation from the original candidate
and a kernel proof of the actual layouts. Source/import/request authentication
and an independent exact executable failure proof remain frontend obligations. -/
def SameCandidateV2.ofLayout (g : GoalPairV2) (candidate : Cand g.importedContract)
    (layout : g.importedContract.vars = g.executableContract.vars) : SameCandidateV2 g :=
  { imported := candidate, executable := candidate.rebindLayoutV2 layout,
    storage := candidate.rebindLayoutV2_storage layout,
    arguments := rfl, transaction := rfl, ledger := rfl, balance := rfl }

theorem SameCandidateV2.ofLayout_imported (g : GoalPairV2) (candidate : Cand g.importedContract)
    (layout : g.importedContract.vars = g.executableContract.vars) :
    (ofLayout g candidate layout).imported = candidate := rfl

/-- V1's source-values equation is not a `Cand.vals` equation. Both are required
before rewriting a retained failure to the candidate-derived values here. -/
structure RetainedValuesBindingV2 (C : Contract) (candidate : Cand C)
    (retained : List (Var × Semantics.CallValue)) : Prop where
  sourceValues : retained = candidate.sourceValuesV1
  candidateValues : retained = candidate.vals

/-- Reuse the retained failure, rewriting only by the separately proved
candidate-values equation. This performs no evaluation or candidate search. -/
theorem RetainedValuesBindingV2.failure {C : Contract} {candidate : Cand C}
    {retained : List (Var × Semantics.CallValue)} {formula : Fml C []}
    (binding : RetainedValuesBindingV2 C candidate retained)
    (failure : Fml.eval3Peel (poolDom candidate.argInts) retained
      (candidate.tstate C) formula = .ff) :
    Fml.eval3Peel (poolDom candidate.argInts) candidate.vals
      (candidate.tstate C) formula = .ff := by
  simpa only [binding.candidateValues] using failure

structure SelectedFailureV2 (g : GoalPairV2) where
  candidate : SameCandidateV2 g
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
theorem SelectedFailureV2.refuted {g : GoalPairV2}
    (w : SelectedFailureV2 g) : ¬ Fml.Valid g.executableFormula :=
  Fml.not_valid_of_eval3Peel w.candidate.executable.vals
    (w.candidate.executable.tstate g.executableContract) w.executableFailure

end Solidity.Tools
