import Solidity.Backend.InternalFlow.RuntimeFrameV3GeneralBoundary
import Solidity.Backend.InternalFlow.RuntimeFrameV3FrozenScopeCoverage

/-! Controls for `V3GeneralBoundary`.

Positive: the generic `callRec` transport `of_unrolled` rebuilds the existing
scoped scalar-family V3 producer from the ordinary-call claims of its actual
unrolled bodies, with the same plan and code image. The only remaining input
is the same external approved-domain agreement `with_profile` needs.

Negative: the trivial uniform family has no V3 producer at any domain, and its
source is not exhausted at a positive index, so the emptiness comes from the
missing bare revert, not from exhaustion. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.V3GeneralBoundaryControls
open Evm Evm.Memory V3GeneralBoundary
open DisjointScalarReturn.Client (Γ F reference)

/-- Round trip through the ordinary-call obligations of every unrolled body. -/
def rebuilt (approved : Nat → InterfaceV3.Admission SameCallInputs.C Γ)
    (agreement : InterfaceV3.FamilyAdmissionAgreement approved FrozenScopeCoverage.inputs) :
    InterfaceV3.PendingRecursiveReturns 1 F approved FrozenScopeCoverage.inputs "scalarCountdown"
      (DisjointScalarEntry.args rfl reference ScalarReentry.count)
      (.val .uint (.user "result") (some (.here : Idx Γ (.val .uint))))
      (FrozenScopeFamily.step CountdownWitness.A rfl .uint (.user "sameCall")) :=
  let p := FrozenScopeCoverage.with_profile approved agreement
  let h := unrolled_returns p
  of_unrolled approved FrozenScopeCoverage.inputs p.plan agreement p.required_coverage
    p.required_source_coherence h.2.2.1 h.2.2.2 h.1 h.2.1

theorem rebuilt_plan (approved : Nat → InterfaceV3.Admission SameCallInputs.C Γ)
    (agreement : InterfaceV3.FamilyAdmissionAgreement approved FrozenScopeCoverage.inputs) :
    (rebuilt approved agreement).plan = (FrozenScopeCoverage.with_profile approved agreement).plan :=
  rfl

/-- The trivial family is empty at every domain, including the full one. -/
theorem trivial_empty (C : Contract) (F : Frag ([] : Ctx)) :
    ¬ Nonempty (InterfaceV3.PendingRecursiveReturns (C := C) 0 F
      (fun _ _ _ _ _ _ _ => True) (fun _ _ _ _ _ _ _ => True) "f" .nil .none trivialStep) :=
  no_recursive_producer (trivial_never_reverts "f")

/-- At index one the trivial source returns, so it is not an exhausted-only
family: positive indices succeed, index zero exhausts, none bare-reverts. -/
theorem trivial_succeeds {C : Contract} (σ : State C []) :
    ∃ out, (InterfaceV1.recursiveSource (C := C) (Γ := []) "f" .nil .none trivialStep 1).run σ
      = .ok out :=
  ⟨_, rfl⟩

theorem trivial_exhausts {C : Contract} (σ : State C []) :
    (InterfaceV1.recursiveSource (C := C) (Γ := []) "f" .nil .none trivialStep 0).run σ
      = .error .exhausted :=
  rfl

end Solidity.Backend.InternalFlow.RuntimeFrame.V3GeneralBoundaryControls
