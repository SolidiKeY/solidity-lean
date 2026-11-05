import Solidity.Source.Session
import Solidity.Source.FailureResources

/-! P8 boundary of the ACTUAL published horizon language. This is a checked
obstruction to packaging it unchanged with nontrivial failure choices, not a
new SourceSpec instance or a substitute failure-aware interpreter. -/
namespace Solidity.Lowering.P8
open Roadmap

/-- Only the frame projection of no resource failure; NOT a definition of the
canonical NoFail predicate (transactions, funds and stipend remain separate). -/
def FrameClear (f : Evm.FailurePoints) : Prop := ∀ i, f.frame i = none

def immediateFailure : Evm.FailurePoints :=
  ⟨fun _ => .runs 0 none, fun _ => some 0⟩

theorem immediateFailure_not_clear : ¬ FrameClear immediateFailure := by
  intro h
  have he := h 0
  cases he

theorem actual_source_forward {E : Source.Env} (p : Source.SrcProg E) (e : SessionEnv) (r : Nat) :
    (Source.sourceLangEvents E).Forward p e r := trivial

/-- The unchanged source Lang defaults Forward to True. A right-inverse failure
setter and even the NECESSARY clear-frame consequence of Forward contradict
that default. Proper operational failure hooks and a new resource-aware language
are needed; simply adding SourceSpec fields cannot close the obligation. -/
theorem unmodified_forward_obstruction {E : Source.Env}
    (p : Source.SrcProg E) (e : SessionEnv)
    (failures : Nat → Evm.FailurePoints)
    (withFailures : Nat → Evm.FailurePoints → Nat)
    (roundtrip : ∀ r f, failures (withFailures r f) = f)
    (forward_clear : ∀ r, (Source.sourceLangEvents E).Forward p e r → FrameClear (failures r)) : False := by
  have hc := forward_clear (withFailures 0 immediateFailure) (actual_source_forward p e _)
  rw [roundtrip] at hc
  exact immediateFailure_not_clear hc

/-- A data component for the required resource extension only. No semantics is
attached: ignoring these failures when executing would not implement G06. -/
abbrev FailureResource := Source.FailureResources.Bound

def failuresOf (r : FailureResource) : Evm.FailurePoints := Source.FailureResources.Bound.points r
def setFailures (r : FailureResource) (f : Evm.FailurePoints) : FailureResource := Source.FailureResources.Bound.withFailures r f

theorem failures_set (r : FailureResource) (f : Evm.FailurePoints) : failuresOf (setFailures r f) = f := Source.FailureResources.Bound.failures_with r f

theorem horizon_set (r : FailureResource) (f : Evm.FailurePoints) : (setFailures r f).1 = r.1 := Source.FailureResources.Bound.horizon_with r f

theorem failure_choice_inhabited : ∃ r : FailureResource, ¬ FrameClear (failuresOf r) :=
  ⟨(0, immediateFailure), immediateFailure_not_clear⟩

#print axioms unmodified_forward_obstruction
#print axioms failures_set
#print axioms failure_choice_inhabited
end Solidity.Lowering.P8
