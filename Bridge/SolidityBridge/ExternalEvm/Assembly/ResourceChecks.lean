import SolidityBridge.ExternalEvm.Assembly.ResourceReady
import SolidityBridge.ExternalEvm.Assembly.SafeFetched
import SolidityBridge.ExternalEvm.Assembly.TerminationChecks

namespace Solidity.Evm.External.Assembly.ResourceChecks
open EvmYul EvmYul.EVM
open TerminationChecks

def safeFetched : SafeFetched program.scanner.destinations 21 reference :=
  ((checkSafeFetched program.scanner.destinations 21 reference).get (by decide +kernel)).down

def safePrefix : SafeTrace program.scanner.destinations 21 reference fetched :=
  safeFetched.trace fetchedRun

/-- This proof contains no real destination array; all original resource
checks are computed on the actual charged dispatcher prefix. -/
def resources : ResourceReady 21 24 LinkedChecks.input :=
  ((checkResources 21 24 LinkedChecks.input).get (by decide +kernel)).down

theorem originalReady : DriverReady 21 24 program.validJumps LinkedChecks.input :=
  safePrefix.driver_ready 24 LinkedChecks.input rfl resources

/-- Inhabited compiler-facing resource-only theorem, with the actual
successful loop input and automatically generated scanned certificate. -/
example := program.resource_success_simulation layout sourceInput sourceOutput reference entry sourceRun

/-- The scanner-safe/resource-only shared proof path yields actual X success;
neither full destination readiness nor any X outcome is an input premise. -/
theorem compiledSuccess : ∃ out,
    X 24 program.validJumps LinkedChecks.input = .ok (.success out .empty) ∧
      SuccessBoundary layout sourceOutput out := by
  obtain ⟨terminal, counted, related, finish⟩ := layout.resource_success_of_fetched 21 0 sourceOutput
    reference fetched LinkedChecks.input safePrefix fetchedBoundary rfl resources
  have he : terminal = charged := Except.ok.inj (counted.symm.trans chargedRun)
  subst terminal
  exact finish gates

#guard (checkSafeFetched [] 21 reference).isNone
#guard (checkResources 21 24 {LinkedChecks.input with gasAvailable := .ofNat 0}).isNone
#guard (checkResources 21 21 LinkedChecks.input).isNone
#guard (checkSafeFetched program.scanner.destinations 21 reference).isSome

private def branchDestinations := ([5,40,74,108] : List Nat).map UInt256.ofNat
private def branchFrame := ComposedBranch.initial (.ofNat 1) []
private def branchSite : AtomicSite ComposedBranch.image branchFrame 0 (.jumpi 1) :=
  (checkAtom ComposedBranch.image branchFrame 0 (.jumpi 1)).get (by decide +kernel)
private def branchLabels : ScannedLabels ComposedBranch.code 5 branchDestinations :=
  ((checkLabels ComposedBranch.code 5 branchDestinations).get (by decide +kernel)).down

/-- Both source-conditional outcomes inhabit the scanner-consuming atomic
proof path for a relocated branch, not just the emitted loop guard. -/
example : ∃ n t, SafeTrace branchDestinations n branchFrame t ∧
    Boundary ComposedBranch.image branchFrame 2 Machine.init t := by
  exact branchSite.safe_refinement (targetsSafeOfLabels branchLabels (.jumpi 1))
    {Machine.init with stack := [w[1]]} Machine.init 1 branchFrame
    ⟨by decide, rfl, rfl, rfl, rfl⟩ rfl

example : ∃ n t, SafeTrace branchDestinations n (ComposedBranch.initial (.ofNat 0) []) t ∧
    Boundary ComposedBranch.image branchFrame 1 Machine.init t := by
  exact branchSite.safe_refinement (targetsSafeOfLabels branchLabels (.jumpi 1))
    {Machine.init with stack := [w[0]]} Machine.init 0 (ComposedBranch.initial (.ofNat 0) [])
    ⟨by decide, rfl, rfl, rfl, rfl⟩ rfl

#guard (fetchedSteps 3 branchFrame).toOption.map (fun t => (t.pc.toNat, words t.stack)) = some (74, [])
#guard (fetchedSteps 3 (ComposedBranch.initial (.ofNat 0) [])).toOption.map
  (fun t => (t.pc.toNat, words t.stack)) = some (40, [])

end Solidity.Evm.External.Assembly.ResourceChecks

/-- info: 'Solidity.Evm.External.Assembly.ResourceChecks.compiledSuccess' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Evm.External.Assembly.ResourceChecks.compiledSuccess
