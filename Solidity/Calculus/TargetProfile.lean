import Solidity.Calculus.Assumptions
import Solidity.Roadmap.TypedRun
import Solidity.Semantics.Nondeterminism.Fork

/-!
# The target profile of a verdict (`docs/options.md`, O13)

One named bundle of what a verdict targets: the solc version, the
compiler pipeline and the EVM fork.  It adds no parameter of its own: the
pipeline is G01's (`Roadmap.Pipeline`, `Roadmap/Contracts.lean`), whose
expression order is `Pipeline.order` (`Roadmap/TypedRun.lean`), the
parameter VS4's split reads as compiler nondeterminism (S5.1,
`Semantics/Nondeterminism/Split.lean`); the fork is VS4's `ForkSpec`
(S6.1, `Semantics/Nondeterminism/Fork.lean`), Osaka its pinned instance.

A record is read under a profile when its order is the pipeline's
(`TargetProfile.fits`); a proof that fits is then about a contract
elaborated in the pipeline's order (`TargetProfile.evalOrder_of_fits`).
Only the pipeline is tied to `ValidA`: the version and the fork are carried
as data, since no formula reads them (the intrinsic run has no fork
argument; VS4's fork reaches the block environment and gas, `BlockEnv`).
-/

namespace Solidity

open Solidity.Roadmap (Pipeline)
open Solidity.Semantics.Nondeterminism (ForkSpec Fork)

variable {C : Contract}

/-- The O9 order a pipeline selects, as the record names it. -/
def OrderReading.ofPipeline : Pipeline → OrderReading
  | .legacy => .legacy
  | .viaIR => .viaIR

/-- The record's order elaborates as the pipeline's (`Pipeline.order`). -/
theorem OrderReading.ofPipeline_toEvalOrder (q : Pipeline) :
    (OrderReading.ofPipeline q).toEvalOrder = q.order := by
  cases q <;> rfl

/-- A solc version. -/
structure SolcVersion where
  major : Nat
  minor : Nat
  patch : Nat
  deriving DecidableEq, Repr

/-- **A target profile**: compiler version, pipeline and fork. -/
structure TargetProfile where
  solc : SolcVersion
  pipeline : Pipeline := .legacy
  fork : ForkSpec := .osaka

/-- The runner's profile: solkey's pinned compiler (0.8.34), legacy,
Osaka. -/
def TargetProfile.pinned : TargetProfile := { solc := ⟨0, 8, 34⟩ }

/-- The pinned profile's fork is the pinned EVM's (`ForkSpec.osaka_pin`). -/
theorem TargetProfile.pinned_pin : TargetProfile.pinned.fork.pin? = some Roadmap.Evm.osaka :=
  ForkSpec.osaka_pin

/-- A record is read under a profile when its order is the pipeline's. -/
def TargetProfile.fits (p : TargetProfile) (a : Assumptions) : Bool :=
  a.order == OrderReading.ofPipeline p.pipeline

/-- **A proof that fits the profile is about the profile's pipeline**: the
contract elaborates in the pipeline's expression order. -/
theorem TargetProfile.evalOrder_of_fits {p : TargetProfile} {I : Invariant C}
    {a : Assumptions} {φ : Fml C []} (hp : p.fits a = true) (h : ValidA I a φ) :
    C.evalOrder = p.pipeline.order := by
  have ho : a.order = OrderReading.ofPipeline p.pipeline := beq_iff_eq.mp hp
  rw [← OrderReading.ofPipeline_toEvalOrder, ← ho]
  exact (OrderReading.matches_iff _ _).1 h.1

/-- Conversely, a record that does not fit the profile is never valid at a
contract in the profile's order: the orders differ. -/
theorem TargetProfile.not_validA_of_not_fits {p : TargetProfile} {I : Invariant C}
    {a : Assumptions} {φ : Fml C []} (hp : p.fits a = false) (hC : C.evalOrder = p.pipeline.order) :
    ¬ ValidA I a φ := by
  intro h
  have h1 : a.order.matches (OrderReading.ofPipeline p.pipeline).toEvalOrder = true := by
    rw [OrderReading.ofPipeline_toEvalOrder, ← hC]
    exact h.1
  revert hp h1
  unfold fits
  cases a.order <;> cases p.pipeline <;> decide

end Solidity
