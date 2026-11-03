import Solidity.Lowering.P8.FrozenInterface
import Solidity.Source.FailureResources

/-! Failure-plan operations on `FailureResources.Bound`; no P8a instance is built.
These reuse the transferred resource carrier, not a duplicate failure model.
A frozen `P8a.FailureProjection S` additionally needs the actual SourceSpec's
failure fields and NoFail contract; this module does not invent that instance. -/
namespace Solidity.Lowering.P8.SpecFailures
open Solidity.Roadmap
abbrev Resource := Source.FailureResources.Bound
abbrev Choices := Evm.FailurePoints

def points (resource : Resource) : Choices := resource.points
def withPoints (resource : Resource) (choices : Choices) : Resource :=
  resource.withFailures choices
abbrev NoFail := Source.FailureResources.NoFail

def failureFree (horizon : Nat) (balances : Nat → Nat) : Resource :=
  (horizon, Source.FailureResources.noFailures balances)

/-- A scheduled request cut is incompatible with NoFail, even with a
positive sender balance and with every external-frame cut absent. This is a
failure-plan fact; it does not inject the cut into the current Source runner. -/
theorem request_cut_not_noFail {p : Choices} {i balance cut : Nat}
    (h : p.tx i = .runs balance (some cut)) : ¬ NoFail p := by
  intro hn
  obtain ⟨other, hnone⟩ := hn.1 i
  rw [h] at hnone
  cases hnone

/-- A concrete plan with exactly one scheduled request cut. The other request
balances and all frame choices come from the existing failure-free plan. -/
def requestCut (horizon : Nat) (balances : Nat → Nat)
    (index balance cut : Nat) : Resource :=
  (horizon, { Source.FailureResources.noFailures balances with
    tx := fun i => if i = index then .runs balance (some cut)
      else .runs (balances i) none })

/-- The minimal diagonal uses no dropped requests, no request cuts and only
frame choices none/some 0. At coordinate n it disagrees with candidate n. -/
def frameDiagonal (extract : Nat → Choices) : Choices where
  tx _ := .runs 0 none
  frame n := match (extract n).frame n with
    | none => some 0
    | some _ => none

/-- A cut-at-zero plan with nonzero post-fee balance (not yet used by any theorem). No actual
Source execution is claimed to honor this plan before the resource decision. -/
def requestCutWitness : Resource := requestCut 3 (fun i => i + 1) 7 257 0

/-- No candidate horizon enumerates this plan: a single frame coordinate
already contradicts equality. The request component is uniformly uncut. -/
theorem frameDiagonal_ne (extract : Nat → Choices) (j : Nat) :
    extract j ≠ frameDiagonal extract := by
  intro h
  have he := congrArg (fun p : Choices => p.frame j) h
  change (extract j).frame j = (match (extract j).frame j with
    | none => some 0
    | some _ => none) at he
  cases hf : (extract j).frame j with
  | none => rw [hf] at he; cases he
  | some cut => rw [hf] at he; cases he

end Solidity.Lowering.P8.SpecFailures
