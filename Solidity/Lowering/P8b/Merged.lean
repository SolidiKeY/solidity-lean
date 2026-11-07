import Solidity.Lowering.P8.DeclarationGraphAdmission
import Solidity.Lowering.P8.FailureContractV2
import Solidity.Lowering.P8b.P8aInterface

/-!
# One Producer interface for P8a and P8b (H57)

The P8/P8b `Producer` merge as an ADDITIVE pairing: the source half is the
frozen `P8a.Producer` itself and the lowering half is the frozen P8b
`ProducerOutput` (G01 `Lowering`) at the SAME `S`. No field of either frozen
structure is changed, dropped, weakened or made optional, so no versioned pair
is needed and no consumer has to migrate: every merged producer projects to
both frozen ones, and any two frozen ones pair into a merged one, with both
round trips definitional.

`H24` is the same pairing over the H24 declaration-graph wrapper; it projects
to the plain merged producer (forgetting only the graph admission).

The inhabitant and its controls live in `P8/PlanWitness.lean` and
`P8b/MergedControls.lean`.
-/
namespace Solidity.Lowering.P8b.Merged
open Solidity.Roadmap Solidity.Lowering.P8

/-- The merged Producer: P8a admission/realization plus the P8b lowering of
the SAME source specification. -/
structure Producer (S : P8a.Spec) (reference : P8a.OperationalReference)
    (origins : P8a.SourceOrigins S) (roots : P8a.RootModel S) (I : IntrinsicSpec) where
  source : P8a.Producer S reference origins roots
  lowering : P8aInterface.ProducerOutput S I

variable {S : P8a.Spec} {reference : P8a.OperationalReference}
  {origins : P8a.SourceOrigins S} {roots : P8a.RootModel S} {I : IntrinsicSpec}

/-- The frozen P8a projection. -/
def Producer.toP8a (p : Producer S reference origins roots I) :
    P8a.Producer S reference origins roots := p.source

/-- The frozen P8a V2 (split failure coverage) projection. -/
def Producer.toV2 (p : Producer S reference origins roots I) :
    FailureContractV2.Producer S reference origins roots :=
  FailureContractV2.Producer.ofV1 p.source

/-- The frozen P8b projection. -/
def Producer.toP8b (p : Producer S reference origins roots I) :
    P8aInterface.ProducerOutput S I := p.lowering

/-- The G01 `Lowering` contract carried by the P8b half. -/
def Producer.toLowering (p : Producer S reference origins roots I) : Lowering S I :=
  p.lowering.toLowering

def Producer.ofPair (a : P8a.Producer S reference origins roots)
    (b : P8aInterface.ProducerOutput S I) : Producer S reference origins roots I := ⟨a, b⟩

theorem Producer.ofPair_toP8a (a : P8a.Producer S reference origins roots)
    (b : P8aInterface.ProducerOutput S I) : (Producer.ofPair a b).toP8a = a := rfl

theorem Producer.ofPair_toP8b (a : P8a.Producer S reference origins roots)
    (b : P8aInterface.ProducerOutput S I) : (Producer.ofPair a b).toP8b = b := rfl

theorem Producer.ofPair_eta (p : Producer S reference origins roots I) :
    Producer.ofPair p.toP8a p.toP8b = p := rfl

/-- The merged producer is inhabited exactly when both frozen halves are:
merging adds and removes no obligation. -/
theorem nonempty_iff :
    Nonempty (Producer S reference origins roots I) ↔
      Nonempty (P8a.Producer S reference origins roots) ∧
        Nonempty (P8aInterface.ProducerOutput S I) :=
  ⟨fun ⟨p⟩ => ⟨⟨p.toP8a⟩, ⟨p.toP8b⟩⟩, fun ⟨⟨a⟩, ⟨b⟩⟩ => ⟨Producer.ofPair a b⟩⟩

/-- A checked frontend receipt of the merged producer is the frozen P8b one
at its source half. -/
abbrev CertifiedInput (p : Producer S reference origins roots I) (input : S.Input) :=
  P8aInterface.CertifiedInput p.source input

/-- The merged producer over the H24 declaration-graph wrapper. -/
structure H24 (S : P8a.Spec) (reference : P8a.OperationalReference)
    (origins : P8a.SourceOrigins S) (roots : P8a.RootModel S) (I : IntrinsicSpec) where
  source : DeclarationGraphAdmission.Producer S reference origins roots
  lowering : P8aInterface.ProducerOutput S I

def H24.toProducer (p : H24 S reference origins roots I) : Producer S reference origins roots I :=
  ⟨p.source.base, p.lowering⟩

/-- info: 'Solidity.Lowering.P8b.Merged.nonempty_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonempty_iff

end Solidity.Lowering.P8b.Merged
