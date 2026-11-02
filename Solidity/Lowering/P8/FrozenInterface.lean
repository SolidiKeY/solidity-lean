import Solidity.Roadmap.Contracts
import Solidity.Source.Semantics
import Solidity.Language.Features

/-!
# FROZEN P8a producer interface (H12, 2026-11-02)

Signatures and explicit proof obligations only. No SourceSpec instance,
extractor, operational semantics, admission proof, or adequacy theorem is
provided here. In particular these structures are NOT evidence that G15 or
S05 is complete. Every proof field is an unimplemented producer obligation.

V16 owns the G01 Lowering dom/agrees/cert half and consumes the external
`S : Spec` parameter, exactly the existing Roadmap.SourceSpec. The actual operational reference is an
explicit parameter, not a relation chosen by the producer to prove itself.
A reference implementation must be supplied and validated against the actual
source machine before any actual-source correctness claim. No such value is
exported by this module. Frozen signatures change only with coordinator notice.
-/
namespace Solidity.Lowering.P8.P8a
open Solidity.Roadmap
open Solidity.Language

/-- The shared G01 source contract, reused without a parallel definition. -/
abbrev Spec := SourceSpec

/-- Actual existing intrinsic Source programs, retaining their environment. -/
abbrev SourceProgram := (E : Source.Env) × Source.SrcProg E

/-- An explicit, as-yet unimplemented operational-reference parameter.
`Executes` is a premise of the interface, not a supplied semantics or axiom. -/
structure OperationalReference where
  Resource : Type
  points : Resource → Evm.FailurePoints
  Executes : SourceProgram → SessionEnv → Resource → Prefix Event Outcome → Prop

/-- Independently supplied source-origin interpretation. Its implementation
must come from actual parsing/resolution/elaboration, not producer choice. -/
structure SourceOrigins (S : Spec) where
  meaning : (r : S.Resolved) → S.WellFormed r → S.InProfile r → Artifact → SourceProgram

/-- Root and feature relations are explicit source-model parameters. They must
be instantiated from actual source execution/observation roots; this module
supplies none. `classify` must include feature combinations and settings, not
merely test each feature's individual policy flag. -/
structure RootModel (S : Spec) where
  Root : Type
  executionRoot : S.Resolved → Root → Prop
  observationRoot : S.Resolved → Root → Prop
  featureAt : S.Resolved → Root → Feature → Prop
  classify : S.Resolved → List Feature → Bool

/-- Complete extraction obligations: both execution and observation roots,
no missing or invented features, and exact approved-profile classification.
These are deliberately not discharged by ScopeScan.within alone. -/
structure Extraction {S : Spec} (M : RootModel S) (r : S.Resolved) where
  roots : List M.Root
  features : List Feature
  roots_exact : ∀ root, root ∈ roots ↔ M.executionRoot r root ∨ M.observationRoot r root
  features_exact : ∀ feature, feature ∈ features ↔
    ∃ root ∈ roots, M.featureAt r root feature
  classification_exact : M.classify r features = true ↔ S.InProfile r

structure Extractor {S : Spec} (M : RootModel S) where
  extract : (r : S.Resolved) → Extraction M r

/-- Necessary G06 projections only; no alternative NoFail definition and no
claim that the current horizon evaluator consults these points. Retraction
is already required by SourceSpec.failures_with. -/
structure FailureProjection (S : Spec) where
  points : S.Failures → Evm.FailurePoints
  ofPoints : Evm.FailurePoints → S.Failures
  points_ofPoints : ∀ p, points (ofPoints p) = p
  noFail_requests : ∀ f, S.NoFail f → ∀ i, ∃ balance,
    (points f).tx i = .runs balance none
  noFail_frames : ∀ f, S.NoFail f → ∀ k, (points f).frame k = none

/-- Required agreement with the independently supplied operational and
source-origin references, including preservation of the actual failure plan.
This is an obligation record, not an assumed theorem or implementation. -/
structure SourceRealization (reference : OperationalReference) {S : Spec}
    (origins : SourceOrigins S) (failures : FailureProjection S) where
  program : S.lang.Prog → SourceProgram
  resource : S.lang.Res → reference.Resource
  exact : ∀ p e r out, reference.Executes (program p) (S.session e) (resource r) out ↔
    S.lang.sem p e r = out
  meaning_origin : ∀ r w p art, program (S.meaning r w p art) = origins.meaning r w p art
  resource_points : ∀ r, reference.points (resource r) = failures.points (S.failures r)

/-- FROZEN producer obligations RELATIVE TO independent reference models.
No inhabitant is exported. `S`, `reference`, `origins` and `roots` are external
parameters, not models chosen inside this producer to certify itself. Actual
Source adequacy of those reference parameters must be established separately;
an arbitrary parameter bundle does not establish actual-source completeness.
V16's G01 Lowering consumes the unchanged `S : Roadmap.SourceSpec`. -/
structure Producer (S : Spec) (reference : OperationalReference)
    (origins : SourceOrigins S) (roots : RootModel S) where
  failures : FailureProjection S
  realization : SourceRealization reference origins failures
  extraction : Extractor roots
  checkedFrontend : CheckedFrontend S
  admission : Admission S
  frontend_agrees : ∀ i, admission.frontend i = (checkedFrontend.produce i).map Prod.fst
  unambiguous : S.Unambiguous
  approved : S.Approved
  allPipelines : S.AllPipelines
  nonVacuous : S.NonVacuous

end Solidity.Lowering.P8.P8a
