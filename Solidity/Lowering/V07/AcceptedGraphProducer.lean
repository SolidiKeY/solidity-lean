import Solidity.Lowering.V07.P8Bindings
import Solidity.Lowering.V07.RecursiveGraph
import Solidity.Lowering.V07.GraphAdmissionBoundary

/-! G18.01's computed graph producer bound to the EXACT frozen P8a origin.
Successful checks return a real certificate. None does not reject Source.
No assumption that all producer-admitted inputs pass these checks is supplied. Everything indexed by `P8a.Producer` is vacuous until P8-SPEC-LAW1 is
resolved: the frozen V1 `Producer` is uninhabited over the current `Nat`
resource (`Lowering/P8/ResourceContractLaw1.lean`). -/
namespace Solidity.Lowering.V07.AcceptedGraphProducer
open Solidity.Lowering.P8
open P8Bindings
variable {S : P8a.Spec} {reference : P8a.OperationalReference}
  {origins : P8a.SourceOrigins S} {roots : P8a.RootModel S}

def produce (producer : P8a.Producer S reference origins roots)
    (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r)
    (art : Roadmap.Artifact) (origin : Name) (loc : Source.DataLoc) :
    Option ((G : TypeGraph.Schema (PrimitiveGraph.nodes (acceptedSource producer i r h art).1).length) ×
      AcceptedGraph producer i r h art loc G) :=
  RecursiveGraph.produce origin (acceptedSource producer i r h art).1 loc

theorem successful (producer : P8a.Producer S reference origins roots)
    (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r)
    (art : Roadmap.Artifact) (origin : Name) (loc : Source.DataLoc)
    (success : (produce producer i r h art origin loc).isSome = true) :
    ∃ n, ∃ G : TypeGraph.Schema n, Nonempty (AcceptedGraph producer i r h art loc G) := by
  let result := (produce producer i r h art origin loc).get success
  exact ⟨_,result.1,⟨result.2⟩⟩

/-- Origin invariant on the `directEnv` fixture (a restatement of
`direct_not_certifiable` for a supplied producer; no totality premise). Not a
proposed source-profile exclusion or added premise. -/
theorem certificate_excludes_inline_self_origin (producer : P8a.Producer S reference origins roots)
    (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r)
    (art : Roadmap.Artifact) (loc : Source.DataLoc)
    (existsGraph : ∃ n, ∃ G : TypeGraph.Schema n,
      Nonempty (AcceptedGraph producer i r h art loc G)) :
    (acceptedSource producer i r h art).1 ≠ GraphAdmissionBoundary.directEnv := by
  intro same
  obtain ⟨n,G,⟨c⟩⟩ := existsGraph
  have moved : DeclarationGraph GraphAdmissionBoundary.directEnv loc G :=
    Eq.mp (congrArg (fun E => DeclarationGraph E loc G) same) c
  exact GraphAdmissionBoundary.direct_not_certifiable loc G ⟨moved⟩

/-- The exact requested output still needs origin-admission invariants, not
merely an external frozen record with no graph/inline-cycle obligation. -/
theorem inline_self_origin_fails (producer : P8a.Producer S reference origins roots)
    (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r)
    (art : Roadmap.Artifact) (origin : Name) (loc : Source.DataLoc)
    (same : (acceptedSource producer i r h art).1 = GraphAdmissionBoundary.directEnv) :
    produce producer i r h art origin loc = none := by
  cases he : produce producer i r h art origin loc with
  | none => rfl
  | some result =>
    have success : (produce producer i r h art origin loc).isSome = true := by rw [he]; rfl
    exact False.elim (certificate_excludes_inline_self_origin producer i r h art loc
      (successful producer i r h art origin loc success) same)

end Solidity.Lowering.V07.AcceptedGraphProducer
