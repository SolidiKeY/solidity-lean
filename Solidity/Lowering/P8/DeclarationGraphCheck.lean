import Solidity.Lowering.P8.DeclarationGraphAdmission
import Solidity.Lowering.V07.LocationGraphProducer

/-! Concrete fail-closed location-graph computation. Success carries actual
certificates, including complete selected physical declaration identities.
Failure is not Source rejection; success is not Source refusal or totality.
The H24 companion's declarationGraphs field remains separately required.
-/
namespace Solidity.Lowering.P8.DeclarationGraphCheck
open V07.LocationGraphInterface

abbrev Certificate (E : Source.Env) (loc : Source.DataLoc) :=
  (n : Nat) × (G : TypeGraph.Schema n) × LocationDeclarationGraph E loc G

structure OriginGraphs (E : Source.Env) where
  storage : Certificate E .storage
  memory : Certificate E .memory
  calldata : Certificate E .calldata

/-- Every successful component returns its computed graph and certificate. -/
def checkLocation (origin : Name) (E : Source.Env) (loc : Source.DataLoc) :
    Option (Certificate E loc) := do
  let result ← V07.LocationGraphProducer.produce origin E loc
  pure ⟨_, result.1, result.2⟩

/-- All three views use the same environment and physical declaration IDs.
A storage-only declaration may have an empty memory/calldata view under H15. -/
def checkOrigin (origin : Name) (E : Source.Env) : Option (OriginGraphs E) := do
  let storage ← checkLocation origin E .storage
  let memory ← checkLocation origin E .memory
  let calldata ← checkLocation origin E .calldata
  pure ⟨storage, memory, calldata⟩

/-- The exact admitted Source origin and artifact; no substituted environment.
No all-admitted success or Source-refusal conclusion is supplied. -/
def checkAccepted {S : P8a.Spec} {reference : P8a.OperationalReference}
    {origins : P8a.SourceOrigins S} {roots : P8a.RootModel S}
    (producer : P8a.Producer S reference origins roots)
    (i : S.Input) (r : S.Resolved) (h : producer.admission.frontend i = some r)
    (art : Roadmap.Artifact) (origin : Name) :
    Option (OriginGraphs (V07.P8Bindings.acceptedSource producer i r h art).1) :=
  checkOrigin origin (V07.P8Bindings.acceptedSource producer i r h art).1

end Solidity.Lowering.P8.DeclarationGraphCheck
