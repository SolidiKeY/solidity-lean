import Solidity.Backend.MemoryCopies.PublishedStorageInterface

/-! Exact fields of the published storage endpoint discharge the existing
local execution premise. General producers and Source adequacy stay explicit. -/
namespace Solidity.Backend.MemoryCopies
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
variable {n N L R : Nat} {G : Schema n} {A : TypeGraph.Ty n}
    {root : Value G A} {queries : List (Query G A)} {base : Solidity.Storage.Loc}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} {symbolic : Store} {numeric : WordStore}
    {code : List Evm.Instr} {before after : Evm.Machine}

theorem published_storage_step
    (endpoint : StorageOps.ProducerInterface.ReachedEndpoint (N:=N) (L:=L) (R:=R)
      root queries base hash preimages locations symbolic numeric code before after) :
    LocationStepPremise code before after := ⟨endpoint.execution⟩

def publishedStorageConsumer
    (endpoint : StorageOps.ProducerInterface.ReachedEndpoint (N:=N) (L:=L) (R:=R)
      root queries base hash preimages locations symbolic numeric code before after) : PublishedStorageConsumer endpoint where
  step := published_storage_step endpoint
  compose := by
    intro firstCode initial firstStep
    constructor
    rw [Evm.run_append_ok firstStep.execution]
    exact endpoint.execution

theorem published_storage_same_store {original : Evm.Machine}
    (endpoint : StorageOps.ProducerInterface.StateEndpoint (N:=N) (L:=L) (R:=R)
      root queries base hash preimages locations symbolic numeric original)
    (target : Evm.Machine) (stores : target.store = original.store) :
    StorageOps.ProducerInterface.StateEndpoint (N:=N) (L:=L) (R:=R)
      root queries base hash preimages locations symbolic numeric target := by
  refine ⟨endpoint.represented,endpoint.run,endpoint.transport,endpoint.covered,endpoint.fitting,?_⟩
  intro location member
  rw [stores]
  exact endpoint.observations location member

#print axioms published_storage_step
#print axioms publishedStorageConsumer
#print axioms published_storage_same_store
end Solidity.Backend.MemoryCopies
