import Solidity.Backend.MemoryCopies.Premises
import Solidity.Backend.StorageOps.ProducerInterface

/-! Consume the published reached-storage endpoint at the unchanged local
composition boundary. No universal storage producer is constructed here. -/
namespace Solidity.Backend.MemoryCopies
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

variable {n N L R : Nat} {G : Schema n} {A : TypeGraph.Ty n}
    {root : Value G A} {queries : List (Query G A)} {base : Solidity.Storage.Loc}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} {symbolic : Store} {numeric : WordStore}
    {code : List Evm.Instr} {before after : Evm.Machine}

structure PublishedStorageConsumer
    (endpoint : StorageOps.ProducerInterface.ReachedEndpoint (N:=N) (L:=L) (R:=R)
      root queries base hash preimages locations symbolic numeric code before after) : Prop where
  step : LocationStepPremise code before after
  compose : ∀ (firstCode : List Evm.Instr) (initial : Evm.Machine),
    LocationStepPremise firstCode initial before → LocationStepPremise (firstCode ++ code) initial after
end Solidity.Backend.MemoryCopies
