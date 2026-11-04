import Solidity.Backend.StorageOps.TargetOperations

/-! H26 G27 layout and reached-execution endpoints for downstream consumers.
All pending laws are explicit fields over published intrinsic types. No global
producer, new representation, hash premise or executable machine is postulated.
`Evm.run` is the existing intrinsic target boundary, not raw EVM bytecode.
The execution field is definitionally the equation used by the already-public
MemoryCopies.LocationStepPremise; no Source-dependent import is introduced. -/
namespace Solidity.Backend.StorageOps.ProducerInterface
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Agreement of a typed graph path and the actual selected target operand.
Support/word bounds do not assert path liveness, Source origin or authority. -/
structure PathEndpoint {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
 (path : TypeGraph.Path G A B) (base : Solidity.Storage.Loc) (slot : Evm.Slot) : Prop where
 supported : PathSupported path
 fits : TargetOperations.KeysFit base
 image : slot=TargetOperations.toSlot (pathLoc path base) (TargetOperations.path_keysFit path base fits)

/-- Published graph, finite-run numeric and symbolic-target observations at
ONE reached state. Query coverage and all per-run region/bound premises remain
explicit. This does not identify ordinary Source paths or packed byte stores. -/
structure StateEndpoint {n N L R : Nat} {G : Schema n} {A : TypeGraph.Ty n}
 (root : Value G A) (queries : List (Query G A)) (base : Solidity.Storage.Loc)
 (hash : Solidity.Storage.Pre → Nat) (preimages : List Solidity.Storage.Pre)
 (locations : List Solidity.Storage.Loc) (symbolic : Store) (numeric : WordStore)
 (target : Evm.Machine) : Prop where
 represented : Represented root queries base symbolic
 run : FiniteRun N L R hash preimages locations
 transport : Transport N hash locations symbolic numeric
 covered : ∀ q ∈ queries,q.location base ∈ locations
 fitting : ∀ l ∈ locations,TargetOperations.KeysFit l
 observations : ∀ l (member : l ∈ locations),
   target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (symbolic l)

/-- Actual selected code reaches the SAME target state whose observations
are certified. The execution equation converts directly to the existing
MemoryCopies.LocationStepPremise. No compiler selection/source adequacy law is
inferred from these fields, and no unconditional producer instance is supplied. -/
structure ReachedEndpoint {n N L R : Nat} {G : Schema n} {A : TypeGraph.Ty n}
 (root : Value G A) (queries : List (Query G A)) (base : Solidity.Storage.Loc)
 (hash : Solidity.Storage.Pre → Nat) (preimages : List Solidity.Storage.Pre)
 (locations : List Solidity.Storage.Loc) (symbolic : Store) (numeric : WordStore)
 (code : List Evm.Instr) (before after : Evm.Machine) : Prop where
 state : StateEndpoint (N:=N) (L:=L) (R:=R) root queries base hash preimages locations symbolic numeric after
 execution : Evm.run code before=.ok after 0

end Solidity.Backend.StorageOps.ProducerInterface
