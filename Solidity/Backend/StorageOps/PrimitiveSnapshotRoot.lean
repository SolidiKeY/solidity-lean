import Solidity.Backend.StorageOps.PrimitiveSnapshotOwner
import Solidity.Backend.StorageOps.PathRepresentation

/-! Captured fixed primitive snapshots through existing typed ROOT paths.
No address evaluation, representation, liveness or source/compiler layer is added. -/
namespace Solidity.Backend.StorageOps.PrimitiveSnapshotRoot
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Actual successful root copy supplies the destination readback. Both source
and destination are captured from the OLD root, so aliases need not be disjoint.
Path support, physical regions and OLD agreements remain explicit. -/
theorem complete {n N L R : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy} {m : FixedSize}
 {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations)
 (root result : Value G A) (dst src : TypeGraph.Path G A (.fixed (.prim p) m))
 (old snapshot : Value G (.fixed (.prim p) m))
 (readDst : root.find dst=some old) (readSrc : root.find src=some snapshot)
 (copied : recursiveCopyAt root dst src=some result) (supported : PathSupported dst)
 (indices : List (Fin m.val)) (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base)
 (captured : Store) (initial : WordStore) (target : Evm.Machine)
 (before : Transport N hash locations captured initial)
 (sourceOwner : Represented root ((indices.map (PrimitiveSnapshotOwner.query (G:=G) (p:=p))).map (Query.prefix src)) base captured)
 (sourceCovered : ∀ i<m.val,(pathLoc src base).add i ∈ locations)
 (dstCovered : ∀ i<m.val,(pathLoc dst base).add i ∈ locations)
 (fitting : ∀ l ∈ locations,TargetOperations.KeysFit l)
 (targetBefore : ∀ l (member : l ∈ locations),target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (captured l)) :
 let dstLoc := pathLoc dst base
 let srcLoc := pathLoc src base
 let afterStore := PrimitiveSnapshotNumeric.symbolic captured dstLoc srcLoc m.val
 let afterNumeric := PrimitiveSnapshotNumeric.numeric N hash initial dstLoc srcLoc m.val
 let afterTarget := TargetFixedSnapshot.afterCopy p m target
  (TargetOperations.toSlot srcLoc (TargetOperations.path_keysFit src base fits))
  (TargetOperations.toSlot dstLoc (TargetOperations.path_keysFit dst base fits))
 result.find dst=some (recursiveCopy old snapshot) ∧
 Represented result ((indices.map (PrimitiveSnapshotOwner.query (G:=G) (p:=p))).map (Query.prefix dst)) base afterStore ∧
 Transport N hash locations afterStore afterNumeric ∧
 Evm.run (TargetFixedSnapshot.code p m
  (TargetOperations.toSlot srcLoc (TargetOperations.path_keysFit src base fits))
  (TargetOperations.toSlot dstLoc (TargetOperations.path_keysFit dst base fits))) target=.ok afterTarget 0 ∧
 (∀ l (member : l ∈ locations),afterTarget.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (afterNumeric (l.word N hash))) := by
 have localOwner := PathRepresentation.focus root snapshot src readSrc _ base captured sourceOwner
 have component := PrimitiveSnapshotOwner.complete run old snapshot indices (pathLoc dst base) (pathLoc src base)
  (TargetOperations.path_keysFit dst base fits) (TargetOperations.path_keysFit src base fits)
  captured initial target before localOwner sourceCovered dstCovered fitting targetBefore
 have readback := recursiveCopyAt_readback root result dst src old snapshot readDst readSrc copied
 exact ⟨readback,Represented.prefix dst readback supported component.1,component.2⟩

/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotRoot.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.PrimitiveSnapshotRoot
