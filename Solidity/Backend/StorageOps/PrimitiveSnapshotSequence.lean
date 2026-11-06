import Solidity.Backend.StorageOps.PrimitiveSnapshotFrames

/-! Two actual ROOT copies with derived intermediate owners. Existing paths,
values, selected representation and actual target programs are reused. -/
namespace Solidity.Backend.StorageOps.PrimitiveSnapshotSequence
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def queries {n : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy} {m : FixedSize}
 (path : TypeGraph.Path G A (.fixed (.prim p) m)) (indices : List (Fin m.val)) : List (Query G A) :=
 (indices.map (PrimitiveSnapshotOwner.query (G:=G) (p:=p))).map (Query.prefix path)

/-- OLD source and frame evidence derive the second operation's source owner;
no intermediate/final owner or preservation theorem is supplied as a premise.
Actual Option successes/reads remain explicit; no world rollback is inferred. -/
theorem complete {n N L R : Nat} {G : Schema n} {A : TypeGraph.Ty n}
 {pa pb : PrimTy} {ma mb : FixedSize}
 {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations)
 (root middle result : Value G A)
 (da sa : TypeGraph.Path G A (.fixed (.prim pa) ma)) (db sb : TypeGraph.Path G A (.fixed (.prim pb) mb))
 (oldA snapshotA : Value G (.fixed (.prim pa) ma)) (oldB snapshotB : Value G (.fixed (.prim pb) mb))
 (readDa : root.find da=some oldA) (readSa : root.find sa=some snapshotA)
 (copyA : recursiveCopyAt root da sa=some middle)
 (readDb : middle.find db=some oldB) (readSb : middle.find sb=some snapshotB)
 (copyB : recursiveCopyAt middle db sb=some result)
 (supportedA : PathSupported da) (supportedB : PathSupported db)
 (indicesA : List (Fin ma.val)) (indicesB : List (Fin mb.val)) (frames : List (Query G A))
 (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base)
 (captured : Store) (initial : WordStore) (machine : Evm.Machine)
 (before : Transport N hash locations captured initial)
 (sourceA : Represented root (queries sa indicesA) base captured)
 (oldFrames : Represented root (queries sb indicesB++frames) base captured)
 (apartA : ∀ q ∈ queries sb indicesB++frames,q.apart da)
 (outsideA : ∀ q ∈ queries sb indicesB++frames,∀ i<ma.val,q.location base≠(pathLoc da base).add i)
 (apartB : ∀ q ∈ queries da indicesA++frames,q.apart db)
 (outsideB : ∀ q ∈ queries da indicesA++frames,∀ j<mb.val,q.location base≠(pathLoc db base).add j)
 (dstA : ∀ i<ma.val,(pathLoc da base).add i ∈ locations) (srcA : ∀ i<ma.val,(pathLoc sa base).add i ∈ locations)
 (dstB : ∀ j<mb.val,(pathLoc db base).add j ∈ locations) (srcB : ∀ j<mb.val,(pathLoc sb base).add j ∈ locations)
 (fitting : ∀ l ∈ locations,TargetOperations.KeysFit l)
 (initialAgreement : ∀ l (member : l ∈ locations),machine.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (initial (l.word N hash))) :
 let storeA := PrimitiveSnapshotNumeric.symbolic captured (pathLoc da base) (pathLoc sa base) ma.val
 let numericA := PrimitiveSnapshotNumeric.numeric N hash initial (pathLoc da base) (pathLoc sa base) ma.val
 let targetA := TargetFixedSnapshot.afterCopy pa ma machine
  (TargetOperations.toSlot (pathLoc sa base) (TargetOperations.path_keysFit sa base fits))
  (TargetOperations.toSlot (pathLoc da base) (TargetOperations.path_keysFit da base fits))
 let finalStore := PrimitiveSnapshotNumeric.symbolic storeA (pathLoc db base) (pathLoc sb base) mb.val
 let finalNumeric := PrimitiveSnapshotNumeric.numeric N hash numericA (pathLoc db base) (pathLoc sb base) mb.val
 let finalTarget := TargetFixedSnapshot.afterCopy pb mb targetA
  (TargetOperations.toSlot (pathLoc sb base) (TargetOperations.path_keysFit sb base fits))
  (TargetOperations.toSlot (pathLoc db base) (TargetOperations.path_keysFit db base fits))
 result.find db=some (recursiveCopy oldB snapshotB) ∧
 Represented result (queries db indicesB++(queries da indicesA++frames)) base finalStore ∧
 Transport N hash locations finalStore finalNumeric ∧
 Evm.run (TargetFixedSnapshot.code pa ma
  (TargetOperations.toSlot (pathLoc sa base) (TargetOperations.path_keysFit sa base fits))
  (TargetOperations.toSlot (pathLoc da base) (TargetOperations.path_keysFit da base fits)) ++
  TargetFixedSnapshot.code pb mb
  (TargetOperations.toSlot (pathLoc sb base) (TargetOperations.path_keysFit sb base fits))
  (TargetOperations.toSlot (pathLoc db base) (TargetOperations.path_keysFit db base fits))) machine=.ok finalTarget 0 ∧
 (∀ l (member : l ∈ locations),finalTarget.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (finalNumeric (l.word N hash))) := by
 have targetBefore : ∀ l (member : l ∈ locations),machine.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (captured l) := by
  intro l member
  exact (initialAgreement l member).trans (congrArg TargetOperations.encodeWord (before l member))
 have first := PrimitiveSnapshotFrames.complete run root middle da sa oldA snapshotA readDa readSa copyA supportedA
  indicesA (queries sb indicesB++frames) base fits captured initial machine before sourceA oldFrames apartA outsideA srcA dstA fitting targetBefore
 have sourceB : Represented middle (queries sb indicesB) base
   (PrimitiveSnapshotNumeric.symbolic captured (pathLoc da base) (pathLoc sa base) ma.val) := by
  intro q member
  exact first.2.1 q (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl member))))
 have newFrames : Represented middle (queries da indicesA++frames) base
   (PrimitiveSnapshotNumeric.symbolic captured (pathLoc da base) (pathLoc sa base) ma.val) := by
  intro q member
  rcases List.mem_append.mp member with copied|later
  · exact first.2.1 q (List.mem_append.mpr (Or.inl copied))
  · exact first.2.1 q (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr later))))
 have nextBefore : ∀ l (member : l ∈ locations),
  (TargetFixedSnapshot.afterCopy pa ma machine
   (TargetOperations.toSlot (pathLoc sa base) (TargetOperations.path_keysFit sa base fits))
   (TargetOperations.toSlot (pathLoc da base) (TargetOperations.path_keysFit da base fits))).store.cells
  (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord
   (PrimitiveSnapshotNumeric.symbolic captured (pathLoc da base) (pathLoc sa base) ma.val l) := by
  intro l member
  exact (first.2.2.2.2 l member).trans (congrArg TargetOperations.encodeWord (first.2.2.1 l member))
 have second := PrimitiveSnapshotFrames.complete run middle result db sb oldB snapshotB readDb readSb copyB supportedB
  indicesB (queries da indicesA++frames) base fits _ _ _ first.2.2.1 sourceB newFrames apartB outsideB srcB dstB fitting nextBefore
 refine ⟨second.1,second.2.1,second.2.2.1,?_,second.2.2.2.2⟩
 rw [Evm.run_append_ok first.2.2.2.1]
 exact second.2.2.2.1

/-- The shared ancestor header is framed through both ACTUAL saves without
pretending it is logically apart from a descendant operation. -/
theorem headers {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n} {pa pb : PrimTy} {ma mb : FixedSize}
 (root middle result : Value G A) (stem : TypeGraph.Path G A (.array E))
 (ia ib : Index) (ta : TypeGraph.Path G E (.fixed (.prim pa) ma)) (tb : TypeGraph.Path G E (.fixed (.prim pb) mb))
 (sa : TypeGraph.Path G A (.fixed (.prim pa) ma)) (sb : TypeGraph.Path G A (.fixed (.prim pb) mb))
 (oldA snapshotA : Value G (.fixed (.prim pa) ma)) (oldB snapshotB : Value G (.fixed (.prim pb) mb))
 (readDa : root.find (stem.append (.cons (.index ia) ta))=some oldA) (readSa : root.find sa=some snapshotA)
 (copyA : recursiveCopyAt root (stem.append (.cons (.index ia) ta)) sa=some middle)
 (readDb : middle.find (stem.append (.cons (.index ib) tb))=some oldB) (readSb : middle.find sb=some snapshotB)
 (copyB : recursiveCopyAt middle (stem.append (.cons (.index ib) tb)) sb=some result)
 (base : Solidity.Storage.Loc) (captured : Store)
 (before : Represented root [.length stem] base captured)
 (outsideA : ∀ i<ma.val,pathLoc stem base≠(pathLoc (stem.append (.cons (.index ia) ta)) base).add i)
 (outsideB : ∀ j<mb.val,pathLoc stem base≠(pathLoc (stem.append (.cons (.index ib) tb)) base).add j) :
 Represented result [.length stem] base
  (PrimitiveSnapshotNumeric.symbolic
   (PrimitiveSnapshotNumeric.symbolic captured (pathLoc (stem.append (.cons (.index ia) ta)) base) (pathLoc sa base) ma.val)
   (pathLoc (stem.append (.cons (.index ib) tb)) base) (pathLoc sb base) mb.val) := by
 have first := PrimitiveSnapshotFrames.represented_header root middle stem ia ta sa oldA snapshotA
  readDa readSa copyA base captured before outsideA
 exact PrimitiveSnapshotFrames.represented_header middle result stem ib tb sb oldB snapshotB
  readDb readSb copyB base _ first outsideB

/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSequence.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotSequence.headers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms headers
end Solidity.Backend.StorageOps.PrimitiveSnapshotSequence
