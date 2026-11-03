import Solidity.Backend.StorageOps.PrimitiveSnapshotSequence

/-! Actual dependent ROOT snapshots: the second copy consumes the first
copied destination, including its implicit-default/presence behavior. -/
namespace Solidity.Backend.StorageOps.PrimitiveSnapshotDependent
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph PrimitiveSnapshotSequence

private theorem queries_append {n : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy} {m : FixedSize}
 (path : TypeGraph.Path G A (.fixed (.prim p) m)) (a b : List (Fin m.val)) :
 queries path (a++b)=queries path a++queries path b := by
 simp only [queries,List.map_append]

/-- The second source IS the first destination. Its CURRENT readback and owner
come from the first ACTUAL copy, never an inapplicable OLD-source frame.
Only OLD source/frame evidence and actual operation facts are premises. -/
theorem complete {n N L R : Nat} {G : Schema n} {A : TypeGraph.Ty n}
 {p : PrimTy} {m : FixedSize}
 {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations)
 (root middle result : Value G A)
 (da sa : TypeGraph.Path G A (.fixed (.prim p) m)) (db : TypeGraph.Path G A (.fixed (.prim p) m))
 (oldA snapshotA : Value G (.fixed (.prim p) m)) (oldB : Value G (.fixed (.prim p) m))
 (readDa : root.find da=some oldA) (readSa : root.find sa=some snapshotA)
 (copyA : recursiveCopyAt root da sa=some middle)
 (readDb : middle.find db=some oldB)
 (copyB : recursiveCopyAt middle db da=some result)
 (supportedA : PathSupported da) (supportedB : PathSupported db)
 (indicesA : List (Fin m.val)) (indicesB : List (Fin m.val)) (frames : List (Query G A))
 (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base)
 (captured : Store) (initial : WordStore) (machine : Evm.Machine)
 (before : Transport N hash locations captured initial)
 (sourceA : Represented root (queries sa (indicesA++indicesB)) base captured)
 (oldFrames : Represented root frames base captured)
 (apartA : ∀ q ∈ frames,q.apart da)
 (outsideA : ∀ q ∈ frames,∀ i<m.val,q.location base≠(pathLoc da base).add i)
 (apartB : ∀ q ∈ queries da indicesA++frames,q.apart db)
 (outsideB : ∀ q ∈ queries da indicesA++frames,∀ j<m.val,q.location base≠(pathLoc db base).add j)
 (dstA : ∀ i<m.val,(pathLoc da base).add i ∈ locations) (srcA : ∀ i<m.val,(pathLoc sa base).add i ∈ locations)
 (dstB : ∀ j<m.val,(pathLoc db base).add j ∈ locations)
 (fitting : ∀ l ∈ locations,TargetOperations.KeysFit l)
 (initialAgreement : ∀ l (member : l ∈ locations),machine.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (initial (l.word N hash))) :
 let storeA := PrimitiveSnapshotNumeric.symbolic captured (pathLoc da base) (pathLoc sa base) m.val
 let numericA := PrimitiveSnapshotNumeric.numeric N hash initial (pathLoc da base) (pathLoc sa base) m.val
 let targetA := TargetFixedSnapshot.afterCopy p m machine
  (TargetOperations.toSlot (pathLoc sa base) (TargetOperations.path_keysFit sa base fits))
  (TargetOperations.toSlot (pathLoc da base) (TargetOperations.path_keysFit da base fits))
 let finalStore := PrimitiveSnapshotNumeric.symbolic storeA (pathLoc db base) (pathLoc da base) m.val
 let finalNumeric := PrimitiveSnapshotNumeric.numeric N hash numericA (pathLoc db base) (pathLoc da base) m.val
 let finalTarget := TargetFixedSnapshot.afterCopy p m targetA
  (TargetOperations.toSlot (pathLoc da base) (TargetOperations.path_keysFit da base fits))
  (TargetOperations.toSlot (pathLoc db base) (TargetOperations.path_keysFit db base fits))
 result.find db=some (recursiveCopy oldB (recursiveCopy oldA snapshotA)) ∧
 Represented result (queries db indicesB++(queries da indicesA++frames)) base finalStore ∧
 Transport N hash locations finalStore finalNumeric ∧
 Evm.run (TargetFixedSnapshot.code p m
  (TargetOperations.toSlot (pathLoc sa base) (TargetOperations.path_keysFit sa base fits))
  (TargetOperations.toSlot (pathLoc da base) (TargetOperations.path_keysFit da base fits)) ++
  TargetFixedSnapshot.code p m
  (TargetOperations.toSlot (pathLoc da base) (TargetOperations.path_keysFit da base fits))
  (TargetOperations.toSlot (pathLoc db base) (TargetOperations.path_keysFit db base fits))) machine=.ok finalTarget 0 ∧
 (∀ l (member : l ∈ locations),finalTarget.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (finalNumeric (l.word N hash))) := by
 have targetBefore : ∀ l (member : l ∈ locations),machine.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (captured l) := by
  intro l member
  exact (initialAgreement l member).trans (congrArg TargetOperations.encodeWord (before l member))
 have first := PrimitiveSnapshotFrames.complete run root middle da sa oldA snapshotA readDa readSa copyA supportedA
  (indicesA++indicesB) frames base fits captured initial machine before sourceA oldFrames apartA outsideA srcA dstA fitting targetBefore
 have selected : Represented middle ((queries da indicesA++queries da indicesB)++frames) base
   (PrimitiveSnapshotNumeric.symbolic captured (pathLoc da base) (pathLoc sa base) m.val) := by
  have owned := first.2.1
  change Represented middle (queries da (indicesA++indicesB)++frames) base _ at owned
  rwa [queries_append] at owned
 have sourceB : Represented middle (queries da indicesB) base
   (PrimitiveSnapshotNumeric.symbolic captured (pathLoc da base) (pathLoc sa base) m.val) := by
  intro q member
  exact selected q (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr member))))
 have newFrames : Represented middle (queries da indicesA++frames) base
   (PrimitiveSnapshotNumeric.symbolic captured (pathLoc da base) (pathLoc sa base) m.val) := by
  intro q member
  rcases List.mem_append.mp member with copied|later
  · exact selected q (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl copied))))
  · exact selected q (List.mem_append.mpr (Or.inr later))
 have nextBefore : ∀ l (member : l ∈ locations),
  (TargetFixedSnapshot.afterCopy p m machine
   (TargetOperations.toSlot (pathLoc sa base) (TargetOperations.path_keysFit sa base fits))
   (TargetOperations.toSlot (pathLoc da base) (TargetOperations.path_keysFit da base fits))).store.cells
  (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord
   (PrimitiveSnapshotNumeric.symbolic captured (pathLoc da base) (pathLoc sa base) m.val l) := by
  intro l member
  exact (first.2.2.2.2 l member).trans (congrArg TargetOperations.encodeWord (first.2.2.1 l member))
 have second := PrimitiveSnapshotFrames.complete run middle result db da oldB (recursiveCopy oldA snapshotA) readDb first.1 copyB supportedB
  indicesB (queries da indicesA++frames) base fits _ _ _ first.2.2.1 sourceB newFrames apartB outsideB dstA dstB fitting nextBefore
 refine ⟨second.1,second.2.1,second.2.2.1,?_,second.2.2.2.2⟩
 rw [Evm.run_append_ok first.2.2.2.1]
 exact second.2.2.2.1


/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotDependent.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.PrimitiveSnapshotDependent
