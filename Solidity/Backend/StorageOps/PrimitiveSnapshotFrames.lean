import Solidity.Backend.StorageOps.PrimitiveSnapshotRoot

/-! Actual generated fixed snapshot writes frame OLD root observations.
Logical separation and physical span separation remain independent premises. -/
namespace Solidity.Backend.StorageOps.PrimitiveSnapshotFrames
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

theorem symbolic_outside (captured : Store) (dst src observer : Solidity.Storage.Loc) (count : Nat)
 (outside : ∀ i<count,observer≠dst.add i) :
 PrimitiveSnapshotNumeric.symbolic captured dst src count observer=captured observer := by
 induction count with
 | zero => rfl
 | succ count ih =>
  rw [PrimitiveSnapshotNumeric.symbolic,Representation.write_other _ _ _ _ (outside count (Nat.lt_succ_self _))]
  exact ih (fun i inside => outside i (by omega))

private theorem saved {n : Nat} {G : Schema n} {A T : TypeGraph.Ty n}
 (root result : Value G A) (dst src : TypeGraph.Path G A T) (old snapshot : Value G T)
 (readDst : root.find dst=some old) (readSrc : root.find src=some snapshot)
 (copied : recursiveCopyAt root dst src=some result) : root.save dst (recursiveCopy old snapshot)=some result := by
 simpa only [recursiveCopyAt,readSrc,readDst,Option.bind_some] using copied

/-- Frame all selected OLD demands outside the actual logical save and every
operation-generated physical word, without assuming post-copy preservation. -/
theorem represented_frame {n : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy} {m : FixedSize}
 (root result : Value G A) (dst src : TypeGraph.Path G A (.fixed (.prim p) m))
 (old snapshot : Value G (.fixed (.prim p) m))
 (readDst : root.find dst=some old) (readSrc : root.find src=some snapshot)
 (copied : recursiveCopyAt root dst src=some result)
 (queries : List (Query G A)) (base : Solidity.Storage.Loc) (captured : Store)
 (before : Represented root queries base captured)
 (apart : ∀ q ∈ queries,q.apart dst)
 (outside : ∀ q ∈ queries,∀ i<m.val,q.location base≠(pathLoc dst base).add i) :
 Represented result queries base (PrimitiveSnapshotNumeric.symbolic captured (pathLoc dst base) (pathLoc src base) m.val) := by
 have actualSave := saved root result dst src old snapshot readDst readSrc copied
 intro q member
 obtain ⟨supported,compatible,owner⟩:=before q member
 refine ⟨supported,?_,?_⟩
 · rw [Query.compatible_frame root result dst _ actualSave q (apart q member)]
   exact compatible
 · intro value observed
   rw [symbolic_outside captured _ _ _ _ (outside q member)]
   apply owner value
   rwa [Query.read_frame root result dst _ actualSave q (apart q member)] at observed

/-- Ancestor headers are not logically apart. The owner's exact header-save
law supplies their frame; the generated physical span must still miss them. -/
theorem represented_header {n : Nat} {G : Schema n} {A E : TypeGraph.Ty n} {p : PrimTy} {m : FixedSize}
 (root result : Value G A) (stem : TypeGraph.Path G A (.array E)) (i : Index)
 (tail : TypeGraph.Path G E (.fixed (.prim p) m))
 (src : TypeGraph.Path G A (.fixed (.prim p) m)) (old snapshot : Value G (.fixed (.prim p) m))
 (readDst : root.find (stem.append (.cons (.index i) tail))=some old) (readSrc : root.find src=some snapshot)
 (copied : recursiveCopyAt root (stem.append (.cons (.index i) tail)) src=some result)
 (base : Solidity.Storage.Loc) (captured : Store)
 (before : Represented root [.length stem] base captured)
 (outside : ∀ j<m.val,pathLoc stem base≠(pathLoc (stem.append (.cons (.index i) tail)) base).add j) :
 Represented result [.length stem] base
  (PrimitiveSnapshotNumeric.symbolic captured (pathLoc (stem.append (.cons (.index i) tail)) base) (pathLoc src base) m.val) := by
 have actualSave := saved root result _ src old snapshot readDst readSrc copied
 have header := ancestor_header_frame stem i tail root result (recursiveCopy old snapshot) actualSave
 intro q member
 have same : q=.length stem := List.mem_singleton.mp member
 subst q
 obtain ⟨supported,compatible,owner⟩:=before (.length stem) (List.mem_singleton.mpr rfl)
 refine ⟨supported,?_,?_⟩
 · simpa only [Query.compatible,header] using compatible
 · intro value observed
   change PrimitiveSnapshotNumeric.symbolic captured _ _ _ (pathLoc stem base)=value
   rw [symbolic_outside captured _ _ _ _ outside]
   apply owner value
   simpa only [Query.read,header] using observed

/-- Compose actual target execution with the derived copied ROOT owner and
OLD outside owners. Logical/path support, physical regions and OLD evidence
are premises; output ownership is a conclusion. -/
theorem complete {n N L R : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy} {m : FixedSize}
 {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations)
 (root result : Value G A) (dst src : TypeGraph.Path G A (.fixed (.prim p) m))
 (old snapshot : Value G (.fixed (.prim p) m))
 (readDst : root.find dst=some old) (readSrc : root.find src=some snapshot)
 (copied : recursiveCopyAt root dst src=some result) (supported : PathSupported dst)
 (indices : List (Fin m.val)) (queries : List (Query G A))
 (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base)
 (captured : Store) (initial : WordStore) (target : Evm.Machine)
 (before : Transport N hash locations captured initial)
 (sourceOwner : Represented root ((indices.map (PrimitiveSnapshotOwner.query (G:=G) (p:=p))).map (Query.prefix src)) base captured)
 (frameOwner : Represented root queries base captured)
 (apart : ∀ q ∈ queries,q.apart dst)
 (outside : ∀ q ∈ queries,∀ i<m.val,q.location base≠(pathLoc dst base).add i)
 (sourceCovered : ∀ i<m.val,(pathLoc src base).add i ∈ locations)
 (dstCovered : ∀ i<m.val,(pathLoc dst base).add i ∈ locations)
 (fitting : ∀ l ∈ locations,TargetOperations.KeysFit l)
 (targetBefore : ∀ l (member : l ∈ locations),target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (captured l)) :
 let afterStore := PrimitiveSnapshotNumeric.symbolic captured (pathLoc dst base) (pathLoc src base) m.val
 let afterNumeric := PrimitiveSnapshotNumeric.numeric N hash initial (pathLoc dst base) (pathLoc src base) m.val
 let afterTarget := TargetFixedSnapshot.afterCopy p m target
  (TargetOperations.toSlot (pathLoc src base) (TargetOperations.path_keysFit src base fits))
  (TargetOperations.toSlot (pathLoc dst base) (TargetOperations.path_keysFit dst base fits))
 result.find dst=some (recursiveCopy old snapshot) ∧
 Represented result (((indices.map (PrimitiveSnapshotOwner.query (G:=G) (p:=p))).map (Query.prefix dst))++queries) base afterStore ∧
 Transport N hash locations afterStore afterNumeric ∧
 Evm.run (TargetFixedSnapshot.code p m
  (TargetOperations.toSlot (pathLoc src base) (TargetOperations.path_keysFit src base fits))
  (TargetOperations.toSlot (pathLoc dst base) (TargetOperations.path_keysFit dst base fits))) target=.ok afterTarget 0 ∧
 (∀ l (member : l ∈ locations),afterTarget.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (afterNumeric (l.word N hash))) := by
 have component := PrimitiveSnapshotRoot.complete run root result dst src old snapshot readDst readSrc copied supported
  indices base fits captured initial target before sourceOwner sourceCovered dstCovered fitting targetBefore
 have frame := represented_frame root result dst src old snapshot readDst readSrc copied queries base captured frameOwner apart outside
 refine ⟨component.1,?_,component.2.2⟩
 intro q member
 rcases List.mem_append.mp member with copiedQuery|framedQuery
 · exact component.2.1 q copiedQuery
 · exact frame q framedQuery

/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotFrames.symbolic_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms symbolic_outside
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotFrames.represented_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_frame
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotFrames.represented_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_header
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotFrames.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.PrimitiveSnapshotFrames
