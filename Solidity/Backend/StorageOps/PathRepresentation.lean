import Solidity.Backend.StorageOps.CopyTransport

/-! Operation-side application of PUBLIC represented graph queries through
actual typed find/save paths. Prefixes may be arbitrarily long; logical retained
reads are not silently replaced by live reads or ordinary Source semantics. -/
namespace Solidity.Backend.StorageOps.PathRepresentation
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Focus the old root relation through an ACTUAL successful typed read.
Uses the owner's prefix/query laws; no new representation is defined. -/
theorem focus {n : Nat} {G : Schema n} {A B : TypeGraph.Ty n}
    (root : Value G A) (child : Value G B) (pre : TypeGraph.Path G A B)
    (found : root.find pre = some child) (queries : List (Query G B))
    (base : Solidity.Storage.Loc) (store : Store)
    (before : Represented root (queries.map (Query.prefix pre)) base store) :
    Represented child queries (pathLoc pre base) store := by
  intro q member
  have oldRep := before (q.prefix pre) (List.mem_map.mpr ⟨q, member, rfl⟩)
  refine ⟨((Query.supported_prefix pre q).mp oldRep.1).2, ?_, ?_⟩
  · rw [← Query.compatible_prefix root child pre q found]
    exact oldRep.2.1
  · intro word observed
    rw [← Query.location_prefix]
    apply oldRep.2.2 word
    rwa [Query.read_prefix root child pre q found]

private theorem array_prefix_supported {n : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy}
    (root : Value G A) (pre : TypeGraph.Path G A (.array (.prim p))) (indices : List Index)
    (base : Solidity.Storage.Loc) (store : Store)
    (before : Represented root ((PrimitivePop.queries indices).map (Query.prefix pre)) base store) :
    PathSupported pre :=
  ((Query.supported_prefix pre (.length .nil)).mp
    (before ((Query.length .nil).prefix pre) (List.mem_map.mpr ⟨_, List.mem_cons_self, rfl⟩)).1).1

/-- Actual two captured typed root reads and destination save are connected to
current-header numeric copy and full selected ROOT result representation.
No disjointness/exclusion of aliases is assumed; source is captured before save. -/
theorem copy_at {n N L R : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash preimages locations)
    (root result : Value G A) (dst src : TypeGraph.Path G A (.array (.prim p)))
    (old snapshot : Value G (.array (.prim p)))
    (readDst : root.find dst = some old) (readSrc : root.find src = some snapshot)
    (copied : recursiveCopyAt root dst src = some result) (indices : List Index)
    (base : Solidity.Storage.Loc) (captured : Store) (initial : WordStore)
    (beforeDst : Represented root ((PrimitivePop.queries indices).map (Query.prefix dst)) base captured)
    (beforeSrc : Represented root ((PrimitivePop.queries indices).map (Query.prefix src)) base captured)
    (transport : Transport N hash locations captured initial)
    (dstHeader : pathLoc dst base ∈ locations) (srcHeader : pathLoc src base ∈ locations)
    (dstCovered : ∀ i ∈ indices, Solidity.Storage.Loc.data (pathLoc dst base) i.val ∈ locations)
    (srcCovered : ∀ i ∈ indices, Solidity.Storage.Loc.data (pathLoc src base) i.val ∈ locations)
    (sourceCovered : ∀ i < snapshot.length.val, Solidity.Storage.Loc.data (pathLoc src base) i ∈ locations)
    (visitedCovered : ∀ i < max old.length.val snapshot.length.val,
      Solidity.Storage.Loc.data (pathLoc dst base) i ∈ locations) :
    let after := CopyTransport.symbolicCopy (pathLoc dst base) (pathLoc src base) captured
    let final := NumericTraversal.copy N hash (pathLoc dst base) (pathLoc src base) initial
    Transport N hash locations after final ∧
      Represented result ((PrimitivePop.queries indices).map (Query.prefix dst)) base after := by
  have complete := CopyTransport.complete run old snapshot indices (pathLoc dst base) (pathLoc src base)
    captured initial (focus root old dst readDst _ base captured beforeDst)
    (focus root snapshot src readSrc _ base captured beforeSrc) transport dstHeader srcHeader
    dstCovered srcCovered sourceCovered visitedCovered
  refine ⟨complete.1, ?_⟩
  exact Represented.prefix dst
    (recursiveCopyAt_readback root result dst src old snapshot readDst readSrc copied)
    (array_prefix_supported root dst indices base captured beforeDst) complete.2

/-- Actual popAt exposes its independently executed child operation/save.
The numeric header/reset and full selected child relation lift to ROOT queries. -/
theorem pop_at {n N L R : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash preimages locations)
    (root result : Value G A) (pre : TypeGraph.Path G A (.array (.prim p)))
    (old : Value G (.array (.prim p))) (found : root.find pre = some old)
    (popped : popAt root pre = some result) (indices : List Index)
    (base : Solidity.Storage.Loc) (captured : Store) (initial : WordStore)
    (before : Represented root ((PrimitivePop.queries indices).map (Query.prefix pre)) base captured)
    (transport : Transport N hash locations captured initial)
    (covered : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, q.location (pathLoc pre base) ∈ locations)
    (lastCovered : Solidity.Storage.Loc.data (pathLoc pre base) (old.length.val - 1) ∈ locations) :
    ∃ child final,
      result.find pre = some child ∧ PrimitivePop.execute N hash (pathLoc pre base) initial = some final ∧
      let after := Representation.write
        (Representation.write captured (.data (pathLoc pre base) (old.length.val - 1)) ClearDemands.zero)
        (pathLoc pre base) (lengthWord child.length.val child.length.isLt)
      Transport N hash locations after final ∧
        Represented result ((PrimitivePop.queries indices).map (Query.prefix pre)) base after := by
  obtain ⟨actual, child, read, changed, saved⟩ :=
    modifyAt_success root result pre recursivePop popped
  rw [found] at read
  cases read
  have readBack := Value.find_save root result pre child saved
  obtain ⟨final, executed, represented, transported, _, _⟩ := PrimitivePop.complete_numeric run old child changed
    indices (pathLoc pre base) captured initial (focus root old pre found _ base captured before)
    transport covered lastCovered
  exact ⟨child, final, readBack, executed, transported,
    Represented.prefix pre readBack (array_prefix_supported root pre indices base captured before) represented⟩

/-- info: 'Solidity.Backend.StorageOps.PathRepresentation.focus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms focus
/-- info: 'Solidity.Backend.StorageOps.PathRepresentation.copy_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy_at
/-- info: 'Solidity.Backend.StorageOps.PathRepresentation.pop_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pop_at

end Solidity.Backend.StorageOps.PathRepresentation
