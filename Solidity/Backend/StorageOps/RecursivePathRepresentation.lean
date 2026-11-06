import Solidity.Backend.StorageOps.CopyOutputInduction
import Solidity.Backend.StorageOps.PathRepresentation

/-! Actual typed-root recursive copy capture/save representation. Root and
child values/paths/stores are the published intrinsic interfaces. This is not
ordinary Source lowering, machine-discovered path checks or world rollback. -/
namespace Solidity.Backend.StorageOps.RecursivePathRepresentation
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- An actual successful operation exposes its original captured source and
destination plus the actual save. No desired preservation theorem is assumed. -/
theorem capture_success {n : Nat} {G : Schema n} {A T : TypeGraph.Ty n}
    (root result : Value G A) (dst src : TypeGraph.Path G A T)
    (copied : recursiveCopyAt root dst src = some result) :
    ∃ old snapshot, root.find dst = some old ∧ root.find src = some snapshot ∧
      root.save dst (recursiveCopy old snapshot) = some result := by
  unfold recursiveCopyAt at copied
  cases readSrc : root.find src with
  | none =>
    simp only [Option.bind_eq_bind,readSrc,Option.bind_none] at copied
    cases copied
  | some snapshot =>
    cases readDst : root.find dst with
    | none =>
      simp only [Option.bind_eq_bind,readSrc,readDst,Option.bind_some,Option.bind_none] at copied
      cases copied
    | some old =>
      refine ⟨old,snapshot,rfl,rfl,?_⟩
      simpa only [Option.bind_eq_bind,readSrc,readDst,Option.bind_some] using copied

/-- Actual recursive copied-root representation and generated numeric transport
through arbitrary finite typed destination/source prefixes. Aliases are NOT
excluded. Empty observation lists introduce no artificial path-support premise. -/
theorem copy_at {n N L R : Nat} {G : Schema n} {A T : TypeGraph.Ty n}
    (root result : Value G A) (dst src : TypeGraph.Path G A T)
    (old snapshot : Value G T) (permit : CopyPermit G T)
    (readDst : root.find dst = some old) (readSrc : root.find src = some snapshot)
    (copied : recursiveCopyAt root dst src = some result)
    (queries : List (Query G T)) (base : Solidity.Storage.Loc) (store : Store) (initial : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (beforeDst : Represented root (queries.map (Query.prefix dst)) base store)
    (beforeSrc : Represented root ((ClearDemands.demands snapshot).map (Query.prefix src)) base store)
    (before : Transport N hash locations store initial)
    (sourceCovered : ∀ q ∈ ClearDemands.demands snapshot, (q.prefix src).location base ∈ locations)
    (queriesCovered : ∀ q ∈ queries, (q.prefix dst).location base ∈ locations)
    (writesCovered : ∀ d ∈ CopyDemands.demands old snapshot, (d.prefix dst).location base ∈ locations)
    (separate : ∀ q ∈ queries, ∀ d ∈ CopyDemands.demands old snapshot,
      (d.prefix dst).location base = (q.prefix dst).location base → d.prefix dst = q.prefix dst) :
    let log := CopyWrites.updates (N := N) old snapshot (pathLoc dst base) (pathLoc src base) hash initial
    let after := log.foldl (fun w op => write w op.1 op.2) store
    Represented result (queries.map (Query.prefix dst)) base after ∧
    Transport N hash locations after
      (CopyWrites.numericCopy (N := N) old snapshot (pathLoc dst base) (pathLoc src base) hash initial) := by
  have child := CopyOutput.represented_copy old snapshot permit queries (pathLoc dst base) (pathLoc src base)
    store initial run (PathRepresentation.focus root old dst readDst queries base store beforeDst)
    (PathRepresentation.focus root snapshot src readSrc _ base store beforeSrc) before
    (fun q member => by simpa only [Query.location_prefix] using sourceCovered q member)
    (fun q member => by simpa only [Query.location_prefix] using queriesCovered q member)
    (fun d member => by simpa only [Query.location_prefix] using writesCovered d member)
    (by
      intro q member d written same
      apply CopyReadback.prefix_injective dst d q
      apply separate q member d written
      simpa only [Query.location_prefix] using same)
  refine ⟨?_,child.2⟩
  cases queries with
  | nil => intro q member; cases member
  | cons first rest =>
    have supported : PathSupported dst :=
      ((Query.supported_prefix dst first).mp
        (beforeDst (first.prefix dst) (List.mem_map.mpr ⟨first,List.mem_cons_self,rfl⟩)).1).1
    exact Represented.prefix dst (recursiveCopyAt_readback root result dst src old snapshot readDst readSrc copied)
      supported child.1

/-- Every selected successful ROOT observation agrees with the actual numeric
copy. This is a consequence of the derived ROOT relation and finite transport. -/
theorem copy_at_readback {n N L R : Nat} {G : Schema n} {A T : TypeGraph.Ty n}
    (root result : Value G A) (dst src : TypeGraph.Path G A T)
    (old snapshot : Value G T) (permit : CopyPermit G T)
    (readDst : root.find dst = some old) (readSrc : root.find src = some snapshot)
    (copied : recursiveCopyAt root dst src = some result)
    (queries : List (Query G T)) (base : Solidity.Storage.Loc) (store : Store) (initial : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (beforeDst : Represented root (queries.map (Query.prefix dst)) base store)
    (beforeSrc : Represented root ((ClearDemands.demands snapshot).map (Query.prefix src)) base store)
    (before : Transport N hash locations store initial)
    (sourceCovered : ∀ q ∈ ClearDemands.demands snapshot, (q.prefix src).location base ∈ locations)
    (queriesCovered : ∀ q ∈ queries, (q.prefix dst).location base ∈ locations)
    (writesCovered : ∀ d ∈ CopyDemands.demands old snapshot, (d.prefix dst).location base ∈ locations)
    (separate : ∀ q ∈ queries, ∀ d ∈ CopyDemands.demands old snapshot,
      (d.prefix dst).location base = (q.prefix dst).location base → d.prefix dst = q.prefix dst) :
    ∀ q ∈ queries, ∀ word, (q.prefix dst).read result = some word →
      CopyWrites.numericCopy (N := N) old snapshot (pathLoc dst base) (pathLoc src base) hash initial
        (((q.prefix dst).location base).word N hash) = word := by
  have complete := copy_at root result dst src old snapshot permit readDst readSrc copied queries base store initial
    run beforeDst beforeSrc before sourceCovered queriesCovered writesCovered separate
  intro q member word observed
  rw [complete.2 _ (queriesCovered q member)]
  exact (complete.1 (q.prefix dst) (List.mem_map.mpr ⟨q,member,rfl⟩)).2.2 word observed

theorem saved_after_copy {n : Nat} {G : Schema n} {A T : TypeGraph.Ty n}
    (root result : Value G A) (dst src : TypeGraph.Path G A T) (old snapshot : Value G T)
    (readDst : root.find dst = some old) (readSrc : root.find src = some snapshot)
    (copied : recursiveCopyAt root dst src = some result) :
    root.save dst (recursiveCopy old snapshot) = some result := by
  simpa only [recursiveCopyAt,Option.bind_eq_bind,readSrc,readDst,Option.bind_some] using copied

/-- Independent outside-ROOT source observations and actual numeric words frame
the whole generated recursive copy. Payload representation is unnecessary for
this frame, while logical Apart and finite symbolic nonalias are both explicit. -/
theorem frame_at {n N L R : Nat} {G : Schema n} {A T : TypeGraph.Ty n}
    (root result : Value G A) (dst src : TypeGraph.Path G A T) (old snapshot : Value G T)
    (readDst : root.find dst = some old) (readSrc : root.find src = some snapshot)
    (copied : recursiveCopyAt root dst src = some result)
    (queries : List (Query G A)) (base : Solidity.Storage.Loc) (store : Store) (initial : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (beforeQueries : Represented root queries base store) (before : Transport N hash locations store initial)
    (queriesCovered : ∀ q ∈ queries, q.location base ∈ locations)
    (writesCovered : ∀ d ∈ CopyDemands.demands old snapshot, (d.prefix dst).location base ∈ locations)
    (apart : ∀ q ∈ queries, q.apart dst)
    (nonalias : ∀ q ∈ queries, ∀ d ∈ CopyDemands.demands old snapshot,
      q.location base ≠ (d.prefix dst).location base) :
    let log := CopyWrites.updates (N := N) old snapshot (pathLoc dst base) (pathLoc src base) hash initial
    let after := log.foldl (fun w op => write w op.1 op.2) store
    Represented result queries base after ∧
    Transport N hash locations after
      (CopyWrites.numericCopy (N := N) old snapshot (pathLoc dst base) (pathLoc src base) hash initial) := by
  dsimp only
  have saved := saved_after_copy root result dst src old snapshot readDst readSrc copied
  have transported := transport_sequence run before
    (CopyWrites.updates (N := N) old snapshot (pathLoc dst base) (pathLoc src base) hash initial) (by
      intro op member
      obtain ⟨d,written,same⟩ := CopyWrites.generated old snapshot (pathLoc dst base) (pathLoc src base) hash initial op member
      rw [same]
      simpa only [Query.location_prefix] using writesCovered d written)
  refine ⟨?_,transported⟩
  intro q member
  obtain ⟨supported,compatible,oldRead⟩ := beforeQueries q member
  refine ⟨supported,?_,?_⟩
  · rw [Query.compatible_frame root result dst (recursiveCopy old snapshot) saved q (apart q member)]
    exact compatible
  · intro word observed
    have oldObserved : q.read root = some word := by
      rwa [Query.read_frame root result dst (recursiveCopy old snapshot) saved q (apart q member)] at observed
    have numericFrame := CopyWrites.numeric_outside (N := N) old snapshot (pathLoc dst base) (pathLoc src base)
      hash initial ((q.location base).word N hash) (by
        intro d written same
        apply nonalias q member d written
        have writtenCovered : d.location (pathLoc dst base) ∈ locations := by
          simpa only [Query.location_prefix] using writesCovered d written
        have equal := run.word_inj (queriesCovered q member) writtenCovered same
        simpa only [Query.location_prefix] using equal)
    exact (transported _ (queriesCovered q member)).symm.trans
      (numericFrame.trans ((before _ (queriesCovered q member)).trans (oldRead word oldObserved)))

/-- Destination observations and independently framed ROOT context compose
around the same actual generated numeric execution. No whole-world rollback or
Source/compiler relation is inferred from this local operation certificate. -/
theorem copy_at_context {n N L R : Nat} {G : Schema n} {A T : TypeGraph.Ty n}
    (root result : Value G A) (dst src : TypeGraph.Path G A T)
    (old snapshot : Value G T) (permit : CopyPermit G T)
    (readDst : root.find dst = some old) (readSrc : root.find src = some snapshot)
    (copied : recursiveCopyAt root dst src = some result)
    (queries : List (Query G T)) (outside : List (Query G A))
    (base : Solidity.Storage.Loc) (store : Store) (initial : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (beforeDst : Represented root (queries.map (Query.prefix dst)) base store)
    (beforeSrc : Represented root ((ClearDemands.demands snapshot).map (Query.prefix src)) base store)
    (beforeOutside : Represented root outside base store) (before : Transport N hash locations store initial)
    (sourceCovered : ∀ q ∈ ClearDemands.demands snapshot, (q.prefix src).location base ∈ locations)
    (queriesCovered : ∀ q ∈ queries, (q.prefix dst).location base ∈ locations)
    (outsideCovered : ∀ q ∈ outside, q.location base ∈ locations)
    (writesCovered : ∀ d ∈ CopyDemands.demands old snapshot, (d.prefix dst).location base ∈ locations)
    (separate : ∀ q ∈ queries, ∀ d ∈ CopyDemands.demands old snapshot,
      (d.prefix dst).location base = (q.prefix dst).location base → d.prefix dst = q.prefix dst)
    (apart : ∀ q ∈ outside, q.apart dst)
    (nonalias : ∀ q ∈ outside, ∀ d ∈ CopyDemands.demands old snapshot,
      q.location base ≠ (d.prefix dst).location base) :
    let log := CopyWrites.updates (N := N) old snapshot (pathLoc dst base) (pathLoc src base) hash initial
    let after := log.foldl (fun w op => write w op.1 op.2) store
    Represented result (queries.map (Query.prefix dst) ++ outside) base after ∧
    Transport N hash locations after
      (CopyWrites.numericCopy (N := N) old snapshot (pathLoc dst base) (pathLoc src base) hash initial) := by
  have inside := copy_at root result dst src old snapshot permit readDst readSrc copied queries base store initial run
    beforeDst beforeSrc before sourceCovered queriesCovered writesCovered separate
  have framed := frame_at root result dst src old snapshot readDst readSrc copied outside base store initial run
    beforeOutside before outsideCovered writesCovered apart nonalias
  refine ⟨?_,inside.2⟩
  intro q member
  rcases List.mem_append.mp member with child | context
  · exact inside.1 q child
  · exact framed.1 q context

/-- An actual copy saved below an array element preserves that ANCESTOR's
length AND retained extent, with actual generated numeric header framing.
This is distinct from the sibling Apart frame and uses the PUBLIC ancestor law. -/
theorem header_frame_at {n N L R : Nat} {G : Schema n} {A E T : TypeGraph.Ty n}
    (root result : Value G A) (dst src : TypeGraph.Path G A T) (old snapshot : Value G T)
    (readDst : root.find dst = some old) (readSrc : root.find src = some snapshot)
    (copied : recursiveCopyAt root dst src = some result)
    (stem : TypeGraph.Path G A (.array E)) (index : Index) (tail : TypeGraph.Path G E T)
    (shape : dst = stem.append (.cons (.index index) tail))
    (base : Solidity.Storage.Loc) (store : Store) (initial : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (beforeHeader : Represented root [.length stem] base store)
    (before : Transport N hash locations store initial)
    (headerCovered : pathLoc stem base ∈ locations)
    (writesCovered : ∀ d ∈ CopyDemands.demands old snapshot, (d.prefix dst).location base ∈ locations)
    (nonalias : ∀ d ∈ CopyDemands.demands old snapshot, pathLoc stem base ≠ (d.prefix dst).location base) :
    let log := CopyWrites.updates (N := N) old snapshot (pathLoc dst base) (pathLoc src base) hash initial
    let after := log.foldl (fun w op => write w op.1 op.2) store
    Represented result [.length stem] base after ∧
    Transport N hash locations after
      (CopyWrites.numericCopy (N := N) old snapshot (pathLoc dst base) (pathLoc src base) hash initial) := by
  dsimp only
  have saved := saved_after_copy root result dst src old snapshot readDst readSrc copied
  have header := ancestor_header_frame stem index tail root result (recursiveCopy old snapshot) (by
    rw [← shape]
    exact saved)
  have transported := transport_sequence run before
    (CopyWrites.updates (N := N) old snapshot (pathLoc dst base) (pathLoc src base) hash initial) (by
      intro op member
      obtain ⟨d,written,same⟩ := CopyWrites.generated old snapshot (pathLoc dst base) (pathLoc src base) hash initial op member
      rw [same]
      simpa only [Query.location_prefix] using writesCovered d written)
  refine ⟨?_,transported⟩
  intro q member
  have same := List.mem_singleton.mp member
  subst q
  obtain ⟨supported,compatible,oldRead⟩ := beforeHeader (.length stem) (List.mem_singleton_self _)
  refine ⟨supported,?_,?_⟩
  · simpa only [Query.compatible,header] using compatible
  · intro word observed
    have oldObserved : (Query.length stem).read root = some word := by
      simpa only [Query.read,header] using observed
    have numericFrame := CopyWrites.numeric_outside (N := N) old snapshot (pathLoc dst base) (pathLoc src base)
      hash initial ((pathLoc stem base).word N hash) (by
        intro d written same
        apply nonalias d written
        have writtenCovered : d.location (pathLoc dst base) ∈ locations := by
          simpa only [Query.location_prefix] using writesCovered d written
        have equal := run.word_inj headerCovered writtenCovered same
        simpa only [Query.location_prefix] using equal)
    exact (transported _ headerCovered).symm.trans
      (numericFrame.trans ((before _ headerCovered).trans (oldRead word oldObserved)))

/-- info: 'Solidity.Backend.StorageOps.RecursivePathRepresentation.capture_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms capture_success
/-- info: 'Solidity.Backend.StorageOps.RecursivePathRepresentation.copy_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_at
/-- info: 'Solidity.Backend.StorageOps.RecursivePathRepresentation.copy_at_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_at_readback
/-- info: 'Solidity.Backend.StorageOps.RecursivePathRepresentation.saved_after_copy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms saved_after_copy
/-- info: 'Solidity.Backend.StorageOps.RecursivePathRepresentation.frame_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms frame_at
/-- info: 'Solidity.Backend.StorageOps.RecursivePathRepresentation.copy_at_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_at_context
/-- info: 'Solidity.Backend.StorageOps.RecursivePathRepresentation.header_frame_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms header_frame_at

end Solidity.Backend.StorageOps.RecursivePathRepresentation
