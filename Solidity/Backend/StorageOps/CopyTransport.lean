import Solidity.Backend.StorageOps.NumericTraversal

/-! Actual finite generated primitive-copy writes over the owner's existing
Loc/Store update interface. This is transport, not a new value/state/IR layer.
Both symbolic and numeric runtime headers choose their own counts; old owner
transport connects them, rather than supplying a graph result oracle. -/
namespace Solidity.Backend.StorageOps.CopyTransport
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def body (dst src : Solidity.Storage.Loc) (live count : Nat) (captured : Store) :
    List (Solidity.Storage.Loc × Semantics.Word) :=
  (List.range count).map (fun i => (.data dst i, if i < live then captured (.data src i) else ClearDemands.zero))

def updates (dst src : Solidity.Storage.Loc) (captured : Store) : List (Solidity.Storage.Loc × Semantics.Word) :=
  let live := (captured src).val.toNat
  let oldLive := (captured dst).val.toNat
  body dst src live (max oldLive live) captured ++ [(dst, captured src)]

def symbolicCopy (dst src : Solidity.Storage.Loc) (captured : Store) : Store :=
  (updates dst src captured).foldl (fun w op => Representation.write w op.1 op.2) captured

private theorem body_succ (dst src : Solidity.Storage.Loc) (live count : Nat) (captured : Store) :
    body dst src live (count + 1) captured = body dst src live count captured ++
      [(.data dst count, if count < live then captured (.data src count) else ClearDemands.zero)] := by
  simp only [body, List.range_succ, List.map_append, List.map_singleton]

/-- Numeric loop reads the actual captured machine. OLD Transport, not a
preservation premise, derives every payload equality required by the fold. -/
theorem numeric_body {N : Nat} (hash : Solidity.Storage.Pre → Nat) (locations : List Solidity.Storage.Loc)
    (dst src : Solidity.Storage.Loc) (live count : Nat) (captured : Store) (initial : WordStore)
    (transport : Transport N hash locations captured initial)
    (sourceCovered : ∀ i < live, Solidity.Storage.Loc.data src i ∈ locations) :
    (body dst src live count captured).foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial =
    NumericTraversal.writePrefix (fun i => (Solidity.Storage.Loc.data dst i).word N hash)
      (fun i => if i < live then initial ((Solidity.Storage.Loc.data src i).word N hash) else ClearDemands.zero)
      count initial := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [body_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, NumericTraversal.writePrefix, ih]
    by_cases liveIndex : count < live
    · rw [if_pos liveIndex, if_pos liveIndex, transport _ (sourceCovered count liveIndex)]
    · rw [if_neg liveIndex, if_neg liveIndex]

theorem numeric_eq_fold {N : Nat} (hash : Solidity.Storage.Pre → Nat) (locations : List Solidity.Storage.Loc)
    (dst src : Solidity.Storage.Loc) (captured : Store) (initial : WordStore)
    (transport : Transport N hash locations captured initial)
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (sourceCovered : ∀ i < (captured src).val.toNat, Solidity.Storage.Loc.data src i ∈ locations) :
    NumericTraversal.copy N hash dst src initial =
      (updates dst src captured).foldl (fun m op => writeWord m (op.1.word N hash) op.2) initial := by
  have dstWord := transport dst dstHeader
  have srcWord := transport src srcHeader
  simp only [updates, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [numeric_body hash locations dst src _ _ captured initial transport sourceCovered]
  simp only [NumericTraversal.copy, LifecycleNumeric.headerLength, dstWord, srcWord]

/-- Complete transport of the ACTUAL runtime copy from the owner's existing
finite-run update theorem. Covered sets include all source reads and writes. -/
theorem transported {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations)
    (dst src : Solidity.Storage.Loc) (captured : Store) (initial : WordStore)
    (transport : Transport N hash locations captured initial)
    (dstHeader : dst ∈ locations) (srcHeader : src ∈ locations)
    (sourceCovered : ∀ i < (captured src).val.toNat, Solidity.Storage.Loc.data src i ∈ locations)
    (visitedCovered : ∀ i < max (captured dst).val.toNat (captured src).val.toNat,
      Solidity.Storage.Loc.data dst i ∈ locations) :
    Transport N hash locations (symbolicCopy dst src captured) (NumericTraversal.copy N hash dst src initial) := by
  rw [numeric_eq_fold hash locations dst src captured initial transport dstHeader srcHeader sourceCovered]
  apply transport_sequence run transport (updates dst src captured)
  intro op member
  simp only [updates, List.mem_append, List.mem_singleton] at member
  rcases member with bodyMember | rfl
  · obtain ⟨i, inside, rfl⟩ := List.mem_map.mp bodyMember
    exact visitedCovered i (List.mem_range.mp inside)
  · exact dstHeader

/-- Full selected owner representation AND actual generated-write numeric
transport after the independently specified primitive graph copy. Old relations
supply support/metadata and actual reads; no result preservation is assumed. -/
theorem complete {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash preimages locations)
    (old src : Value G (.array (.prim p))) (indices : List Index)
    (dstBase srcBase : Solidity.Storage.Loc) (captured : Store) (initial : WordStore)
    (beforeDst : Represented old (PrimitivePop.queries indices) dstBase captured)
    (beforeSrc : Represented src (PrimitivePop.queries indices) srcBase captured)
    (transport : Transport N hash locations captured initial)
    (dstHeader : dstBase ∈ locations) (srcHeader : srcBase ∈ locations)
    (dstCovered : ∀ i ∈ indices, Solidity.Storage.Loc.data dstBase i.val ∈ locations)
    (srcCovered : ∀ i ∈ indices, Solidity.Storage.Loc.data srcBase i.val ∈ locations)
    (sourceCovered : ∀ i < src.length.val, Solidity.Storage.Loc.data srcBase i ∈ locations)
    (visitedCovered : ∀ i < max old.length.val src.length.val, Solidity.Storage.Loc.data dstBase i ∈ locations) :
    Transport N hash locations (symbolicCopy dstBase srcBase captured)
      (NumericTraversal.copy N hash dstBase srcBase initial) ∧
    Represented (recursiveCopy old src) (PrimitivePop.queries indices) dstBase (symbolicCopy dstBase srcBase captured) := by
  have dstWord : captured dstBase = lengthWord old.length.val old.length.isLt :=
    (beforeDst (.length .nil) List.mem_cons_self).2.2 _ (by cases old; rfl)
  have srcWord : captured srcBase = lengthWord src.length.val src.length.isLt :=
    (beforeSrc (.length .nil) List.mem_cons_self).2.2 _ (by cases src; rfl)
  have dstLen : (captured dstBase).val.toNat = old.length.val := by rw [dstWord]; rfl
  have srcLen : (captured srcBase).val.toNat = src.length.val := by rw [srcWord]; rfl
  have afterTransport := transported run dstBase srcBase captured initial transport dstHeader srcHeader
    (by simpa only [srcLen] using sourceCovered) (by simpa only [dstLen, srcLen] using visitedCovered)
  have observations := NumericTraversal.represented_observations run old src indices dstBase srcBase
    captured initial beforeDst beforeSrc transport dstHeader srcHeader dstCovered srcCovered visitedCovered
  refine ⟨afterTransport, ?_⟩
  intro q member
  simp only [PrimitivePop.queries, List.mem_cons, List.mem_map] at member
  rcases member with rfl | ⟨i, inside, rfl⟩
  · have dstBounded := (beforeDst (.length .nil) List.mem_cons_self).2.1
    have srcBounded := (beforeSrc (.length .nil) List.mem_cons_self).2.1
    refine ⟨True.intro, ?_, ?_⟩
    · rw [recursiveCopy_eq_overlay]
      cases old with
      | array oe ol oh os =>
        cases src with
        | array ne nl nh ns =>
          change ol.val ≤ lmax ∧ oe.val ≤ lmax at dstBounded
          change nl.val ≤ lmax ∧ ne.val ≤ lmax at srcBounded
          change nl.val ≤ lmax ∧ max oe.val nl.val ≤ lmax
          constructor <;> omega
    · intro word observed
      have actual := Option.some.inj (observations.1.symm.trans observed)
      exact (afterTransport dstBase dstHeader).symm.trans actual
  · have oldRep := beforeDst (PrimitivePop.elementQuery i)
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, inside, rfl⟩))
    refine ⟨oldRep.1, True.intro, ?_⟩
    intro word observed
    rw [PrimitivePop.element_location]
    exact (afterTransport (.data dstBase i.val) (dstCovered i inside)).symm.trans
      (observations.2.1 i inside word observed)

/-- info: 'Solidity.Backend.StorageOps.CopyTransport.body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms body
/-- info: 'Solidity.Backend.StorageOps.CopyTransport.updates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms updates
/-- info: 'Solidity.Backend.StorageOps.CopyTransport.symbolicCopy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms symbolicCopy
/-- info: 'Solidity.Backend.StorageOps.CopyTransport.numeric_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms numeric_body
/-- info: 'Solidity.Backend.StorageOps.CopyTransport.numeric_eq_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms numeric_eq_fold
/-- info: 'Solidity.Backend.StorageOps.CopyTransport.transported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms transported
/-- info: 'Solidity.Backend.StorageOps.CopyTransport.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete

end Solidity.Backend.StorageOps.CopyTransport
