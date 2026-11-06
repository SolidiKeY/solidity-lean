import Solidity.Backend.StorageOps.PathRepresentation
import Solidity.Backend.StorageOps.PushTransport
import Solidity.Backend.StorageOps.NumericCommutation
import Solidity.Backend.StorageOps.IndexedOperations

/-! Nonempty shared-key/fixed-member prefix with real hash/region premises.
The actual root operations are related to represented symbolic/numeric storage,
not two invocations of the same evaluator. -/
namespace Solidity.Backend.StorageOps.PathRepresentationControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
private def graph : Schema 0 where
  origin := "v10-path-representation-controls"
  declId := fun i => nomatch i
  declId_injective := by intro i; exact Fin.elim0 i
  name := fun i => nomatch i
  fields := fun i => nomatch i
  rank := fun i => nomatch i
  nonempty := by intro i; exact Fin.elim0 i
  distinct := by intro i; exact Fin.elim0 i
  guarded := by intro i; exact Fin.elim0 i
private def size : FixedSize := ⟨2, by decide⟩
private def ix (i : Fin 4) : Index := ⟨i.val, by have bound := i.isLt; omega⟩
private def indices : List Index := [ix 0, ix 1, ix 2, ix 3]
private abbrev Elem : TypeGraph.Ty 0 := TypeGraph.Ty.array (TypeGraph.Ty.prim PrimTy.bool)
private abbrev Pair : TypeGraph.Ty 0 := TypeGraph.Ty.fixed Elem size
private abbrev Root : TypeGraph.Ty 0 := TypeGraph.Ty.mapping PrimTy.bool Pair
private def old : Value graph Elem :=
  .array ⟨4, by decide⟩ ⟨3, by decide⟩ (by decide) (fun _ => .present (.prim true))
private def snapshot : Value graph Elem :=
  .array ⟨2, by decide⟩ ⟨1, by decide⟩ (by decide) (fun i => .present (.prim (decide (i.val = 1))))
private def empty : Value graph Elem := .array ⟨0, by decide⟩ ⟨0, by decide⟩ (by decide) (fun i => nomatch i)
private def inside : Value graph Pair := .fixed (fun i => .present (if i.val = 0 then old else snapshot))
private def outside : Value graph Pair := .fixed (fun _ => .present empty)
private def root : Value graph Root := .mapping (fun key => .present (if key = true then outside else inside))
private def common : TypeGraph.Path graph Root Pair := .cons (.key false) .nil
private def dstPath : TypeGraph.Path graph Root Elem := .cons (.key false) (.cons (.fixed (ix 0)) .nil)
private def srcPath : TypeGraph.Path graph Root Elem := .cons (.key false) (.cons (.fixed (ix 1)) .nil)
private def otherPath (i : Fin 2) : TypeGraph.Path graph Root Elem :=
  .cons (.key true) (.cons (.fixed ⟨i.val, by have h := i.isLt; omega⟩) .nil)
private def payloadPath (pre : TypeGraph.Path graph Root Elem) (i : Index) : TypeGraph.Path graph Root (.prim .bool) := pre.append (.cons (.index i) .nil)
private def copiedRoot : Value graph Root := (recursiveCopyAt root dstPath srcPath).getD root
private def poppedRoot : Value graph Root := (popAt root dstPath).getD root
private def base : Solidity.Storage.Loc := .root 0
private def dst : Solidity.Storage.Loc := .hash 0 base 0
private def src : Solidity.Storage.Loc := .hash 0 base 1
private def zero : Semantics.Word := ClearDemands.zero
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def two : Semantics.Word := lengthWord 2 (by decide)
private def three : Semantics.Word := lengthWord 3 (by decide)
private def seven : Semantics.Word := ⟨7, by decide⟩
private def hash (p : Solidity.Storage.Pre) : Nat :=
  if p = .entry 0 0 then 4 else if p = .entry 1 0 then 8 else
  if p = .data 4 then 16 else if p = .data 5 then 24 else 0
private def preimages : List Solidity.Storage.Pre := [.entry 0 0, .entry 1 0, .data 4, .data 5]
private def locations : List Solidity.Storage.Loc := [dst, src,
  .data dst 0, .data dst 1, .data dst 2, .data dst 3,
  .data src 0, .data src 1, .data src 2, .data src 3,
  .hash 1 base 0, .hash 1 base 1]
private def store : Store := fun l => if l = dst then three else if l = src then one else
  if l = .root 2 then seven else if l = .data dst 0 ∨ l = .data dst 1 ∨ l = .data dst 2 ∨
    l = .data dst 3 ∨ l = .data src 1 then one else zero
private def machine : WordStore := fun a => if a = 4 then three else if a = 5 then one else if a = 2 then seven else
  if a = 16 ∨ a = 17 ∨ a = 18 ∨ a = 19 ∨ a = 25 ∨ a = 40 ∨ a = 44 then one else zero
private def after : Store := CopyTransport.symbolicCopy dst src store
private def final : WordStore := NumericTraversal.copy 64 hash dst src machine
private def numericView (m : WordStore) :=
  (m 4, m 5, m 16, m 17, m 18, m 19, m 24, m 25, m 26, m 27, m 8, m 9, m 40, m 44, m 2)
private theorem dst_location : pathLoc dstPath base = dst := rfl
private theorem src_location : pathLoc srcPath base = src := rfl
private theorem readDst : root.find dstPath = some old := rfl
private theorem readSrc : root.find srcPath = some snapshot := rfl
private theorem dstSupported : PathSupported dstPath := by change True ∧ (0 < 2 ∧ True); decide
private theorem srcSupported : PathSupported srcPath := by change True ∧ (1 < 2 ∧ True); decide
private theorem run : FiniteRun 64 4 1 hash preimages locations := by
  constructor
  · intro p; simp only [hash]; split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> decide))))))
  · decide
  · decide
  · decide
  · intro l member
    simp only [locations, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [dst, src, base, Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    simp only [locations, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem initial : Transport 64 hash locations store machine := by
  intro l member
  simp only [locations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
private theorem childBeforeDst : Represented old (PrimitivePop.queries indices) dst store := by
  intro q member
  simp only [PrimitivePop.queries, indices, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
    intro word observed; change some three = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 3 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
private theorem childBeforeSrc : Represented snapshot (PrimitivePop.queries indices) src store := by
  intro q member
  simp only [PrimitivePop.queries, indices, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · refine ⟨True.intro, ⟨by decide, by decide⟩, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 0 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some zero = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 1 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change some one = some word at observed; cases observed; rfl
  · refine ⟨⟨by change 2 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
  · refine ⟨⟨by change 3 < lmax; decide, True.intro⟩, True.intro, ?_⟩
    intro word observed; change (none : Option Semantics.Word) = some word at observed; cases observed
private theorem beforeDst : Represented root ((PrimitivePop.queries indices).map (Query.prefix dstPath)) base store :=
  Represented.prefix dstPath readDst dstSupported childBeforeDst
private theorem beforeSrc : Represented root ((PrimitivePop.queries indices).map (Query.prefix srcPath)) base store :=
  Represented.prefix srcPath readSrc srcSupported childBeforeSrc
private theorem covered : ∀ i ∈ indices,
    Solidity.Storage.Loc.data dst i.val ∈ locations ∧ Solidity.Storage.Loc.data src i.val ∈ locations := by
  intro i member
  simp only [indices, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide
private theorem visited : ∀ i < max old.length.val snapshot.length.val, Solidity.Storage.Loc.data dst i ∈ locations := by
  intro i inside
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by change i < max 3 1 at inside; omega
  rcases cases with rfl | rfl | rfl <;> decide

theorem actual_root_operations : recursiveCopyAt root dstPath srcPath = some copiedRoot ∧
    popAt root dstPath = some poppedRoot := ⟨rfl, rfl⟩

theorem shared_prefix : dstPath = common.append (.cons (.fixed (ix 0)) .nil) ∧
    srcPath = common.append (.cons (.fixed (ix 1)) .nil) := ⟨rfl, rfl⟩

/-- Real per-run hash, shared-key prefix, actual root find/save, and both OLD
root owner relations are consumed; postrepresentation/transport is derived. -/
theorem copy_bridge : Transport 64 hash locations after final ∧
    Represented copiedRoot ((PrimitivePop.queries indices).map (Query.prefix dstPath)) base after :=
  PathRepresentation.copy_at run root copiedRoot dstPath srcPath old snapshot readDst readSrc actual_root_operations.1
    indices base store machine beforeDst beforeSrc initial (by decide) (by decide)
    (fun i member => (covered i member).1) (fun i member => (covered i member).2)
    (by
      intro i inside
      have equal : i = 0 := by change i < 1 at inside; omega
      subst i
      decide) visited

private theorem popCovered : ∀ q ∈ PrimitivePop.queries (G := graph) (p := .bool) indices,
    q.location (pathLoc dstPath base) ∈ locations := by
  intro q member
  simp only [PrimitivePop.queries, indices, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The actual shared-prefix root pop consumes its OLD ROOT relation, not a
hypothetical result-child preservation certificate. -/
theorem pop_bridge : ∃ child final,
    poppedRoot.find dstPath = some child ∧ PrimitivePop.execute 64 hash dst machine = some final ∧
    let after := Representation.write (Representation.write store (.data dst (old.length.val - 1)) zero)
      dst (lengthWord child.length.val child.length.isLt)
    Transport 64 hash locations after final ∧
      Represented poppedRoot ((PrimitivePop.queries indices).map (Query.prefix dstPath)) base after :=
  PathRepresentation.pop_at run root poppedRoot dstPath old readDst actual_root_operations.2 indices base store machine
    beforeDst initial popCovered (by decide)

private def header (v : Value graph Root) (pre : TypeGraph.Path graph Root Elem) :=
  (v.observe pre).map (fun h => (h.1.val, h.2.val))
private def raw (v : Value graph Root) (pre : TypeGraph.Path graph Root Elem) (i : Index) :=
  v.observe (payloadPath pre i)
private def live (v : Value graph Root) (pre : TypeGraph.Path graph Root Elem) (i : Index) :=
  ((payloadPath pre i).readLive Value.dflt v).map Value.head
private def rootView (v : Value graph Root) :=
  (header v dstPath, header v srcPath, header v (otherPath 0), header v (otherPath 1),
    raw v dstPath (ix 0), raw v dstPath (ix 1), raw v dstPath (ix 2), raw v dstPath (ix 3),
    raw v srcPath (ix 0), raw v srcPath (ix 1), raw v srcPath (ix 2), raw v srcPath (ix 3),
    raw v (otherPath 0) (ix 0), raw v (otherPath 1) (ix 0), live v dstPath (ix 0), live v dstPath (ix 2))
private def popFinal : WordStore := (PrimitivePop.execute 64 hash dst machine).getD machine

/-- Complete root observations for BOTH mapping keys/fixed children, all
payloads/source failures, outside-prefix reads and live-vs-retained aliases. -/
theorem root_ordered : (rootView root, rootView copiedRoot, rootView poppedRoot) =
    ((some (3,4), some (1,2), some (0,0), some (0,0),
       some true, some true, some true, some true, some false, some true, none, none, none, none, some true, some true),
     (some (1,4), some (1,2), some (0,0), some (0,0),
       some false, some false, some false, some true, some false, some true, none, none, none, none, some false, none),
     (some (2,4), some (1,2), some (0,0), some (0,0),
       some true, some true, some false, some true, some false, some true, none, none, none, none, some true, none)) := rfl

theorem numeric_ordered : (numericView machine, numericView final, numericView popFinal) =
    ((three,one,one,one,one,one,zero,one,zero,zero,zero,zero,one,one,seven),
     (one,one,zero,zero,zero,one,zero,one,zero,zero,zero,zero,one,one,seven),
     (two,one,one,one,zero,one,zero,one,zero,zero,zero,zero,one,one,seven)) := rfl

private def bad : TypeGraph.Path graph Root Elem := .cons (.key false) (.cons (.fixed (ix 2)) .nil)
/-- Malformed fixed-member lookup fails; a numeric/world rollback claim is NOT
inferred. Such an unsupported lvalue cannot satisfy the root header relation. -/
theorem malformed : root.find bad = none ∧ recursiveCopyAt root bad srcPath = none ∧
    popAt root bad = none ∧ ¬ PathSupported bad := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  change ¬ (True ∧ (2 < 2 ∧ True))
  omega

private def copyThenPop := (recursiveCopyAt root dstPath srcPath).bind (fun v => popAt v dstPath)
private def popThenCopy := (popAt root dstPath).bind (fun v => recursiveCopyAt v dstPath srcPath)
private def numericCopyThenPop := PrimitivePop.execute 64 hash dst final
private def numericPopThenCopy := (PrimitivePop.execute 64 hash dst machine).map (NumericTraversal.copy 64 hash dst src)

/-- Same-target wrong-order negative: operational root and numeric results
differ in headers/liveness; all other ordered observations are retained. -/
theorem wrong_order_root : copyThenPop.map rootView =
    some (some (0,4), some (1,2), some (0,0), some (0,0),
      some false, some false, some false, some true, some false, some true, none, none, none, none, none, none) ∧
    popThenCopy.map rootView =
    some (some (1,4), some (1,2), some (0,0), some (0,0),
      some false, some false, some false, some true, some false, some true, none, none, none, none, some false, none) ∧
    copyThenPop.map (fun v => header v dstPath) ≠ popThenCopy.map (fun v => header v dstPath) :=
  ⟨rfl, rfl, by decide⟩

theorem wrong_order_numeric : (numericCopyThenPop.map numericView, numericPopThenCopy.map numericView) =
    (some (zero,one,zero,zero,zero,one,zero,one,zero,zero,zero,zero,one,one,seven),
     some (one,one,zero,zero,zero,one,zero,one,zero,zero,zero,zero,one,one,seven)) ∧
    numericCopyThenPop.map (fun m => m 4) ≠ numericPopThenCopy.map (fun m => m 4) := ⟨rfl, by decide⟩

/-- Actual retained outer prefix is readable logically while BOTH live reads
fail. It is a graph witness only, not an ordinary-source admission decision. -/
private def retained : Value graph (.array Root) := .array ⟨1, by decide⟩ ⟨0, by decide⟩ (by decide) (fun _ => .present root)
private def retainedPre : TypeGraph.Path graph (.array Root) Root := .cons (.index (ix 0)) .nil
private def retainedDst := retainedPre.append dstPath
private def retainedSrc := retainedPre.append srcPath
private def retainedResult : Value graph (.array Root) := (recursiveCopyAt retained retainedDst retainedSrc).getD retained

theorem retained_vs_live : retained.find retainedDst = some old ∧ retained.find retainedSrc = some snapshot ∧
    retainedDst.readLive Value.dflt retained = none ∧ retainedSrc.readLive Value.dflt retained = none ∧
    recursiveCopyAt retained retainedDst retainedSrc = some retainedResult ∧
    (retainedResult.observe retainedDst).map (fun h => (h.1.val,h.2.val)) = some (1,4) ∧
    retainedDst.readLive Value.dflt retainedResult = none ∧
    (retainedResult.length.val, retainedResult.extent.val,
      retainedResult.observe (retainedDst.append (.cons (.index (ix 0)) .nil)),
      retainedResult.observe (retainedDst.append (.cons (.index (ix 1)) .nil)),
      retainedResult.observe (retainedDst.append (.cons (.index (ix 2)) .nil)),
      retainedResult.observe (retainedDst.append (.cons (.index (ix 3)) .nil)),
      (retainedResult.observe retainedSrc).map (fun h => (h.1.val,h.2.val))) =
      (0,1,some false,some false,some false,some true,some (1,2)) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.actual_root_operations' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms actual_root_operations
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.shared_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms shared_prefix
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.copy_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms copy_bridge
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.pop_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_bridge
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.root_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms root_ordered
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.numeric_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_ordered
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.malformed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms malformed
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.wrong_order_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms wrong_order_root
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.wrong_order_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_order_numeric
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.retained_vs_live' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms retained_vs_live

private def pushedRoot : Value graph Root := (pushAt root dstPath).getD root
private def pushFinal : WordStore := (LifecycleNumeric.pushPrimitive 64 hash dst machine).getD machine
private def four : Semantics.Word := lengthWord 4 (by decide)

theorem actual_root_push : pushAt root dstPath = some pushedRoot := rfl

/-- Positive selected ROOT result follows from the exact characterized range;
no new source admission rule or assumed preservation theorem is used. -/
theorem push_prefix_bridge : ∃ child final,
    pushedRoot.find dstPath = some child ∧ LifecycleNumeric.pushPrimitive 64 hash dst machine = some final ∧
    let after := Representation.write (Representation.write store (.data dst old.length.val) zero)
      dst (lengthWord child.length.val child.length.isLt)
    Transport 64 hash locations after final ∧
      Represented pushedRoot ((PrimitivePop.queries indices).map (Query.prefix dstPath)) base after := by
  obtain ⟨child, m, readBack, executed, transported, iffCovered⟩ :=
    PushTransport.push_at run root pushedRoot dstPath old readDst actual_root_push indices base store machine
      beforeDst initial (by decide) (by decide)
  exact ⟨child,m,readBack,executed,transported,iffCovered.mpr (by decide)⟩

theorem push_root_ordered :
    (rootView pushedRoot, raw root dstPath (ix 3), raw pushedRoot dstPath (ix 3),
      live root dstPath (ix 3), live pushedRoot dstPath (ix 3), numericView pushFinal) =
    ((some (4,4),some (1,2),some (0,0),some (0,0),
      some true,some true,some true,some false,some false,some true,none,none,none,none,some true,some true),
      some true,some false,none,some false,
      (four,one,one,one,one,zero,zero,one,zero,zero,zero,zero,one,one,seven)) := rfl

private def wrongReuseStore : Store := Representation.write store dst four
private def wrongReuseMachine : WordStore := writeWord machine 4 four

theorem primitive_reuse_negative :
    ¬ Represented pushedRoot ((PrimitivePop.queries indices).map (Query.prefix dstPath)) base wrongReuseStore ∧
    wrongReuseMachine 19 ≠ pushFinal 19 ∧
    numericView wrongReuseMachine = (four,one,one,one,one,one,zero,one,zero,zero,zero,zero,one,one,seven) := by
  refine ⟨?_, by decide, rfl⟩
  intro bad
  have wrong := (bad ((PrimitivePop.elementQuery (ix 3)).prefix dstPath)
    (List.mem_map.mpr ⟨_,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))),rfl⟩)).2.2 zero rfl
  change one = zero at wrong
  exact (by decide : one ≠ zero) wrong

/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.actual_root_push' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms actual_root_push
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.push_prefix_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_prefix_bridge
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.push_root_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_root_ordered
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.primitive_reuse_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_reuse_negative

/-- Actual ROOT numeric read agreement follows from post-root representation
and transported covered queries, independently of the ordered rfl vectors. -/
theorem push_root_numeric : ∀ q ∈ (PrimitivePop.queries (G := graph) (p := .bool) indices).map (Query.prefix dstPath),
    ∀ word, q.read pushedRoot = some word → pushFinal ((q.location base).word 64 hash) = word := by
  obtain ⟨child,m,readBack,executed,transported,represented⟩ := push_prefix_bridge
  have actual : LifecycleNumeric.pushPrimitive 64 hash dst machine = some pushFinal := rfl
  have same : m = pushFinal := Option.some.inj (executed.symm.trans actual)
  subst m
  intro q member word observed
  apply represented.numeric transported q member _ word observed
  obtain ⟨suffix,inside,rfl⟩ := List.mem_map.mp member
  rw [Query.location_prefix]
  exact popCovered suffix inside

/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.push_root_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms push_root_numeric

private def numericPushA := LifecycleNumeric.pushPrimitive 64 hash dst
private def numericPushB := LifecycleNumeric.pushPrimitive 64 hash src
private def numericPopA := PrimitivePop.execute 64 hash dst
private def numericPopB := PrimitivePop.execute 64 hash src
private def pushBoth := (pushAt root dstPath).bind (fun v => pushAt v srcPath)
private def pushPopBoth := (pushAt root dstPath).bind (fun v => popAt v srcPath)
private def popBoth := (popAt root dstPath).bind (fun v => popAt v srcPath)

/-- Reuse checked arbitrary-prefix graph commutation; no duplicate local
semantics or commutation premise is assumed for these real root operations. -/
theorem graph_disjoint_pushes : pushBoth = (pushAt root srcPath).bind (fun v => pushAt v dstPath) := by
  unfold pushBoth pushAt
  rw [shared_prefix.1,shared_prefix.2]
  exact common_prefix_fixed_commute root common (ix 0) (ix 1) (by decide) .nil .nil operationPush operationPush

theorem graph_disjoint_push_pop : pushPopBoth = (popAt root srcPath).bind (fun v => pushAt v dstPath) := by
  unfold pushPopBoth pushAt popAt
  rw [shared_prefix.1,shared_prefix.2]
  exact common_prefix_fixed_commute root common (ix 0) (ix 1) (by decide) .nil .nil operationPush recursivePop

theorem graph_disjoint_pops : popBoth = (popAt root srcPath).bind (fun v => popAt v dstPath) := by
  unfold popBoth popAt
  rw [shared_prefix.1,shared_prefix.2]
  exact common_prefix_fixed_commute root common (ix 0) (ix 1) (by decide) .nil .nil recursivePop recursivePop

private theorem ppCovered : ∀ l ∈ NumericCommutation.pushTouches 64 hash dst machine ++
    NumericCommutation.pushTouches 64 hash src machine, l ∈ locations := by decide
private theorem ppSeparate : ∀ x ∈ NumericCommutation.pushTouches 64 hash dst machine,
    ∀ y ∈ NumericCommutation.pushTouches 64 hash src machine, x ≠ y := by decide
private theorem pmCovered : ∀ l ∈ NumericCommutation.pushTouches 64 hash dst machine ++
    NumericCommutation.popTouches 64 hash src machine, l ∈ locations := by decide
private theorem pmSeparate : ∀ x ∈ NumericCommutation.pushTouches 64 hash dst machine,
    ∀ y ∈ NumericCommutation.popTouches 64 hash src machine, x ≠ y := by decide
private theorem mmCovered : ∀ l ∈ NumericCommutation.popTouches 64 hash dst machine ++
    NumericCommutation.popTouches 64 hash src machine, l ∈ locations := by decide
private theorem mmSeparate : ∀ x ∈ NumericCommutation.popTouches 64 hash dst machine,
    ∀ y ∈ NumericCommutation.popTouches 64 hash src machine, x ≠ y := by decide

theorem numeric_disjoint_pushes : (numericPushA machine).bind numericPushB = (numericPushB machine).bind numericPushA :=
  NumericCommutation.push_push run dst src machine ppCovered ppSeparate

theorem numeric_disjoint_push_pop : (numericPushA machine).bind numericPopB = (numericPopB machine).bind numericPushA :=
  NumericCommutation.push_pop run dst src machine pmCovered pmSeparate

theorem numeric_disjoint_pops : (numericPopA machine).bind numericPopB = (numericPopB machine).bind numericPopA :=
  NumericCommutation.pop_pop run dst src machine mmCovered mmSeparate

private def bothFinal : WordStore := (numericPushB pushFinal).getD pushFinal
private def pmFinal : WordStore := (numericPopB pushFinal).getD pushFinal
private def mmFinal : WordStore := (numericPopB popFinal).getD popFinal
private def bothStore : Store :=
  (NumericCommutation.pushUpdates 64 hash src pushFinal).foldl (fun w op => Representation.write w op.1 op.2)
    ((NumericCommutation.pushUpdates 64 hash dst machine).foldl (fun w op => Representation.write w op.1 op.2) store)

/-- Both actual numeric stages transport generated writes under the real
shared-prefix run; second touches are DERIVED stable, not assumed unchanged. -/
theorem generated_sequence_transport : Transport 64 hash locations bothStore bothFinal :=
  NumericCommutation.disjoint_sequence_transport run dst src store machine pushFinal bothFinal initial
    rfl rfl ppCovered ppSeparate

theorem second_accesses_stable :
    NumericCommutation.pushTouches 64 hash src pushFinal = NumericCommutation.pushTouches 64 hash src machine ∧
    NumericCommutation.pushUpdates 64 hash src pushFinal = NumericCommutation.pushUpdates 64 hash src machine :=
  (NumericCommutation.disjoint_frame run dst src machine pushFinal rfl ppCovered ppSeparate).2

/-- COMPLETE root vectors of three disjoint combinations. Both push targets
change TRUE retained payloads; pop targets change headers/live aliases. -/
theorem disjoint_root_ordered :
    (pushBoth.map rootView,pushPopBoth.map rootView,popBoth.map rootView) =
    (some (some (4,4),some (2,2),some (0,0),some (0,0),
       some true,some true,some true,some false,some false,some false,none,none,none,none,some true,some true),
     some (some (4,4),some (0,2),some (0,0),some (0,0),
       some true,some true,some true,some false,some false,some true,none,none,none,none,some true,some true),
     some (some (2,4),some (0,2),some (0,0),some (0,0),
       some true,some true,some false,some true,some false,some true,none,none,none,none,some true,none)) := rfl

theorem disjoint_numeric_ordered : (numericView bothFinal,numericView pmFinal,numericView mmFinal) =
    ((four,two,one,one,one,zero,zero,zero,zero,zero,zero,zero,one,one,seven),
     (four,zero,one,one,one,zero,zero,one,zero,zero,zero,zero,one,one,seven),
     (two,zero,one,one,zero,one,zero,one,zero,zero,zero,zero,one,one,seven)) := rfl

private def bothResult : Value graph Root := pushBoth.getD root
private def rootBothSymbolicView (w : Store) :=
  (w dst,w src,w (.data dst 0),w (.data dst 1),w (.data dst 2),w (.data dst 3),
    w (.data src 0),w (.data src 1),w (.data src 2),w (.data src 3),w (.hash 1 base 0),w (.hash 1 base 1),w (.root 2))

theorem generated_symbolic_ordered : rootBothSymbolicView bothStore =
    (four,two,one,one,one,zero,zero,zero,zero,zero,zero,zero,seven) := rfl

theorem both_regrown_aliases :
    (raw root dstPath (ix 3),raw bothResult dstPath (ix 3),live root dstPath (ix 3),live bothResult dstPath (ix 3),
      raw root srcPath (ix 1),raw bothResult srcPath (ix 1),live root srcPath (ix 1),live bothResult srcPath (ix 1)) =
    (some true,some false,none,some false,some true,some false,none,some false) := rfl

/-- Empty pop at the OTHER mapping key has no phantom data8 access/preimage.
This failure fixture uses the actual root empty child and good finite run. -/
private def emptyBase : Solidity.Storage.Loc := .hash 1 base 0
private theorem emptyCovered : ∀ l ∈ NumericCommutation.pushTouches 64 hash dst machine ++
    NumericCommutation.popTouches 64 hash emptyBase machine, l ∈ locations := by decide
private theorem emptySeparate : ∀ x ∈ NumericCommutation.pushTouches 64 hash dst machine,
    ∀ y ∈ NumericCommutation.popTouches 64 hash emptyBase machine, x ≠ y := by decide

theorem empty_failure_commutes :
    (numericPushA machine).bind (PrimitivePop.execute 64 hash emptyBase) =
      (PrimitivePop.execute 64 hash emptyBase machine).bind numericPushA :=
  NumericCommutation.push_pop run dst emptyBase machine emptyCovered emptySeparate

theorem empty_failure_ordered :
    NumericCommutation.popTouches 64 hash emptyBase machine = [emptyBase] ∧
    (pushAt root dstPath).bind (fun v => popAt v (otherPath 0)) = none ∧
    (popAt root (otherPath 0)).bind (fun v => pushAt v dstPath) = none ∧
    (numericPushA machine).bind (PrimitivePop.execute 64 hash emptyBase) = none ∧
    (PrimitivePop.execute 64 hash emptyBase machine).bind numericPushA = none := ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Full-Word capacity failure is a NUMERIC-ONLY fixture, without a falsely
claimed old Graph.Represented relation for the deliberately changed header. -/
private def fullHeader : Semantics.Word := lengthWord (2 ^ 256 - 1) (by decide)
private def failureMachine : WordStore := writeWord machine 4 fullHeader

theorem capacity_failure_commutes :
    (numericPushA failureMachine).bind numericPushB = (numericPushB failureMachine).bind numericPushA := by
  apply NumericCommutation.push_push run dst src failureMachine <;> decide

theorem capacity_failure_ordered :
    NumericCommutation.pushTouches 64 hash dst failureMachine = [dst] ∧
    (numericPushA failureMachine).bind numericPushB = none ∧
    (numericPushB failureMachine).bind numericPushA = none := ⟨rfl,rfl,rfl⟩

/-- Same-target push/pop fails to commute EVEN THOUGH final headers agree;
retained payloads and live aliases distinguish the actual operation order. -/
private def samePushPop := (pushAt root dstPath).bind (fun v => popAt v dstPath)
private def samePopPush := (popAt root dstPath).bind (fun v => pushAt v dstPath)
private def numericSamePushPop := (numericPushA machine).bind numericPopA
private def numericSamePopPush := (numericPopA machine).bind numericPushA

theorem same_target_negative : samePushPop.map rootView =
    some (some (3,4),some (1,2),some (0,0),some (0,0),
      some true,some true,some true,some false,some false,some true,none,none,none,none,some true,some true) ∧
    samePopPush.map rootView =
    some (some (3,4),some (1,2),some (0,0),some (0,0),
      some true,some true,some false,some true,some false,some true,none,none,none,none,some true,some false) ∧
    (numericSamePushPop.map numericView,numericSamePopPush.map numericView) =
    (some (three,one,one,one,one,zero,zero,one,zero,zero,zero,zero,one,one,seven),
     some (three,one,one,one,zero,one,zero,one,zero,zero,zero,zero,one,one,seven)) ∧
    samePushPop.map (fun v => raw v dstPath (ix 2)) ≠ samePopPush.map (fun v => raw v dstPath (ix 2)) :=
  ⟨rfl,rfl,rfl,by change (some (some true) : Option (Option Bool)) ≠ some (some false); decide⟩

/-- Raw malformed-layout countermodel, explicitly OUTSIDE RegionsDisjoint:
first push changes the OTHER header/reset index, so operation order matters. -/
private def badHash (p : Solidity.Storage.Pre) : Nat := if p = .data 0 then 1 else if p = .data 1 then 4 else 0
private def badMachine : WordStore := fun a => if a = 1 ∨ a = 4 ∨ a = 5 then one else if a = 2 then seven else zero
private def badA := LifecycleNumeric.pushPrimitive 16 badHash (.root 0)
private def badB := LifecycleNumeric.pushPrimitive 16 badHash (.root 1)
private def badView (m : WordStore) := (m 0,m 1,m 4,m 5,m 2)

theorem bad_region_negative :
    ¬ Solidity.Hash.RegionsDisjoint 16 2 badHash (List.range 2) [.data 0,.data 1] ∧
    ((badA badMachine).bind badB).map badView = some (one,one,zero,one,seven) ∧
    ((badB badMachine).bind badA).map badView = some (one,zero,one,zero,seven) ∧
    ((badA badMachine).bind badB).map badView ≠ ((badB badMachine).bind badA).map badView :=
  ⟨by decide,rfl,rfl,by decide⟩

private def popPushBoth := (popAt root dstPath).bind (fun v => pushAt v srcPath)
private def mpFinal : WordStore := (numericPushB popFinal).getD popFinal

theorem graph_disjoint_pop_push : popPushBoth = (pushAt root srcPath).bind (fun v => popAt v dstPath) := by
  unfold popPushBoth pushAt popAt
  rw [shared_prefix.1,shared_prefix.2]
  exact common_prefix_fixed_commute root common (ix 0) (ix 1) (by decide) .nil .nil recursivePop operationPush

theorem numeric_disjoint_pop_push : (numericPopA machine).bind numericPushB = (numericPushB machine).bind numericPopA := by
  apply NumericCommutation.pop_push run dst src machine <;> decide

theorem pop_push_ordered : (popPushBoth.map rootView,numericView mpFinal) =
    (some (some (2,4),some (2,2),some (0,0),some (0,0),
      some true,some true,some false,some true,some false,some false,none,none,none,none,some true,none),
      (two,two,one,one,zero,one,zero,zero,zero,zero,zero,zero,one,one,seven)) := rfl

/-- The actual pop family's generated writes also use the existing finite
transport theorem, on the same inhabited prefix run and stored source values. -/
theorem generated_pop_transport : Transport 64 hash locations
    ((NumericCommutation.popUpdates 64 hash dst machine).foldl (fun w op => Representation.write w op.1 op.2) store) popFinal :=
  NumericCommutation.pop_transport run dst store machine popFinal initial rfl (by decide)

/-- Actual mixed sequence transport is composed from the TWO checked operation
families, not an assumed final relation or a world-rollback property. -/
theorem generated_mixed_transport : Transport 64 hash locations
    ((NumericCommutation.popUpdates 64 hash src pushFinal).foldl (fun w op => Representation.write w op.1 op.2)
      ((NumericCommutation.pushUpdates 64 hash dst machine).foldl (fun w op => Representation.write w op.1 op.2) store)) pmFinal := by
  apply NumericCommutation.pop_transport run src _ pushFinal pmFinal
    (NumericCommutation.push_transport run dst store machine pushFinal initial rfl (by decide)) rfl
  decide

/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.graph_disjoint_pushes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms graph_disjoint_pushes
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.graph_disjoint_push_pop' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms graph_disjoint_push_pop
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.graph_disjoint_pops' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms graph_disjoint_pops
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.numeric_disjoint_pushes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_disjoint_pushes
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.numeric_disjoint_push_pop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_disjoint_push_pop
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.numeric_disjoint_pops' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_disjoint_pops
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.generated_sequence_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms generated_sequence_transport
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.second_accesses_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms second_accesses_stable
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.disjoint_root_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms disjoint_root_ordered
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.disjoint_numeric_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms disjoint_numeric_ordered
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.generated_symbolic_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms generated_symbolic_ordered
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.both_regrown_aliases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms both_regrown_aliases
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.empty_failure_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_failure_commutes
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.empty_failure_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_failure_ordered
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.capacity_failure_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms capacity_failure_commutes
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.capacity_failure_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms capacity_failure_ordered
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.same_target_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms same_target_negative
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.bad_region_negative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms bad_region_negative
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.graph_disjoint_pop_push' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms graph_disjoint_pop_push
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.numeric_disjoint_pop_push' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_disjoint_pop_push
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.pop_push_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_push_ordered
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.generated_pop_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms generated_pop_transport
/-- info: 'Solidity.Backend.StorageOps.PathRepresentationControls.generated_mixed_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms generated_mixed_transport

end Solidity.Backend.StorageOps.PathRepresentationControls
