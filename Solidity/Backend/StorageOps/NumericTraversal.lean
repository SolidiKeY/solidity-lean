import Solidity.Backend.StorageOps.PrimitivePop
import Solidity.Backend.StorageOps.RecursiveCopy

/-! Actual runtime numeric primitive-array traversal. Machine headers and a
captured source WordStore drive the loop, not graph overlay. The unchanged
recursive graph operation remains the independent specification. -/
namespace Solidity.Backend.StorageOps.NumericTraversal
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Total Nat recursion over an actual runtime count. A single WordStore is
updated; no alternate IR/value/state or source depth bound is introduced. -/
def writePrefix (address : Nat → Nat) (payload : Nat → Semantics.Word) : Nat → WordStore → WordStore
  | 0, initial => initial
  | count + 1, initial => writeWord (writePrefix address payload count initial) (address count) (payload count)

/-- Exact processed-prefix/unvisited observation. Separation is only for the
queried physical word against ACTUALLY visited distinct indices. -/
theorem prefix_read (address : Nat → Nat) (payload : Nat → Semantics.Word)
    (count : Nat) (initial : WordStore) (i : Nat)
    (separate : ∀ j < count, j ≠ i → address i ≠ address j) :
    writePrefix address payload count initial (address i) = if i < count then payload i else initial (address i) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    by_cases equal : i = count
    · subst i
      simp only [writePrefix, writeWord, if_true, Nat.lt_succ_self]
    · have neq := separate count (Nat.lt_succ_self _) (Ne.symm equal)
      simp only [writePrefix, writeWord, if_neg neq]
      rw [ih (fun j before different => separate j (by omega) different)]
      by_cases before : i < count
      · simp only [if_pos before, if_pos (show i < count + 1 by omega)]
      · simp only [if_neg before, if_neg (show ¬ i < count + 1 by omega)]

theorem prefix_outside (address : Nat → Nat) (payload : Nat → Semantics.Word)
    (count : Nat) (initial : WordStore) (a : Nat)
    (outside : ∀ j < count, a ≠ address j) : writePrefix address payload count initial a = initial a := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [writePrefix, writeWord, if_neg (outside count (Nat.lt_succ_self _))]
    exact ih (fun j before => outside j (by omega))

/-- Numeric source is captured BEFORE ANY destination write. Runtime lengths
come from the initial actual source/destination headers. -/
def copy (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (dst src : Solidity.Storage.Loc) (initial : WordStore) : WordStore :=
  let live := LifecycleNumeric.headerLength N hash src initial
  let oldLive := LifecycleNumeric.headerLength N hash dst initial
  let address := fun i => (Solidity.Storage.Loc.data dst i).word N hash
  let payload := fun i => if i < live then initial ((Solidity.Storage.Loc.data src i).word N hash) else ClearDemands.zero
  writeWord (writePrefix address payload (max oldLive live) initial) (dst.word N hash) (initial (src.word N hash))

theorem copy_header (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (dst src : Solidity.Storage.Loc) (initial : WordStore) :
    copy N hash dst src initial (dst.word N hash) = initial (src.word N hash) := by
  simp only [copy, writeWord, if_true]

/-- Exact runtime loop prefix at each numeric array element, including the
cleared shortened live tail and all unvisited older shadows. Existing per-run
conditions derive separation; no new/global hash premise. -/
theorem copy_element {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations)
    (dst src : Solidity.Storage.Loc) (initial : WordStore) (i : Nat)
    (headerCovered : dst ∈ locations) (queryCovered : Solidity.Storage.Loc.data dst i ∈ locations)
    (visitedCovered : ∀ j < max (LifecycleNumeric.headerLength N hash dst initial)
      (LifecycleNumeric.headerLength N hash src initial), Solidity.Storage.Loc.data dst j ∈ locations) :
    let live := LifecycleNumeric.headerLength N hash src initial
    let oldLive := LifecycleNumeric.headerLength N hash dst initial
    copy N hash dst src initial ((Solidity.Storage.Loc.data dst i).word N hash) =
      if i < max oldLive live then
        (if i < live then initial ((Solidity.Storage.Loc.data src i).word N hash) else ClearDemands.zero)
      else initial ((Solidity.Storage.Loc.data dst i).word N hash) := by
  have neq := LifecycleNumeric.header_element_ne run dst i headerCovered queryCovered
  simp only [copy, writeWord, if_neg neq]
  apply prefix_read
  intro j inside different equal
  have same := run.word_inj queryCovered (visitedCovered j inside) equal
  exact different (Solidity.Storage.Loc.data.inj same).2.symm

theorem copy_outside (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (dst src : Solidity.Storage.Loc) (initial : WordStore) (a : Nat)
    (outsideHeader : a ≠ dst.word N hash)
    (outside : ∀ j < max (LifecycleNumeric.headerLength N hash dst initial)
      (LifecycleNumeric.headerLength N hash src initial), a ≠ (Solidity.Storage.Loc.data dst j).word N hash) :
    copy N hash dst src initial a = initial a := by
  simp only [copy, writeWord, if_neg outsideHeader]
  exact prefix_outside _ _ _ _ _ outside

private theorem slot_overlay_word {n : Nat} {G : Schema n} {p : PrimTy}
    (old src : Slot G (.prim p)) :
    PrimTy.toWord ((old.overlay src).getD (Value.dflt _)).head =
      PrimTy.toWord (src.getD (Value.dflt _)).head := by
  cases src with
  | absent => cases old with
    | absent => rfl
    | present value => cases value; rfl
  | present value =>
    cases value
    cases old with
    | absent => rfl
    | present value => cases value; rfl

private theorem slot_clear_word {n : Nat} {G : Schema n} {p : PrimTy}
    (slot : Slot G (.prim p)) :
    PrimTy.toWord (slot.clear.getD (Value.dflt _)).head = ClearDemands.zero := by
  cases slot with
  | absent => exact ClearDemands.default_zero p
  | present value => cases value; exact ClearDemands.default_zero p

/-- Independent existing graph copy read: source LIVE prefix, shortened old
LIVE tail cleared, every older retained/failing observation unchanged. Overlay
is used ONLY in this specification proof, never in numeric execution. -/
theorem graph_read {n : Nat} {G : Schema n} {p : PrimTy}
    (old src : Value G (.array (.prim p))) (i : Index) :
    (PrimitivePop.elementQuery i).read (recursiveCopy old src) =
      if i.val < src.length.val then (PrimitivePop.elementQuery i).read src
      else if i.val < old.length.val then some ClearDemands.zero
      else (PrimitivePop.elementQuery i).read old := by
  cases old with
  | array oe ol oh os =>
    cases src with
    | array ne nl nh ns =>
      rw [recursiveCopy_eq_overlay]
      simp only [Value.length]
      by_cases live : i.val < nl.val
      · have inside : i.val < max oe.val nl.val := by omega
        have sourceInside : i.val < ne.val := by omega
        simp only [PrimitivePop.elementQuery, Query.read, Value.observe, Value.find,
          TypeGraph.Path.read, Value.overlay, Step.get, dif_pos inside, dif_pos live,
          dif_pos sourceInside, if_pos live, Option.bind_some, Option.map_some, Value.head]
        exact congrArg some (slot_overlay_word _ _)
      · by_cases tail : i.val < ol.val
        · have inside : i.val < max oe.val nl.val := by omega
          have oldInside : i.val < oe.val := by omega
          simp only [PrimitivePop.elementQuery, Query.read, Value.observe, Value.find,
            TypeGraph.Path.read, Value.overlay, Step.get, dif_pos inside, dif_neg live,
            if_neg live, if_pos tail, dif_pos oldInside, Option.bind_some, Option.map_some, Value.head]
          exact congrArg some (slot_clear_word _)
        · by_cases allocated : i.val < oe.val
          · have inside : i.val < max oe.val nl.val := by omega
            simp only [PrimitivePop.elementQuery, Query.read, Value.observe, Value.find,
              TypeGraph.Path.read, Value.overlay, Step.get, dif_pos inside, dif_neg live,
              if_neg live, if_neg tail, dif_pos allocated, Option.bind_some, Option.map_some, Value.head]
          · have outside : ¬ i.val < max oe.val nl.val := by omega
            simp only [PrimitivePop.elementQuery, Query.read, Value.observe, Value.find,
              TypeGraph.Path.read, Value.overlay, Step.get, dif_neg outside, dif_neg allocated,
              if_neg live, if_neg tail, Option.bind_none, Option.map_none]

/-- Finite requested owner relations for BOTH captured arrays imply actual
runtime numeric agreement for EVERY successful result query. This is a
primitive-loop component, not a recursive emitted-code/Source/world theorem. -/
theorem represented_observations {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash preimages locations)
    (old src : Value G (.array (.prim p))) (indices : List Index)
    (dstBase srcBase : Solidity.Storage.Loc) (store : Store) (initial : WordStore)
    (beforeDst : Represented old (PrimitivePop.queries indices) dstBase store)
    (beforeSrc : Represented src (PrimitivePop.queries indices) srcBase store)
    (transport : Transport N hash locations store initial)
    (dstHeader : dstBase ∈ locations) (srcHeader : srcBase ∈ locations)
    (dstCovered : ∀ i ∈ indices, Solidity.Storage.Loc.data dstBase i.val ∈ locations)
    (srcCovered : ∀ i ∈ indices, Solidity.Storage.Loc.data srcBase i.val ∈ locations)
    (visitedCovered : ∀ j < max old.length.val src.length.val, Solidity.Storage.Loc.data dstBase j ∈ locations) :
    (Query.length .nil).read (recursiveCopy old src) =
      some (copy N hash dstBase srcBase initial (dstBase.word N hash)) ∧
    (∀ i ∈ indices, ∀ word, (PrimitivePop.elementQuery i).read (recursiveCopy old src) = some word →
      copy N hash dstBase srcBase initial ((Solidity.Storage.Loc.data dstBase i.val).word N hash) = word) ∧
    (∀ a, a ≠ dstBase.word N hash →
      (∀ j < max old.length.val src.length.val, a ≠ (Solidity.Storage.Loc.data dstBase j).word N hash) →
      copy N hash dstBase srcBase initial a = initial a) := by
  have dstRep : Represented old [.length .nil] dstBase store := by
    intro q member; simp only [List.mem_singleton] at member; subst q
    exact beforeDst (.length .nil) List.mem_cons_self
  have srcRep : Represented src [.length .nil] srcBase store := by
    intro q member; simp only [List.mem_singleton] at member; subst q
    exact beforeSrc (.length .nil) List.mem_cons_self
  have dstWord := LifecycleNumeric.array_header_numeric old dstBase store initial hash locations dstRep transport dstHeader
  have srcWord := LifecycleNumeric.array_header_numeric src srcBase store initial hash locations srcRep transport srcHeader
  have dstLen := LifecycleNumeric.headerLength_known hash dstBase initial old.length dstWord
  have srcLen := LifecycleNumeric.headerLength_known hash srcBase initial src.length srcWord
  refine ⟨?_, ?_, ?_⟩
  · rw [copy_header, srcWord]
    cases old; cases src; rfl
  · intro i member word observed
    have numeric := copy_element run dstBase srcBase initial i.val dstHeader (dstCovered i member)
      (by simp only [dstLen, srcLen]; exact visitedCovered)
    dsimp only at numeric
    rw [dstLen, srcLen] at numeric
    rw [graph_read] at observed
    have queryMember : PrimitivePop.elementQuery (G := G) (p := p) i ∈ PrimitivePop.queries indices :=
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, member, rfl⟩)
    by_cases live : i.val < src.length.val
    · rw [if_pos live] at observed
      rw [if_pos (show i.val < max old.length.val src.length.val by omega), if_pos live] at numeric
      rw [numeric]
      simpa only [PrimitivePop.element_location] using beforeSrc.numeric transport _ queryMember
        (by rw [PrimitivePop.element_location]; exact srcCovered i member) word observed
    · rw [if_neg live] at observed
      by_cases tail : i.val < old.length.val
      · rw [if_pos tail] at observed
        cases observed
        rw [if_pos (show i.val < max old.length.val src.length.val by omega), if_neg live] at numeric
        exact numeric
      · rw [if_neg tail] at observed
        rw [if_neg (show ¬ i.val < max old.length.val src.length.val by omega)] at numeric
        rw [numeric]
        simpa only [PrimitivePop.element_location] using beforeDst.numeric transport _ queryMember
          (by rw [PrimitivePop.element_location]; exact dstCovered i member) word observed
  · intro a outsideHeader outside
    apply copy_outside N hash dstBase srcBase initial a outsideHeader
    simpa only [dstLen, srcLen] using outside

/-- Restarting from a processed prefix with the SAME captured payload has
max-prefix behavior. Only finite visited-index separation is required. -/
theorem prefix_restart (address : Nat → Nat) (payload : Nat → Semantics.Word)
    (first second : Nat) (initial : WordStore)
    (separate : ∀ i < max first second, ∀ j < max first second, i ≠ j → address i ≠ address j) :
    writePrefix address payload second (writePrefix address payload first initial) =
      writePrefix address payload (max first second) initial := by
  induction second with
  | zero => simp only [writePrefix, Nat.max_zero]
  | succ second ih =>
    change writeWord (writePrefix address payload second (writePrefix address payload first initial))
      (address second) (payload second) = _
    rw [ih (fun i beforeI j beforeJ different => separate i (by omega) j (by omega) different)]
    by_cases inside : second < first
    · have equalMax : max first second = first := Nat.max_eq_left (by omega)
      have equalNext : max first (second + 1) = first := Nat.max_eq_left (by omega)
      rw [equalMax, equalNext]
      have known := prefix_read address payload first initial second
        (fun j before different => separate second (by omega) j (by omega) (Ne.symm different))
      rw [if_pos inside] at known
      funext a
      by_cases equal : a = address second
      · simp only [writeWord, equal, if_true, known]
      · simp only [writeWord, if_neg equal]
    · have equalMax : max first second = second := Nat.max_eq_right (by omega)
      have equalNext : max first (second + 1) = second + 1 := Nat.max_eq_right (by omega)
      rw [equalMax, equalNext]
      rfl

/-- info: 'Solidity.Backend.StorageOps.NumericTraversal.writePrefix' does not depend on any axioms -/
#guard_msgs in #print axioms writePrefix
/-- info: 'Solidity.Backend.StorageOps.NumericTraversal.prefix_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prefix_read
/-- info: 'Solidity.Backend.StorageOps.NumericTraversal.prefix_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prefix_outside
/-- info: 'Solidity.Backend.StorageOps.NumericTraversal.copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy
/-- info: 'Solidity.Backend.StorageOps.NumericTraversal.copy_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy_header
/-- info: 'Solidity.Backend.StorageOps.NumericTraversal.copy_element' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy_element
/-- info: 'Solidity.Backend.StorageOps.NumericTraversal.copy_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy_outside
/-- info: 'Solidity.Backend.StorageOps.NumericTraversal.graph_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms graph_read
/-- info: 'Solidity.Backend.StorageOps.NumericTraversal.represented_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_observations
/-- info: 'Solidity.Backend.StorageOps.NumericTraversal.prefix_restart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prefix_restart

end Solidity.Backend.StorageOps.NumericTraversal
