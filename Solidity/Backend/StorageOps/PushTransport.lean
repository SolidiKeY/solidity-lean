import Solidity.Backend.StorageOps.PathRepresentation

/-! Complete primitive-push operation transport and EXACT public header-
coverage characterization. The original intrinsic Word capacity/profile stays
unchanged; no new source cap or post-preservation premise is introduced. -/
namespace Solidity.Backend.StorageOps.PushTransport
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Actual push resets exactly the newly live primitive slot, fresh or reused;
every other retained/default/failing logical read is preserved. -/
theorem element_read {n : Nat} {G : Schema n} {p : PrimTy}
    (old result : Value G (.array (.prim p))) (pushed : operationPush old = some result) (i : Index) :
    (PrimitivePop.elementQuery i).read result = if i.val = old.length.val then some ClearDemands.zero
      else (PrimitivePop.elementQuery i).read old := by
  cases old with
  | array extent length bound slots =>
    simp only [operationPush, Value.length, Value.extent, Value.slots] at pushed
    split at pushed
    next room =>
      cases pushed
      simp only [Value.length]
      by_cases fresh : i.val = length.val
      · have inside : i.val < max extent.val (length.val + 1) := by omega
        simp only [PrimitivePop.elementQuery, Query.read, Value.observe, Value.find, TypeGraph.Path.read,
          Step.get, dif_pos inside, TypeGraph.Ty.isPrimitive, true_and, if_pos fresh,
          Slot.getD, Option.bind_some, Option.map_some, Value.head]
        exact congrArg some (ClearDemands.default_zero p)
      · by_cases allocated : i.val < extent.val
        · have inside : i.val < max extent.val (length.val + 1) := by omega
          simp only [PrimitivePop.elementQuery, Query.read, Value.observe, Value.find, TypeGraph.Path.read,
            Step.get, dif_pos inside, TypeGraph.Ty.isPrimitive, true_and, if_neg fresh, dif_pos allocated,
            Option.bind_some, Option.map_some, Value.head]
        · have outside : ¬ i.val < max extent.val (length.val + 1) := by omega
          simp only [PrimitivePop.elementQuery, Query.read, Value.observe, Value.find, TypeGraph.Path.read,
            Step.get, dif_neg outside, dif_neg allocated, if_neg fresh, Option.bind_none, Option.map_none]
    next full => cases pushed

private theorem data_ne_base (base : Solidity.Storage.Loc) (i : Nat) : Solidity.Storage.Loc.data base i ≠ base := by
  intro same
  have depth := congrArg Solidity.Storage.Loc.depth same
  simp only [Solidity.Storage.Loc.depth] at depth
  omega

/-- The post-owner relation holds IFF its original header coverage holds.
This characterizes the real public-interface boundary without adding a source
restriction, assuming post-preservation or weakening any predicate. -/
theorem represented_iff {n : Nat} {G : Schema n} {p : PrimTy}
    (old result : Value G (.array (.prim p))) (pushed : operationPush old = some result)
    (indices : List Index) (base : Solidity.Storage.Loc) (store : Store)
    (before : Represented old (PrimitivePop.queries indices) base store) :
    Represented result (PrimitivePop.queries indices) base
      (Representation.write (Representation.write store (.data base old.length.val) ClearDemands.zero)
        base (lengthWord result.length.val result.length.isLt)) ↔ old.length.val + 1 ≤ lmax := by
  have lengths := operationPush_header old result pushed
  constructor
  · intro represented
    have bounded := (represented (.length .nil) List.mem_cons_self).2.1
    have newBound : result.length.val ≤ lmax := by cases result; exact bounded.1
    omega
  · intro coverage q member
    simp only [PrimitivePop.queries, List.mem_cons, List.mem_map] at member
    rcases member with rfl | ⟨i, inside, rfl⟩
    · have oldBounded := (before (.length .nil) List.mem_cons_self).2.1
      have oldExtent : old.extent.val ≤ lmax := by cases old; exact oldBounded.2
      refine ⟨True.intro, ?_, ?_⟩
      · cases result with
        | array extent length bound slots =>
          change length.val = old.length.val + 1 ∧ extent.val = max old.extent.val (old.length.val + 1) at lengths
          change length.val ≤ lmax ∧ extent.val ≤ lmax
          constructor <;> omega
      · intro word observed
        have observed' : lengthWord result.length.val result.length.isLt = word := by
          cases result; exact Option.some.inj observed
        rw [← observed']
        simp only [Query.location, pathLoc, Representation.write, if_true]
    · have oldRep := before (PrimitivePop.elementQuery i)
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, inside, rfl⟩))
      refine ⟨oldRep.1, True.intro, ?_⟩
      intro word observed
      rw [element_read old result pushed i] at observed
      rw [PrimitivePop.element_location]
      simp only [Representation.write, if_neg (data_ne_base base i.val)]
      by_cases newIndex : i.val = old.length.val
      · rw [if_pos newIndex] at observed
        cases observed
        simp only [newIndex, if_true]
      · rw [if_neg newIndex] at observed
        have neq : Solidity.Storage.Loc.data base i.val ≠ .data base old.length.val := by
          intro same
          exact newIndex (Solidity.Storage.Loc.data.inj same).2
        simp only [if_neg neq]
        have original := oldRep.2.2 word observed
        rwa [PrimitivePop.element_location] at original

/-- Actual numeric execution and finite transport always hold on success.
Selected postrepresentation is characterized EXACTLY, not assumed or promoted
to a complete Source/compiler theorem beyond the owner's header range. -/
theorem complete_numeric {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash preimages locations)
    (old result : Value G (.array (.prim p))) (pushed : operationPush old = some result)
    (indices : List Index) (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    (before : Represented old (PrimitivePop.queries indices) base store)
    (initial : Transport N hash locations store machine) (headerCovered : base ∈ locations)
    (elementCovered : Solidity.Storage.Loc.data base old.length.val ∈ locations) :
    let after := Representation.write (Representation.write store (.data base old.length.val) ClearDemands.zero)
      base (lengthWord result.length.val result.length.isLt)
    ∃ final : WordStore, LifecycleNumeric.pushPrimitive N hash base machine = some final ∧
      Transport N hash locations after final ∧
      (Represented result (PrimitivePop.queries indices) base after ↔ old.length.val + 1 ≤ lmax) ∧
      (∀ a, a ≠ base.word N hash → a ≠ (Solidity.Storage.Loc.data base old.length.val).word N hash → final a = machine a) := by
  have headerRep : Represented old [.length .nil] base store := by
    intro q member; simp only [List.mem_singleton] at member; subst q
    exact before (.length .nil) List.mem_cons_self
  have header := LifecycleNumeric.array_header_numeric old base store machine hash locations headerRep initial headerCovered
  have lengths := (operationPush_header old result pushed).1
  have room : old.length.val + 1 < 2 ^ 256 := by have bound := result.length.isLt; omega
  let final := writeWord (writeWord machine ((Solidity.Storage.Loc.data base old.length.val).word N hash) ClearDemands.zero)
    (base.word N hash) (lengthWord result.length.val result.length.isLt)
  refine ⟨final, ?_, ?_, represented_iff old result pushed indices base store before, ?_⟩
  · rw [LifecycleNumeric.pushPrimitive_known hash base machine old.length header, dif_pos room]
    have words : lengthWord (old.length.val + 1) room = lengthWord result.length.val result.length.isLt := by
      apply Subtype.ext
      exact congrArg Int.ofNat lengths.symm
    rw [words]
  · exact transport_write run (transport_write run initial _ elementCovered ClearDemands.zero)
      base headerCovered (lengthWord result.length.val result.length.isLt)
  · intro a outsideHeader outsideElement
    simp only [final, writeWord, if_neg outsideHeader, if_neg outsideElement]

/-- Selected numeric read agreement is independent of the narrower owner
header metadata range. All selected physical locations MUST be covered. -/
theorem selected_numeric {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash preimages locations)
    (old result : Value G (.array (.prim p))) (pushed : operationPush old = some result)
    (indices : List Index) (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    (before : Represented old (PrimitivePop.queries indices) base store)
    (initial : Transport N hash locations store machine)
    (covered : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, q.location base ∈ locations)
    (elementCovered : Solidity.Storage.Loc.data base old.length.val ∈ locations) :
    ∃ final : WordStore, LifecycleNumeric.pushPrimitive N hash base machine = some final ∧
      ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, ∀ word,
        q.read result = some word → final ((q.location base).word N hash) = word := by
  have headerRep : Represented old [.length .nil] base store := by
    intro q member; simp only [List.mem_singleton] at member; subst q
    exact before (.length .nil) List.mem_cons_self
  have headerCovered : base ∈ locations := covered (.length .nil) List.mem_cons_self
  obtain ⟨final, executed, header, newWord, frame⟩ := LifecycleNumeric.primitive_push_points run old result pushed
    base store machine headerRep initial headerCovered elementCovered
  refine ⟨final, executed, ?_⟩
  intro q member word observed
  simp only [PrimitivePop.queries, List.mem_cons, List.mem_map] at member
  rcases member with rfl | ⟨i, inside, rfl⟩
  · have actual : lengthWord result.length.val result.length.isLt = word := by cases result; exact Option.some.inj observed
    exact header.trans actual
  · have member : PrimitivePop.elementQuery (G := G) (p := p) i ∈ PrimitivePop.queries indices :=
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, inside, rfl⟩)
    have queryCovered : Solidity.Storage.Loc.data base i.val ∈ locations := by
      rw [← PrimitivePop.element_location (G := G) (p := p) base i]
      exact covered _ member
    rw [element_read old result pushed i] at observed
    rw [PrimitivePop.element_location]
    by_cases newIndex : i.val = old.length.val
    · rw [if_pos newIndex] at observed
      cases observed
      rw [newIndex, newWord, ClearDemands.default_zero]
    · rw [if_neg newIndex] at observed
      have neqHeader := LifecycleNumeric.header_element_ne run base i.val headerCovered queryCovered
      have neqElement : (Solidity.Storage.Loc.data base i.val).word N hash ≠
          (Solidity.Storage.Loc.data base old.length.val).word N hash := by
        intro same
        exact newIndex (Solidity.Storage.Loc.data.inj (run.word_inj queryCovered elementCovered same)).2
      rw [frame _ neqHeader neqElement]
      simpa only [PrimitivePop.element_location] using before.numeric initial _ member (covered _ member) word observed

/-- Actual typed-root push transports its actual writes and characterizes
selected ROOT postrepresentation by the unchanged owner header range. -/
theorem push_at {n N L R : Nat} {G : Schema n} {A : TypeGraph.Ty n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash preimages locations)
    (root result : Value G A) (pre : TypeGraph.Path G A (.array (.prim p)))
    (old : Value G (.array (.prim p))) (found : root.find pre = some old)
    (pushed : pushAt root pre = some result) (indices : List Index)
    (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    (before : Represented root ((PrimitivePop.queries indices).map (Query.prefix pre)) base store)
    (initial : Transport N hash locations store machine) (headerCovered : pathLoc pre base ∈ locations)
    (elementCovered : Solidity.Storage.Loc.data (pathLoc pre base) old.length.val ∈ locations) :
    ∃ child final, result.find pre = some child ∧
      LifecycleNumeric.pushPrimitive N hash (pathLoc pre base) machine = some final ∧
      let after := Representation.write (Representation.write store (.data (pathLoc pre base) old.length.val) ClearDemands.zero)
        (pathLoc pre base) (lengthWord child.length.val child.length.isLt)
      Transport N hash locations after final ∧
        (Represented result ((PrimitivePop.queries indices).map (Query.prefix pre)) base after ↔ old.length.val + 1 ≤ lmax) := by
  obtain ⟨actual, child, read, changed, saved⟩ := modifyAt_success root result pre operationPush pushed
  rw [found] at read
  cases read
  have readBack := Value.find_save root result pre child saved
  have childBefore := PathRepresentation.focus root old pre found _ base store before
  have supported : PathSupported pre := ((Query.supported_prefix pre (.length .nil)).mp
    (before ((Query.length .nil).prefix pre) (List.mem_map.mpr ⟨_, List.mem_cons_self, rfl⟩)).1).1
  obtain ⟨final, executed, transported, iffCovered, _⟩ :=
    complete_numeric run old child changed indices (pathLoc pre base) store machine childBefore initial headerCovered elementCovered
  refine ⟨child, final, readBack, executed, transported, ?_⟩
  constructor
  · intro afterRep
    exact iffCovered.mp (PathRepresentation.focus result child pre readBack _ base _ afterRep)
  · intro coverage
    exact Represented.prefix pre readBack supported (iffCovered.mpr coverage)

/-- info: 'Solidity.Backend.StorageOps.PushTransport.element_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms element_read
/-- info: 'Solidity.Backend.StorageOps.PushTransport.represented_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms represented_iff
/-- info: 'Solidity.Backend.StorageOps.PushTransport.complete_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete_numeric
/-- info: 'Solidity.Backend.StorageOps.PushTransport.selected_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms selected_numeric
/-- info: 'Solidity.Backend.StorageOps.PushTransport.push_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms push_at

end Solidity.Backend.StorageOps.PushTransport
