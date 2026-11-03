import Solidity.Backend.StorageOps.ClearDemands
import Solidity.Backend.StorageOps.OperationPush
import Solidity.Storage.HashedSeparation

/-! Numeric lifecycle operation components over the PUBLIC WordStore.
The actual CURRENT header drives the capacity check and reset address. No
alternative state/value layer or emitted-EVM/world preservation is claimed. -/
namespace Solidity.Backend.StorageOps.LifecycleNumeric
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- The numeric array header is read from the current machine, not a graph
result supplied as a target oracle. -/
def headerLength (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (machine : WordStore) : Nat :=
  (machine (base.word N hash)).val.toNat

/-- Header operation only. Aggregate allocation needs further initialization
invariants; this component alone is not a complete aggregate push compiler. -/
def pushHeader (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (machine : WordStore) : Option WordStore :=
  let length := headerLength N hash base machine
  if room : length + 1 < 2 ^ 256 then
    some (writeWord machine (base.word N hash) (lengthWord (length + 1) room))
  else none

/-- Primitive default push resets the newly live word, even when already
retained. Address/count derive from the actual numeric header read. -/
def pushPrimitive (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (machine : WordStore) : Option WordStore :=
  let length := headerLength N hash base machine
  if room : length + 1 < 2 ^ 256 then
    some (writeWord (writeWord machine ((Solidity.Storage.Loc.data base length).word N hash) ClearDemands.zero)
      (base.word N hash) (lengthWord (length + 1) room))
  else none

/-- Owner relation and finite transport derive the actual header read. -/
theorem array_header_numeric {n N : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    (hash : Solidity.Storage.Pre → Nat) (locations : List Solidity.Storage.Loc)
    (before : Represented old [.length .nil] base store)
    (transport : Transport N hash locations store machine) (covered : base ∈ locations) :
    machine (base.word N hash) = lengthWord old.length.val old.length.isLt := by
  apply before.numeric transport (.length .nil) List.mem_cons_self covered
  cases old
  rfl

theorem headerLength_known {N : Nat} (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (machine : WordStore) (length : Index)
    (header : machine (base.word N hash) = lengthWord length.val length.isLt) :
    headerLength N hash base machine = length.val := by
  unfold headerLength
  rw [header]
  rfl

theorem pushHeader_known {N : Nat} (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (machine : WordStore) (length : Index)
    (header : machine (base.word N hash) = lengthWord length.val length.isLt) :
    pushHeader N hash base machine = if room : length.val + 1 < 2 ^ 256 then
      some (writeWord machine (base.word N hash) (lengthWord (length.val + 1) room)) else none := by
  unfold pushHeader
  rw [headerLength_known hash base machine length header]

theorem pushPrimitive_known {N : Nat} (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (machine : WordStore) (length : Index)
    (header : machine (base.word N hash) = lengthWord length.val length.isLt) :
    pushPrimitive N hash base machine = if room : length.val + 1 < 2 ^ 256 then
      some (writeWord (writeWord machine ((Solidity.Storage.Loc.data base length.val).word N hash) ClearDemands.zero)
        (base.word N hash) (lengthWord (length.val + 1) room)) else none := by
  unfold pushPrimitive
  rw [headerLength_known hash base machine length header]

/-- Both success/failure capacity outcomes match the existing graph operation;
this is an Option result, not a world rollback assertion. -/
theorem pushPrimitive_failure_known {N : Nat} (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (machine : WordStore) (length : Index)
    (header : machine (base.word N hash) = lengthWord length.val length.isLt) :
    pushPrimitive N hash base machine = none ↔ 2 ^ 256 ≤ length.val + 1 := by
  rw [pushPrimitive_known hash base machine length header]
  constructor
  · intro failed
    by_cases room : length.val + 1 < 2 ^ 256
    · rw [dif_pos room] at failed
      cases failed
    · omega
  · intro full
    exact dif_neg (by omega)

theorem pushPrimitive_failure_matches {n N : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    (hash : Solidity.Storage.Pre → Nat) (locations : List Solidity.Storage.Loc)
    (before : Represented old [.length .nil] base store)
    (transport : Transport N hash locations store machine) (covered : base ∈ locations) :
    pushPrimitive N hash base machine = none ↔ operationPush old = none := by
  exact (pushPrimitive_failure_known hash base machine old.length
    (array_header_numeric old base store machine hash locations before transport covered)).trans
    (operationPush_failure old).symm

/-- Per-run numeric separation of header and newly live primitive element.
The symbolic depth argument reuses the published intrinsic layout fact. -/
theorem header_element_ne {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations) (base : Solidity.Storage.Loc) (length : Nat)
    (headerCovered : base ∈ locations) (elementCovered : Solidity.Storage.Loc.data base length ∈ locations) :
    (Solidity.Storage.Loc.data base length).word N hash ≠ base.word N hash := by
  intro same
  have equal := run.word_inj elementCovered headerCovered same
  have depth := congrArg Solidity.Storage.Loc.depth equal
  simp only [Solidity.Storage.Loc.depth] at depth
  omega

/-- Successful actual primitive graph push is paired with concrete numeric
execution, correct header/reset and all outside numeric words preserved. This
pointwise certificate does not drop the owner's lmax representation bounds. -/
theorem primitive_push_points {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash preimages locations)
    (old result : Value G (.array (.prim p))) (pushed : operationPush old = some result)
    (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    (before : Represented old [.length .nil] base store)
    (transport : Transport N hash locations store machine) (headerCovered : base ∈ locations)
    (elementCovered : Solidity.Storage.Loc.data base old.length.val ∈ locations) :
    ∃ final : WordStore, pushPrimitive N hash base machine = some final ∧
      final (base.word N hash) = lengthWord result.length.val result.length.isLt ∧
      final ((Solidity.Storage.Loc.data base old.length.val).word N hash) = PrimTy.toWord p.dflt ∧
      ∀ a, a ≠ base.word N hash → a ≠ (Solidity.Storage.Loc.data base old.length.val).word N hash →
        final a = machine a := by
  have header := array_header_numeric old base store machine hash locations before transport headerCovered
  have neq := header_element_ne run base old.length.val headerCovered elementCovered
  have lengths := (operationPush_header old result pushed).1
  have room : old.length.val + 1 < 2 ^ 256 := by
    have bound := result.length.isLt
    omega
  let final := writeWord (writeWord machine ((Solidity.Storage.Loc.data base old.length.val).word N hash)
      ClearDemands.zero) (base.word N hash) (lengthWord (old.length.val + 1) room)
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · rw [pushPrimitive_known hash base machine old.length header, dif_pos room]
  · simp only [final, writeWord, if_true]
    apply Subtype.ext
    exact congrArg Int.ofNat lengths.symm
  · change writeWord (writeWord machine ((Solidity.Storage.Loc.data base old.length.val).word N hash)
        ClearDemands.zero) (base.word N hash) (lengthWord (old.length.val + 1) room)
        ((Solidity.Storage.Loc.data base old.length.val).word N hash) = PrimTy.toWord p.dflt
    simp only [writeWord, if_neg neq, if_true, ClearDemands.default_zero]
  · intro a outsideHeader outsideElement
    simp only [final, writeWord, if_neg outsideHeader, if_neg outsideElement]

/-- Readback is derived from the ACTUAL graph push, including the reset of a
previously retained primitive slot, not posited as an output value premise. -/
theorem primitive_push_graph_read {n : Nat} {G : Schema n} {p : PrimTy}
    (old result : Value G (.array (.prim p))) (pushed : operationPush old = some result) :
    (Query.word (.cons (.index old.length) .nil)).read result = some (PrimTy.toWord p.dflt) := by
  have reset := operationPush_reset old result rfl pushed
  have found : result.find (.cons (.index old.length) .nil) = some (.prim p.dflt) := by
    change (Step.get Value.dflt (.index old.length) result).bind (TypeGraph.Path.read Value.dflt .nil) = _
    rw [reset]
    rfl
  simp only [Query.read, Value.observe, found, Option.map_some, Value.head]

/-- Both numeric points agree with independent graph queries of the actual
result. Full represented output still requires the owner's metadata coverage. -/
theorem primitive_push_observations {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash preimages locations)
    (old result : Value G (.array (.prim p))) (pushed : operationPush old = some result)
    (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    (before : Represented old [.length .nil] base store)
    (transport : Transport N hash locations store machine) (headerCovered : base ∈ locations)
    (elementCovered : Solidity.Storage.Loc.data base old.length.val ∈ locations) :
    ∃ final : WordStore, pushPrimitive N hash base machine = some final ∧
      (Query.length .nil).read result = some (final (base.word N hash)) ∧
      (Query.word (.cons (.index old.length) .nil)).read result =
        some (final ((Solidity.Storage.Loc.data base old.length.val).word N hash)) ∧
      ∀ a, a ≠ base.word N hash → a ≠ (Solidity.Storage.Loc.data base old.length.val).word N hash →
        final a = machine a := by
  obtain ⟨final, executed, header, element, frame⟩ :=
    primitive_push_points run old result pushed base store machine before transport headerCovered elementCovered
  refine ⟨final, executed, ?_, ?_, frame⟩
  · rw [header]
    cases result
    rfl
  · rw [element]
    exact primitive_push_graph_read old result pushed

/-- The two ACTUAL numeric writes transport the symbolic store under the same
owner FiniteRun; no new representation relation is introduced. -/
theorem primitive_push_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
    {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash preimages locations) (base : Solidity.Storage.Loc) (length : Index)
    (store : Store) (machine : WordStore) (initial : Transport N hash locations store machine)
    (header : machine (base.word N hash) = lengthWord length.val length.isLt)
    (room : length.val + 1 < 2 ^ 256) (headerCovered : base ∈ locations)
    (elementCovered : Solidity.Storage.Loc.data base length.val ∈ locations) :
    let final := writeWord (writeWord machine ((Solidity.Storage.Loc.data base length.val).word N hash) ClearDemands.zero)
      (base.word N hash) (lengthWord (length.val + 1) room)
    pushPrimitive N hash base machine = some final ∧
    Transport N hash locations
      (write (write store (.data base length.val) ClearDemands.zero) base (lengthWord (length.val + 1) room)) final := by
  constructor
  · rw [pushPrimitive_known hash base machine length header, dif_pos room]
  · exact transport_write run (transport_write run initial (.data base length.val) elementCovered ClearDemands.zero)
      base headerCovered (lengthWord (length.val + 1) room)

/-- info: 'Solidity.Backend.StorageOps.LifecycleNumeric.headerLength' does not depend on any axioms -/
#guard_msgs in #print axioms headerLength
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumeric.pushHeader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pushHeader
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumeric.pushPrimitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pushPrimitive
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumeric.array_header_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms array_header_numeric
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumeric.headerLength_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms headerLength_known
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumeric.pushHeader_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pushHeader_known
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumeric.pushPrimitive_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pushPrimitive_known
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumeric.pushPrimitive_failure_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pushPrimitive_failure_known
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumeric.pushPrimitive_failure_matches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pushPrimitive_failure_matches
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumeric.header_element_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms header_element_ne
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumeric.primitive_push_points' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_push_points
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumeric.primitive_push_graph_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_push_graph_read
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumeric.primitive_push_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_push_observations
/-- info: 'Solidity.Backend.StorageOps.LifecycleNumeric.primitive_push_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms primitive_push_transport

end Solidity.Backend.StorageOps.LifecycleNumeric
