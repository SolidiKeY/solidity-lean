import Solidity.Backend.StorageOps.CopyOutput
import Solidity.Backend.StorageOps.PrimitivePop

/-! Aggregate pop reads the current numeric header, generates only the last
live slot's recursive clear writes and decrements the header last. The supplied
intrinsic graph provides retained slot shapes, not a desired output oracle.
This does not discover shapes from machine storage or emit target loops. -/
namespace Solidity.Backend.StorageOps.AggregatePop
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- No depth/length cutoff: shape traversal is the checked recursive clear
query generator. Missing slots and mappings generate no writes. -/
noncomputable def clearUpdates {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (slot : Slot G E) (base : Solidity.Storage.Loc) : List (Solidity.Storage.Loc × Semantics.Word) :=
  (CopyWrites.zeros (ClearDemands.slotDemands slot)).map (fun op => (op.1.location base,op.2))

noncomputable def execute {n N : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (machine : WordStore) : Option WordStore :=
  let length := LifecycleNumeric.headerLength N hash base machine
  if live : 0 < length then
    let slot := oldSlot old.extent old.slots (length - 1)
    let child := Solidity.Storage.Loc.data base ((length - 1) * inlineSize G E)
    let cleared := (clearUpdates slot child).foldl
      (fun w op => writeWord w (op.1.word N hash) op.2) machine
    some (writeWord cleared (base.word N hash) (lengthWord (length - 1) (by
      have bound := (machine (base.word N hash)).property
      simp only [PrimTy.inRange,decide_eq_true_eq] at bound
      dsimp only [length,LifecycleNumeric.headerLength]
      omega)))
  else none

def lastIndex {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) : Index := ⟨old.length.val - 1,by have h := old.length.isLt; omega⟩

def lastPath {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) : TypeGraph.Path G (.array E) E := .cons (.index (lastIndex old)) .nil

def lastSlot {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) : Slot G E := oldSlot old.extent old.slots (old.length.val - 1)

noncomputable def childBase {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) (base : Solidity.Storage.Loc) : Solidity.Storage.Loc := pathLoc (lastPath old) base

theorem child_location {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) (base : Solidity.Storage.Loc) :
    childBase old base = .data base ((old.length.val - 1) * inlineSize G E) := rfl

theorem old_last_read {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) (live : 0 < old.length.val) :
    old.find (lastPath old) = some ((lastSlot old).getD (Value.dflt E)) := by
  cases old with
  | array extent length bound slots =>
    have inside : length.val - 1 < extent.val := by change 0 < length.val at live; omega
    simp only [Value.find,lastPath,lastIndex,Path.read,Step.get,Value.length,Value.extent,Value.slots,
      dif_pos inside,Option.bind_some,lastSlot,oldSlot]

theorem popped_last_read {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (popped : recursivePop old = some result) :
    result.find (lastPath old) = some ((recursiveClearSlot (lastSlot old)).getD (Value.dflt E)) := by
  cases old with
  | array extent length bound slots =>
    simp only [recursivePop,Value.length,Value.extent,Value.slots] at popped
    split at popped
    next live =>
      cases popped
      have inside : length.val - 1 < extent.val := by omega
      simp only [Value.find,lastPath,lastIndex,Path.read,Step.get,Value.length,Value.extent,Value.slots,
        dif_pos inside,Option.bind_some,lastSlot,oldSlot,ite_true]
    next dead => cases popped

theorem execute_known {n N : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (machine : WordStore)
    (header : machine (base.word N hash) = lengthWord old.length.val old.length.isLt) :
    execute (N := N) old hash base machine = if live : 0 < old.length.val then
      some (writeWord ((clearUpdates (lastSlot old) (childBase old base)).foldl
        (fun w op => writeWord w (op.1.word N hash) op.2) machine)
        (base.word N hash) (lengthWord (old.length.val - 1) (by omega)))
      else none := by
  unfold execute
  simp only [LifecycleNumeric.headerLength_known hash base machine old.length header]
  rfl

/-- Both Option outcomes, derived from OLD representation; not world rollback. -/
theorem failure_matches {n N : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    (hash : Solidity.Storage.Pre → Nat) (locations : List Solidity.Storage.Loc)
    (before : Represented old [.length .nil] base store)
    (initial : Transport N hash locations store machine) (covered : base ∈ locations) :
    execute (N := N) old hash base machine = none ↔ recursivePop old = none := by
  rw [execute_known old hash base machine
    (LifecycleNumeric.array_header_numeric old base store machine hash locations before initial covered),
    recursivePop_failure]
  by_cases live : 0 < old.length.val
  · rw [dif_pos live]
    constructor
    · intro impossible; cases impossible
    · intro impossible; omega
  · rw [dif_neg live]
    exact ⟨fun _ => by omega,fun _ => rfl⟩

/-- Scalar readback of ACTUAL recursive slot clear writes. Successful retained
DEFAULT reads require OLD agreement; absent slots are not eagerly zeroed. -/
theorem slot_readback {n N L R : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (slot : Slot G E) (q : Query G E) (base : Solidity.Storage.Loc) (machine : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (covered : q.location base ∈ locations)
    (writesCovered : ∀ d ∈ ClearDemands.slotDemands slot, d.location base ∈ locations)
    (separate : ∀ d ∈ ClearDemands.slotDemands slot, d.location base = q.location base → d = q)
    (before : ∀ word, q.read (slot.getD (Value.dflt E)) = some word → machine ((q.location base).word N hash) = word)
    (word : Semantics.Word) (observed : q.read ((recursiveClearSlot slot).getD (Value.dflt E)) = some word) :
    ((clearUpdates slot base).foldl (fun w op => writeWord w (op.1.word N hash) op.2) machine)
      ((q.location base).word N hash) = word := by
  rw [show ((clearUpdates slot base).foldl (fun w op => writeWord w (op.1.word N hash) op.2) machine)
      ((q.location base).word N hash) =
      CopyReadback.traceWord q (CopyWrites.zeros (ClearDemands.slotDemands slot))
        (machine ((q.location base).word N hash)) from by
    apply CopyReadback.numeric_trace
    intro op member
    obtain ⟨d,inside,same⟩ := List.mem_map.mp member
    subst op
    constructor
    · intro equal
      exact separate d inside (run.word_inj (writesCovered d inside) covered equal)
    · intro equal; rw [equal]]
  exact CopyOutput.clear_slot_output slot q _ before word observed


/-- Generated recursive clear writes followed by exactly one header decrement. -/
noncomputable def updates {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) (base : Solidity.Storage.Loc) : List (Solidity.Storage.Loc × Semantics.Word) :=
  clearUpdates (lastSlot old) (childBase old base) ++
    [(base,lengthWord (old.length.val - 1) (by have h := old.length.isLt; omega))]

def queries {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) (selected : List (Query G E)) : List (Query G (.array E)) :=
  .length .nil :: selected.map (Query.prefix (lastPath old))

theorem slot_compatible {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (slot : Slot G E) (q : Query G E) (before : q.compatible (slot.getD (Value.dflt E))) :
    q.compatible ((recursiveClearSlot slot).getD (Value.dflt E)) := by
  classical
  by_cases member : q ∈ ClearDemands.slotDemands slot
  · exact ClearDemands.listed_slot_compatible slot q member before
  · rw [(ClearDemands.outside_slot_frame slot q member).2]
    exact before

/-- Full selected last-slot ROOT representation and actual current-header
numeric execution. OLD relations, finite coverage/run and symbolic separation
are required; no post-result preservation is assumed. The selected child can
be a recursively nested aggregate or mapping. -/
theorem complete_numeric {n N L R : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old result : Value G (.array E)) (popped : recursivePop old = some result)
    (selected : List (Query G E)) (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (before : Represented old (queries old selected) base store)
    (initial : Transport N hash locations store machine) (headerCovered : base ∈ locations)
    (queryCovered : ∀ q ∈ selected, q.location (childBase old base) ∈ locations)
    (writesCovered : ∀ d ∈ ClearDemands.slotDemands (lastSlot old), d.location (childBase old base) ∈ locations)
    (separate : ∀ q ∈ selected, ∀ d ∈ ClearDemands.slotDemands (lastSlot old),
      d.location (childBase old base) = q.location (childBase old base) → d = q)
    (headerSeparate : ∀ q ∈ selected, q.location (childBase old base) ≠ base) :
    ∃ final, execute (N := N) old hash base machine = some final ∧
      let after := (updates old base).foldl (fun w op => write w op.1 op.2) store
      Represented result (queries old selected) base after ∧ Transport N hash locations after final := by
  have live : 0 < old.length.val := by
    have notZero : old.length.val ≠ 0 := by
      intro zero
      have failed := (recursivePop_failure old).mpr zero
      rw [failed] at popped
      cases popped
    omega
  have headerBefore : Represented old [.length .nil] base store := by
    intro q member
    have same := List.mem_singleton.mp member
    subst q
    exact before _ List.mem_cons_self
  have header := LifecycleNumeric.array_header_numeric old base store machine hash locations headerBefore initial headerCovered
  let cleared := (clearUpdates (lastSlot old) (childBase old base)).foldl
    (fun w op => writeWord w (op.1.word N hash) op.2) machine
  let final := writeWord cleared (base.word N hash)
    (lengthWord (old.length.val - 1) (by have h := old.length.isLt; omega))
  have executed : execute (N := N) old hash base machine = some final := by
    rw [execute_known old hash base machine header,dif_pos live]
  have covered : ∀ op ∈ updates old base, op.1 ∈ locations := by
    intro op member
    rcases List.mem_append.mp member with child | root
    · obtain ⟨pair,pairMember,same⟩ := List.mem_map.mp child
      obtain ⟨q,generated,samePair⟩ := List.mem_map.mp pairMember
      subst pair
      subst op
      exact writesCovered q generated
    · have same := List.mem_singleton.mp root
      subst op
      exact headerCovered
  have transported : Transport N hash locations
      ((updates old base).foldl (fun w op => write w op.1 op.2) store) final := by
    simpa only [updates,List.foldl_append,List.foldl_cons,List.foldl_nil] using
      transport_sequence run initial (updates old base) covered
  refine ⟨final,executed,?_,transported⟩
  intro q member
  rcases List.mem_cons.mp member with same | childMember
  · subst q
    have prior := headerBefore (.length .nil) (List.mem_singleton_self _)
    have sizes := recursivePop_header old result popped
    have bounds : old.length.val ≤ lmax ∧ old.extent.val ≤ lmax := by cases old; exact prior.2.1
    refine ⟨True.intro,?_,?_⟩
    · cases result with
      | array extent length bound slots =>
        change length.val + 1 = old.length.val ∧ extent = old.extent at sizes
        change length.val ≤ lmax ∧ extent.val ≤ lmax
        rw [sizes.2]
        constructor <;> omega
    · intro word observed
      change ((updates old base).foldl (fun w op => write w op.1 op.2) store) base = word
      rw [← transported base headerCovered]
      change final (base.word N hash) = word
      have seen : lengthWord result.length.val result.length.isLt = word := by cases result; exact Option.some.inj observed
      have count : result.length.val = old.length.val - 1 := by omega
      simp only [final,writeWord,if_true]
      rw [← seen]
      simp only [count]
  · obtain ⟨child,inside,same⟩ := List.mem_map.mp childMember
    subst q
    have prior := before (child.prefix (lastPath old))
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨child,inside,rfl⟩))
    have oldFound := old_last_read old live
    have newFound := popped_last_read old result popped
    refine ⟨prior.1,?_,?_⟩
    · rw [Query.compatible_prefix result _ (lastPath old) child newFound]
      apply slot_compatible
      rw [← Query.compatible_prefix old _ (lastPath old) child oldFound]
      exact prior.2.1
    · intro word observed
      have observedChild : child.read ((recursiveClearSlot (lastSlot old)).getD (Value.dflt E)) = some word := by
        rwa [Query.read_prefix result _ (lastPath old) child newFound] at observed
      have readback := slot_readback (lastSlot old) child (childBase old base) machine run
        (queryCovered child inside) writesCovered (separate child inside) (by
          intro value seen
          have rootSeen : (child.prefix (lastPath old)).read old = some value := by
            rw [Query.read_prefix old _ (lastPath old) child oldFound]
            exact seen
          have numeric := before.numeric initial (child.prefix (lastPath old))
            (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨child,inside,rfl⟩))
            (by simpa only [Query.location_prefix] using queryCovered child inside) value rootSeen
          simpa only [Query.location_prefix] using numeric) word observedChild
      have different : (child.location (childBase old base)).word N hash ≠ base.word N hash := by
        intro same
        exact headerSeparate child inside (run.word_inj (queryCovered child inside) headerCovered same)
      rw [← transported _ (by simpa only [Query.location_prefix] using queryCovered child inside)]
      rw [Query.location_prefix]
      change final ((child.location (childBase old base)).word N hash) = word
      simp only [final,writeWord,if_neg different]
      exact readback

/-- Every numeric word outside the generated last-slot and header addresses is
unchanged, including older retained shadows covered by those exact premises. -/
theorem outside {n N : Nat} {G : Schema n} {E : TypeGraph.Ty n}
    (old : Value G (.array E)) (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (machine final : WordStore)
    (header : machine (base.word N hash) = lengthWord old.length.val old.length.isLt)
    (executed : execute (N := N) old hash base machine = some final)
    (address : Nat) (apart : ∀ op ∈ updates old base, address ≠ op.1.word N hash) :
    final address = machine address := by
  rw [execute_known old hash base machine header] at executed
  split at executed
  · cases executed
    simpa only [updates,List.foldl_append,List.foldl_cons,List.foldl_nil] using
      sequence_outside_frame N hash machine (updates old base) address apart
  · cases executed

/-- info: 'Solidity.Backend.StorageOps.AggregatePop.child_location' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms child_location
/-- info: 'Solidity.Backend.StorageOps.AggregatePop.old_last_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms old_last_read
/-- info: 'Solidity.Backend.StorageOps.AggregatePop.popped_last_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms popped_last_read
/-- info: 'Solidity.Backend.StorageOps.AggregatePop.execute_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms execute_known
/-- info: 'Solidity.Backend.StorageOps.AggregatePop.failure_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms failure_matches
/-- info: 'Solidity.Backend.StorageOps.AggregatePop.slot_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms slot_readback
/-- info: 'Solidity.Backend.StorageOps.AggregatePop.slot_compatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms slot_compatible
/-- info: 'Solidity.Backend.StorageOps.AggregatePop.complete_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete_numeric
/-- info: 'Solidity.Backend.StorageOps.AggregatePop.outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms outside
end Solidity.Backend.StorageOps.AggregatePop
