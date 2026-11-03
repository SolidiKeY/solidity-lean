import Solidity.Backend.StorageOps.LifecycleNumeric
import Solidity.Backend.StorageOps.RecursivePop

/-! Primitive array pop over the PUBLIC numeric store. Current machine headers
choose the last-live reset. Finite represented queries include failures and
older retained shadows; no aggregate/compiler/world closure is claimed. -/
namespace Solidity.Backend.StorageOps.PrimitivePop
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def elementQuery {n : Nat} {G : Schema n} {p : PrimTy} (i : Index) : Query G (.array (.prim p)) :=
  .word (.cons (.index i) .nil)

def queries {n : Nat} {G : Schema n} {p : PrimTy} (indices : List Index) :
    List (Query G (.array (.prim p))) := .length .nil :: indices.map elementQuery

def execute (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (machine : WordStore) : Option WordStore :=
  let length := LifecycleNumeric.headerLength N hash base machine
  if live : 0 < length then
    some (writeWord (writeWord machine ((Solidity.Storage.Loc.data base (length - 1)).word N hash) ClearDemands.zero)
      (base.word N hash) (lengthWord (length - 1) (by
        have bound := (machine (base.word N hash)).property
        simp only [PrimTy.inRange, decide_eq_true_eq] at bound
        dsimp only [length, LifecycleNumeric.headerLength]
        omega)))
  else none

theorem other_read {n : Nat} {G : Schema n} {p : PrimTy}
    (old result : Value G (.array (.prim p))) (popped : recursivePop old = some result)
    (i : Index) (other : i.val ≠ old.length.val - 1) :
    (elementQuery i).read result = (elementQuery i).read old := by
  simp only [elementQuery, Query.read, Value.observe, Value.find, TypeGraph.Path.read,
    recursivePop_other old result popped i other]

theorem last_read {n : Nat} {G : Schema n} {p : PrimTy}
    (old result : Value G (.array (.prim p))) (popped : recursivePop old = some result)
    (i : Index) (last : i.val = old.length.val - 1) :
    (elementQuery i).read result = some ClearDemands.zero := by
  cases old with
  | array extent length bound slots =>
    change i.val = length.val - 1 at last
    simp only [recursivePop, Value.length, Value.extent, Value.slots] at popped
    split at popped
    next live =>
      cases popped
      have inside : i.val < extent.val := by omega
      simp only [elementQuery, Query.read, Value.observe, Value.find, TypeGraph.Path.read,
        Step.get, dif_pos inside, if_pos last]
      cases slots ⟨i.val, inside⟩ with
      | absent => exact congrArg some (ClearDemands.default_zero p)
      | present value => cases value; exact congrArg some (ClearDemands.default_zero p)
    next dead => cases popped

theorem element_location {n : Nat} {G : Schema n} {p : PrimTy} (base : Solidity.Storage.Loc) (i : Index) :
    (elementQuery (G := G) (p := p) i).location base = .data base i.val := by
  simp only [elementQuery, Query.location, pathLoc, stepLoc, inlineSize_prim, Nat.mul_one]

private theorem data_ne_base (base : Solidity.Storage.Loc) (i : Nat) : Solidity.Storage.Loc.data base i ≠ base := by
  intro same
  have depth := congrArg Solidity.Storage.Loc.depth same
  simp only [Solidity.Storage.Loc.depth] at depth
  omega

/-- Full requested primitive-array query representation, not only two numeric
points. Header compatibility follows from the OLD relation and actual pop;
all failed/other retained reads keep their exact Option outcomes. -/
theorem represented {n : Nat} {G : Schema n} {p : PrimTy}
    (old result : Value G (.array (.prim p))) (popped : recursivePop old = some result)
    (indices : List Index) (base : Solidity.Storage.Loc) (store : Store)
    (before : Represented old (queries indices) base store) :
    Represented result (queries indices) base
      (write (write store (.data base (old.length.val - 1)) ClearDemands.zero)
        base (lengthWord result.length.val result.length.isLt)) := by
  intro q member
  simp only [queries, List.mem_cons, List.mem_map] at member
  rcases member with rfl | ⟨i, member, rfl⟩
  · have bounded := (before (.length .nil) List.mem_cons_self).2.1
    have oldBounds : old.length.val ≤ lmax ∧ old.extent.val ≤ lmax := by cases old; exact bounded
    have lengths := recursivePop_header old result popped
    refine ⟨True.intro, ?_, ?_⟩
    · cases result with
      | array extent length bound slots =>
        change length.val + 1 = old.length.val ∧ extent = old.extent at lengths
        change length.val ≤ lmax ∧ extent.val ≤ lmax
        rw [lengths.2]
        constructor <;> omega
    · intro word observed
      have observed' : lengthWord result.length.val result.length.isLt = word := by
        cases result
        exact Option.some.inj observed
      rw [← observed']
      simp only [Query.location, pathLoc, Representation.write, if_true]
  · have oldRep := before (elementQuery i) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, member, rfl⟩))
    refine ⟨oldRep.1, True.intro, ?_⟩
    intro word observed
    rw [element_location]
    simp only [Representation.write, if_neg (data_ne_base base i.val)]
    by_cases last : i.val = old.length.val - 1
    · rw [last_read old result popped i last] at observed
      cases observed
      simp only [last, if_true]
    · have different : Solidity.Storage.Loc.data base i.val ≠ .data base (old.length.val - 1) := by
        intro equal
        exact last (Solidity.Storage.Loc.data.inj equal).2
      simp only [if_neg different]
      have was := oldRep.2.2 word ((other_read old result popped i last).symm.trans observed)
      rwa [element_location] at was

theorem execute_known {N : Nat} (hash : Solidity.Storage.Pre → Nat)
    (base : Solidity.Storage.Loc) (machine : WordStore) (length : Index)
    (header : machine (base.word N hash) = lengthWord length.val length.isLt) :
    execute N hash base machine = if live : 0 < length.val then
      some (writeWord (writeWord machine ((Solidity.Storage.Loc.data base (length.val - 1)).word N hash) ClearDemands.zero)
        (base.word N hash) (lengthWord (length.val - 1) (by omega))) else none := by
  unfold execute
  simp only [LifecycleNumeric.headerLength_known hash base machine length header]

/-- Both Option outcomes match. Failure makes no assertion about a World. -/
theorem failure_matches {n N : Nat} {G : Schema n} {p : PrimTy}
    (old : Value G (.array (.prim p))) (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    (hash : Solidity.Storage.Pre → Nat) (locations : List Solidity.Storage.Loc)
    (before : Represented old [.length .nil] base store)
    (initial : Transport N hash locations store machine) (covered : base ∈ locations) :
    execute N hash base machine = none ↔ recursivePop old = none := by
  rw [execute_known hash base machine old.length
    (LifecycleNumeric.array_header_numeric old base store machine hash locations before initial covered),
    recursivePop_failure]
  by_cases live : 0 < old.length.val
  · rw [dif_pos live]
    constructor
    · intro bad; cases bad
    · intro bad; omega
  · rw [dif_neg live]
    exact ⟨fun _ => by omega, fun _ => rfl⟩

/-- Actual current-header execution, full requested owner relation, finite
numeric transport, EVERY successful selected read and all outside words.
No result preservation premise or world rollback is assumed. -/
theorem complete_numeric {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {preimages : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash preimages locations)
    (old result : Value G (.array (.prim p))) (popped : recursivePop old = some result)
    (indices : List Index) (base : Solidity.Storage.Loc) (store : Store) (machine : WordStore)
    (before : Represented old (queries indices) base store)
    (initial : Transport N hash locations store machine)
    (covered : ∀ q ∈ queries (G := G) (p := p) indices, q.location base ∈ locations)
    (lastCovered : Solidity.Storage.Loc.data base (old.length.val - 1) ∈ locations) :
    let after := Representation.write
      (Representation.write store (.data base (old.length.val - 1)) ClearDemands.zero)
      base (lengthWord result.length.val result.length.isLt)
    ∃ final : WordStore, execute N hash base machine = some final ∧
      Represented result (queries indices) base after ∧ Transport N hash locations after final ∧
      (∀ q ∈ queries (G := G) (p := p) indices, ∀ word, q.read result = some word →
        final ((q.location base).word N hash) = word) ∧
      (∀ a, a ≠ base.word N hash → a ≠ (Solidity.Storage.Loc.data base (old.length.val - 1)).word N hash →
        final a = machine a) := by
  have headerRep : Represented old [.length .nil] base store := by
    intro q member
    simp only [List.mem_singleton] at member
    subst q
    exact before (.length .nil) List.mem_cons_self
  have headerCovered : base ∈ locations := covered (.length .nil) List.mem_cons_self
  have header := LifecycleNumeric.array_header_numeric old base store machine hash locations headerRep initial headerCovered
  have lengths := (recursivePop_header old result popped).1
  have live : 0 < old.length.val := by omega
  have lastLength : result.length.val = old.length.val - 1 := by omega
  let final := writeWord (writeWord machine ((Solidity.Storage.Loc.data base (old.length.val - 1)).word N hash)
    ClearDemands.zero) (base.word N hash) (lengthWord result.length.val result.length.isLt)
  have transported := transport_write run (transport_write run initial _ lastCovered ClearDemands.zero)
    base headerCovered (lengthWord result.length.val result.length.isLt)
  have afterRep := represented old result popped indices base store before
  refine ⟨final, ?_, afterRep, transported, ?_, ?_⟩
  · rw [execute_known hash base machine old.length header, dif_pos live]
    dsimp only [final]
    have words : lengthWord (old.length.val - 1) (by have bound := old.length.isLt; omega) =
        lengthWord result.length.val result.length.isLt := by
      apply Subtype.ext
      exact congrArg Int.ofNat lastLength.symm
    rw [words]
  · intro q member word observed
    exact afterRep.numeric transported q member (covered q member) word observed
  · intro a outsideHeader outsideLast
    simp only [final, writeWord, if_neg outsideHeader, if_neg outsideLast]

/-- info: 'Solidity.Backend.StorageOps.PrimitivePop.elementQuery' does not depend on any axioms -/
#guard_msgs in #print axioms elementQuery
/-- info: 'Solidity.Backend.StorageOps.PrimitivePop.queries' does not depend on any axioms -/
#guard_msgs in #print axioms queries
/-- info: 'Solidity.Backend.StorageOps.PrimitivePop.execute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms execute
/-- info: 'Solidity.Backend.StorageOps.PrimitivePop.other_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms other_read
/-- info: 'Solidity.Backend.StorageOps.PrimitivePop.last_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms last_read
/-- info: 'Solidity.Backend.StorageOps.PrimitivePop.element_location' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms element_location
/-- info: 'Solidity.Backend.StorageOps.PrimitivePop.represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms represented
/-- info: 'Solidity.Backend.StorageOps.PrimitivePop.execute_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms execute_known
/-- info: 'Solidity.Backend.StorageOps.PrimitivePop.failure_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms failure_matches
/-- info: 'Solidity.Backend.StorageOps.PrimitivePop.complete_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete_numeric

end Solidity.Backend.StorageOps.PrimitivePop
