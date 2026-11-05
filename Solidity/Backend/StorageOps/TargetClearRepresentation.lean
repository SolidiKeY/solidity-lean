import Solidity.Backend.StorageOps.TargetArrayClear

/-! Operation-side adapters from independent existing graph clear to PUBLIC
represented observations and actual runtime target/numeric prefix writes.
No representation/value/state layer or Source admission restriction is added. -/
namespace Solidity.Backend.StorageOps.TargetClearRepresentation
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Exact independent graph read: live primitives default tozero; every other
retained/defaulted/malformed/out-of-extent Option outcome is OLD. -/
theorem element_read {n : Nat} {G : Schema n} {p : PrimTy}
    (old : Value G (.array (.prim p))) (i : Index) :
    (PrimitivePop.elementQuery i).read (recursiveClear old) =
      if i.val < old.length.val then some ClearDemands.zero else (PrimitivePop.elementQuery i).read old := by
  cases old with
  | array extent length bound slots =>
    by_cases live : i.val < length.val
    · have inside : i.val < extent.val := by omega
      simp only [recursiveClear,PrimitivePop.elementQuery,Query.read,Value.observe,Value.find,TypeGraph.Path.read,
        Step.get,dif_pos inside,visit_prefix,Value.length,if_pos live,Option.bind_some,Option.map_some]
      cases current : slots ⟨i.val,inside⟩ with
      | absent =>
        simp only [recursiveClearSlot,Slot.getD,Value.dflt,Value.head]
        exact congrArg some (ClearDemands.default_zero p)
      | present value =>
        cases value
        simp only [recursiveClearSlot,recursiveClear,Slot.getD,Value.head]
        exact congrArg some (ClearDemands.default_zero p)
    · by_cases inside : i.val < extent.val
      · simp only [recursiveClear,PrimitivePop.elementQuery,Query.read,Value.observe,Value.find,TypeGraph.Path.read,
          Step.get,dif_pos inside,visit_prefix,Value.length,if_neg live,Option.bind_some,Option.map_some]
      · simp only [recursiveClear,PrimitivePop.elementQuery,Query.read,Value.observe,Value.find,TypeGraph.Path.read,
          Step.get,dif_neg inside,Value.length,if_neg live,Option.bind_none,Option.map_none]

/-- Generated writes act on the EXISTING public symbolic Store. -/
def symbolicPrefix (store : Store) (base : Solidity.Storage.Loc) : Nat → Store
  | 0 => store
  | count+1 => Representation.write (symbolicPrefix store base count) (.data base count) ClearDemands.zero

/-- Same actual generated prefix over the EXISTING numeric WordStore. -/
def numericPrefix (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (store : WordStore) (base : Solidity.Storage.Loc) : Nat → WordStore
  | 0 => store
  | count+1 => writeWord (numericPrefix N hash store base count) ((Solidity.Storage.Loc.data base count).word N hash) ClearDemands.zero

/-- The numeric operation reads CURRENT numeric header, then clears live words
and writes headerzero LAST; no graph value is passed to this routine. -/
def execute (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc)
    (store : WordStore) : WordStore :=
  writeWord (numericPrefix N hash store base (LifecycleNumeric.headerLength N hash base store)) (base.word N hash) ClearDemands.zero


/-- Exact operation-generated symbolic data prefix, using PUBLIC writes. -/
theorem symbolic_data (store : Store) (base : Solidity.Storage.Loc) (count j : Nat) :
    symbolicPrefix store base count (.data base j) = if j < count then ClearDemands.zero else store (.data base j) := by
  induction count with
  | zero => rw [symbolicPrefix,if_neg (Nat.not_lt_zero _) ]
  | succ count ih =>
    by_cases last : j = count
    · subst j
      rw [symbolicPrefix,Representation.write_same,if_pos (by omega)]
    · have different : Solidity.Storage.Loc.data base j ≠ .data base count := by
        intro same; exact last (Solidity.Storage.Loc.data.inj same).2
      rw [symbolicPrefix,Representation.write_other _ _ _ _ different,ih]
      by_cases visited : j < count
      · rw [if_pos visited,if_pos (by omega)]
      · rw [if_neg visited,if_neg (by omega)]

theorem symbolic_outside (store : Store) (base observer : Solidity.Storage.Loc) (count : Nat)
    (apart : ∀ j, j < count → observer ≠ .data base j) : symbolicPrefix store base count observer = store observer := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [symbolicPrefix,Representation.write_other _ _ _ _ (apart count (by omega))]
    exact ih (fun j inside => apart j (by omega))

/-- ALL covered target-cell agreements follow by applying the PUBLIC concrete
write adapter to every generated child. No desired postagreement premise. -/
theorem prefix_target (store : Store) (target : Evm.Machine) (base : Solidity.Storage.Loc)
    (baseFits : TargetOperations.KeysFit base) (locations : List Solidity.Storage.Loc)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (initial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
    (count : Nat) :
    ∀ l (member : l ∈ locations), (TargetArrayClear.clearPrefix target.store (TargetOperations.toSlot base baseFits) count).cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord (symbolicPrefix store base count l) := by
  induction count with
  | zero => exact initial
  | succ count ih =>
    exact TargetOperations.write_agreement locations fitting (.data base count) baseFits ClearDemands.zero
      (symbolicPrefix store base count) { target with store := TargetArrayClear.clearPrefix target.store (TargetOperations.toSlot base baseFits) count } ih

/-- Generated-access transport uses the ORIGINAL finite run and every actual
write's coverage; no global hash injectivity or replacement representation. -/
theorem prefix_numeric {N L R : Nat} {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre}
    {locations : List Solidity.Storage.Loc} (run : FiniteRun N L R hash P locations)
    (store : Store) (numeric : WordStore) (base : Solidity.Storage.Loc)
    (initial : Transport N hash locations store numeric) (count : Nat)
    (covered : ∀ j, j < count → Solidity.Storage.Loc.data base j ∈ locations) :
    Transport N hash locations (symbolicPrefix store base count) (numericPrefix N hash numeric base count) := by
  induction count with
  | zero => exact initial
  | succ count ih =>
    exact transport_write run (ih (fun j inside => covered j (by omega))) (.data base count) (covered count (by omega)) ClearDemands.zero


/-- OLD observations needed for clear are header plus unvisited requested
indices. Overwritten primitive words need no old payload/default-zero premise. -/
def oldQueries {n : Nat} {G : Schema n} {p : PrimTy} (old : Value G (.array (.prim p)))
    (indices : List Index) : List (Query G (.array (.prim p))) :=
  PrimitivePop.queries (indices.filter (fun i => decide (old.length.val ≤ i.val)))

def afterStore {n : Nat} {G : Schema n} {p : PrimTy}
    (old : Value G (.array (.prim p))) (base : Solidity.Storage.Loc) (store : Store) : Store :=
  Representation.write (symbolicPrefix store base old.length.val) base ClearDemands.zero

private theorem data_ne_base (base : Solidity.Storage.Loc) (j : Nat) : Solidity.Storage.Loc.data base j ≠ base := by
  intro same
  have depths := congrArg Solidity.Storage.Loc.depth same
  change base.depth+1 = base.depth at depths
  omega

/-- Selected PUBLIC postowner is DERIVED from OLD header/unvisited observations
and independent graph clear; no desired postrelation or old cleared-word0 premise.
The original PUBLIC lmax metadata interface is retained exactly. -/
theorem represented {n : Nat} {G : Schema n} {p : PrimTy}
    (old : Value G (.array (.prim p))) (indices : List Index) (base : Solidity.Storage.Loc) (store : Store)
    (before : Represented old (oldQueries old indices) base store) :
    Represented (recursiveClear old) (PrimitivePop.queries indices) base (afterStore old base store) := by
  have oldBounds : old.length.val ≤ lmax ∧ old.extent.val ≤ lmax := by
    have compatibility := (before (.length .nil) List.mem_cons_self).2.1
    cases old
    exact compatibility
  intro q member
  simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
  rcases member with rfl | ⟨i,inside,rfl⟩
  · refine ⟨True.intro,?_,?_⟩
    · cases old with
      | array extent length bound slots =>
        change 0 ≤ lmax ∧ extent.val ≤ lmax
        exact ⟨Nat.zero_le _,oldBounds.2⟩
    · intro word observed
      have cleared : (Query.length (.nil : TypeGraph.Path G (.array (.prim p)) (.array (.prim p)))).read (recursiveClear old) = some ClearDemands.zero := by cases old; rfl
      have equal : word = ClearDemands.zero := Option.some.inj (observed.symm.trans cleared)
      subst word
      exact Representation.write_same _ _ _
  · by_cases live : i.val < old.length.val
    · refine ⟨?_,True.intro,?_⟩
      · change i.val < lmax ∧ True
        exact ⟨by omega,True.intro⟩
      · intro word observed
        rw [element_read old i,if_pos live] at observed
        cases observed
        rw [PrimitivePop.element_location]
        unfold afterStore
        rw [Representation.write_other _ _ _ _ (data_ne_base base i.val),symbolic_data,if_pos live]
    · have oldMember : PrimitivePop.elementQuery (G := G) (p := p) i ∈ oldQueries old indices :=
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,List.mem_filter.mpr ⟨inside,by simp only [decide_eq_true_eq]; omega⟩,rfl⟩)
      have oldOwner := before _ oldMember
      refine ⟨oldOwner.1,True.intro,?_⟩
      intro word observed
      rw [element_read old i,if_neg live] at observed
      have oldRead := oldOwner.2.2 word observed
      rw [PrimitivePop.element_location] at oldRead ⊢
      unfold afterStore
      rw [Representation.write_other _ _ _ _ (data_ne_base base i.val),symbolic_data,if_neg live]
      exact oldRead


/-- The result is explicitly the INDEPENDENT published clear specification,
using the already checked operation-to-specification correspondence. -/
theorem represented_spec {n : Nat} {G : Schema n} {p : PrimTy}
    (old : Value G (.array (.prim p))) (indices : List Index) (base : Solidity.Storage.Loc) (store : Store)
    (before : Represented old (oldQueries old indices) base store) :
    Represented old.clear (PrimitivePop.queries indices) base (afterStore old base store) := by
  simpa only [recursiveClear_eq_clear] using represented old indices base store before

/-- ACTUAL structured target loop, CURRENT numeric-header algorithm, independent
clear specification, PUBLIC owner and selected numeric readbacks compose from
OLD evidence. All per-run generated access/selected-query coverage is explicit. -/
theorem complete {n N L R : Nat} {G : Schema n} {p : PrimTy}
    {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
    (run : FiniteRun N L R hash P locations)
    (old : Value G (.array (.prim p))) (indices : List Index) (base : Solidity.Storage.Loc)
    (baseFits : TargetOperations.KeysFit base) (store : Store) (numeric : WordStore)
    (target : Evm.Machine) (tail : List Evm.Word)
    (before : Represented old (oldQueries old indices) base store)
    (initial : Transport N hash locations store numeric)
    (covered : ∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, q.location base ∈ locations)
    (visitedCovered : ∀ j, j < old.length.val → Solidity.Storage.Loc.data base j ∈ locations)
    (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
    (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l)) :
    Evm.run TargetArrayClear.code { target with stack := .slot (TargetOperations.toSlot base baseFits) :: tail } =
      .ok (TargetArrayClear.afterClear target tail (TargetOperations.toSlot base baseFits)) 0 ∧
    Represented old.clear (PrimitivePop.queries indices) base (afterStore old base store) ∧
    Transport N hash locations (afterStore old base store) (execute N hash base numeric) ∧
    (∀ l (member : l ∈ locations), (TargetArrayClear.afterClear target tail (TargetOperations.toSlot base baseFits)).store.cells (TargetOperations.toSlot l (fitting l member)) =
      TargetOperations.encodeWord ((execute N hash base numeric) (l.word N hash))) ∧
    (∀ q ∈ PrimitivePop.queries (G := G) (p := p) indices, ∀ word, q.read old.clear = some word →
      (execute N hash base numeric) ((q.location base).word N hash) = word) := by
  have headerOwner : Represented old [.length .nil] base store := by
    intro q member; have same := List.mem_singleton.mp member; subst q
    exact before _ List.mem_cons_self
  have headerCovered : base ∈ locations := covered (.length .nil) List.mem_cons_self
  have numericHeader := LifecycleNumeric.array_header_numeric old base store numeric hash locations headerOwner initial headerCovered
  have numericLength := LifecycleNumeric.headerLength_known hash base numeric old.length numericHeader
  have targetLength := TargetHeaderPush.source_header old base baseFits store target headerOwner (targetInitial base headerCovered)
  have transportedPrefix := prefix_numeric run store numeric base initial old.length.val visitedCovered
  have transportedFinal := transport_write run transportedPrefix base headerCovered ClearDemands.zero
  have transported : Transport N hash locations (afterStore old base store) (execute N hash base numeric) := by
    unfold execute
    rw [numericLength]
    exact transportedFinal
  have agreementPrefix := prefix_target store target base baseFits locations fitting targetInitial old.length.val
  have agreementFinal := TargetOperations.write_agreement locations fitting base baseFits ClearDemands.zero
    (symbolicPrefix store base old.length.val)
    { target with store := TargetArrayClear.clearPrefix target.store (TargetOperations.toSlot base baseFits) old.length.val } agreementPrefix
  have agreement : ∀ l (member : l ∈ locations),
      (TargetArrayClear.afterClear target tail (TargetOperations.toSlot base baseFits)).store.cells (TargetOperations.toSlot l (fitting l member)) =
        TargetOperations.encodeWord (afterStore old base store l) := by
    intro l member
    unfold TargetArrayClear.afterClear
    rw [targetLength]
    exact agreementFinal l member
  have owner := represented_spec old indices base store before
  refine ⟨TargetArrayClear.run_current target tail (TargetOperations.toSlot base baseFits),owner,transported,?_,?_⟩
  · intro l member
    exact (agreement l member).trans (congrArg TargetOperations.encodeWord (transported l member).symm)
  · intro q member word observed
    exact owner.numeric transported q member (covered q member) word observed


/-- Numeric frames concern actual generated physical accesses, including
unrepresented words, and retain explicit per-access address separation. -/
theorem numeric_prefix_outside (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (store : WordStore) (base : Solidity.Storage.Loc) (count address : Nat)
    (apart : ∀ j, j < count → address ≠ (Solidity.Storage.Loc.data base j).word N hash) :
    numericPrefix N hash store base count address = store address := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [numericPrefix,writeWord,if_neg (apart count (by omega))]
    exact ih (fun j inside => apart j (by omega))

theorem numeric_outside (N : Nat) (hash : Solidity.Storage.Pre → Nat)
    (store : WordStore) (base : Solidity.Storage.Loc) (address : Nat)
    (headerApart : address ≠ base.word N hash)
    (dataApart : ∀ j, j < LifecycleNumeric.headerLength N hash base store → address ≠ (Solidity.Storage.Loc.data base j).word N hash) :
    execute N hash base store address = store address := by
  rw [execute,writeWord,if_neg headerApart]
  exact numeric_prefix_outside N hash store base _ address dataApart


/-- info: 'Solidity.Backend.StorageOps.TargetClearRepresentation.element_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms element_read
/-- info: 'Solidity.Backend.StorageOps.TargetClearRepresentation.symbolic_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms symbolic_data
/-- info: 'Solidity.Backend.StorageOps.TargetClearRepresentation.symbolic_outside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms symbolic_outside
/-- info: 'Solidity.Backend.StorageOps.TargetClearRepresentation.prefix_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms prefix_target
/-- info: 'Solidity.Backend.StorageOps.TargetClearRepresentation.prefix_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms prefix_numeric
/-- info: 'Solidity.Backend.StorageOps.TargetClearRepresentation.represented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented
/-- info: 'Solidity.Backend.StorageOps.TargetClearRepresentation.represented_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented_spec
/-- info: 'Solidity.Backend.StorageOps.TargetClearRepresentation.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete
/-- info: 'Solidity.Backend.StorageOps.TargetClearRepresentation.numeric_prefix_outside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_prefix_outside
/-- info: 'Solidity.Backend.StorageOps.TargetClearRepresentation.numeric_outside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_outside

end Solidity.Backend.StorageOps.TargetClearRepresentation
