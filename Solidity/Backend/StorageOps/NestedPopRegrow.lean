import Solidity.Backend.StorageOps.NestedPopFrames
import Solidity.Backend.StorageOps.PopPush
import Solidity.Backend.StorageOps.TargetHeaderPush

/-! Actual header-driven nested pop followed by RETAINED header regrowth.
Existing intrinsic pop/push and PUBLIC represented stores remain independent
specifications. No fresh allocation/default/generation/world claim is made. -/
namespace Solidity.Backend.StorageOps.NestedPopRegrow
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open NestedPopTransport

def execute (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc) (numeric : WordStore) : Option WordStore := do
 let middle ← NestedPopTransport.execute N hash base numeric
 LifecycleNumeric.pushHeader N hash base middle

def code (slot : Evm.Slot) : List Evm.Instr := TargetNestedPop.code slot ++ TargetHeaderPush.code slot

def allGroups {n : Nat} {G : Schema n} {p : PrimTy}
 (old : Value G (.array (.array (.prim p)))) (indices : List Index)
 (groups : List (Index × List (Query G (.array (.prim p))))) : List (Index × List (Query G (.array (.prim p)))) :=
 (AggregatePop.lastIndex old,PrimitivePop.queries indices) :: groups

/-- Pop frees capacity under the ORIGINAL full uint256 bound. No new legacy
metadata/admission cap is needed to obtain the actual intrinsic push witness. -/
theorem push_exists {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
 (old middle : Value G (.array E)) (popped : recursivePop old = some middle) :
 ∃ result, operationPush middle = some result := by
 have headers := recursivePop_header old middle popped
 have bound := old.length.isLt
 cases performed : operationPush middle with
 | none =>
   have full := (operationPush_failure middle).mp performed
   omega
 | some result => exact ⟨result,rfl⟩

/-- Compose DERIVED selected and context owners using existing typed groups. -/
theorem collected_owner {n : Nat} {G : Schema n} {p : PrimTy}
 (old middle : Value G (.array (.array (.prim p)))) (indices : List Index)
 (groups : List (Index × List (Query G (.array (.prim p))))) (base : Solidity.Storage.Loc) (store : Store)
 (selected : Represented middle (AggregatePop.queries old (PrimitivePop.queries indices)) base store)
 (context : Represented middle (AggregatePopFrames.contexts groups) base store) :
 Represented middle (RetainedPush.requested (allGroups old indices groups)) base store := by
 intro query member
 change query ∈ .length .nil :: ((PrimitivePop.queries indices).map (Query.prefix (AggregatePop.lastPath old)) ++ AggregatePopFrames.contexts groups) at member
 rcases List.mem_cons.mp member with same | rest
 · subst query
   exact selected _ List.mem_cons_self
 · rcases List.mem_append.mp rest with last | other
   · exact selected query (List.mem_cons_of_mem _ last)
   · exact context query other

private theorem collected_covered {n : Nat} {G : Schema n} {p : PrimTy}
 (old : Value G (.array (.array (.prim p)))) (indices : List Index)
 (groups : List (Index × List (Query G (.array (.prim p))))) (base : Solidity.Storage.Loc) (locations : List Solidity.Storage.Loc)
 (root : base ∈ locations)
 (selected : ∀ query ∈ PrimitivePop.queries (G := G) (p := p) indices, query.location (.data base (old.length.val-1)) ∈ locations)
 (context : ∀ query ∈ AggregatePopFrames.contexts groups, query.location base ∈ locations) :
 ∀ query ∈ RetainedPush.requested (allGroups old indices groups), query.location base ∈ locations := by
 intro query member
 change query ∈ .length .nil :: ((PrimitivePop.queries indices).map (Query.prefix (AggregatePop.lastPath old)) ++ AggregatePopFrames.contexts groups) at member
 rcases List.mem_cons.mp member with same | rest
 · subst query
   exact root
 · rcases List.mem_append.mp rest with last | other
   · obtain ⟨child,inside,rfl⟩ := List.mem_map.mp last
     rw [Query.location_prefix]
     have location : pathLoc (AggregatePop.lastPath old) base = Solidity.Storage.Loc.data base (old.length.val-1) := by
       change AggregatePop.childBase old base = _
       rw [AggregatePop.child_location,inlineSize_array,Nat.mul_one]
     rw [location]
     exact selected child inside
   · exact context query other

/-- Empty target pop halts before header regrowth. This is an execution result,
not an automatically restored world/state relation. -/
theorem run_empty (slot : Evm.Slot) (target : Evm.Machine) (empty : target.store slot = 0) :
 Evm.run (code slot) target = .revert := by
 unfold code
 apply Evm.run_append_revert
 rw [TargetNestedPop.run_current,if_pos empty]

theorem complete {n N L R : Nat} {G : Schema n} {p : PrimTy}
 {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations)
 (old middle result : Value G (.array (.array (.prim p)))) (popped : recursivePop old = some middle)
 (pushed : operationPush middle = some result)
 (indices : List Index) (groups : List (Index × List (Query G (.array (.prim p))))) (base : Solidity.Storage.Loc) (baseFits : TargetOperations.KeysFit base)
 (store : Store) (numeric : WordStore) (target : Evm.Machine)
 (rootBefore : Represented old [.length .nil] base store)
 (childBefore : Represented (childValue old) (TargetClearRepresentation.oldQueries (childValue old) indices)
   (.data base (old.length.val-1)) store)
 (initial : Transport N hash locations store numeric) (rootCovered : base ∈ locations)
 (childCovered : ∀ query ∈ PrimitivePop.queries (G := G) (p := p) indices,
   query.location (.data base (old.length.val-1)) ∈ locations)
 (visited : ∀ j, j < (childValue old).length.val → Solidity.Storage.Loc.data (.data base (old.length.val-1)) j ∈ locations)
 (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
 (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l))
 (contextBefore : Represented old (AggregatePopFrames.contexts groups) base store)
 (other : ∀ group ∈ groups, group.1.val ≠ old.length.val-1)
 (outside : ∀ query ∈ AggregatePopFrames.contexts groups,
   query.location base ≠ base ∧ query.location base ≠ .data base (old.length.val-1) ∧
   ∀ j, j < (childValue old).length.val → query.location base ≠ .data (.data base (old.length.val-1)) j)
 (contextCovered : ∀ query ∈ AggregatePopFrames.contexts groups, query.location base ∈ locations) :
 let popWord := lengthWord middle.length.val middle.length.isLt
 let childBase := Solidity.Storage.Loc.data base (old.length.val-1)
 let popStore := TargetClearRepresentation.afterStore (childValue old) childBase (Representation.write store base popWord)
 let growWord := lengthWord result.length.val result.length.isLt
 let finalStore := Representation.write popStore base growWord
 let popTarget := TargetNestedPop.after target (TargetOperations.toSlot base baseFits)
 let finalTarget := {popTarget with store := Evm.WordStore.write popTarget.store (TargetOperations.toSlot base baseFits) (TargetOperations.encodeWord growWord).val}
 ∃ finalNumeric, execute N hash base numeric = some finalNumeric ∧
 Evm.run (code (TargetOperations.toSlot base baseFits)) target = .ok finalTarget 0 ∧
 Represented result (RetainedPush.requested (allGroups old indices groups)) base finalStore ∧
 Transport N hash locations finalStore finalNumeric ∧
 (∀ l (member : l ∈ locations), finalTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (finalNumeric (l.word N hash))) ∧
 (∀ query ∈ RetainedPush.requested (allGroups old indices groups), ∀ word, query.read result = some word → finalNumeric ((query.location base).word N hash) = word) ∧
 result.length.val = old.length.val ∧ result.extent = old.extent := by
 dsimp only
 have first := NestedPopFrames.complete run old middle popped indices groups base baseFits store numeric target
   rootBefore childBefore initial rootCovered childCovered visited fitting targetInitial contextBefore other outside contextCovered
 have owner := collected_owner old middle indices groups base _ first.1.2.2.2.1 first.2.1
 have agreement : ∀ l (member : l ∈ locations),
   (TargetNestedPop.after target (TargetOperations.toSlot base baseFits)).store.cells (TargetOperations.toSlot l (fitting l member)) =
     TargetOperations.encodeWord (TargetClearRepresentation.afterStore (childValue old) (.data base (old.length.val-1))
       (Representation.write store base (lengthWord middle.length.val middle.length.isLt)) l) := by
   intro l member
   exact (first.1.2.2.2.2.2.1 l member).trans (congrArg TargetOperations.encodeWord (first.1.2.2.2.2.1 l member))
 have covered := collected_covered old indices groups base locations rootCovered childCovered contextCovered
 obtain ⟨final,performed,executed,postOwner,transported,postAgreement⟩ :=
   TargetHeaderPush.numeric_retained middle result pushed rfl (PopPush.retained old middle popped)
     (allGroups old indices groups) base baseFits _ (TargetNestedPop.after target (TargetOperations.toSlot base baseFits)) _
     run fitting owner first.1.2.2.2.2.1 agreement covered
 have headers := PopPush.headers old middle result popped pushed
 refine ⟨final,?_,?_,postOwner,transported,postAgreement,?_,headers.1,headers.2⟩
 · simp only [execute,first.1.1]
   exact performed
 · unfold code
   rw [Evm.run_append_ok first.1.2.1]
   exact executed
 · intro query member word observed
   exact postOwner.numeric transported query member (covered query member) word observed

/-- info: 'Solidity.Backend.StorageOps.NestedPopRegrow.push_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms push_exists
/-- info: 'Solidity.Backend.StorageOps.NestedPopRegrow.collected_owner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms collected_owner
/-- info: 'Solidity.Backend.StorageOps.NestedPopRegrow.run_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_empty
/-- info: 'Solidity.Backend.StorageOps.NestedPopRegrow.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.NestedPopRegrow
