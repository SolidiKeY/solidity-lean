import Solidity.Backend.StorageOps.NestedPopTransport
import Solidity.Backend.StorageOps.AggregatePopFrames

/-! Other-context owner transport through the ACTUAL current-header nested pop.
Existing typed query groups and intrinsic read/compatibility frames are reused;
no alternate representation, source evaluator, path/value/state or compiler IR. -/
namespace Solidity.Backend.StorageOps.NestedPopFrames
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open NestedPopTransport

/-- Apply the EXISTING owner to this operation's concrete root-header write and
selected-child header/live-prefix clear; exact symbolic exclusions are explicit. -/
theorem store_frame {n m : Nat} {G : Schema n} {H : Schema m} {p : PrimTy} {A : TypeGraph.Ty m}
 (cleared : Value G (.array (.prim p))) (value : Value H A) (queries : List (Query H A))
 (base observerBase : Solidity.Storage.Loc) (i : Nat) (word : Semantics.Word) (store : Store)
 (before : Represented value queries observerBase store)
 (outside : ∀ query ∈ queries, query.location observerBase ≠ base ∧
   query.location observerBase ≠ .data base i ∧
   ∀ j, j < cleared.length.val → query.location observerBase ≠ .data (.data base i) j) :
 Represented value queries observerBase (TargetClearRepresentation.afterStore cleared (.data base i) (Representation.write store base word)) := by
 intro query member
 obtain ⟨ok,compatible,observed⟩ := before query member
 refine ⟨ok,compatible,?_⟩
 intro result found
 unfold TargetClearRepresentation.afterStore
 rw [Representation.write_other _ _ _ _ (outside query member).2.1,
   TargetClearRepresentation.symbolic_outside _ (.data base i) (query.location observerBase) cleared.length.val (outside query member).2.2,
   Representation.write_other _ _ _ _ (outside query member).1]
 exact observed result found

/-- Independent source pop frames and generated actual-store writes derive the
popped ROOT context owner. Logical other-index and symbolic nonalias stay distinct. -/
theorem context_owner {n : Nat} {G : Schema n} {p : PrimTy}
 (old result : Value G (.array (.array (.prim p)))) (popped : recursivePop old = some result)
 (groups : List (Index × List (Query G (.array (.prim p)))) ) (base : Solidity.Storage.Loc) (store : Store)
 (before : Represented old (AggregatePopFrames.contexts groups) base store)
 (other : ∀ group ∈ groups, group.1.val ≠ old.length.val-1)
 (outside : ∀ query ∈ AggregatePopFrames.contexts groups,
   query.location base ≠ base ∧ query.location base ≠ .data base (old.length.val-1) ∧
   ∀ j, j < (childValue old).length.val → query.location base ≠ .data (.data base (old.length.val-1)) j) :
 Represented result (AggregatePopFrames.contexts groups) base
   (TargetClearRepresentation.afterStore (childValue old) (.data base (old.length.val-1))
     (Representation.write store base (lengthWord result.length.val result.length.isLt))) := by
 have framed := store_frame (childValue old) old (AggregatePopFrames.contexts groups) base base (old.length.val-1)
   (lengthWord result.length.val result.length.isLt) store before outside
 intro query member
 obtain ⟨group,groupMember,queryMember⟩ := List.mem_flatMap.mp member
 obtain ⟨child,childMember,same⟩ := List.mem_map.mp queryMember
 subst query
 have prior := framed _ member
 refine ⟨prior.1,?_,?_⟩
 · rw [AggregatePopFrames.compatible_other old result popped group.1 (other group groupMember) child]
   exact prior.2.1
 · intro word observed
   apply prior.2.2 word
   rwa [AggregatePopFrames.read_other old result popped group.1 (other group groupMember) child] at observed

theorem complete {n N L R : Nat} {G : Schema n} {p : PrimTy}
 {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations)
 (old result : Value G (.array (.array (.prim p)))) (popped : recursivePop old = some result)
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
 let word := lengthWord result.length.val result.length.isLt
 let childBase := Solidity.Storage.Loc.data base (old.length.val-1)
 let middleStore := Representation.write store base word
 let finalStore := TargetClearRepresentation.afterStore (childValue old) childBase middleStore
 let finalNumeric := TargetClearRepresentation.execute N hash childBase (writeWord numeric (base.word N hash) word)
 let finalTarget := TargetNestedPop.after target (TargetOperations.toSlot base baseFits)
 (execute N hash base numeric = some finalNumeric ∧
 Evm.run (TargetNestedPop.code (TargetOperations.toSlot base baseFits)) target = .ok finalTarget 0 ∧
 Represented (childValue old).clear (PrimitivePop.queries indices) childBase finalStore ∧
 Represented result (AggregatePop.queries old (PrimitivePop.queries (G := G) (p := p) indices)) base finalStore ∧
 Transport N hash locations finalStore finalNumeric ∧
 (∀ l (member : l ∈ locations), finalTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (finalNumeric (l.word N hash))) ∧
 (∀ query ∈ PrimitivePop.queries (G := G) (p := p) indices, ∀ word, query.read (childValue old).clear = some word →
   finalNumeric ((query.location childBase).word N hash) = word)) ∧
 Represented result (AggregatePopFrames.contexts groups) base finalStore ∧
 (∀ query ∈ AggregatePopFrames.contexts groups, ∀ word, query.read result = some word →
   finalNumeric ((query.location base).word N hash) = word) := by
 dsimp only
 have certificate := NestedPopTransport.complete run old result popped indices base baseFits store numeric target
   rootBefore childBefore initial rootCovered childCovered visited fitting targetInitial
 have owner := context_owner old result popped groups base store contextBefore other outside
 refine ⟨certificate,owner,?_⟩
 intro query member word observed
 exact owner.numeric certificate.2.2.2.2.1 query member (contextCovered query member) word observed

/-- info: 'Solidity.Backend.StorageOps.NestedPopFrames.store_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms store_frame
/-- info: 'Solidity.Backend.StorageOps.NestedPopFrames.context_owner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms context_owner
/-- info: 'Solidity.Backend.StorageOps.NestedPopFrames.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.NestedPopFrames
