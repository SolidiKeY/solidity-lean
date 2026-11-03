import Solidity.Backend.StorageOps.TargetNestedPop
import Solidity.Backend.StorageOps.TargetClearRepresentation
import Solidity.Backend.StorageOps.AggregatePop

/-! Actual current-header numeric nested primitive-array pop and composition
with existing PUBLIC child representation, independent graph pop and target code.
No source/default/shape oracle is an input to executable numeric traversal. -/
namespace Solidity.Backend.StorageOps.NestedPopTransport
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def execute (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc) (numeric : WordStore) : Option WordStore :=
 let length := LifecycleNumeric.headerLength N hash base numeric
 if live : 0 < length then
   let word := lengthWord (length-1) (by
     have bound := (numeric (base.word N hash)).property
     simp only [PrimTy.inRange,decide_eq_true_eq] at bound
     dsimp only [length,LifecycleNumeric.headerLength]
     omega)
   some (TargetClearRepresentation.execute N hash (.data base (length-1)) (writeWord numeric (base.word N hash) word))
 else none

def childValue {n : Nat} {G : Schema n} {p : PrimTy}
 (old : Value G (.array (.array (.prim p)))) : Value G (.array (.prim p)) :=
 (AggregatePop.lastSlot old).getD (Value.dflt (.array (.prim p)))

/-- Independent pop's retained last-child read is exactly independent clear,
including absent-slot defaults; existing clear_dflt supplies default provenance. -/
theorem popped_child {n : Nat} {G : Schema n} {p : PrimTy}
 (old result : Value G (.array (.array (.prim p)))) (popped : recursivePop old = some result) :
 result.find (AggregatePop.lastPath old) = some (childValue old).clear := by
 rw [AggregatePop.popped_last_read old result popped]
 unfold childValue
 cases AggregatePop.lastSlot old with
 | absent =>
   simp only [recursiveClearSlot,Slot.getD]
   rw [Value.clear_dflt]
 | present value =>
   simp only [recursiveClearSlot,Slot.getD,recursiveClear_eq_clear]

private theorem child_ne_root (base : Solidity.Storage.Loc) (i : Nat) : Solidity.Storage.Loc.data base i ≠ base := by
 intro same
 have depths := congrArg Solidity.Storage.Loc.depth same
 change base.depth+1=base.depth at depths
 omega
private theorem grand_ne_root (base : Solidity.Storage.Loc) (i j : Nat) : Solidity.Storage.Loc.data (.data base i) j ≠ base := by
 intro same
 have depths := congrArg Solidity.Storage.Loc.depth same
 change base.depth+1+1=base.depth at depths
 omega

/-- The concrete outer-header write frames OLD primitive-child query outcomes.
This operation adapter applies the EXISTING owner, without new representation. -/
theorem header_frame {n : Nat} {G : Schema n} {p : PrimTy}
 (value : Value G (.array (.prim p))) (indices : List Index) (base : Solidity.Storage.Loc) (i : Nat)
 (store : Store) (word : Semantics.Word)
 (before : Represented value (TargetClearRepresentation.oldQueries value indices) (.data base i) store) :
 Represented value (TargetClearRepresentation.oldQueries value indices) (.data base i) (Representation.write store base word) := by
 intro query member
 obtain ⟨ok,compatible,observed⟩ := before query member
 refine ⟨ok,compatible,?_⟩
 intro result found
 have apart : query.location (.data base i) ≠ base := by
   simp only [TargetClearRepresentation.oldQueries,PrimitivePop.queries,List.mem_cons,List.mem_map] at member
   rcases member with rfl | ⟨j,_,rfl⟩
   · exact child_ne_root base i
   · rw [PrimitivePop.element_location]
     exact grand_ne_root base i j.val
 rw [Representation.write_other _ _ _ _ apart]
 exact observed result found

/-- Original numeric root/header agreement determines BOTH failure outcomes.
The child header is read only after successful current outer-header decrement. -/
theorem failure_matches {n N : Nat} {G : Schema n} {p : PrimTy}
 (old : Value G (.array (.array (.prim p)))) (base : Solidity.Storage.Loc)
 (store : Store) (numeric : WordStore) (hash : Solidity.Storage.Pre → Nat) (locations : List Solidity.Storage.Loc)
 (before : Represented old [.length .nil] base store)
 (initial : Transport N hash locations store numeric) (covered : base ∈ locations) :
 execute N hash base numeric = none ↔ recursivePop old = none := by
 have header := LifecycleNumeric.array_header_numeric old base store numeric hash locations before initial covered
 have length := LifecycleNumeric.headerLength_known hash base numeric old.length header
 simp only [execute,length]
 rw [recursivePop_failure]
 by_cases live : 0 < old.length.val
 · rw [dif_pos live]
   constructor
   · intro impossible; cases impossible
   · intro zero; omega
 · rw [dif_neg live]
   exact ⟨fun _ => by omega,fun _ => rfl⟩

/-- Successful operation composition: every middle owner/Transport/target cell
is DERIVED from OLD root+child evidence, not assumed as a preservation premise. -/
theorem complete {n N L R : Nat} {G : Schema n} {p : PrimTy}
 {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations)
 (old result : Value G (.array (.array (.prim p)))) (popped : recursivePop old = some result)
 (indices : List Index) (base : Solidity.Storage.Loc) (baseFits : TargetOperations.KeysFit base)
 (store : Store) (numeric : WordStore) (target : Evm.Machine)
 (rootBefore : Represented old [.length .nil] base store)
 (childBefore : Represented (childValue old) (TargetClearRepresentation.oldQueries (childValue old) indices)
   (.data base (old.length.val-1)) store)
 (initial : Transport N hash locations store numeric) (rootCovered : base ∈ locations)
 (childCovered : ∀ query ∈ PrimitivePop.queries (G := G) (p := p) indices,
   query.location (.data base (old.length.val-1)) ∈ locations)
 (visited : ∀ j, j < (childValue old).length.val → Solidity.Storage.Loc.data (.data base (old.length.val-1)) j ∈ locations)
 (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
 (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (store l)) :
 let word := lengthWord result.length.val result.length.isLt
 let childBase := Solidity.Storage.Loc.data base (old.length.val-1)
 let middleStore := Representation.write store base word
 let finalStore := TargetClearRepresentation.afterStore (childValue old) childBase middleStore
 let finalNumeric := TargetClearRepresentation.execute N hash childBase (writeWord numeric (base.word N hash) word)
 let finalTarget := TargetNestedPop.after target (TargetOperations.toSlot base baseFits)
 execute N hash base numeric = some finalNumeric ∧
 Evm.run (TargetNestedPop.code (TargetOperations.toSlot base baseFits)) target = .ok finalTarget 0 ∧
 Represented (childValue old).clear (PrimitivePop.queries indices) childBase finalStore ∧
 Represented result (AggregatePop.queries old (PrimitivePop.queries (G := G) (p := p) indices)) base finalStore ∧
 Transport N hash locations finalStore finalNumeric ∧
 (∀ l (member : l ∈ locations), finalTarget.store.cells (TargetOperations.toSlot l (fitting l member)) = TargetOperations.encodeWord (finalNumeric (l.word N hash))) ∧
 (∀ query ∈ PrimitivePop.queries (G := G) (p := p) indices, ∀ word, query.read (childValue old).clear = some word →
   finalNumeric ((query.location childBase).word N hash) = word) := by
 dsimp only
 have popHeaders := recursivePop_header old result popped
 have live : 0 < old.length.val := by have bound := result.length.isLt; omega
 have lengthResult : old.length.val-1 = result.length.val := by omega
 have numericHeader := LifecycleNumeric.array_header_numeric old base store numeric hash locations rootBefore initial rootCovered
 have numericLength := LifecycleNumeric.headerLength_known hash base numeric old.length numericHeader
 have targetHeader := TargetHeaderPush.source_header old base baseFits store target rootBefore (targetInitial base rootCovered)
 let word := lengthWord result.length.val result.length.isLt
 let middleStore := Representation.write store base word
 let middleNumeric := writeWord numeric (base.word N hash) word
 let middleTarget : Evm.Machine := {target with store := Evm.WordStore.write target.store (TargetOperations.toSlot base baseFits) (TargetOperations.encodeWord word).val}
 have middleOwner := header_frame (childValue old) indices base (old.length.val-1) store word childBefore
 have middleTransport := transport_write run initial base rootCovered word
 have middleAgreement := TargetOperations.write_agreement locations fitting base baseFits word store target targetInitial
 have certificate := TargetClearRepresentation.complete run (childValue old) indices (.data base (old.length.val-1)) baseFits
   middleStore middleNumeric middleTarget target.stack middleOwner middleTransport childCovered visited fitting middleAgreement
 have targetResult : TargetNestedPop.after target (TargetOperations.toSlot base baseFits) =
   TargetArrayClear.afterClear middleTarget target.stack (TargetOperations.toSlot (.data base (old.length.val-1)) baseFits) := by
   unfold TargetNestedPop.after TargetNestedPop.decremented TargetNestedPop.selected
   rw [targetHeader,lengthResult]
   rfl
 have found := popped_child old result popped
 have bounds : old.length.val ≤ lmax ∧ old.extent.val ≤ lmax := by
   have compatible := (rootBefore (.length .nil) List.mem_cons_self).2.1
   cases old
   exact compatible
 have supported : PathSupported (AggregatePop.lastPath old) := by
   change old.length.val-1 < lmax ∧ True
   exact ⟨by omega,True.intro⟩
 have location : pathLoc (AggregatePop.lastPath old) base = Solidity.Storage.Loc.data base (old.length.val-1) := by
   change AggregatePop.childBase old base = _
   rw [AggregatePop.child_location,inlineSize_array,Nat.mul_one]
 have resultOwner := Represented.prefix (AggregatePop.lastPath old) found supported
   (by rw [location]; exact certificate.2.1)
 have resultBounds : result.length.val ≤ lmax ∧ result.extent.val ≤ lmax := by
   have sameExtent := congrArg Fin.val popHeaders.2
   exact ⟨by omega,by omega⟩
 have rootRead : TargetClearRepresentation.afterStore (childValue old) (.data base (old.length.val-1)) middleStore base = word := by
   unfold TargetClearRepresentation.afterStore
   rw [Representation.write_other _ _ _ _ (Ne.symm (child_ne_root base _)),
     TargetClearRepresentation.symbolic_outside middleStore (.data base (old.length.val-1)) base (childValue old).length.val
       (by intro j _; exact Ne.symm (grand_ne_root base _ j))]
   exact Representation.write_same _ _ _
 have rootOwner : Represented result [.length .nil] base
     (TargetClearRepresentation.afterStore (childValue old) (.data base (old.length.val-1)) middleStore) := by
   intro query member
   have same := List.mem_singleton.mp member
   subst query
   refine ⟨True.intro,?_,?_⟩
   · cases result
     exact resultBounds
   · intro observedWord foundWord
     have observedHeader : (Query.length (.nil : TypeGraph.Path G (.array (.array (.prim p))) (.array (.array (.prim p))))).read result = some word := by
       cases result
       rfl
     rw [observedHeader] at foundWord
     have equal := Option.some.inj foundWord
     rw [← equal]
     exact rootRead
 have combinedOwner : Represented result (AggregatePop.queries old (PrimitivePop.queries indices)) base
     (TargetClearRepresentation.afterStore (childValue old) (.data base (old.length.val-1)) middleStore) := by
   intro query member
   simp only [AggregatePop.queries,List.mem_cons] at member
   rcases member with rfl | member
   · exact rootOwner _ List.mem_cons_self
   · exact resultOwner query member
 refine ⟨?_,?_,certificate.2.1,combinedOwner,certificate.2.2.1,?_,certificate.2.2.2.2⟩
 · simp only [execute,numericLength,dif_pos live,lengthResult]
 · rw [TargetNestedPop.run_current,targetHeader,if_neg (by omega)]
 · rw [targetResult]
   exact certificate.2.2.2.1

/-- info: 'Solidity.Backend.StorageOps.NestedPopTransport.popped_child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms popped_child
/-- info: 'Solidity.Backend.StorageOps.NestedPopTransport.header_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms header_frame
/-- info: 'Solidity.Backend.StorageOps.NestedPopTransport.failure_matches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms failure_matches
/-- info: 'Solidity.Backend.StorageOps.NestedPopTransport.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.NestedPopTransport
