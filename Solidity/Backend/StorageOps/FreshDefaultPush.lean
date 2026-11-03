import Solidity.Backend.StorageOps.TargetDefaultInit
import Solidity.Backend.StorageOps.TargetFreshMapping

/-! Actual fresh outer push followed by schema-directed initialization at the
CORRECT typed element stride. New cells may be dirty: no untouched-history or
default/postowner premise. Captured typed target address remains explicit. -/
namespace Solidity.Backend.StorageOps.FreshDefaultPush
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- The original layout's element stride, not a one-word aggregate assumption. -/
theorem child_location {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
 (i : Index) (base : Solidity.Storage.Loc) :
 pathLoc (AggregatePopFrames.indexPath (G:=G) (E:=E) i) base=.data base (i.val*inlineSize G E) := by
 simp only [AggregatePopFrames.indexPath,pathLoc,stepLoc]

/-- Every typed default query is below the new child, so it cannot overwrite
its ancestor header. Derived symbolically; no global physical hash premise. -/
theorem root_separation {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
 (i : Index) (base : Solidity.Storage.Loc) (q : Query G E) :
 base ≠ q.location (pathLoc (AggregatePopFrames.indexPath (G:=G) (E:=E) i) base) := by
 have other := OperationDepth.indexed_ne_header q i base
 rw [Query.location_prefix] at other
 exact Ne.symm other

/-- Fresh graph allocation exposes exactly the PUBLISHED default. -/
theorem fresh_find {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
 (old result : Value G (.array E)) (fresh : old.extent.val=old.length.val)
 (pushed : operationPush old=some result) :
 result.find (AggregatePopFrames.indexPath (G:=G) (E:=E) old.length)=some (Value.dflt E) := by
 simp only [AggregatePopFrames.indexPath,Value.find,TypeGraph.Path.read]
 rw [operationPush_fresh old result fresh pushed]
 rfl

/-- Actual numeric code captures the CURRENT ORIGINAL header before pushing,
then initializes the correctly strided selected child. No graph value input. -/
noncomputable def execute {n : Nat} (G : Schema n) (E : TypeGraph.Ty n)
 (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc) (numeric : WordStore) : Option WordStore := do
 let index := LifecycleNumeric.headerLength N hash base numeric
 let middle ← LifecycleNumeric.pushHeader N hash base numeric
 pure (CopyDefaults.numericInit (N:=N) G E (.data base (index*inlineSize G E)) hash middle)

/-- Existing capacity failure is exact; initialization is total after push. -/
theorem execute_failure {n : Nat} (G : Schema n) (E : TypeGraph.Ty n)
 (N : Nat) (hash : Solidity.Storage.Pre → Nat) (base : Solidity.Storage.Loc) (numeric : WordStore) :
 execute G E N hash base numeric=none ↔ 2^256≤LifecycleNumeric.headerLength N hash base numeric+1 := by
 unfold execute LifecycleNumeric.pushHeader
 dsimp only
 by_cases room : LifecycleNumeric.headerLength N hash base numeric+1<2^256
 · rw [dif_pos room]
   constructor
   · intro impossible; cases impossible
   · intro impossible; omega
 · rw [dif_neg room]
   constructor
   · intro ignored; omega
   · intro ignored; rfl

/-- Whole captured operation: OLD root/header, run/Transport/agreement and
coverage derive the new ROOT prefix owner after actual header+initializer code.
No old readable new-child/default owner or untouched history is assumed. -/
theorem complete {n N L R : Nat} {G : Schema n} {E : TypeGraph.Ty n}
 (old result : Value G (.array E)) (fresh : old.extent.val=old.length.val)
 (pushed : operationPush old=some result) (permit : CopyPermit G E)
 (queries : List (Query G E)) (supported : ∀ q ∈ queries, q.supported)
 (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base)
 {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (captured : Store) (numeric : WordStore) (machine : Evm.Machine)
 (before : Represented old [.length .nil] base captured)
 (initial : Transport N hash locations captured numeric) (rootCovered : base ∈ locations)
 (covered : ∀ q ∈ CopyDefaults.demands G E ++ queries, q.location (pathLoc (AggregatePopFrames.indexPath (G:=G) (E:=E) old.length) base) ∈ locations)
 (coverage : old.length.val+1≤lmax)
 (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
 (agreement : ∀ l (member : l ∈ locations), machine.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (captured l)) :
 let pre := AggregatePopFrames.indexPath (G:=G) (E:=E) old.length
 let child := pathLoc pre base
 let childFits := TargetOperations.path_keysFit pre base fits
 let word := lengthWord result.length.val result.length.isLt
 let middleStore := Representation.write captured base word
 let middleNumeric := writeWord numeric (base.word N hash) word
 let middleTarget := {machine with store := Evm.WordStore.write machine.store (TargetOperations.toSlot base fits) (TargetOperations.encodeWord word).val}
 let afterStore := (CopyDefaults.updates G E child).foldl (fun store op => Representation.write store op.1 op.2) middleStore
 let afterNumeric := CopyDefaults.numericInit (N:=N) G E child hash middleNumeric
 let afterTarget := TargetDefaultInit.afterInit G E child childFits middleTarget
 execute G E N hash base numeric=some afterNumeric ∧
 Evm.run (TargetHeaderPush.code (TargetOperations.toSlot base fits) ++ TargetDefaultInit.code G E permit child childFits) machine=.ok afterTarget 0 ∧
 Represented result (.length .nil :: queries.map (Query.prefix pre)) base afterStore ∧
 Transport N hash locations afterStore afterNumeric ∧
 (∀ l (member : l ∈ locations), afterTarget.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (afterNumeric (l.word N hash))) := by
 let pre := AggregatePopFrames.indexPath (G:=G) (E:=E) old.length
 let child := pathLoc pre base
 let childFits := TargetOperations.path_keysFit pre base fits
 let word := lengthWord result.length.val result.length.isLt
 let middleStore := Representation.write captured base word
 let middleNumeric := writeWord numeric (base.word N hash) word
 let middleTarget : Evm.Machine := {machine with store := Evm.WordStore.write machine.store (TargetOperations.toSlot base fits) (TargetOperations.encodeWord word).val}
 have headers := operationPush_header old result pushed
 have rootWord := LifecycleNumeric.array_header_numeric old base captured numeric hash locations before initial rootCovered
 have indexKnown := LifecycleNumeric.headerLength_known hash base numeric old.length rootWord
 have room : old.length.val+1<2^256 := by have bound:=result.length.isLt; omega
 have numericOuter : LifecycleNumeric.pushHeader N hash base numeric=some middleNumeric := by
  rw [LifecycleNumeric.pushHeader_known hash base numeric old.length rootWord,dif_pos room]
  have same : lengthWord (old.length.val+1) room=word := by
   apply Subtype.ext; exact congrArg Int.ofNat headers.1.symm
  rw [same]
 have targetOuter := TargetFreshMapping.run_source_header old result pushed base fits captured machine before (agreement base rootCovered)
 have midTransport : Transport N hash locations middleStore middleNumeric := transport_write run initial base rootCovered word
 have midAgreement := TargetOperations.write_agreement locations fitting base fits word captured machine agreement
 have initialized := TargetDefaultInit.complete G E permit queries supported child childFits run middleStore middleNumeric middleTarget midTransport covered fitting midAgreement
 have readback := fresh_find old result fresh pushed
 have prefixSupported : PathSupported pre := by
  change old.length.val<lmax ∧ True
  exact ⟨by omega,True.intro⟩
 have childOwner := Represented.prefix pre readback prefixSupported initialized.2.1
 have rootAfter :
   ((CopyDefaults.updates G E child).foldl (fun store op => Representation.write store op.1 op.2) middleStore) base=word := by
  simp only [CopyDefaults.updates,List.foldl_map]
  exact (ClearDemands.fold_outside (CopyDefaults.demands G E) child base middleStore
   (fun q _member => root_separation old.length base q)).trans (write_same _ _ _)
 have rootOwner : Represented result [.length .nil] base
   ((CopyDefaults.updates G E child).foldl (fun store op => Representation.write store op.1 op.2) middleStore) := by
  intro q member
  have same:=List.mem_singleton.mp member; subst q
  refine ⟨True.intro,?_,?_⟩
  · have bounds : result.length.val≤lmax ∧ result.extent.val≤lmax := by
     rw [headers.1,headers.2,fresh]
     constructor <;> omega
    cases result
    exact bounds
  · intro value observed
    have seen : word=value := by cases result; exact Option.some.inj observed
    rw [← seen]
    exact rootAfter
 refine ⟨?_,?_,?_,initialized.2.2.1,initialized.2.2.2.1⟩
 · unfold execute
   rw [indexKnown,numericOuter]
   change some (CopyDefaults.numericInit (N:=N) G E (.data base (old.length.val*inlineSize G E)) hash middleNumeric)=_
   rw [← child_location (G:=G) (E:=E) old.length base]
 · rw [Evm.run_append_ok targetOuter]
   exact initialized.1
 · intro q member
   rcases List.mem_cons.mp member with same | inside
   · subst q; exact rootOwner _ List.mem_cons_self
   · exact childOwner q inside

/-- info: 'Solidity.Backend.StorageOps.FreshDefaultPush.child_location' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms child_location
/-- info: 'Solidity.Backend.StorageOps.FreshDefaultPush.root_separation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms root_separation
/-- info: 'Solidity.Backend.StorageOps.FreshDefaultPush.fresh_find' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fresh_find
/-- info: 'Solidity.Backend.StorageOps.FreshDefaultPush.execute_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms execute_failure
/-- info: 'Solidity.Backend.StorageOps.FreshDefaultPush.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.FreshDefaultPush
