import Solidity.Backend.StorageOps.TargetFreshMapping
import Solidity.Backend.StorageOps.TargetPrimitivePush
import Solidity.Backend.StorageOps.NestedRetainedCopy

/-! Fresh outer-array allocation followed by an ACTUAL push into its new child.
Default header provenance derives from original zero-origin history; failed old
reads never imply zero raw storage. Captured typed target slots stay explicit. -/
namespace Solidity.Backend.StorageOps.FreshArrayHistory
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- The actual newly allocated aggregate child is the published array default. -/
theorem fresh_find {n : Nat} {G : Schema n} {p : PrimTy}
 (old middle : Value G (.array (.array (.prim p))))
 (fresh : old.extent.val=old.length.val) (pushed : operationPush old=some middle) :
 middle.find (NestedCopyObservations.childPath (G:=G) (p:=p) old.length)=some (Value.dflt (.array (.prim p))) := by
 simp only [NestedCopyObservations.childPath,Value.find,TypeGraph.Path.read]
 rw [operationPush_fresh old middle fresh pushed]
 rfl

/-- Fresh inner push is TOTAL from actual allocation; no desired successful
middle operation is an uninhabited assumption in the composition certificate. -/
theorem inner_total {n : Nat} {G : Schema n} {p : PrimTy}
 (old middle : Value G (.array (.array (.prim p))))
 (fresh : old.extent.val=old.length.val) (pushed : operationPush old=some middle) :
 ∃ result, pushAt middle (NestedCopyObservations.childPath old.length)=some result := by
 have found := fresh_find old middle fresh pushed
 cases effect : operationPush (Value.dflt (G:=G) (.array (.prim p))) with
 | none =>
   have bad := (operationPush_failure (Value.dflt (G:=G) (.array (.prim p)))).mp effect
   change 2^256≤(0:Nat)+1 at bad
   have enough : 1<2^256 := by decide
   omega
 | some child =>
   obtain ⟨result,saved⟩ := prefix_save_exists _ middle _ child found
   refine ⟨result,?_⟩
   simp only [pushAt,modifyAt,Option.bind_eq_bind,found,Option.bind_some,effect,saved]

/-- Actual nested modification keeps its ancestor's length AND retained extent. -/
theorem outer_header {n : Nat} {G : Schema n} {p : PrimTy}
 (middle result : Value G (.array (.array (.prim p)))) (i : Index)
 (inner : pushAt middle (NestedCopyObservations.childPath i)=some result) : result.head=middle.head := by
 obtain ⟨actual,child,found,changed,saved⟩ := modifyAt_success middle result _ operationPush inner
 exact element_save_header middle result i .nil child saved

/-- Default-child owner derives ONLY its header zero from original history.
All out-of-extent word reads remain None and impose no raw payload constraint. -/
theorem default_owner {n N L R : Nat} {G : Schema n} {p : PrimTy}
 {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations)
 (history : List (Solidity.Storage.Loc × Semantics.Word))
 (historyCovered : ∀ op ∈ history, op.1 ∈ locations)
 (base : Solidity.Storage.Loc) (i : Index) (word : Semantics.Word)
 (childCovered : Solidity.Storage.Loc.data base i.val ∈ locations)
 (untouched : ∀ op ∈ history, Solidity.Storage.Loc.data base i.val ≠ op.1)
 (indices : List Index) (supported : ∀ q ∈ PrimitivePop.queries (G:=G) (p:=p) indices, q.supported) :
 Represented (Value.dflt (G:=G) (.array (.prim p))) (PrimitivePop.queries indices) (.data base i.val)
  (write (FreshMappingHistory.symbolic history) base word) := by
 have historyTransport := FreshMappingHistory.history_transport run history historyCovered
 have numericZero := FreshMappingHistory.untouched_zero run history historyCovered (.data base i.val) childCovered untouched
 have symbolicZero : FreshMappingHistory.symbolic history (.data base i.val)=ClearDemands.zero :=
  (historyTransport _ childCovered).symm.trans numericZero
 have different : Solidity.Storage.Loc.data base i.val ≠ base := by
  intro same
  have depths:=congrArg Solidity.Storage.Loc.depth same
  change base.depth+1=base.depth at depths
  omega
 intro q member
 refine ⟨supported q member,?_,?_⟩
 · simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
   rcases member with rfl | ⟨j,_,rfl⟩
   · change (0:Nat)≤lmax ∧ (0:Nat)≤lmax
     constructor <;> omega
   · exact True.intro
 · intro value observed
   simp only [PrimitivePop.queries,List.mem_cons,List.mem_map] at member
   rcases member with rfl | ⟨j,_,rfl⟩
   · change some ClearDemands.zero=some value at observed
     cases observed
     exact (write_other _ _ _ _ different).trans symbolicZero
   · change none=some value at observed
     cases observed

/-- OLD root owner/history derive the middle child owner/Transport/target
agreement used by an actual second push. No desired middle/final owner premise.
Only the new header must be untouched; its raw grandchildren may be dirty. -/
theorem complete_numeric {n N L R : Nat} {G : Schema n} {p : PrimTy}
 {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations)
 (old middle result : Value G (.array (.array (.prim p))))
 (fresh : old.extent.val=old.length.val) (pushed : operationPush old=some middle)
 (inner : pushAt middle (NestedCopyObservations.childPath (G:=G) (p:=p) old.length)=some result)
 (indices : List Index) (base : Solidity.Storage.Loc) (fits : TargetOperations.KeysFit base)
 (target : Evm.Machine) (history : List (Solidity.Storage.Loc × Semantics.Word))
 (historyCovered : ∀ op ∈ history, op.1 ∈ locations)
 (rootCovered : base ∈ locations)
 (childCovered : Solidity.Storage.Loc.data base old.length.val ∈ locations)
 (elementCovered : Solidity.Storage.Loc.data (.data base old.length.val) 0 ∈ locations)
 (untouched : ∀ op ∈ history, Solidity.Storage.Loc.data base old.length.val ≠ op.1)
 (coverage : old.length.val+1≤lmax)
 (supported : ∀ q ∈ PrimitivePop.queries (G:=G) (p:=p) indices, q.supported)
 (before : Represented old [.length .nil] base (FreshMappingHistory.symbolic history))
 (fitting : ∀ l ∈ locations, TargetOperations.KeysFit l)
 (targetInitial : ∀ l (member : l ∈ locations), target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (FreshMappingHistory.symbolic history l)) :
 let outerWord := lengthWord middle.length.val middle.length.isLt
 let middleStore := write (FreshMappingHistory.symbolic history) base outerWord
 let middleTarget := {target with store := Evm.WordStore.write target.store (TargetOperations.toSlot base fits) (TargetOperations.encodeWord outerWord).val}
 let childLoc := Solidity.Storage.Loc.data base old.length.val
 ∃ child firstNumeric finalNumeric,
 let finalWord := lengthWord child.length.val child.length.isLt
 let finalStore := write (write middleStore (.data childLoc 0) ClearDemands.zero) childLoc finalWord
 let finalTarget := {middleTarget with store := Evm.WordStore.write (Evm.WordStore.write middleTarget.store (TargetOperations.toSlot childLoc fits) (TargetOperations.encodeWord finalWord).val) (TargetOperations.toSlot (.data childLoc 0) fits) 0}
 result.find (NestedCopyObservations.childPath (G:=G) (p:=p) old.length)=some child ∧
 LifecycleNumeric.pushHeader N hash base (FreshMappingHistory.numeric N hash history)=some firstNumeric ∧
 LifecycleNumeric.pushPrimitive N hash childLoc firstNumeric=some finalNumeric ∧
 Evm.run (TargetHeaderPush.code (TargetOperations.toSlot base fits) ++ TargetPrimitivePush.code (TargetOperations.toSlot childLoc fits)) target=.ok finalTarget 0 ∧
 Represented result ((PrimitivePop.queries indices).map (Query.prefix (NestedCopyObservations.childPath (G:=G) (p:=p) old.length))) base finalStore ∧
 Transport N hash locations finalStore finalNumeric ∧
 (∀ l (member : l ∈ locations), finalTarget.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (finalNumeric (l.word N hash))) := by
 let outerWord := lengthWord middle.length.val middle.length.isLt
 let middleStore := write (FreshMappingHistory.symbolic history) base outerWord
 let firstNumeric := writeWord (FreshMappingHistory.numeric N hash history) (base.word N hash) outerWord
 let middleTarget : Evm.Machine := {target with store := Evm.WordStore.write target.store (TargetOperations.toSlot base fits) (TargetOperations.encodeWord outerWord).val}
 have initial := FreshMappingHistory.history_transport run history historyCovered
 have headers := operationPush_header old middle pushed
 have rootWord := LifecycleNumeric.array_header_numeric old base (FreshMappingHistory.symbolic history) (FreshMappingHistory.numeric N hash history) hash locations before initial rootCovered
 have room : old.length.val+1<2^256 := by have b:=middle.length.isLt; omega
 have numericOuter : LifecycleNumeric.pushHeader N hash base (FreshMappingHistory.numeric N hash history)=some firstNumeric := by
  rw [LifecycleNumeric.pushHeader_known hash base _ old.length rootWord,dif_pos room]
  have same : lengthWord (old.length.val+1) room=outerWord := by
   apply Subtype.ext
   exact congrArg Int.ofNat headers.1.symm
  rw [same]
 have targetOuter := TargetFreshMapping.run_source_header old middle pushed base fits (FreshMappingHistory.symbolic history) target before (targetInitial base rootCovered)
 have middleTransport : Transport N hash locations middleStore firstNumeric :=
  transport_write run initial base rootCovered outerWord
 have middleAgreement := TargetOperations.write_agreement locations fitting base fits outerWord (FreshMappingHistory.symbolic history) target targetInitial
 have childOwner := default_owner run history historyCovered base old.length outerWord childCovered untouched indices supported
 obtain ⟨actual,child,found,changed,saved⟩ := modifyAt_success middle result _ operationPush inner
 rw [fresh_find old middle fresh pushed] at found
 cases found
 have back := Value.find_save middle result _ child saved
 obtain ⟨finalNumeric,numericInner,targetInner,ownerIff,transported,agreement⟩ :=
  TargetPrimitivePush.complete_numeric run (Value.dflt (.array (.prim p))) child changed indices (.data base old.length.val) fits middleStore middleTarget firstNumeric fitting childOwner middleTransport middleAgreement childCovered elementCovered
 have owner := ownerIff.mpr (by change (0:Nat)+1≤lmax; decide)
 have prefixSupported : PathSupported (NestedCopyObservations.childPath (G:=G) (p:=p) old.length) := by
  change old.length.val<lmax ∧ True
  exact ⟨by omega,True.intro⟩
 have leaf : Represented child (PrimitivePop.queries indices)
   (pathLoc (NestedCopyObservations.childPath (G:=G) (p:=p) old.length) base)
   (write (write middleStore (.data (.data base old.length.val) 0) ClearDemands.zero) (.data base old.length.val) (lengthWord child.length.val child.length.isLt)) := by
  simpa only [NestedRetainedCopy.child_location] using owner
 have rootOwner := Represented.prefix (NestedCopyObservations.childPath (G:=G) (p:=p) old.length) back prefixSupported leaf
 refine ⟨child,firstNumeric,finalNumeric,back,numericOuter,numericInner,?_,rootOwner,transported,agreement⟩
 rw [Evm.run_append_ok targetOuter]
 exact targetInner

/-- info: 'Solidity.Backend.StorageOps.FreshArrayHistory.fresh_find' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fresh_find
/-- info: 'Solidity.Backend.StorageOps.FreshArrayHistory.inner_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms inner_total
/-- info: 'Solidity.Backend.StorageOps.FreshArrayHistory.outer_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms outer_header
/-- info: 'Solidity.Backend.StorageOps.FreshArrayHistory.default_owner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms default_owner
/-- info: 'Solidity.Backend.StorageOps.FreshArrayHistory.complete_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_numeric
end Solidity.Backend.StorageOps.FreshArrayHistory
