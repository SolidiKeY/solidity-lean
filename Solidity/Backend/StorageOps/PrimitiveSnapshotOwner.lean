import Solidity.Backend.StorageOps.PrimitiveSnapshotNumeric
import Solidity.Backend.StorageOps.TargetFixedPrimitive
import Solidity.Backend.StorageOps.RecursiveCopy

/-! Typed operation-side fixed primitive copy readback and applications of the
PUBLIC represented-storage relation. No new relation/representation is defined. -/
namespace Solidity.Backend.StorageOps.PrimitiveSnapshotOwner
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

theorem primitive_slot {n : Nat} {G : Schema n} {p : PrimTy}
 (old source : Slot G (.prim p)) :
 (recursiveSlot old source).getD (Value.dflt (.prim p))=source.getD (Value.dflt (.prim p)) := by
 rw [recursiveSlot_eq_overlay]
 cases source with
 | absent =>
   cases old with
   | absent => rfl
   | present old => cases old; rfl
 | present source =>
   cases source
   cases old with
   | absent => rfl
   | present old => cases old; rfl

/-- Exact successful and failed primitive fixed reads of the actual recursive
operation. Primitive defaulted reads agree without asserting raw slot identity. -/
theorem fixed_read {n : Nat} {G : Schema n} {p : PrimTy} {m : FixedSize}
 (old source : Value G (.fixed (.prim p) m)) (i : Index) :
 (recursiveCopy old source).find (TargetFixedPrimitive.path i)=source.find (TargetFixedPrimitive.path i) := by
 rw [recursiveCopy_eq_overlay]
 cases old with
 | fixed old =>
   cases source with
   | fixed source =>
     simp only [Value.overlay,Value.find,TargetFixedPrimitive.path,TypeGraph.Path.read,Step.get]
     split
     · next inside =>
       simp only [Option.bind_some]
       apply congrArg some
       rw [← recursiveSlot_eq_overlay]
       exact primitive_slot _ _
     · rfl

def query {n : Nat} {G : Schema n} {p : PrimTy} {m : FixedSize} (i : Fin m.val) : Query G (.fixed (.prim p) m) :=
 .word (TargetFixedPrimitive.path ⟨i.val,Nat.lt_trans i.isLt m.property.2⟩)

/-- OLD source owners determine actual copied output owners for selected
fixed primitive observations, including implicit defaults. Original finite-run
conditions and covered addresses are retained; overlapping spans are allowed. -/
theorem represented {n N L R : Nat} {G : Schema n} {p : PrimTy} {m : FixedSize}
 {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations)
 (old source : Value G (.fixed (.prim p) m)) (indices : List (Fin m.val))
 (dst src : Solidity.Storage.Loc) (captured : Store) (initial : WordStore)
 (before : Transport N hash locations captured initial)
 (sourceOwner : Represented source (indices.map (query (G:=G) (p:=p))) src captured)
 (sourceCovered : ∀ i<m.val,src.add i ∈ locations) (dstCovered : ∀ i<m.val,dst.add i ∈ locations) :
 Represented (recursiveCopy old source) (indices.map (query (G:=G) (p:=p))) dst
  (PrimitiveSnapshotNumeric.symbolic captured dst src m.val) := by
 have transport := PrimitiveSnapshotNumeric.transported run captured initial before dst src m.val sourceCovered dstCovered m.val (Nat.le_refl _)
 intro q member
 obtain ⟨i,inside,rfl⟩ := List.mem_map.mp member
 have original := sourceOwner (query (G:=G) (p:=p) i) (List.mem_map.mpr ⟨i,inside,rfl⟩)
 refine ⟨original.1,True.intro,?_⟩
 intro value observed
 have read : (query (G:=G) (p:=p) i).read (recursiveCopy old source)=(query (G:=G) (p:=p) i).read source := by
  simp only [query,Query.read,Value.observe,fixed_read]
 have oldWord := original.2.2 value (by rw [← read]; exact observed)
 have location : (query (G:=G) (p:=p) i).location dst=dst.add i.val := TargetFixedPrimitive.location (G:=G) (p:=p) (m:=m) _ _
 have sourceLocation : (query (G:=G) (p:=p) i).location src=src.add i.val := TargetFixedPrimitive.location (G:=G) (p:=p) (m:=m) _ _
 rw [location]
 rw [sourceLocation] at oldWord
 rw [← transport (dst.add i.val) (dstCovered i.val i.isLt)]
 rw [PrimitiveSnapshotNumeric.numeric_read run initial dst src m.val i.val (dstCovered i.val i.isLt) dstCovered,if_pos i.isLt]
 exact (before (src.add i.val) (sourceCovered i.val i.isLt)).trans oldWord

/-- Compose the derived actual graph output owner, PUBLIC numeric Transport
and actual target execution. Only OLD owner/transport/target agreements are
premises, not a desired result representation or a compiler relation. -/
theorem complete {n N L R : Nat} {G : Schema n} {p : PrimTy} {m : FixedSize}
 {hash : Solidity.Storage.Pre → Nat} {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations)
 (old source : Value G (.fixed (.prim p) m)) (indices : List (Fin m.val))
 (dst src : Solidity.Storage.Loc) (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
 (captured : Store) (initial : WordStore) (target : Evm.Machine)
 (before : Transport N hash locations captured initial)
 (sourceOwner : Represented source (indices.map (query (G:=G) (p:=p))) src captured)
 (sourceCovered : ∀ i<m.val,src.add i ∈ locations) (dstCovered : ∀ i<m.val,dst.add i ∈ locations)
 (fitting : ∀ l ∈ locations,TargetOperations.KeysFit l)
 (targetBefore : ∀ l (member : l ∈ locations),target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (captured l)) :
 let afterStore := PrimitiveSnapshotNumeric.symbolic captured dst src m.val
 let afterNumeric := PrimitiveSnapshotNumeric.numeric N hash initial dst src m.val
 let afterTarget := TargetFixedSnapshot.afterCopy p m target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)
 Represented (recursiveCopy old source) (indices.map (query (G:=G) (p:=p))) dst afterStore ∧
 Transport N hash locations afterStore afterNumeric ∧
 Evm.run (TargetFixedSnapshot.code p m (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)) target=.ok afterTarget 0 ∧
 (∀ l (member : l ∈ locations),afterTarget.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (afterNumeric (l.word N hash))) := by
 have targetNumeric : ∀ l (member : l ∈ locations),target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (initial (l.word N hash)) := by
  intro l member
  exact (targetBefore l member).trans (congrArg TargetOperations.encodeWord (before l member).symm)
 have executed := PrimitiveSnapshotNumeric.target_complete run p m target initial dst src dstFits srcFits sourceCovered dstCovered fitting targetNumeric
 exact ⟨represented run old source indices dst src captured initial before sourceOwner sourceCovered dstCovered,
  PrimitiveSnapshotNumeric.transported run captured initial before dst src m.val sourceCovered dstCovered m.val (Nat.le_refl _),executed.1,executed.2⟩

/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotOwner.primitive_slot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms primitive_slot
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotOwner.fixed_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fixed_read
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotOwner.represented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms represented
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotOwner.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.PrimitiveSnapshotOwner
