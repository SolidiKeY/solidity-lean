import Solidity.Backend.StorageOps.PrimitiveSnapshotNumeric
import Solidity.Backend.StorageOps.NumericCopyCommutation

/-! Fixed runtime-prefix snapshot logs and two-operation numeric composition.
The existing numeric writer and PUBLIC finite write-log interface are reused. -/
namespace Solidity.Backend.StorageOps.PrimitiveSnapshotCommutation
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def log (N : Nat) (hash : Solidity.Storage.Pre → Nat) (captured : WordStore)
 (dst src : Solidity.Storage.Loc) (count : Nat) : List (Solidity.Storage.Loc × Semantics.Word) :=
 (List.range count).map (fun i => (dst.add i,captured ((src.add i).word N hash)))

theorem numeric_log (N : Nat) (hash : Solidity.Storage.Pre → Nat) (captured : WordStore)
 (dst src : Solidity.Storage.Loc) (count : Nat) :
 PrimitiveSnapshotNumeric.numeric N hash captured dst src count=
 (log N hash captured dst src count).foldl (fun m op => writeWord m (op.1.word N hash) op.2) captured := by
 induction count with
 | zero => rfl
 | succ count ih =>
  change writeWord (PrimitiveSnapshotNumeric.numeric N hash captured dst src count)
   ((dst.add count).word N hash) (captured ((src.add count).word N hash))=_
  rw [ih]
  simp only [log,List.range_succ,List.map_append,List.map_singleton,List.foldl_append,List.foldl_cons,List.foldl_nil]

/-- The second invocation reads its CURRENT input. Cross-read separation
DERIVES equality of its generated OLD payload log to the initial payload log. -/
theorem log_stable {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (initial : WordStore)
 (da sa : Solidity.Storage.Loc) (ca : Nat) (db sb : Solidity.Storage.Loc) (cb : Nat)
 (coveredA : ∀ i<ca,da.add i ∈ locations) (coveredB : ∀ j<cb,sb.add j ∈ locations)
 (separate : ∀ j<cb,∀ i<ca,sb.add j≠da.add i) :
 log N hash (PrimitiveSnapshotNumeric.numeric N hash initial da sa ca) db sb cb=log N hash initial db sb cb := by
 apply List.map_congr_left
 intro j member
 have inside:=List.mem_range.mp member
 apply congrArg (fun word => (db.add j,word))
 apply NumericTraversal.prefix_outside
 intro i before equal
 exact separate j inside i before (run.word_inj (coveredB j inside) (coveredA i before) equal)

/-- Whole numeric-store equality follows from actually generated write logs,
source noninterference and the original per-run region premise. Counts are
arbitrary runtime Nats; no length/depth restriction or global hash premise. -/
theorem commute {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (initial : WordStore)
 (da sa : Solidity.Storage.Loc) (ca : Nat) (db sb : Solidity.Storage.Loc) (cb : Nat)
 (dstA : ∀ i<ca,da.add i ∈ locations) (srcA : ∀ i<ca,sa.add i ∈ locations)
 (dstB : ∀ j<cb,db.add j ∈ locations) (srcB : ∀ j<cb,sb.add j ∈ locations)
 (writes : ∀ i<ca,∀ j<cb,da.add i≠db.add j)
 (readA : ∀ i<ca,∀ j<cb,sa.add i≠db.add j)
 (readB : ∀ j<cb,∀ i<ca,sb.add j≠da.add i) :
 PrimitiveSnapshotNumeric.numeric N hash (PrimitiveSnapshotNumeric.numeric N hash initial da sa ca) db sb cb=
 PrimitiveSnapshotNumeric.numeric N hash (PrimitiveSnapshotNumeric.numeric N hash initial db sb cb) da sa ca := by
 rw [numeric_log N hash (PrimitiveSnapshotNumeric.numeric N hash initial da sa ca) db sb cb,
  log_stable run initial da sa ca db sb cb dstA srcB readB,
  numeric_log N hash (PrimitiveSnapshotNumeric.numeric N hash initial db sb cb) da sa ca,
  log_stable run initial db sb cb da sa ca dstB srcA readA,
  numeric_log N hash initial da sa ca,numeric_log N hash initial db sb cb]
 apply NumericCopyCommutation.write_logs_commute
 intro a memberA b memberB
 obtain ⟨i,insideA,rfl⟩:=List.mem_map.mp memberA
 obtain ⟨j,insideB,rfl⟩:=List.mem_map.mp memberB
 intro equal
 exact writes i (List.mem_range.mp insideA) j (List.mem_range.mp insideB)
  (run.word_inj (dstA i (List.mem_range.mp insideA)) (dstB j (List.mem_range.mp insideB)) equal)

/-- Ordered transport needs no cross-operation noninterference. Both actual
invocations capture their own CURRENT input; dependent and overlapping runs
remain valid ordered executions, even when they do not commute. -/
theorem sequence_transport {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (captured : Store) (initial : WordStore)
 (before : Transport N hash locations captured initial)
 (da sa : Solidity.Storage.Loc) (ca : Nat) (db sb : Solidity.Storage.Loc) (cb : Nat)
 (dstA : ∀ i<ca,da.add i ∈ locations) (srcA : ∀ i<ca,sa.add i ∈ locations)
 (dstB : ∀ j<cb,db.add j ∈ locations) (srcB : ∀ j<cb,sb.add j ∈ locations) :
 Transport N hash locations
 (PrimitiveSnapshotNumeric.symbolic (PrimitiveSnapshotNumeric.symbolic captured da sa ca) db sb cb)
 (PrimitiveSnapshotNumeric.numeric N hash (PrimitiveSnapshotNumeric.numeric N hash initial da sa ca) db sb cb) := by
 have first := PrimitiveSnapshotNumeric.transported run captured initial before da sa ca srcA dstA ca (Nat.le_refl _)
 exact PrimitiveSnapshotNumeric.transported run _ _ first db sb cb srcB dstB cb (Nat.le_refl _)

/-- Compose actual compiler sequences with ordered symbolic/numeric transport.
No commutation hypotheses are required: each second operation consumes the
first operation's ACTUAL output and agreement is derived from OLD evidence. -/
theorem target_sequence {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (pa pb : PrimTy) (ma mb : FixedSize)
 (captured : Store) (initial : WordStore) (machine : Evm.Machine)
 (before : Transport N hash locations captured initial)
 (da sa db sb : Solidity.Storage.Loc)
 (daFits : TargetOperations.KeysFit da) (saFits : TargetOperations.KeysFit sa)
 (dbFits : TargetOperations.KeysFit db) (sbFits : TargetOperations.KeysFit sb)
 (dstA : ∀ i<ma.val,da.add i ∈ locations) (srcA : ∀ i<ma.val,sa.add i ∈ locations)
 (dstB : ∀ j<mb.val,db.add j ∈ locations) (srcB : ∀ j<mb.val,sb.add j ∈ locations)
 (fitting : ∀ l ∈ locations,TargetOperations.KeysFit l)
 (initialAgreement : ∀ l (member : l ∈ locations),machine.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (initial (l.word N hash))) :
 let first := TargetFixedSnapshot.afterCopy pa ma machine (TargetOperations.toSlot sa saFits) (TargetOperations.toSlot da daFits)
 let final := TargetFixedSnapshot.afterCopy pb mb first (TargetOperations.toSlot sb sbFits) (TargetOperations.toSlot db dbFits)
 let symbolic := PrimitiveSnapshotNumeric.symbolic (PrimitiveSnapshotNumeric.symbolic captured da sa ma.val) db sb mb.val
 let numeric := PrimitiveSnapshotNumeric.numeric N hash (PrimitiveSnapshotNumeric.numeric N hash initial da sa ma.val) db sb mb.val
 Transport N hash locations symbolic numeric ∧
 Evm.run (TargetFixedSnapshot.code pa ma (TargetOperations.toSlot sa saFits) (TargetOperations.toSlot da daFits) ++
  TargetFixedSnapshot.code pb mb (TargetOperations.toSlot sb sbFits) (TargetOperations.toSlot db dbFits)) machine=.ok final 0 ∧
 (∀ l (member : l ∈ locations),final.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (numeric (l.word N hash))) := by
 have first := PrimitiveSnapshotNumeric.target_complete run pa ma machine initial da sa daFits saFits srcA dstA fitting initialAgreement
 have second := PrimitiveSnapshotNumeric.target_complete run pb mb
  (TargetFixedSnapshot.afterCopy pa ma machine (TargetOperations.toSlot sa saFits) (TargetOperations.toSlot da daFits))
  (PrimitiveSnapshotNumeric.numeric N hash initial da sa ma.val) db sb dbFits sbFits srcB dstB fitting first.2
 refine ⟨sequence_transport run captured initial before da sa ma.val db sb mb.val dstA srcA dstB srcB,?_,second.2⟩
 rw [Evm.run_append_ok first.1]
 exact second.1

/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotCommutation.numeric_log' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms numeric_log
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotCommutation.log_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms log_stable
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotCommutation.commute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms commute
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotCommutation.sequence_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms sequence_transport
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotCommutation.target_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_sequence
end Solidity.Backend.StorageOps.PrimitiveSnapshotCommutation
