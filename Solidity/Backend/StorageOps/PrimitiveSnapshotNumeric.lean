import Solidity.Backend.StorageOps.TargetFixedSnapshot
import Solidity.Backend.StorageOps.TargetFixedArrayTransport

/-! Operation-side frozen-payload fixed snapshot transport. Existing Store,
WordStore, writePrefix, FiniteRun and target instructions are reused. CURRENT
source child traversal is not substituted for a whole OLD snapshot. -/
namespace Solidity.Backend.StorageOps.PrimitiveSnapshotNumeric
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

/-- Existing symbolic Store updated with an immutable OLD source reader. -/
def symbolic (captured : Store) (dst src : Solidity.Storage.Loc) : Nat → Store
 | 0 => captured
 | count+1 => Representation.write (symbolic captured dst src count) (dst.add count) (captured (src.add count))

/-- The existing runtime Nat prefix writer, with its OLD payload frozen. -/
def numeric (N : Nat) (hash : Solidity.Storage.Pre → Nat) (captured : WordStore)
 (dst src : Solidity.Storage.Loc) (count : Nat) : WordStore :=
 NumericTraversal.writePrefix (fun i => (dst.add i).word N hash)
  (fun i => captured ((src.add i).word N hash)) count captured

/-- Every actual prefix transports using only original finite-run premises
and actually covered reads/writes. `limit` is the run's total, not a source cap. -/
theorem transported {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (captured : Store) (initial : WordStore)
 (before : Transport N hash locations captured initial) (dst src : Solidity.Storage.Loc) (limit : Nat)
 (sourceCovered : ∀ i<limit,src.add i ∈ locations) (dstCovered : ∀ i<limit,dst.add i ∈ locations) :
 ∀ count,count≤limit → Transport N hash locations (symbolic captured dst src count) (numeric N hash initial dst src count) := by
 intro count
 induction count with
 | zero => intro _; exact before
 | succ count ih =>
   intro bound
   have previous := ih (by omega)
   have step := transport_write run previous (dst.add count) (dstCovered count (by omega)) (captured (src.add count))
   have read := before (src.add count) (sourceCovered count (by omega))
   simpa only [symbolic,numeric,NumericTraversal.writePrefix,read] using step

/-- Processed/unvisited numeric observations derive from existing prefix
invariant plus per-run address separation; overlap with SOURCE is allowed. -/
theorem numeric_read {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (initial : WordStore)
 (dst src : Solidity.Storage.Loc) (count i : Nat)
 (queryCovered : dst.add i ∈ locations) (dstCovered : ∀ j<count,dst.add j ∈ locations) :
 numeric N hash initial dst src count ((dst.add i).word N hash)=
 if i<count then initial ((src.add i).word N hash) else initial ((dst.add i).word N hash) := by
 apply NumericTraversal.prefix_read
 intro j inside different equal
 have same := run.word_inj queryCovered (dstCovered j inside) equal
 exact different (Solidity.Storage.Loc.add_inj same).symm

theorem numeric_outside {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (initial : WordStore)
 (dst src : Solidity.Storage.Loc) (count : Nat) (observer : Solidity.Storage.Loc)
 (queryCovered : observer ∈ locations) (dstCovered : ∀ j<count,dst.add j ∈ locations)
 (outside : ¬∃ i,i<count ∧ observer=dst.add i) :
 numeric N hash initial dst src count (observer.word N hash)=initial (observer.word N hash) := by
 apply NumericTraversal.prefix_outside
 intro j inside equal
 exact outside ⟨j,inside,run.word_inj queryCovered (dstCovered j inside) equal⟩

/-- Actual OLD-snapshot instructions agree at EVERY covered location with the
existing numeric runtime prefix writer. Numeric hashes/regions are per-run;
no source-determined trace, representation or world premise is invented. -/
theorem target_complete {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (p : PrimTy) (size : FixedSize)
 (target : Evm.Machine) (initial : WordStore) (dst src : Solidity.Storage.Loc)
 (dstFits : TargetOperations.KeysFit dst) (srcFits : TargetOperations.KeysFit src)
 (sourceCovered : ∀ i<size.val,src.add i ∈ locations) (dstCovered : ∀ i<size.val,dst.add i ∈ locations)
 (fitting : ∀ l ∈ locations,TargetOperations.KeysFit l)
 (before : ∀ l (member : l ∈ locations),target.store.cells (TargetOperations.toSlot l (fitting l member))=TargetOperations.encodeWord (initial (l.word N hash))) :
 let after := TargetFixedSnapshot.afterCopy p size target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)
 Evm.run (TargetFixedSnapshot.code p size (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)) target=.ok after 0 ∧
 (∀ l (member : l ∈ locations),after.store.cells (TargetOperations.toSlot l (fitting l member))=
  TargetOperations.encodeWord (numeric N hash initial dst src size.val (l.word N hash))) := by
 classical
 refine ⟨TargetFixedSnapshot.run_code _ _ _ _ _,?_⟩
 intro observer member
 by_cases copied : ∃ i,i<size.val ∧ observer=dst.add i
 · rcases copied with ⟨i,inside,rfl⟩
   rw [numeric_read run initial dst src size.val i member dstCovered,if_pos inside]
   apply Fin.ext
   have copied := TargetFixedSnapshot.after_data p size target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits) i inside
   have dstAddress := TargetFixedArrayTransport.toSlot_add dst dstFits i
   have srcAddress := TargetFixedArrayTransport.toSlot_add src srcFits i
   have read : (TargetFixedSnapshot.afterCopy p size target (TargetOperations.toSlot src srcFits) (TargetOperations.toSlot dst dstFits)).store
       (TargetOperations.toSlot (dst.add i) (TargetOperations.add_keysFit dst dstFits i))=
      target.store (TargetOperations.toSlot (src.add i) (TargetOperations.add_keysFit src srcFits i)) := by
    rw [dstAddress,srcAddress]
    exact copied
   exact read.trans (congrArg Fin.val (before (src.add i) (sourceCovered i inside)))
 · rw [numeric_outside run initial dst src size.val observer member dstCovered copied]
   apply Fin.ext
   have outside : ∀ i<size.val,TargetOperations.toSlot observer (fitting observer member)≠(TargetOperations.toSlot dst dstFits).add i := by
    intro i inside equal
    have address := TargetFixedArrayTransport.toSlot_add dst dstFits i
    have same := TargetOperations.toSlot_injective observer (dst.add i) (fitting observer member)
     (TargetOperations.add_keysFit dst dstFits i) (equal.trans address.symm)
    exact copied ⟨i,inside,same⟩
   have frame := TargetFixedSnapshot.after_outside p size target (TargetOperations.toSlot src srcFits)
    (TargetOperations.toSlot dst dstFits) (TargetOperations.toSlot observer (fitting observer member)) outside
   exact frame.trans (congrArg Fin.val (before observer member))

/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotNumeric.transported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms transported
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotNumeric.numeric_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_read
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotNumeric.numeric_outside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms numeric_outside
/-- info: 'Solidity.Backend.StorageOps.PrimitiveSnapshotNumeric.target_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms target_complete
end Solidity.Backend.StorageOps.PrimitiveSnapshotNumeric
