import Solidity.Evm.SimLemmas
import Solidity.Backend.StorageOps.TargetOperations

/-! Actual fixed-primitive snapshot instructions over EXISTING typed compiler
leaves. PUBLIC loadLeaves captures every OLD source operand before PUBLIC
storeLeaves writes in reverse order. No source-access stability/disjointness
premise is needed for this target snapshot, even with overlapping inline spans.
Ordinary Source/address/representation/numeric/world composition is separate. -/
namespace Solidity.Backend.StorageOps.TargetFixedSnapshot

/-- Derive metadata from the EXISTING intrinsic compiler type, not a new IR. -/
def offsets (p : PrimTy) (size : TypeGraph.FixedSize) : List Nat :=
 Evm.leaves (.ref (.fixed (.prim p) size.val))

def code (p : PrimTy) (size : TypeGraph.FixedSize) (src dst : Evm.Slot) : List Evm.Instr :=
 [.push (.slot src)] ++ (Evm.loadLeaves (offsets p size) ++
  ([.pop,.push (.slot dst)] ++ (Evm.storeLeaves ((offsets p size).reverse) ++ [.pop])))

def afterStore (p : PrimTy) (size : TypeGraph.FixedSize) (machine : Evm.Machine) (src dst : Evm.Slot) : Evm.WordStore :=
 Evm.storeAt machine.store dst (offsets p size).reverse
  (((offsets p size).map (fun o => machine.store.cells (src.add o))).reverse.map Fin.val)

def afterCopy (p : PrimTy) (size : TypeGraph.FixedSize) (machine : Evm.Machine) (src dst : Evm.Slot) : Evm.Machine :=
 {machine with store:=afterStore p size machine src dst}

theorem offsets_range (p : PrimTy) (size : TypeGraph.FixedSize) : offsets p size=List.range size.val := by
 simp only [offsets,Evm.leaves,Semantics.tyRank,Evm.leavesF,Evm.size_prim,Nat.mul_one,Nat.add_zero,List.map_cons,List.map_nil]
 have flatten (xs : List Nat) : xs.flatMap (fun i => [i])=xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.flatMap_cons,ih]; rfl
 exact flatten _

theorem offsets_fit (p : PrimTy) (size : TypeGraph.FixedSize) : ∀ o ∈ offsets p size,o<Evm.W := by
 rw [offsets_range]
 intro o member
 exact Nat.lt_trans (List.mem_range.mp member) size.property.2

/-- Actual target execution captures ALL source words before ANY write;
overlap and self-copy require no assumed preservation of future source reads. -/
theorem run_code (p : PrimTy) (size : TypeGraph.FixedSize) (machine : Evm.Machine) (src dst : Evm.Slot) :
 Evm.run (code p size src dst) machine=.ok (afterCopy p size machine src dst) 0 := by
 let os := offsets p size
 let vs := os.map (fun o => machine.store.cells (src.add o))
 have push : Evm.run [.push (.slot src)] machine=.ok {machine with stack:=.slot src::machine.stack} 0 := by rfl
 have loaded := Evm.loadLeaves_run machine src os (offsets_fit p size) machine.stack
 have moved : Evm.run [.pop,.push (.slot dst)]
  {machine with stack:=.slot src::(vs.reverse.map Evm.Word.val ++ machine.stack)}=
  .ok {machine with stack:=.slot dst::(vs.reverse.map Evm.Word.val ++ machine.stack)} 0 := by rfl
 have stored := Evm.storeLeaves_run machine dst os.reverse vs.reverse machine.stack machine.store
  (by intro o member; exact offsets_fit p size o (List.mem_reverse.mp member))
  (by simp only [vs,List.length_reverse,List.length_map])
 unfold code
 rw [Evm.run_append_ok push,Evm.run_append_ok loaded,Evm.run_append_ok moved,Evm.run_append_ok stored]
 rfl

/-- Exact old-snapshot word at EVERY written fixed offset, including overlap. -/
theorem after_data (p : PrimTy) (size : TypeGraph.FixedSize) (machine : Evm.Machine) (src dst : Evm.Slot)
 (o : Nat) (inside : o<size.val) :
 (afterCopy p size machine src dst).store (dst.add o)=machine.store (src.add o) := by
 have mapped : (((offsets p size).map (fun j => machine.store.cells (src.add j))).reverse.map Fin.val)=
  ((offsets p size).reverse.map (fun j => machine.store (src.add j))) := by
  simp only [List.map_reverse,List.map_map,Function.comp_def,Evm.WordStore.read]
 change Evm.storeAt machine.store dst (offsets p size).reverse _ (dst.add o)=_
 rw [mapped]
 apply Evm.storeAt_map (fun j => machine.store (src.add j)) (fun j => (machine.store.cells (src.add j)).isLt)
 apply List.mem_reverse.mpr
 rw [offsets_range]
 exact List.mem_range.mpr inside

theorem after_outside (p : PrimTy) (size : TypeGraph.FixedSize) (machine : Evm.Machine) (src dst observer : Evm.Slot)
 (apart : ∀ o<size.val,observer≠dst.add o) :
 (afterCopy p size machine src dst).store observer=machine.store observer := by
 apply Evm.storeAt_other
 intro o member
 apply apart o
 have typed := List.mem_reverse.mp member
 rw [offsets_range] at typed
 exact List.mem_range.mp typed

/-- Current target SLOAD reads the copied OLD source word. -/
theorem readback (p : PrimTy) (size : TypeGraph.FixedSize) (machine : Evm.Machine) (src dst : Evm.Slot)
 (o : Nat) (inside : o<size.val) :
 Evm.run (TargetOperations.readCode (dst.add o)) (afterCopy p size machine src dst)=
 .ok {afterCopy p size machine src dst with stack:=.val (machine.store.cells (src.add o))::machine.stack} 0 := by
 have cell : (afterCopy p size machine src dst).store.cells (dst.add o)=machine.store.cells (src.add o) :=
  Fin.ext (after_data p size machine src dst o inside)
 rw [TargetOperations.run_read,cell]
 rfl

/-- A genuine prefix of the EXISTING reverse store instruction list consumes
only its captured OLD operands. Remaining OLD operands stay on the stack even
if already-processed writes overlap their source memory addresses. -/
theorem store_prefix (p : PrimTy) (size : TypeGraph.FixedSize) (machine : Evm.Machine) (src dst : Evm.Slot)
 (processed remaining : List Nat) (partition : processed++remaining=(offsets p size).reverse) :
 Evm.run (Evm.storeLeaves processed)
  {machine with stack:=.slot dst::(((offsets p size).reverse.map (fun o => machine.store.cells (src.add o))).map Evm.Word.val ++ machine.stack)}=
 .ok {machine with
  stack:=.slot dst::((remaining.map (fun o => machine.store.cells (src.add o))).map Evm.Word.val ++ machine.stack),
  store:=Evm.storeAt machine.store dst processed (processed.map (fun o => machine.store (src.add o)))} 0 := by
 have fits : ∀ o ∈ processed,o<Evm.W := by
  intro o member
  apply offsets_fit p size o
  apply List.mem_reverse.mp
  rw [← partition]
  exact List.mem_append_left _ member
 have step := Evm.storeLeaves_run machine dst processed (processed.map (fun o => machine.store.cells (src.add o)))
  ((remaining.map (fun o => machine.store.cells (src.add o))).map Evm.Word.val ++ machine.stack) machine.store fits
  (by simp only [List.length_map])
 rw [← partition]
 simpa only [List.map_append,List.map_map,List.append_assoc,Function.comp_def,Evm.WordStore.read] using step

/-- info: 'Solidity.Backend.StorageOps.TargetFixedSnapshot.offsets_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms offsets_range
/-- info: 'Solidity.Backend.StorageOps.TargetFixedSnapshot.offsets_fit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms offsets_fit
/-- info: 'Solidity.Backend.StorageOps.TargetFixedSnapshot.run_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_code
/-- info: 'Solidity.Backend.StorageOps.TargetFixedSnapshot.after_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms after_data
/-- info: 'Solidity.Backend.StorageOps.TargetFixedSnapshot.after_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms after_outside
/-- info: 'Solidity.Backend.StorageOps.TargetFixedSnapshot.readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms readback
/-- info: 'Solidity.Backend.StorageOps.TargetFixedSnapshot.store_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms store_prefix
end Solidity.Backend.StorageOps.TargetFixedSnapshot
