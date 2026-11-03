import Solidity.Backend.StorageOps.TargetCopyRepresentation
import Solidity.Backend.StorageOps.PathRepresentation
import Solidity.Backend.StorageOps.MappingPaths

/-! Fixed aggregate blocks invoke genuine runtime primitive-array copy loops.
These are current-source prefix execution/frame laws. Snapshot preservation
across distinct child calls needs a separate noninterference or capture proof;
no unrestricted independent fixed-overlay correspondence is assumed. -/
namespace Solidity.Backend.StorageOps.TargetFixedArrayCopy
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

def fixedIndex (m : FixedSize) (i : Fin m.val) : Index := ⟨i.val,Nat.lt_trans i.isLt m.property.2⟩

def childPath {n : Nat} {G : Schema n} {p : PrimTy} (m : FixedSize) (i : Fin m.val) :
    TypeGraph.Path G (.fixed (.array (.prim p)) m) (.array (.prim p)) := .cons (.fixed (fixedIndex m i)) .nil

def child {n : Nat} {G : Schema n} {p : PrimTy} {m : FixedSize}
    (root : Value G (.fixed (.array (.prim p)) m)) (i : Fin m.val) : Value G (.array (.prim p)) :=
  (root.find (childPath m i)).getD (Value.dflt _)

private theorem child_fixed {n : Nat} {G : Schema n} {p : PrimTy} {m : FixedSize}
    (slots : Fin m.val → Slot G (.array (.prim p))) (i : Fin m.val) :
    child (Value.fixed slots) i = (slots i).getD (Value.dflt _) := by
  simp only [child,Value.find,childPath,fixedIndex,TypeGraph.Path.read,Step.get,
    dif_pos i.isLt,Option.bind_some,Option.getD_some]

theorem find_child {n : Nat} {G : Schema n} {p : PrimTy} {m : FixedSize}
    (root : Value G (.fixed (.array (.prim p)) m)) (i : Fin m.val) :
    root.find (childPath m i) = some (child root i) := by
  cases root with
  | fixed slots =>
    simp only [child_fixed,Value.find,childPath,fixedIndex,TypeGraph.Path.read,Step.get,
      dif_pos i.isLt,Option.bind_some]

/-- Reuse the independently checked slot/default overlay law, retaining both
absent and present children instead of silently materializing source identity. -/
theorem child_overlay {n : Nat} {G : Schema n} {p : PrimTy} {m : FixedSize}
    (old source : Value G (.fixed (.array (.prim p)) m)) (i : Fin m.val) :
    child (old.overlay source) i = (child old i).overlay (child source i) := by
  cases old with
  | fixed oldSlots =>
    cases source with
    | fixed sourceSlots =>
      change child (Value.fixed (fun j => (oldSlots j).overlay (sourceSlots j))) i = _
      rw [child_fixed,child_fixed,child_fixed]
      exact overlay_slot_default (oldSlots i) (sourceSlots i)

theorem child_location {n : Nat} {G : Schema n} {p : PrimTy} (m : FixedSize) (i : Fin m.val) (base : Solidity.Storage.Loc) :
    pathLoc (childPath (G := G) (p := p) m i) base = base.add i.val := by
  simp only [childPath,fixedIndex,pathLoc,stepLoc,inlineSize_array,Nat.mul_one]

/-- An actual child program pushes captured operand slots; its own loop loads
CURRENT child headers and payloads. Fixed count is static type metadata. -/
def block (dst src : Evm.Slot) : List Evm.Instr :=
  [.push (.slot dst),.push (.slot src)] ++ TargetArrayCopy.code

def segment (dst src : Evm.Slot) (start : Nat) : Nat → List Evm.Instr
  | 0 => []
  | count+1 => segment dst src start count ++ block (dst.add (start+count)) (src.add (start+count))

def code (m : FixedSize) (dst src : Evm.Slot) : List Evm.Instr := segment dst src 0 m.val

/-- A prefix invariant over EXISTING Machine, composing checked current-header
child results. This is not a new source value/state or independent evaluator. -/
def prefixMachine (initial : Evm.Machine) (dst src : Evm.Slot) (start : Nat) : Nat → Evm.Machine
  | 0 => initial
  | count+1 =>
    let current := prefixMachine initial dst src start count
    TargetArrayCopyTail.afterCopy current current.stack (src.add (start+count)) (dst.add (start+count))

theorem prefix_stack (initial : Evm.Machine) (dst src : Evm.Slot) (start count : Nat) :
    (prefixMachine initial dst src start count).stack = initial.stack := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

theorem run_block (initial : Evm.Machine) (dst src : Evm.Slot) :
    Evm.run (block dst src) initial = .ok (TargetArrayCopyTail.afterCopy initial initial.stack src dst) 0 := by
  unfold block
  rw [Evm.run_append_ok (m' := { initial with stack := .slot src :: .slot dst :: initial.stack }) (by rfl)]
  exact TargetArrayCopyTail.run_current _ _ _ _

/-- Every finite static fixed span executes genuine runtime child loops.
No fixed source length, nested depth or fuel cap is introduced. -/
theorem run_segment (initial : Evm.Machine) (dst src : Evm.Slot) (start count : Nat) :
    Evm.run (segment dst src start count) initial = .ok (prefixMachine initial dst src start count) 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [segment,Evm.run_append_ok ih,run_block]
    rfl

theorem run_code (m : FixedSize) (initial : Evm.Machine) (dst src : Evm.Slot) :
    Evm.run (code m dst src) initial = .ok (prefixMachine initial dst src 0 m.val) 0 :=
  run_segment _ _ _ _ _

/-- Finite accesses are generated by CURRENT prefix headers, not a declared
source length or desired semantic result. Header is always stored last by child. -/
def touched (initial : Evm.Machine) (dst src : Evm.Slot) (start : Nat) : Nat → List Evm.Slot
  | 0 => []
  | count+1 =>
    let current := prefixMachine initial dst src start count
    let target := dst.add (start+count)
    let source := src.add (start+count)
    touched initial dst src start count ++ target ::
      (List.range (max (current.store source) (current.store target))).map (fun j => Evm.Slot.data target j)

theorem prefix_outside (initial : Evm.Machine) (dst src observer : Evm.Slot) (start count : Nat)
    (outside : observer ∉ touched initial dst src start count) :
    (prefixMachine initial dst src start count).store observer = initial.store observer := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have earlier : observer ∉ touched initial dst src start count := by
      intro member
      exact outside (List.mem_append.mpr (Or.inl member))
    have header : observer ≠ dst.add (start+count) := by
      intro same
      apply outside
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl same)))
    have payload : ∀ j, j < max ((prefixMachine initial dst src start count).store (src.add (start+count)))
        ((prefixMachine initial dst src start count).store (dst.add (start+count))) → observer ≠ .data (dst.add (start+count)) j := by
      intro j inside same
      apply outside
      exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j,List.mem_range.mpr inside,same.symm⟩)))
    change (TargetArrayCopyTail.afterCopy _ _ _ _).store observer = _
    rw [TargetArrayCopyTail.after_outside _ _ _ _ _ header payload]
    exact ih earlier


/-- Prefix composition/restart is exact for the ACTUAL evolving current source,
not for an assumed immutable snapshot of all future child values. -/
theorem prefix_append (initial : Evm.Machine) (dst src : Evm.Slot) (start count rest : Nat) :
    prefixMachine initial dst src start (count+rest) =
      prefixMachine (prefixMachine initial dst src start count) dst src (start+count) rest := by
  induction rest with
  | zero => rfl
  | succ rest ih =>
    change TargetArrayCopyTail.afterCopy (prefixMachine initial dst src start (count+rest))
      (prefixMachine initial dst src start (count+rest)).stack (src.add (start+(count+rest))) (dst.add (start+(count+rest))) =
      TargetArrayCopyTail.afterCopy (prefixMachine (prefixMachine initial dst src start count) dst src (start+count) rest)
        (prefixMachine (prefixMachine initial dst src start count) dst src (start+count) rest).stack
        (src.add ((start+count)+rest)) (dst.add ((start+count)+rest))
    rw [ih,Nat.add_assoc]

theorem run_restart (initial : Evm.Machine) (dst src : Evm.Slot) (start count rest : Nat) :
    Evm.run (segment dst src (start+count) rest) (prefixMachine initial dst src start count) =
      .ok (prefixMachine initial dst src start (count+rest)) 0 := by
  rw [run_segment,← prefix_append]

/-- The finite future read set includes its header and every initially live
payload; default/absence representation remains a separate owner premise. -/
def sourceReads (initial : Evm.Machine) (source : Evm.Slot) : List Evm.Slot :=
  source :: (List.range (initial.store source)).map (fun j => Evm.Slot.data source j)

/-- Actual generated noninterference DERIVES stable future current inputs.
This is an address/touched-set condition, never assumed result preservation;
it is not asserted for overlapping logical spans or as Source admission. -/
theorem source_snapshot_inputs (initial : Evm.Machine) (dst src future : Evm.Slot) (start count : Nat)
    (separate : ∀ l ∈ sourceReads initial future, l ∉ touched initial dst src start count) :
    (prefixMachine initial dst src start count).store future = initial.store future ∧
      ∀ j < initial.store future,
        (prefixMachine initial dst src start count).store (.data future j) = initial.store (.data future j) := by
  constructor
  · exact prefix_outside initial dst src future start count (separate _ List.mem_cons_self)
  · intro j live
    exact prefix_outside initial dst src (.data future j) start count
      (separate _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j,List.mem_range.mpr live,rfl⟩)))

/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopy.fixedIndex' does not depend on any axioms -/
#guard_msgs in #print axioms fixedIndex
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopy.childPath' does not depend on any axioms -/
#guard_msgs in #print axioms childPath
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopy.child' does not depend on any axioms -/
#guard_msgs in #print axioms child
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopy.find_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms find_child
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopy.child_overlay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms child_overlay
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopy.child_location' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms child_location
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopy.block' does not depend on any axioms -/
#guard_msgs in #print axioms block
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopy.segment' does not depend on any axioms -/
#guard_msgs in #print axioms segment
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopy.code' does not depend on any axioms -/
#guard_msgs in #print axioms code
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopy.prefixMachine' does not depend on any axioms -/
#guard_msgs in #print axioms prefixMachine
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopy.prefix_stack' does not depend on any axioms -/
#guard_msgs in #print axioms prefix_stack
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopy.run_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_block
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopy.run_segment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_segment
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopy.run_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_code
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopy.touched' does not depend on any axioms -/
#guard_msgs in #print axioms touched
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopy.prefix_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prefix_outside
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopy.prefix_append' does not depend on any axioms -/
#guard_msgs in #print axioms prefix_append
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopy.run_restart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_restart
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopy.sourceReads' does not depend on any axioms -/
#guard_msgs in #print axioms sourceReads
/-- info: 'Solidity.Backend.StorageOps.TargetFixedArrayCopy.source_snapshot_inputs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms source_snapshot_inputs

end Solidity.Backend.StorageOps.TargetFixedArrayCopy
