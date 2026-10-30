import Solidity.Backend.MemoryOps.HeapSnapshot
import Solidity.Backend.MemoryOps.ContextTransport
import Solidity.Backend.MemoryOps.SnapshotExtension

/-! Inhabited nested-reference controls for the slice and growth adapters.
These kernel witnesses are not source-lowering or external-EVM tests. -/
namespace Solidity.Backend.MemoryOps.Controls

private abbrev Child : RefTy := .array (.prim .bool)
private abbrev Parent : RefTy := .fixed (.ref Child) 2
private abbrev H : HTy := [Child, Parent]
private def child : HRef H Child := ⟨0, rfl⟩
private def parent : HRef H Parent := ⟨1, rfl⟩
private def heap : Heap H := (⟨[true, false], by decide⟩, ⟨[child, child], rfl⟩, ())
private def object : MObj H Child := ⟨[false], by decide⟩

/-- A nonempty reference slice retains the original shared child identities. -/
theorem nested_aliases :
    (sliceElems heap parent .fixed 0 2).map HRef.id = [0, 0] := by
  simp only [sliceElems, MObj.elems_fixed]
  rfl

/-- A slice can be empty at the exact end of a nonempty nested array. -/
theorem nested_empty : sliceElems heap parent .fixed 2 2 = [] := rfl

/-- Bounds reject an end beyond the actual typed parent length. -/
theorem nested_overrun : ¬ SliceBounds (heap.len parent .fixed) 0 3 :=
  overrun_invalid (by
    simp only [Heap.len, MObj.elems_fixed]
    decide)

/-- Allocation preserves nested aliases and separates them from the new object. -/
theorem nested_growth :
    (sliceElems (heap.alloc object).1
      (parent.wk (List.prefix_append H [Child])) .fixed 0 2).map HRef.id = [0, 0] ∧
    child.id ≠ (heap.alloc object).2.id := by
  constructor
  · rw [sliceElems_alloc, List.map_map]
    simp only [sliceElems, MObj.elems_fixed]
    rfl
  · exact old_ne_fresh heap object child

private abbrev H3 : HTy := [Child, Child, Parent]
private def first : HRef H3 Child := ⟨0, rfl⟩
private def second : HRef H3 Child := ⟨1, rfl⟩
private def parent3 : HRef H3 Parent := ⟨2, rfl⟩
private def heap3 : Heap H3 :=
  (⟨[true], by decide⟩, ⟨[false], by decide⟩, ⟨[first, second], rfl⟩, ())
private theorem space3 : 1 + [first].length ≤ heap3.len parent3 .fixed := by
  simp only [Heap.len, MObj.elems_fixed]
  decide
private def overwritten : Heap H3 := overwriteSlice heap3 parent3 .fixed 1 [first] space3

/-- A reference slot really changes, while both child objects retain contents. -/
theorem reference_overwrite :
    (MObj.elems .fixed (overwritten.get parent3)).map HRef.id = [0, 0] ∧
    overwritten.get first = heap3.get first ∧
    overwritten.get second = heap3.get second := by
  constructor
  · rw [overwritten, overwriteSlice_elems]
    simp only [MObj.elems_fixed]
    rfl
  · constructor
    · exact overwriteSlice_frame heap3 parent3 first .fixed 1 [first] space3 (by decide)
    · exact overwriteSlice_frame heap3 parent3 second .fixed 1 [first] space3 (by decide)

private def sourceTree : SVal (.ref Parent) :=
  .fixed (.cons (.array (.cons (.prim true) .nil) .nil (by decide))
    (.cons (.array (.cons (.prim false) .nil) .nil (by decide)) .nil))
private def copied := sourceTree.copyStToM heap3 rfl
private abbrev Γ3 : Ctx := [.mem Parent, .mem Child, .val .bool]
private def env3 : TEnv StandardExample H3 Γ3 := (some parent3, none, true, ())
private def state3 : State StandardExample Γ3 :=
  { storage := Storage.init StandardExample, H := H3, heap := heap3, env := env3 }

/-- Actual nonempty nested storage-tree copying transports initialized and unset
locals through State.adopt, retains old slices, and returns a fresh root. -/
theorem mixed_transport :
    TEnv.get .here (state3.adopt copied).1.env = some (parent3.wk copied.ext) ∧
    TEnv.get (.there .here) (state3.adopt copied).1.env = (none : Option (HRef _ Child)) ∧
    (sliceElems copied.heap (parent3.wk copied.ext) .fixed 0 2).map HRef.id = [0, 1] ∧
    3 ≤ (copied.val : HRef _ Parent).id ∧
    (copied.val : HRef _ Parent).id ≠ parent3.id := by
  refine ⟨local_ref_wk copied.ext env3 .here parent3 rfl,
    local_unset_wk copied.ext env3 (.there .here) rfl, ?_, ?_, ?_⟩
  · have he : sliceElems copied.heap (parent3.wk copied.ext) .fixed 0 2 =
        (sliceElems heap3 parent3 .fixed 0 2).map (MVal.wk copied.ext (.ref Child)) :=
      sliceElems_copyStToM heap3 sourceTree rfl parent3 .fixed 0 2
    rw [he, List.map_map]
    simp only [sliceElems, MObj.elems_fixed]
    rfl
  · exact SVal.copyStToM_id_ge heap3 sourceTree rfl
  · exact (copyStToM_old_ne_fresh heap3 sourceTree rfl parent3).symm

/-- Adding a new Boolean local does not disturb the transported parent alias. -/
theorem pushed_local :
    TEnv.get (Idx.there (u := .val .bool) .here)
      (false, TEnv.wk copied.ext Γ3 env3) = some (parent3.wk copied.ext) :=
  (local_slice_push_wk (t := .val .bool) copied.ext (SVal.keeps_copyStToM sourceTree rfl heap3)
    env3 .here parent3 rfl false ArrTy.fixed 0 2).1

private def grownOverwrite : Heap copied.H' :=
  overwriteSlice copied.heap (parent3.wk copied.ext) .fixed 1 [first.wk copied.ext]
    (overwriteSlice_space copied.ext (SVal.keeps_copyStToM sourceTree rfl heap3)
      parent3 .fixed 1 [first] space3)

/-- A changed reference slot commutes with real nested copy growth. Both old
child objects retain their contents; no claim is made about newly added objects. -/
theorem mixed_overwrite :
    Heap.Keeps copied.ext overwritten grownOverwrite ∧
    (MObj.elems .fixed (grownOverwrite.get (parent3.wk copied.ext))).map HRef.id = [0, 0] ∧
    grownOverwrite.get (first.wk copied.ext) = MObj.wk copied.ext Child (heap3.get first) ∧
    grownOverwrite.get (second.wk copied.ext) = MObj.wk copied.ext Child (heap3.get second) := by
  have hk : Heap.Keeps copied.ext overwritten grownOverwrite :=
    overwriteSlice_keeps copied.ext (SVal.keeps_copyStToM sourceTree rfl heap3)
      parent3 .fixed 1 [first] space3
  refine ⟨hk, ?_, ?_, ?_⟩
  · rw [hk parent3, MObj.elems_wk, List.map_map]
    exact reference_overwrite.1
  · rw [hk first, reference_overwrite.2.1]
  · rw [hk second, reference_overwrite.2.2]

/-- Keeping an identity while changing its contents does not establish Keeps. -/
theorem identity_not_content :
    (first.wk (List.prefix_refl H3)).id = first.id ∧
    ¬ Heap.Keeps (List.prefix_refl H3) heap3
      (heap3.set first (⟨[false], by decide⟩ : MObj H3 Child)) := by
  refine ⟨rfl, ?_⟩
  intro hk
  have he := hk first
  rw [show first.wk (List.prefix_refl H3) = first from rfl, Heap.get_set_same] at he
  have hb := congrArg (fun o : MObj H3 Child => o.1) he
  change [false] = [true] at hb
  cases hb

/-- A nested reference-containing default uses the published constructor and
keeps the old parent view distinct from the fresh default root. -/
theorem nested_default_transport :
    let d := heap3.allocDefault Parent rfl
    (sliceElems d.heap (parent3.wk d.ext) .fixed 0 2).map HRef.id = [0, 1] ∧
      parent3.id ≠ (d.val : HRef _ Parent).id := by
  dsimp only
  constructor
  · have he : sliceElems (heap3.allocDefault Parent rfl).heap
        (parent3.wk (heap3.allocDefault Parent rfl).ext) .fixed 0 2 =
        (sliceElems heap3 parent3 .fixed 0 2).map
          (MVal.wk (heap3.allocDefault Parent rfl).ext (.ref Child)) :=
      sliceElems_allocDefault heap3 Parent rfl parent3 .fixed 0 2
    rw [he, List.map_map]
    simp only [sliceElems, MObj.elems_fixed]
    rfl
  · exact allocDefault_old_ne_fresh heap3 Parent rfl parent3

/-- info: 'Solidity.Backend.MemoryOps.Controls.nested_default_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms nested_default_transport

/-- info: 'Solidity.Backend.MemoryOps.Controls.mixed_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mixed_transport
/-- info: 'Solidity.Backend.MemoryOps.Controls.mixed_overwrite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mixed_overwrite
/-- info: 'Solidity.Backend.MemoryOps.Controls.identity_not_content' depends on axioms: [propext] -/
#guard_msgs in #print axioms identity_not_content

/-- info: 'Solidity.Backend.MemoryOps.Controls.reference_overwrite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reference_overwrite
/-- info: 'Solidity.Backend.MemoryOps.Controls.nested_aliases' depends on axioms: [propext] -/
#guard_msgs in #print axioms nested_aliases
/-- info: 'Solidity.Backend.MemoryOps.Controls.nested_growth' depends on axioms: [propext] -/
#guard_msgs in #print axioms nested_growth

end Solidity.Backend.MemoryOps.Controls
