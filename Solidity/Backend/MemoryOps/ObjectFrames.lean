import Solidity.Backend.MemoryOps.DisjointOverwrite
import Solidity.Evm.MemoryObjectFrame

/-! Operation-side adapters to the published word-object representation.
No byte-memory bridge or copy loop is introduced. Only unchanged objects retain
content representation in the unchanged machine; the destination still needs
its actual emitted-write correctness proof. -/
namespace Solidity.Backend.MemoryOps
open Solidity.Evm.Memory.Objects
open Solidity.Evm

/-- A captured range overwrite preserves every live object's reservation size. -/
theorem overwriteSlice_cells {H : HTy} {R Q : RefTy} {E : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (offset : Nat)
    (payload : List (MVal H E)) (h : offset + payload.length ≤ hp.len r a)
    (q : HRef H Q) : cells (overwriteSlice hp r a offset payload h) q = cells hp q := by
  by_cases he : r.id = q.id
  · obtain ⟨rfl, hh⟩ := HRef.heq_of_id r q he
    cases hh
    cases a with
    | dyn =>
      simp only [cells, Heap.len, overwriteSlice_elems]
      rw [replaceSlice_length _ _ _ h]
    | fixed => rfl
  · cases Q with
    | array T => simp only [cells, Heap.len, overwriteSlice_frame hp r q a offset payload h he]
    | fixed T n => rfl
    | struct s => rfl
    | mapping k T => rfl

/-- Ownership, interval separation and the original frame survive the actual
range operation for primitive and reference-containing arrays alike. -/
theorem overwriteSlice_ownership {H : HTy} {R : RefTy} {E : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (offset : Nat)
    (payload : List (MVal H E)) (h : offset + payload.length ≤ hp.len r a)
    {base : Nat → Fin Evm.W} {frame : Nat} (ho : Ownership hp base frame) :
    Ownership (overwriteSlice hp r a offset payload h) base frame := by
  refine ⟨ho.above, ?_, ?_⟩
  · intro Q q
    simpa only [overwriteSlice_cells] using ho.space q
  · intro Q T q t hn
    simpa only [overwriteSlice_cells] using ho.separated q t hn

/-- A different array, including reference-valued arrays, retains its existing
word representation in the original machine. This does not represent the
written destination without executing its target writes. -/
theorem overwriteSlice_other_repr {H : HTy} {R Q : RefTy} {E F : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (offset : Nat)
    (payload : List (MVal H E)) (h : offset + payload.length ≤ hp.len r a)
    (q : HRef H Q) (b : ArrTy Q F) (hne : r.id ≠ q.id)
    {base : Nat → Fin Evm.W} {m : Machine} (hq : ArrayRepr hp q b base m) :
    ArrayRepr (overwriteSlice hp r a offset payload h) q b base m := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [overwriteSlice_cells] using hq.space
  · intro hb
    simpa only [Heap.len, overwriteSlice_frame hp r q a offset payload h hne] using hq.length hb
  · intro i v hv
    rw [overwriteSlice_frame hp r q a offset payload h hne] at hv
    exact hq.elements i v hv

/-- The operation retains identity/address separation using the existing
positive-reservation ownership theorem, rather than assuming fresh addresses. -/
theorem overwriteSlice_base_identity {H : HTy} {R Q T : RefTy} {E : Ty}
    (hp : Heap H) (r : HRef H R) (a : ArrTy R E) (offset : Nat)
    (payload : List (MVal H E)) (h : offset + payload.length ≤ hp.len r a)
    {base : Nat → Fin Evm.W} {frame : Nat} (ho : Ownership hp base frame)
    (q : HRef H Q) (t : HRef H T) :
    base q.id = base t.id ↔ q.id = t.id := by
  constructor
  · exact (overwriteSlice_ownership hp r a offset payload h ho).base_injective q t
  · intro he
    rw [he]

/-- info: 'Solidity.Backend.MemoryOps.overwriteSlice_cells' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overwriteSlice_cells
/-- info: 'Solidity.Backend.MemoryOps.overwriteSlice_ownership' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overwriteSlice_ownership
/-- info: 'Solidity.Backend.MemoryOps.overwriteSlice_other_repr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overwriteSlice_other_repr
/-- info: 'Solidity.Backend.MemoryOps.overwriteSlice_base_identity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overwriteSlice_base_identity
end Solidity.Backend.MemoryOps
