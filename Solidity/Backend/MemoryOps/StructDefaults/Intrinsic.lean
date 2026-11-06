import Solidity.Backend.MemoryOps.StructDefaults.Frame
import Solidity.Backend.MemoryOps.SourceStructMemory

namespace Solidity.Backend.MemoryOps.StructDefaults
open Semantics

/-- Observers for the actually allocated pair and its empty child. Source and
intrinsic addresses are related explicitly; no solc physical layout is asserted. -/
structure PairAt {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (address childAddress : Nat)
    (hp : Heap H) (root : HRef H (.struct s))
    (layout : SourceBoolStructLayout E dn s tag child) : Prop where
  fields : ∃ fs : Source.DataList E.layout (E.layout.fields dn),
    y.2.heap.get address = some ⟨.struct .memory dn, Source.Data.struct fs⟩ ∧
    fs.nth 0 (.int .u256) = .ok (.val (sourceUint (hp.field root layout.tag_type))) ∧
    fs.nth 1 SourceBoolArrayTy = .ok (.val (.memRef rfl childAddress))
  leaf : SourceBoolMemoryAt y childAddress hp (hp.field root layout.child_type) .dyn

private theorem default_field {H : HTy} {hp : Heap H} {s : Name}
    {root : HRef H (.struct s)} (hd : hp.Dflt (.ref (.struct s)) root)
    {f : Name} {T : Ty} (hf : lookupBy f (structDef s) = some T) :
    hp.Dflt T (hp.field root hf) := by
  cases hd with
  | struct _ fields => exact fields hf

private theorem default_array_length {H : HTy} {hp : Heap H}
    {r : HRef H (.array (.prim .bool))} (hd : hp.Dflt (.ref (.array (.prim .bool))) r) :
    hp.len r .dyn = 0 := by
  cases hd with
  | array _ length => exact length

/-- Actual Source default construction agrees with the actual intrinsic default
at its root observers; old source contents and all intrinsic objects survive. -/
theorem source_pair_intrinsic {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (fuel : Nat)
    (layout : SourceBoolStructLayout E dn s tag child)
    (mapFree : (Ty.ref (.struct s)).mapFree = true) :
    let g := hp.allocDefault (.struct s) mapFree
    let z := ((Source.zeroVal (E := E) (Γ := Γ) (fuel+6) (.struct .memory dn)).run y).2
    PairAt z (y.2.heap.next+1) y.2.heap.next g.heap g.val layout ∧
      Heap.Keeps g.ext hp g.heap ∧
      (∀ a, y.2.heap.get a ≠ none → z.2.heap.get a = y.2.heap.get a) := by
  dsimp only
  let g := hp.allocDefault (.struct s) mapFree
  have hd : g.heap.Dflt (.ref (.struct s)) g.val := Heap.dflt_allocDefault hp _ mapFree
  have tagZero : g.heap.field g.val layout.tag_type = PrimTy.uint.dflt :=
    (default_field hd layout.tag_type).prim_eq
  have childEmpty : MObj.elems .dyn (g.heap.get (g.heap.field g.val layout.child_type)) = [] :=
    List.length_eq_zero_iff.mp (default_array_length (default_field hd layout.child_type))
  obtain ⟨fs, evaluated, first, child⟩ := source_pair_default y dn layout.source_types fuel
  rw [evaluated]
  refine ⟨⟨⟨fs, pairHeap_parent y.2.heap dn fs, ?_, child⟩, ?_⟩,
    SVal.keeps_copyStToM _ mapFree hp, ?_⟩
  · rw [tagZero]
    exact first
  · unfold SourceBoolMemoryAt
    rw [childEmpty]
    exact pairHeap_child y.2.heap dn fs
  · intro a occupied
    exact pairHeap_old y.2.heap dn fs a occupied

#print axioms source_pair_intrinsic
end Solidity.Backend.MemoryOps.StructDefaults
