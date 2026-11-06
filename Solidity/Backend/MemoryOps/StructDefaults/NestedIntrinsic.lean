import Solidity.Backend.MemoryOps.StructDefaults.NestedObservers
import Solidity.Backend.MemoryOps.StructDefaults.Intrinsic

namespace Solidity.Backend.MemoryOps.StructDefaults
open Semantics

structure NestedLayout (E : Source.Env) (innerDN outerDN : Source.DeclName)
    (innerS outerS tag child innerKey flagKey : Name) : Prop where
  inner : SourceBoolStructLayout E innerDN innerS tag child
  source_outer : E.layout.fields outerDN = [.struct .memory innerDN, .bool]
  target_outer : structDef outerS = [(innerKey, .ref (.struct innerS)), (flagKey, Ty.bool)]
  distinct : innerKey ≠ flagKey

theorem NestedLayout.inner_type
    (layout : NestedLayout E innerDN outerDN innerS outerS tag child innerKey flagKey) :
    lookupBy innerKey (structDef outerS) = some (.ref (.struct innerS)) := by
  rw [layout.target_outer]
  simp only [lookupBy, ↓reduceIte]

theorem NestedLayout.flag_type
    (layout : NestedLayout E innerDN outerDN innerS outerS tag child innerKey flagKey) :
    lookupBy flagKey (structDef outerS) = some Ty.bool := by
  rw [layout.target_outer]
  simp only [lookupBy, Ne.symm layout.distinct, ↓reduceIte]

structure NestedAt {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (outerAddress innerAddress childAddress : Nat)
    (hp : Heap H) (root : HRef H (.struct outerS))
    (layout : NestedLayout E innerDN outerDN innerS outerS tag child innerKey flagKey) : Prop where
  fields : ∃ fs : Source.DataList E.layout (E.layout.fields outerDN),
    y.2.heap.get outerAddress = some ⟨.struct .memory outerDN, Source.Data.struct fs⟩ ∧
    fs.nth 0 (.struct .memory innerDN) = .ok (.val (.memRef rfl innerAddress)) ∧
    fs.nth 1 .bool = .ok (.val (.bool (hp.field root layout.flag_type)))
  inner : PairAt y innerAddress childAddress hp (hp.field root layout.inner_type) layout.inner

private theorem dflt_field {H : HTy} {hp : Heap H} {s : Name}
    {root : HRef H (.struct s)} (hd : hp.Dflt (.ref (.struct s)) root)
    {f : Name} {T : Ty} (hf : lookupBy f (structDef s) = some T) :
    hp.Dflt T (hp.field root hf) := by
  cases hd with
  | struct _ fields => exact fields hf

private theorem dflt_length {H : HTy} {hp : Heap H}
    {r : HRef H (.array (.prim .bool))} (hd : hp.Dflt (.ref (.array (.prim .bool))) r) :
    hp.len r .dyn = 0 := by
  cases hd with
  | array _ length => exact length

theorem source_nested_intrinsic {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (hp : Heap H) (fuel : Nat)
    (layout : NestedLayout E innerDN outerDN innerS outerS tag child innerKey flagKey)
    (mapFree : (Ty.ref (.struct outerS)).mapFree = true) :
    let g := hp.allocDefault (.struct outerS) mapFree
    let z := ((Source.zeroVal (E := E) (Γ := Γ) (fuel+9) (.struct .memory outerDN)).run y).2
    NestedAt z (y.2.heap.next+2) (y.2.heap.next+1) y.2.heap.next g.heap g.val layout ∧
      Heap.Keeps g.ext hp g.heap ∧
      (∀ a, y.2.heap.get a ≠ none → z.2.heap.get a = y.2.heap.get a) := by
  dsimp only
  let g := hp.allocDefault (.struct outerS) mapFree
  have hd : g.heap.Dflt (.ref (.struct outerS)) g.val := Heap.dflt_allocDefault hp _ mapFree
  have flagZero : g.heap.field g.val layout.flag_type = false :=
    (dflt_field hd layout.flag_type).prim_eq
  have innerDefault : g.heap.Dflt (.ref (.struct innerS))
      (g.heap.field g.val layout.inner_type) := dflt_field hd layout.inner_type
  have tagZero : g.heap.field (g.heap.field g.val layout.inner_type) layout.inner.tag_type =
      PrimTy.uint.dflt := (dflt_field innerDefault layout.inner.tag_type).prim_eq
  have childEmpty : MObj.elems .dyn (g.heap.get
      (g.heap.field (g.heap.field g.val layout.inner_type) layout.inner.child_type)) = [] :=
    List.length_eq_zero_iff.mp (dflt_length (dflt_field innerDefault layout.inner.child_type))
  obtain ⟨ifs, ofs, evaluated, innerPointer, flag, tagValue, childPointer⟩ :=
    source_nested_default_observers y innerDN outerDN layout.inner.source_types layout.source_outer fuel
  rw [evaluated]
  have childApart : y.2.heap.next ≠ (pairHeap y.2.heap innerDN ifs).next := by
    rw [pairHeap_cursor]; omega
  have innerApart : y.2.heap.next+1 ≠ (pairHeap y.2.heap innerDN ifs).next := by
    rw [pairHeap_cursor]; omega
  refine ⟨⟨⟨ofs, ?_, innerPointer, ?_⟩, ⟨⟨ifs, ?_, ?_, childPointer⟩, ?_⟩⟩,
    SVal.keeps_copyStToM _ mapFree hp, ?_⟩
  · exact Source.Heap.alloc_get _ _
  · rw [flagZero]; exact flag
  · rw [Source.Heap.alloc_other _ _ innerApart]
    exact pairHeap_parent y.2.heap innerDN ifs
  · rw [tagZero]; exact tagValue
  · unfold SourceBoolMemoryAt
    rw [childEmpty, Source.Heap.alloc_other _ _ childApart]
    exact pairHeap_child y.2.heap innerDN ifs
  · intro a occupied
    have below : a < y.2.heap.next := by
      by_cases h : a < y.2.heap.next
      · exact h
      · exact False.elim (occupied (y.2.heap.bounded a (by omega)))
    have apart : a ≠ (pairHeap y.2.heap innerDN ifs).next := by
      rw [pairHeap_cursor]; omega
    rw [Source.Heap.alloc_other _ _ apart]
    exact pairHeap_old y.2.heap innerDN ifs a occupied

#print axioms source_nested_intrinsic
end Solidity.Backend.MemoryOps.StructDefaults
