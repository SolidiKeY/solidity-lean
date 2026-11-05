import Solidity.Backend.MemoryCopies.SnapshotTransport
import Solidity.Backend.MemoryCopies.HeapContents

/-! Actual heap extensions preserve shared old references and complete nested
snapshots. Replacing a reachable old payload is a concrete negative control. -/
namespace Solidity.Backend.MemoryCopies.SnapshotTransportControls
open Evm Evm.Memory
private def seven : SVal (.prim .uint) := .prim ⟨7, by decide⟩
private def eleven : SVal (.prim .uint) := .prim ⟨11, by decide⟩
private def eight : PrimTy.uint.Denote := ⟨8, by decide⟩
private abbrev Child : RefTy := .array (.prim .uint)
private def populated : SVal (.ref Child) := .array (.cons seven (.cons eleven .nil)) .nil (by decide)
private def empty : SVal (.ref Child) := .array .nil .nil (by decide)
private def long : SVal (.ref Child) := .array (SVec.replicate seven 64) .nil (by decide)
private def nested : SVal (.ref (.array (.ref Child))) :=
  .array (.cons populated (.cons empty (.cons long .nil))) .nil (by decide)
private def fixed : SVal (.ref (.fixed (.ref Child) 2)) := .fixed (.cons populated (.cons empty .nil))
private def basket : SVal (.ref (.struct "Basket")) := .struct (.cons populated .nil)
private def initial : Heap [] := ()
private def seed := populated.copyStToM initial rfl
private def shared := seed.heap.alloc (R := .array (.ref Child)) ⟨[seed.val, seed.val], by decide⟩
private def old : HRef (seed.H' ++ [.array (.ref Child)]) Child := seed.val.wk (List.prefix_append _ _)
private def grown := nested.copyStToM shared.1 rfl
private def kept : Heap.Keeps grown.ext shared.1 grown.heap := SVal.keeps_copyStToM nested rfl shared.1

theorem certificate_inhabited : SnapshotTransportCertificate := snapshotTransport

theorem primitive_snapshot :
    MVal.copyMToSt grown.heap (T := .prim .uint) (MVal.wk grown.ext (.prim .uint) (indexValue (wmod 23))) =
      MVal.copyMToSt shared.1 (T := .prim .uint) (indexValue (wmod 23)) :=
  kept_snapshot grown.ext shared.1 grown.heap kept (.prim .uint) (indexValue (wmod 23))

theorem shared_aliases : shared.1.index shared.2 .dyn (indexValue (wmod 0)) = some old ∧
    shared.1.index shared.2 .dyn (indexValue (wmod 1)) = some old := by
  exact ⟨by with_unfolding_all rfl, by with_unfolding_all rfl⟩

theorem shared_indices : grown.heap.index (shared.2.wk grown.ext) .dyn (indexValue (wmod 0)) = some (old.wk grown.ext) ∧
    grown.heap.index (shared.2.wk grown.ext) .dyn (indexValue (wmod 1)) = some (old.wk grown.ext) := by
  exact ⟨(kept_selected_snapshot grown.ext shared.1 grown.heap kept shared.2 .dyn (indexValue (wmod 0)) old shared_aliases.1).1,
    (kept_selected_snapshot grown.ext shared.1 grown.heap kept shared.2 .dyn (indexValue (wmod 1)) old shared_aliases.2).1⟩

theorem shared_snapshot : MVal.copyMToSt grown.heap (T := .ref (.array (.ref Child))) (shared.2.wk grown.ext) =
    MVal.copyMToSt shared.1 (T := .ref (.array (.ref Child))) shared.2 :=
  kept_snapshot grown.ext shared.1 grown.heap kept (.ref (.array (.ref Child))) shared.2

theorem shared_payloads : MVal.copyMToSt grown.heap (T := .ref (.array (.ref Child))) (shared.2.wk grown.ext) =
    SVal.array (.cons populated (.cons populated .nil)) .nil (by decide) := by
  rw [shared_snapshot]
  decide +kernel

theorem missing_index_preserved : shared.1.index shared.2 .dyn (indexValue (wmod 2)) = none ∧
    grown.heap.index (shared.2.wk grown.ext) .dyn (indexValue (wmod 2)) = none := by
  have absent : shared.1.index shared.2 .dyn (indexValue (wmod 2)) = none := by with_unfolding_all rfl
  refine ⟨absent, ?_⟩
  rw [kept_index grown.ext shared.1 grown.heap kept shared.2 .dyn (indexValue (wmod 2)), absent]
  rfl

theorem allocation_preserves {R : RefTy} (value : SVal (.ref R)) (memory : (Ty.ref R).mapFree = true) :
    let first := value.copyStToM initial memory
    let second := nested.copyStToM first.heap rfl
    MVal.copyMToSt second.heap (T := .ref R) (first.val.wk second.ext) = value.strip := by
  dsimp only
  rw [kept_snapshot _ _ _ (SVal.keeps_copyStToM nested rfl _) (.ref R) _]
  exact (storageHeapContents value memory).contents initial

theorem nested_preserved :
    let first := nested.copyStToM initial rfl
    let second := nested.copyStToM first.heap rfl
    MVal.copyMToSt second.heap (T := .ref (.array (.ref Child))) (first.val.wk second.ext) = nested.strip :=
  allocation_preserves nested rfl

theorem fixed_preserved :
    let first := fixed.copyStToM initial rfl
    let second := nested.copyStToM first.heap rfl
    MVal.copyMToSt second.heap (T := .ref (.fixed (.ref Child) 2)) (first.val.wk second.ext) = fixed.strip :=
  allocation_preserves fixed rfl

theorem struct_preserved :
    let first := basket.copyStToM initial rfl
    let second := nested.copyStToM first.heap rfl
    MVal.copyMToSt second.heap (T := .ref (.struct "Basket")) (first.val.wk second.ext) = basket.strip :=
  allocation_preserves basket rfl

theorem empty_preserved :
    let first := empty.copyStToM initial rfl
    let second := nested.copyStToM first.heap rfl
    MVal.copyMToSt second.heap (T := .ref Child) (first.val.wk second.ext) = empty.strip :=
  allocation_preserves empty rfl

theorem long_preserved :
    let first := long.copyStToM initial rfl
    let second := nested.copyStToM first.heap rfl
    MVal.copyMToSt second.heap (T := .ref Child) (first.val.wk second.ext) = long.strip :=
  allocation_preserves long rfl

private def changed := shared.1.set old ⟨[eight, ⟨11, by decide⟩], by decide⟩

theorem changed_snapshot : MVal.copyMToSt changed (T := .ref (.array (.ref Child))) shared.2 ≠
    MVal.copyMToSt shared.1 (T := .ref (.array (.ref Child))) shared.2 := by
  decide +kernel

theorem changed_old_rejected : ¬ Heap.Keeps (List.prefix_refl _) shared.1 changed := by
  intro proposed
  have invariant : MVal.copyMToSt changed (MVal.wk (List.prefix_refl _) (.ref (.array (.ref Child))) shared.2) =
      MVal.copyMToSt shared.1 (T := .ref (.array (.ref Child))) shared.2 :=
    kept_snapshot (List.prefix_refl _) shared.1 changed proposed (.ref (.array (.ref Child))) shared.2
  have same : MVal.copyMToSt changed (T := .ref (.array (.ref Child))) shared.2 =
      MVal.copyMToSt shared.1 (T := .ref (.array (.ref Child))) shared.2 := by
    simpa only [MVal.wk_refl] using invariant
  exact changed_snapshot same

#print axioms certificate_inhabited
#print axioms primitive_snapshot
#print axioms shared_aliases
#print axioms shared_indices
#print axioms shared_snapshot
#print axioms shared_payloads
#print axioms missing_index_preserved
#print axioms allocation_preserves
#print axioms nested_preserved
#print axioms fixed_preserved
#print axioms struct_preserved
#print axioms empty_preserved
#print axioms long_preserved
#print axioms changed_old_rejected
#print axioms changed_snapshot
end Solidity.Backend.MemoryCopies.SnapshotTransportControls
