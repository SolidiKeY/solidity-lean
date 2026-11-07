import Solidity.Evm.MemoryStorageCopyCode
import Solidity.Evm.MemoryPaths

/-!
# Typed source laws for memory-to-storage array copies

The new live prefix is the actual heap snapshot. The old live suffix is
zeroed, the length is replaced, and all slots outside the destination layout
are unchanged. No source heap mutation or heap-equality premise is involved.
-/
-- Retain the existing typed memory-value proof reductions on Lean 4.35.
set_option backward.isDefEq.respectTransparency false

namespace Solidity.Evm.Memory
open Semantics

/-- Extract a numeric machine word; representations below rule out the slot case. -/
def payloadWord : Word → Fin W
  | .val v => v
  | .slot _ => wmod 0

theorem ReprV.payload {p : PrimTy} {v : p.Denote} {w : Word} (h : Evm.ReprV p v w) :
    w = .val (payloadWord w) := by
  cases p with
  | uint => obtain ⟨a, rfl, _⟩ := h; rfl
  | int => obtain ⟨a, rfl, _⟩ := h; rfl
  | bool => cases h; rfl

theorem arrayCopyStore_length (st : WordStore) (dst : Slot) (n : Nat)
    (words : Nat → Fin W) (hn : n < W) : arrayCopyStore st dst n words dst = n :=
  WordStore.write_same_of_lt _ _ _ hn

theorem arrayCopyStore_live (st : WordStore) (dst : Slot) (n : Nat)
    (words : Nat → Fin W) (i : Nat) (hi : i < n) :
    arrayCopyStore st dst n words (.data dst i) = (words i).val := by
  have hd : Slot.data dst i = (Slot.data dst 0).add i := by simp only [Slot.add, Nat.zero_add]
  have hz : (fun j st => WordStore.write st ((Slot.data dst 0).add j) 0) =
      (fun j st => WordStore.write st ((Slot.data dst 0).add j) ((fun _ => wmod 0) j).val) := by
    rfl
  rw [arrayCopyStore, WordStore.write_other _ _ (Ne.symm (Slot.ne_data dst i)), hz, hd,
    rangeStore_other (Slot.data dst 0) (fun _ => wmod 0) _ _ n _ (by
      intro j hj _ he
      have hij : i = j := Slot.add_inj he
      omega)]
  exact rangeStore_written (Slot.data dst 0) words n 0 st i (Nat.zero_le i) (by omega)

/-- Cleanup is observable at every slot discarded from the old live prefix. -/
theorem arrayCopyStore_tail (st : WordStore) (dst : Slot) (n : Nat)
    (words : Nat → Fin W) (i : Nat) (hi : n ≤ i) (hold : i < st dst) :
    arrayCopyStore st dst n words (.data dst i) = 0 := by
  have hd : Slot.data dst i = (Slot.data dst 0).add i := by simp only [Slot.add, Nat.zero_add]
  change (WordStore.write _ dst n) (.data dst i) = 0
  rw [WordStore.write_other _ _ (Ne.symm (Slot.ne_data dst i)), hd]
  exact rangeStore_written (Slot.data dst 0) (fun _ => wmod 0) (st dst - n) n _ i hi (by omega)

/-- Writes never escape the typed destination array layout, including cleanup. -/
theorem arrayCopyStore_other {p : PrimTy} (st : WordStore) (dst : Slot) (n : Nat)
    (words : Nat → Fin W) (x : Slot) (hx : ¬ Occ (.ref (.array (.prim p))) dst x) :
    arrayCopyStore st dst n words x = st x := by
  have hlen : x ≠ dst := fun he => hx (he ▸ Occ.len)
  have hdata : ∀ j, x ≠ (Slot.data dst 0).add j := by
    intro j he
    apply hx
    rw [he]
    simpa only [Slot.add, Nat.zero_add, size_prim, Nat.mul_one] using
      (Occ.elem j (E := .prim p) (s := dst) Occ.prim)
  rw [arrayCopyStore, WordStore.write_other _ _ hlen]
  have hz : (fun j st => WordStore.write st ((Slot.data dst 0).add j) 0) =
      (fun j st => WordStore.write st ((Slot.data dst 0).add j) ((fun _ => wmod 0) j).val) := rfl
  rw [hz, rangeStore_other (Slot.data dst 0) (fun _ => wmod 0) x _ _ _ (fun j _ _ => hdata j),
    rangeStore_other (Slot.data dst 0) words x _ _ _ (fun j _ _ => hdata j)]

/-- The source snapshot contains exactly the primitive heap payload. -/
theorem primitiveArray_snapshot {H : HTy} {p : PrimTy} (hp : Heap H)
    (r : HRef H (.array (.prim p))) :
    MVal.copyMToSt hp (T := .ref (.array (.prim p))) r =
      .array (SVec.ofList ((MObj.elems .dyn (hp.get r)).map SVal.prim)) .nil
        (by rw [List.length_map]; exact hp.len_dyn_lt r) := by
  simp only [MVal.copyMToSt, MVal.copyBelow, MVal.copyAt, MVal.copyRefAt, MObj.elems_dyn]

private theorem primitiveStrip {p : PrimTy} : {n : Nat} → (xs : SVec (.prim p) n) → xs.strip = xs
  | _, .nil => by rw [SVec.strip_nil]
  | _, .cons (.prim v) rest => by rw [SVec.strip_cons, SVal.strip_prim, primitiveStrip rest]

private theorem primitiveOverlay {p : PrimTy} : {n : Nat} → (xs : SVec (.prim p) n) →
    ∀ old, SVec.overlayOn old xs = xs
  | _, .nil, old => by rw [SVec.overlayOn_nil]
  | _, .cons (.prim v) rest, [] => by
    rw [SVec.overlayOn_nil_cons, SVal.strip_prim, primitiveStrip]
  | _, .cons (.prim v) rest, o :: old => by
    rw [SVec.overlayOn_cons_cons, SVal.overlay_prim, primitiveOverlay rest]

/-- The actual source snapshot, overlaid on any old destination, is represented
by the emitted copy algorithm. The length bound is the existing storage
representation bound, rather than sampled agreement. -/
theorem primitiveArray_copy_repr {H : HTy} {p : PrimTy} {hp : Heap H}
    {r : HRef H (.array (.prim p))} {base : Fin W} {m : Machine}
    (h : ArrayRepr hp r base m) (st : WordStore) (dst : Slot) (L : Nat)
    (hn : hp.len r .dyn < L) (old : SVal (.ref (.array (.prim p)))) :
    ReprAt (arrayCopyStore st dst (hp.len r .dyn)
      (fun i => payloadWord (m.mem (base.val + 1 + i)))) L (.ref (.array (.prim p))) dst
      (old.overlay (MVal.copyMToSt hp (T := .ref (.array (.prim p))) r)) := by
  cases old with
  | array oe osh oh =>
    rw [primitiveArray_snapshot, SVal.overlay_array, primitiveOverlay]
    refine .array ?_ ?_ ?_
    · rw [arrayCopyStore_length _ _ _ _ (hp.len_dyn_lt r), List.length_map]
      rfl
    · simpa only [List.length_map, Heap.len] using hn
    · intro i x hx
      rw [SVec.toList_ofList, List.getElem?_map] at hx
      obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hx
      have hi : i < hp.len r .dyn := lt_of_getElem? hv
      have hr := h.elements i v hv
      have he : (arrayCopyStore st dst (hp.len r .dyn)
          (fun i => payloadWord (m.mem (base.val + 1 + i)))).cells (.data dst i) =
          payloadWord (m.mem (base.val + 1 + i)) :=
        Fin.ext (arrayCopyStore_live st dst _ _ i hi)
      simp only [size_prim, Nat.mul_one]
      exact .prim (by rw [he, ← ReprV.payload hr]; exact hr)

end Solidity.Evm.Memory
