import Solidity.Evm.MemoryFixedShapeCode

/-! Snapshot, padding, cleanup and frame laws for primitive fixed sources. -/
namespace Solidity.Evm.Memory
open Semantics

private theorem primStrip {p : PrimTy} : {n : Nat} → (xs : SVec (.prim p) n) → xs.strip = xs
  | _, .nil => by rw [SVec.strip_nil]
  | _, .cons (.prim v) rest => by rw [SVec.strip_cons, SVal.strip_prim, primStrip rest]
private theorem primOverlay {p : PrimTy} : {n : Nat} → (xs : SVec (.prim p) n) →
    ∀ old, SVec.overlayOn old xs = xs
  | _, .nil, _ => by rw [SVec.overlayOn_nil]
  | _, .cons (.prim v) rest, [] => by rw [SVec.overlayOn_nil_cons, SVal.strip_prim, primStrip]
  | _, .cons (.prim v) rest, o :: old => by rw [SVec.overlayOn_cons_cons, SVal.overlay_prim, primOverlay rest]

theorem fixedPadStore_live (st : WordStore) (dst : Slot) (n k : Nat)
    (words : Nat → Fin W) (i : Nat) (hi : i < n) :
    fixedPadStore st dst n k words (dst.add i) = (words i).val := by
  rw [fixedPadStore]
  have hz : (fun j st => WordStore.write st (dst.add j) 0) =
      (fun j st => WordStore.write st (dst.add j) ((fun _ => wmod 0) j).val) := rfl
  rw [hz, rangeStore_other dst (fun _ => wmod 0) _ _ n _ (by
    intro j hj _ he
    have hij := Slot.add_inj he
    omega)]
  exact rangeStore_written dst words n 0 st i (Nat.zero_le _) (by omega)

theorem fixedPadStore_tail (st : WordStore) (dst : Slot) (n k : Nat)
    (words : Nat → Fin W) (i : Nat) (hi : n ≤ i) (hk : i < k) :
    fixedPadStore st dst n k words (dst.add i) = 0 :=
  rangeStore_written dst (fun _ => wmod 0) (k - n) n _ i hi (by omega)

theorem fixedPadStore_other {p : PrimTy} (st : WordStore) (dst : Slot) (n k : Nat)
    (words : Nat → Fin W) (hfit : n ≤ k) (x : Slot)
    (hx : ¬ Occ (.ref (.fixed (.prim p) k)) dst x) :
    fixedPadStore st dst n k words x = st x := by
  have hout : ∀ i, i < k → x ≠ dst.add i := by
    intro i hi he
    apply hx
    rw [he]
    simpa only [size_prim, Nat.mul_one] using
      (Occ.felem i hi (E := .prim p) (s := dst) Occ.prim)
  rw [fixedPadStore]
  have hz : (fun j st => WordStore.write st (dst.add j) 0) =
      (fun j st => WordStore.write st (dst.add j) ((fun _ => wmod 0) j).val) := rfl
  rw [hz, rangeStore_other dst (fun _ => wmod 0) x _ _ _ (by
      intro i _ hi; exact hout i (by omega))]
  exact rangeStore_other dst words x n 0 st (by intro i _ hi; exact hout i (by omega))

theorem primitiveFixed_dynamic_repr {H : HTy} {p : PrimTy} {n : Nat} {hp : Heap H}
    {r : HRef H (.fixed (.prim p) n)} {base : Fin W} {m : Machine}
    (h : FixedArrayRepr hp r base m) (st : WordStore) (dst : Slot) (L : Nat)
    (hn : n < W) (hL : n < L) (old : SVal (.ref (.array (.prim p)))) :
    ReprAt (arrayCopyStore st dst n (fun i => payloadWord (m.mem (base.val + i))))
      L (.ref (.array (.prim p))) dst
      (old.overlay ((FixedCopy.dynamic hn).apply (MVal.copyMToSt hp r))) := by
  cases old with
  | array oe osh oh =>
    rw [primitiveFixed_snapshot, FixedCopy.apply, primStrip, SVal.overlay_array, primOverlay]
    refine .array ?_ hL ?_
    · rw [arrayCopyStore_length _ _ _ _ hn]
    · intro i x hx
      rw [SVec.toList_ofLen, List.getElem?_map] at hx
      obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hx
      have hi : i < n := by have ht := lt_of_getElem? hv; rwa [(hp.get r).property] at ht
      have hr := h.elements i v hv
      have he : (arrayCopyStore st dst n
          (fun i => payloadWord (m.mem (base.val + i)))).cells (.data dst i) =
          payloadWord (m.mem (base.val + i)) := Fin.ext (arrayCopyStore_live st dst n _ i hi)
      simp only [size_prim, Nat.mul_one]
      exact .prim (by rw [he, ← ReprV.payload hr]; exact hr)

theorem primitiveFixed_pad_repr {H : HTy} {p : PrimTy} {n k : Nat} {hp : Heap H}
    {r : HRef H (.fixed (.prim p) n)} {base : Fin W} {m : Machine}
    (h : FixedArrayRepr hp r base m) (st : WordStore) (dst : Slot) (L : Nat) (hfit : n ≤ k) :
    ReprAt (fixedPadStore st dst n k (fun i => payloadWord (m.mem (base.val + i))))
      L (.ref (.fixed (.prim p) k)) dst
      ((FixedCopy.fixed k hfit).apply (MVal.copyMToSt hp r)) := by
  rw [primitiveFixed_snapshot, FixedCopy.apply, primStrip]
  refine .fixed ?_
  intro i x hx
  rw [SVec.getElem?_padRight] at hx
  split at hx <;> rename_i hik
  · split at hx <;> rename_i hin
    · rw [SVec.toList_ofLen, List.getElem?_map] at hx
      obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hx
      have hr := h.elements i v hv
      have he : (fixedPadStore st dst n k
          (fun i => payloadWord (m.mem (base.val + i)))).cells (dst.add i) =
          payloadWord (m.mem (base.val + i)) := Fin.ext (fixedPadStore_live st dst n k _ i hin)
      simp only [size_prim, Nat.mul_one]
      exact .prim (by rw [he, ← ReprV.payload hr]; exact hr)
    · cases hx
      have he : (fixedPadStore st dst n k
          (fun i => payloadWord (m.mem (base.val + i)))).cells (dst.add i) = wmod 0 :=
          Fin.ext (fixedPadStore_tail st dst n k _ i (by omega) hik)
      simp only [size_prim, Nat.mul_one, SVal.dflt_prim, SVal.strip_prim]
      apply ReprAt.prim
      rw [he]
      exact ReprV.dflt_zero p
  · cases hx

end Solidity.Evm.Memory
