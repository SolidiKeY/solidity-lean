import Solidity.Evm.Memory

/-!
# Separated memory objects

One base per heap identity makes aliases agree. Distinct primitive arrays
occupy disjoint intervals, including their length cells. The frame limit
reserves every cell below it for locals; a compiler using this relation must
bound all of its active and future frames by that limit.
-/
namespace Solidity.Evm.Memory

/-- A global primitive-array representation above the reserved local frames.
The base map is indexed by identity, so two aliases cannot choose different
addresses for the same source object. -/
structure HeapRepr {H : HTy} (hp : Heap H) (base : Nat → Fin W)
    (frame : Nat) (m : Machine) : Prop where
  arrays : ∀ {p : PrimTy} (r : HRef H (.array (.prim p))), ArrayRepr hp r (base r.id) m
  above : ∀ {p : PrimTy} (r : HRef H (.array (.prim p))), frame ≤ (base r.id).1
  separated : ∀ {p q : PrimTy} (r : HRef H (.array (.prim p)))
    (s : HRef H (.array (.prim q))), r.id ≠ s.id →
    (base r.id).1 + 1 + hp.len r .dyn ≤ (base s.id).1 ∨
    (base s.id).1 + 1 + hp.len s .dyn ≤ (base r.id).1

/-- Element replacement changes no array's length, including other objects'. -/
theorem arrayLen_set {H : HTy} {p q : PrimTy} (hp : Heap H)
    (r : HRef H (.array (.prim p))) (s : HRef H (.array (.prim q)))
    (i : Nat) (v : p.Denote) :
    (hp.set r (MObj.setElem .dyn (hp.get r) i v)).len s .dyn = hp.len s .dyn := by
  by_cases he : r.id = s.id
  · obtain ⟨ht, hr⟩ := HRef.heq_of_id r s he
    cases ht
    cases hr
    simp only [Heap.len, Heap.get_set_same, MObj.elems_setElem, List.length_set]
  · simp only [Heap.len, Heap.get_set_ne hp r s he]

/-- A heap write above the frame limit preserves every reserved local cell. -/
theorem HeapRepr.write_below {H : HTy} {p : PrimTy} {hp : Heap H}
    {base : Nat → Fin W} {frame : Nat} {m : Machine}
    (h : HeapRepr hp base frame m) (r : HRef H (.array (.prim p)))
    (i : Nat) (w : Word) (l : Nat) (hl : l < frame) :
    (writeMachine m ((base r.id).1 + 1 + i) w).mem l = m.mem l := by
  have hb := h.above r
  exact upd_other _ _ (by omega)

/-- Writing a reserved local cell changes no represented heap object. -/
theorem HeapRepr.localWrite {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : HeapRepr hp base frame m)
    (l : Nat) (hl : l < frame) (w : Word) :
    HeapRepr hp base frame (writeMachine m l w) := by
  constructor
  · intro p r
    have hr := h.arrays r
    have hb := h.above r
    refine ⟨hr.space, ?_, ?_⟩
    · exact (upd_other _ _ (by omega)).trans hr.length
    · intro j x hx
      change ReprV p x (upd m.mem l w ((base r.id).1 + 1 + j))
      rw [upd_other _ _ (by omega)]
      exact hr.elements j x hx
  · exact h.above
  · exact h.separated

/-- An in-bounds write preserves all represented objects and their separation.
This covers aliases of the written object and independent objects together. -/
theorem HeapRepr.set {H : HTy} {p : PrimTy} {hp : Heap H}
    {base : Nat → Fin W} {frame : Nat} {m : Machine}
    (h : HeapRepr hp base frame m) (r : HRef H (.array (.prim p)))
    (i : Nat) (hi : i < hp.len r .dyn) (v : p.Denote) (w : Word)
    (hw : ReprV p v w) :
    HeapRepr (hp.set r (MObj.setElem .dyn (hp.get r) i v)) base frame
      (writeMachine m ((base r.id).1 + 1 + i) w) := by
  constructor
  · intro q s
    by_cases he : r.id = s.id
    · obtain ⟨ht, hr⟩ := HRef.heq_of_id r s he
      cases ht
      cases hr
      exact (h.arrays r).set i hi v w hw
    · have hs := h.arrays s
      have hd := h.separated r s he
      constructor
      · simpa only [arrayLen_set] using hs.space
      · change upd m.mem ((base r.id).1 + 1 + i) w (base s.id).1 = _
        rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
        simpa only [arrayLen_set] using hs.length
      · intro j x hx
        rw [Heap.get_set_ne hp r s he] at hx
        have hj : j < hp.len s .dyn := (List.getElem?_eq_some_iff.mp hx).1
        change ReprV q x (upd m.mem ((base r.id).1 + 1 + i) w ((base s.id).1 + 1 + j))
        rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
        exact hs.elements j x hx
  · exact h.above
  · intro q t s u hsu
    simpa only [arrayLen_set] using h.separated s u hsu

end Solidity.Evm.Memory
