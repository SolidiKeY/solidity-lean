import Solidity.Evm.MemoryRefs

/-!
# Identity words in dynamic memory arrays

This relation supplements primitive-array and struct ownership: every element
is the address of its actual typed child, never a default zero word. These
local simulations deliberately retain the existing checked address code.
-/
namespace Solidity.Evm.Memory
open Semantics

structure RefArrayRepr {H : HTy} {R : RefTy} (hp : Heap H)
    (r : HRef H (.array (.ref R))) (base : Nat → Fin W) (m : Machine) : Prop where
  space : (base r.id).val + 1 + hp.len r .dyn ≤ W
  length : m.mem (base r.id).val = .val (wmod (hp.len r .dyn))
  elements : ∀ i v, (MObj.elems .dyn (hp.get r))[i]? = some v →
    m.mem ((base r.id).val + 1 + i) = .val (base v.id)

/-- The pointer result has the source endpoint type and allows genuine reverts. -/
def RefOut {H : HTy} {R : RefTy} (base : Nat → Fin W)
    (source : TRes (HRef H R)) (target : Out) (m : Machine) : Prop :=
  (∃ r, source = .ok r ∧ target = .ok (m.push (.val (base r.id))) 0) ∨
  (source = .error .revert ∧ target = .revert)

theorem RefArrayRepr.stack {H : HTy} {R : RefTy} {hp : Heap H}
    {r : HRef H (.array (.ref R))} {base : Nat → Fin W} {m : Machine}
    (h : RefArrayRepr hp r base m) (st : List Word) :
    RefArrayRepr hp r base {m with stack := st} :=
  ⟨h.space, h.length, h.elements⟩

/-- Indexed pointer reads agree with the actual typed heap, including bounds. -/
theorem RefArrayRepr.read {H : HTy} {R : RefTy} {hp : Heap H}
    {r : HRef H (.array (.ref R))} {base : Nat → Fin W} {m : Machine}
    (h : RefArrayRepr hp r base m) (i : Fin W) :
    RefOut base (TRes.ofOpt (hp.index r .dyn (indexValue i)))
      (run (readArrayCode (base r.id)) (m.push (.val i))) m := by
  have hc := arrayAddr_run m (base r.id) i _ (hp.len_dyn_lt r) h.length
  by_cases hi : i.val < hp.len r .dyn
  · rw [if_pos hi] at hc
    let v : HRef H R := (MObj.elems .dyn (hp.get r))[i.val]'hi
    have hv : (MObj.elems .dyn (hp.get r))[i.val]? = some v :=
      getElem?_pos (MObj.elems .dyn (hp.get r)) i.val hi
    refine .inl ⟨v, ?_, ?_⟩
    · simp only [Heap.index, indexValue, Int.toNat_natCast, hv, TRes.ofOpt]
    · have ha : (base r.id).val + 1 + i.val < W := by have := h.space; omega
      rw [readArrayCode, run_append_ok hc]
      simp only [run, Machine.push, exec_cons_zero, Instr.step, Machine.next,
        wmod_of_lt ha, Out.ok_bind, exec_nil, h.elements _ _ hv]
  · rw [if_neg hi] at hc
    refine .inr ⟨?_, run_append_revert hc⟩
    simp only [Heap.index, indexValue, Int.toNat_natCast,
      getElem?_neg (MObj.elems .dyn (hp.get r)) i.val hi, TRes.ofOpt]

/-- Parent redirection preserves the header and every other pointer word. -/
theorem RefArrayRepr.set {H : HTy} {R : RefTy} {hp : Heap H}
    {r : HRef H (.array (.ref R))} {base : Nat → Fin W} {m : Machine}
    (h : RefArrayRepr hp r base m) (i : Nat) (hi : i < hp.len r .dyn)
    (v : HRef H R) :
    RefArrayRepr (hp.set r (MObj.setElem .dyn (hp.get r) i v)) r base
      (writeMachine m ((base r.id).val + 1 + i) (.val (base v.id))) := by
  constructor
  · simpa only [Heap.len, Heap.get_set_same, MObj.elems_setElem, List.length_set] using h.space
  · change upd m.mem _ _ (base r.id).val = _
    rw [upd_other _ _ (by omega)]
    simpa only [Heap.len, Heap.get_set_same, MObj.elems_setElem, List.length_set] using h.length
  · intro j x hx
    simp only [Heap.get_set_same, MObj.elems_setElem] at hx
    change upd m.mem _ _ ((base r.id).val + 1 + j) = _
    by_cases he : i = j
    · subst j
      rw [List.getElem?_set_self hi] at hx
      obtain rfl := Option.some.inj hx
      exact upd_same _ _ _
    · rw [List.getElem?_set_ne (l := MObj.elems .dyn (hp.get r)) (a := v) he] at hx
      rw [upd_other _ _ (by omega)]
      exact h.elements j x hx

/-- Writes redirect a pointer, without copying a child, or revert at the bound. -/
theorem RefArrayRepr.write {H : HTy} {R : RefTy} {hp : Heap H}
    {r : HRef H (.array (.ref R))} {base : Nat → Fin W} {m : Machine}
    (h : RefArrayRepr hp r base m) (i : Fin W) (v : HRef H R) :
    (∃ hp', hp.writeAddr (.index r .dyn (indexValue i)) v = some hp' ∧
      run (writeArrayCode (base r.id)) ((m.push (.val (base v.id))).push (.val i)) =
        .ok (writeMachine m ((base r.id).val + 1 + i.val) (.val (base v.id))) 0 ∧
      RefArrayRepr hp' r base
        (writeMachine m ((base r.id).val + 1 + i.val) (.val (base v.id)))) ∨
    (hp.writeAddr (.index r .dyn (indexValue i)) v = none ∧
      run (writeArrayCode (base r.id)) ((m.push (.val (base v.id))).push (.val i)) = .revert) := by
  have hc := arrayAddr_run (m.push (.val (base v.id))) (base r.id) i _
    (hp.len_dyn_lt r) h.length
  by_cases hi : i.val < hp.len r .dyn
  · rw [if_pos hi] at hc
    refine .inl ⟨hp.set r (MObj.setElem .dyn (hp.get r) i.val v), ?_, ?_, h.set _ hi v⟩
    · simp only [Heap.writeAddr, Heap.setIndex, indexValue, Int.toNat_natCast]
      exact if_pos hi
    · have ha : (base r.id).val + 1 + i.val < W := by have := h.space; omega
      rw [writeArrayCode, run_append_ok hc]
      simp only [run, Machine.push, exec_cons_zero, Instr.step,
        wmod_of_lt ha, Out.ok_bind, exec_nil, writeMachine]
  · rw [if_neg hi] at hc
    refine .inr ⟨?_, run_append_revert hc⟩
    simp only [Heap.writeAddr, Heap.setIndex, indexValue, Int.toNat_natCast]
    exact if_neg hi

/-- Parent redirection changes no distinct child object or its retained aliases. -/
theorem refArray_child_kept {H : HTy} {R Q : RefTy} (hp : Heap H)
    (r : HRef H (.array (.ref R))) (child : HRef H Q) (hne : r.id ≠ child.id)
    (i : Nat) (v : HRef H R) :
    (hp.set r (MObj.setElem .dyn (hp.get r) i v)).get child = hp.get child :=
  Heap.get_set_ne hp r child hne _

/-- Reference member words survive a disjoint reference-array write. -/
theorem RefFieldsRepr.refArraySet {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {m : Machine} (h : RefFieldsRepr hp base m) {R : RefTy}
    (a : HRef H (.array (.ref R))) (i : Nat) (hi : i < hp.len a .dyn) (v : HRef H R)
    (hd : ∀ {s : Name} (r : HRef H (.struct s)),
      (base a.id).val + 1 + hp.len a .dyn ≤ (base r.id).val ∨
      (base r.id).val + (structDef s).length ≤ (base a.id).val) :
    RefFieldsRepr (hp.set a (MObj.setElem .dyn (hp.get a) i v)) base
      (writeMachine m ((base a.id).val + 1 + i) (.val (base v.id))) := by
  intro s f Q r hf
  have he : a.id ≠ r.id := by
    intro he
    cases (HRef.heq_of_id a r he).1
  simp only [Heap.field, Heap.get_set_ne hp a r he]
  have ho := fieldOffset_bound hf
  have hs := hd r
  change upd m.mem _ _ _ = _
  rw [upd_other _ _ (by rcases hs with hs | hs <;> omega)]
  exact h r hf

/-- All reference arrays reserve their full header and element intervals. -/
structure RefArrayHeapRepr {H : HTy} (hp : Heap H) (base : Nat → Fin W)
    (frame : Nat) (m : Machine) : Prop where
  arrays : ∀ {R : RefTy} (r : HRef H (.array (.ref R))), RefArrayRepr hp r base m
  above : ∀ {R : RefTy} (r : HRef H (.array (.ref R))), frame ≤ (base r.id).val
  separated : ∀ {R Q : RefTy} (r : HRef H (.array (.ref R)))
    (q : HRef H (.array (.ref Q))), r.id ≠ q.id →
    (base r.id).val + 1 + hp.len r .dyn ≤ (base q.id).val ∨
    (base q.id).val + 1 + hp.len q .dyn ≤ (base r.id).val
  primitives : ∀ {R : RefTy} {p : PrimTy} (r : HRef H (.array (.ref R)))
    (q : HRef H (.array (.prim p))),
    (base r.id).val + 1 + hp.len r .dyn ≤ (base q.id).val ∨
    (base q.id).val + 1 + hp.len q .dyn ≤ (base r.id).val
  structs : ∀ {R : RefTy} {s : Name} (r : HRef H (.array (.ref R)))
    (q : HRef H (.struct s)),
    (base r.id).val + 1 + hp.len r .dyn ≤ (base q.id).val ∨
    (base q.id).val + (structDef s).length ≤ (base r.id).val

theorem RefArrayHeapRepr.stack {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : RefArrayHeapRepr hp base frame m) (st : List Word) :
    RefArrayHeapRepr hp base frame {m with stack := st} :=
  ⟨fun r => (h.arrays r).stack st, h.above, h.separated, h.primitives, h.structs⟩

theorem RefArrayHeapRepr.localWrite {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : RefArrayHeapRepr hp base frame m)
    (l : Nat) (hl : l < frame) (w : Word) :
    RefArrayHeapRepr hp base frame (writeMachine m l w) := by
  refine ⟨?_, h.above, h.separated, h.primitives, h.structs⟩
  intro R r
  have hb := h.above r
  refine ⟨(h.arrays r).space, ?_, ?_⟩
  · exact (upd_other _ _ (by omega)).trans (h.arrays r).length
  · intro i v hv
    exact (upd_other _ _ (by omega)).trans ((h.arrays r).elements i v hv)

/-- Any element replacement preserves every dynamic array length. -/
theorem dynamicLen_setElem {H : HTy} {E T : Ty} (hp : Heap H)
    (r : HRef H (.array E)) (q : HRef H (.array T)) (i : Nat) (v : MVal H E) :
    (hp.set r (MObj.setElem .dyn (hp.get r) i v)).len q .dyn = hp.len q .dyn := by
  by_cases he : r.id = q.id
  · obtain ⟨ht, hr⟩ := HRef.heq_of_id r q he
    cases ht
    cases hr
    simp only [Heap.len, Heap.get_set_same, MObj.elems_setElem, List.length_set]
  · simp only [Heap.len, Heap.get_set_ne hp r q he]

theorem RefArrayHeapRepr.set {H : HTy} {R : RefTy} {hp : Heap H}
    {base : Nat → Fin W} {frame : Nat} {m : Machine}
    (h : RefArrayHeapRepr hp base frame m) (r : HRef H (.array (.ref R)))
    (i : Nat) (hi : i < hp.len r .dyn) (v : HRef H R) :
    RefArrayHeapRepr (hp.set r (MObj.setElem .dyn (hp.get r) i v)) base frame
      (writeMachine m ((base r.id).val + 1 + i) (.val (base v.id))) := by
  refine ⟨?_, h.above, ?_, ?_, ?_⟩
  · intro Q q
    by_cases he : r.id = q.id
    · obtain ⟨ht, hr⟩ := HRef.heq_of_id r q he
      cases ht
      cases hr
      exact (h.arrays r).set i hi v
    · have hq := h.arrays q
      have hd := h.separated r q he
      refine ⟨?_, ?_, ?_⟩
      · simpa only [dynamicLen_setElem] using hq.space
      · change upd m.mem _ _ (base q.id).val = _
        rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
        simpa only [dynamicLen_setElem] using hq.length
      · intro j x hx
        rw [Heap.get_set_ne hp r q he] at hx
        have hj : j < hp.len q .dyn := (List.getElem?_eq_some_iff.mp hx).1
        change upd m.mem _ _ ((base q.id).val + 1 + j) = _
        rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
        exact hq.elements j x hx
  · intro Q T q s hn
    simpa only [dynamicLen_setElem] using h.separated q s hn
  · intro Q p q s
    simpa only [dynamicLen_setElem] using h.primitives q s
  · intro Q s q t
    simpa only [dynamicLen_setElem] using h.structs q t

end Solidity.Evm.Memory
