import Solidity.Evm.MemoryRefArray
import Solidity.Evm.MemoryLocals

/-! Reference-array ownership supplements the existing state relation without
changing its representation or admitting unconstrained pointer words. -/
namespace Solidity.Evm.Memory
open Semantics
variable {C : Contract}

structure RefArrayStateRepr (L b frame : Nat) {Γ : Ctx} (F : Frag Γ)
    (σ : State C Γ) (base : Nat → Fin W) (m : Machine) : Prop where
  state : StateRepr L b frame F σ base m
  arrays : RefArrayHeapRepr σ.heap base frame m

theorem RefArrayStateRepr.push {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : RefArrayStateRepr L b frame F σ base m) (w : Word) :
    RefArrayStateRepr L b frame F σ base (m.push w) :=
  ⟨h.state.push w, h.arrays.stack _⟩

theorem RefArrayStateRepr.setMem {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : RefArrayStateRepr L b frame F σ base m) {R : RefTy}
    (dst : Idx Γ (.mem R)) (r : HRef σ.H R) :
    RefArrayStateRepr L b frame F (σ.setLocal dst (some r)) base
      (writeMachine m (cellOf b dst) (.val (base r.id))) :=
  ⟨h.state.setMem dst r, h.arrays.localWrite _
    (Nat.lt_of_lt_of_le (lvl_lt b dst) h.state.locals) _⟩

/-- Primitive child writes preserve all parent pointers and their ownership. -/
theorem RefArrayHeapRepr.setPrimitive {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : RefArrayHeapRepr hp base frame m)
    {p : PrimTy} (a : HRef H (.array (.prim p))) (i : Nat)
    (hi : i < hp.len a .dyn) (v : p.Denote) (w : Word) :
    RefArrayHeapRepr (hp.set a (MObj.setElem .dyn (hp.get a) i v)) base frame
      (writeMachine m ((base a.id).val + 1 + i) w) := by
  refine ⟨?_, h.above, ?_, ?_, ?_⟩
  · intro R r
    have he : a.id ≠ r.id := by
      intro he
      cases (HRef.heq_of_id a r he).1
    have hd := h.primitives r a
    have hr := h.arrays r
    refine ⟨?_, ?_, ?_⟩
    · simpa only [dynamicLen_setElem] using hr.space
    · change upd m.mem _ _ (base r.id).val = _
      rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
      simpa only [dynamicLen_setElem] using hr.length
    · intro j x hx
      rw [Heap.get_set_ne hp a r he] at hx
      have hj : j < hp.len r .dyn := (List.getElem?_eq_some_iff.mp hx).1
      change upd m.mem _ _ _ = _
      rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
      exact hr.elements j x hx
  · intro R Q r q hn
    simpa only [dynamicLen_setElem] using h.separated r q hn
  · intro R q r t
    simpa only [dynamicLen_setElem] using h.primitives r t
  · intro R s r q
    simpa only [dynamicLen_setElem] using h.structs r q

theorem RefArrayStateRepr.setPrimitive {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : RefArrayStateRepr L b frame F σ base m) {p : PrimTy}
    (r : HRef σ.H (.array (.prim p))) (i : Nat) (hi : i < σ.heap.len r .dyn)
    (v : p.Denote) (w : Word) (hw : ReprV p v w) :
    RefArrayStateRepr L b frame F
      (σ.withHeap (σ.heap.set r (MObj.setElem .dyn (σ.heap.get r) i v))) base
      (writeMachine m ((base r.id).val + 1 + i) w) :=
  ⟨h.state.set r i hi v w hw, h.arrays.setPrimitive r i hi v w⟩

theorem ArrayRepr.refArraySet {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {m : Machine} {R : RefTy} {p : PrimTy} (a : HRef H (.array (.ref R)))
    (r : HRef H (.array (.prim p))) (h : ArrayRepr hp r (base r.id) m)
    (i : Nat) (hi : i < hp.len a .dyn) (v : HRef H R)
    (hd : (base a.id).val + 1 + hp.len a .dyn ≤ (base r.id).val ∨
      (base r.id).val + 1 + hp.len r .dyn ≤ (base a.id).val) :
    ArrayRepr (hp.set a (MObj.setElem .dyn (hp.get a) i v)) r (base r.id)
      (writeMachine m ((base a.id).val + 1 + i) (.val (base v.id))) := by
  have he : a.id ≠ r.id := by intro he; cases (HRef.heq_of_id a r he).1
  refine ⟨?_, ?_, ?_⟩
  · simpa only [dynamicLen_setElem] using h.space
  · change upd m.mem _ _ (base r.id).val = _
    rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
    simpa only [dynamicLen_setElem] using h.length
  · intro j x hx
    rw [Heap.get_set_ne hp a r he] at hx
    have hj : j < hp.len r .dyn := (List.getElem?_eq_some_iff.mp hx).1
    change ReprV p x (upd m.mem _ _ _)
    rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
    exact h.elements j x hx

/-- Redirecting a parent keeps child representations, locals and struct words. -/
theorem RefArrayStateRepr.setReference {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : RefArrayStateRepr L b frame F σ base m) {R : RefTy}
    (a : HRef σ.H (.array (.ref R))) (i : Nat) (hi : i < σ.heap.len a .dyn)
    (v : HRef σ.H R) :
    RefArrayStateRepr L b frame F
      (σ.withHeap (σ.heap.set a (MObj.setElem .dyn (σ.heap.get a) i v))) base
      (writeMachine m ((base a.id).val + 1 + i) (.val (base v.id))) := by
  have hm : ∀ l, l < frame →
      (writeMachine m ((base a.id).val + 1 + i) (.val (base v.id))).mem l = m.mem l := by
    intro l hl
    have hb := h.arrays.above a
    exact upd_other _ _ (by omega)
  have hc := h.state.core.congrMem (fun l _ hl => hm l (Nat.lt_of_lt_of_le hl h.state.locals))
  refine ⟨⟨⟨hc.store, hc.vals, hc.aliases, hc.net, hc.netSelf, hc.bound,
    hc.fragile, hc.env, hc.funds, hc.oracle⟩, ?_, ?_, h.state.locals, ?_, ?_,
    RefFieldsRepr.refArraySet h.state.refs a i hi v (h.arrays.structs a)⟩, h.arrays.set a i hi v⟩
  · refine ⟨fun r => (h.state.heap.arrays r).refArraySet a r i hi v (h.arrays.primitives a r),
      h.state.heap.above, ?_⟩
    intro p q r t hn
    simpa only [State.withHeap, dynamicLen_setElem] using h.state.heap.separated r t hn
  · intro Q j
    obtain ⟨r, hr, hp⟩ := h.state.pointers j
    exact ⟨r, hr, (hm _ (Nat.lt_of_lt_of_le (lvl_lt b j) h.state.locals)).trans hp⟩
  · refine ⟨?_, h.state.structs.above, h.state.structs.separated⟩
    intro s r
    have he : a.id ≠ r.id := by intro he; cases (HRef.heq_of_id a r he).1
    refine ⟨(h.state.structs.objects r).space, ?_⟩
    intro f p hf
    simp only [State.withHeap, Heap.field, Heap.get_set_ne σ.heap a r he]
    have hd := h.arrays.structs a r
    have ho := fieldOffset_bound hf
    change ReprV p _ (upd m.mem _ _ _)
    rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
    exact (h.state.structs.objects r).fields hf
  · intro p s r q
    simpa only [State.withHeap, dynamicLen_setElem] using h.state.separated r q

end Solidity.Evm.Memory
