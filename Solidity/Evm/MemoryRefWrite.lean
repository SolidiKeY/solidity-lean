import Solidity.Evm.MemoryPaths

/-!
# Reference-valued member assignment

Assigning an existing typed reference changes one pointer word in its parent
struct. It does not copy, allocate or mutate the child object. Whole-object
interval ownership still frames that word against primitive fields, other
objects and locals, while the reference-word relation tracks its new child.
-/
namespace Solidity.Evm.Memory
open Semantics
variable {C : Contract}

theorem arrayLen_setRefField {H : HTy} {hp : Heap H} {p : PrimTy} {s f : Name} {R : RefTy}
    (a : HRef H (.array (.prim p))) (r : HRef H (.struct s))
    (hf : lookupBy f (structDef s) = some (.ref R)) (v : HRef H R) :
    (hp.setField r hf v).len a .dyn = hp.len a .dyn := by
  have he : r.id ≠ a.id := by
    intro he
    have ht := (HRef.heq_of_id r a he).1
    cases ht
  simp only [Heap.len, Heap.setField, Heap.get_set_ne hp r a he]

theorem StructRepr.setReference {H : HTy} {s f : Name} {R : RefTy} {hp : Heap H}
    {r : HRef H (.struct s)} {base : Fin W} {m : Machine}
    (h : StructRepr hp r base m) (hf : lookupBy f (structDef s) = some (.ref R))
    (v : HRef H R) (w : Word) :
    StructRepr (hp.setField r hf v) r base
      (writeMachine m (base.val + fieldOffset (structDef s) f) w) := by
  refine ⟨h.space, ?_⟩
  intro g p hg
  have hn : f ≠ g := Ne.symm (primitive_reference_fields_ne hg hf)
  have ho := fieldOffset_ne hf hg hn
  simp only [Heap.field, Heap.setField, Heap.get_set_same,
    MFields.get_set_ne _ _ _ _ hn, writeMachine]
  rw [upd_other _ _ (by omega)]
  exact h.fields hg

theorem StructHeapRepr.setReference {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : StructHeapRepr hp base frame m)
    {s f : Name} {R : RefTy} (r : HRef H (.struct s))
    (hf : lookupBy f (structDef s) = some (.ref R)) (v : HRef H R) (w : Word) :
    StructHeapRepr (hp.setField r hf v) base frame
      (writeMachine m ((base r.id).val + fieldOffset (structDef s) f) w) := by
  refine ⟨?_, h.above, h.separated⟩
  intro t q
  by_cases he : r.id = q.id
  · obtain ⟨ht, hr⟩ := HRef.heq_of_id r q he
    cases ht
    cases hr
    exact (h.objects r).setReference hf v w
  · refine ⟨(h.objects q).space, ?_⟩
    intro g p hg
    have hd := h.separated r q he
    have ho := fieldOffset_bound hf
    have hgo := fieldOffset_bound hg
    simp only [Heap.field, Heap.setField, Heap.get_set_ne hp r q he, writeMachine]
    rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
    exact (h.objects q).fields hg

theorem RefFieldsRepr.setReference {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : RefFieldsRepr hp base m)
    (hs : StructHeapRepr hp base frame m) {s f : Name} {R : RefTy}
    (r : HRef H (.struct s)) (hf : lookupBy f (structDef s) = some (.ref R)) (v : HRef H R) :
    RefFieldsRepr (hp.setField r hf v) base
      (writeMachine m ((base r.id).val + fieldOffset (structDef s) f) (.val (base v.id))) := by
  intro t g Q q hg
  by_cases he : r.id = q.id
  · obtain ⟨ht, hr⟩ := HRef.heq_of_id r q he
    cases ht
    cases hr
    by_cases hn : f = g
    · subst g
      have et : R = Q := Ty.ref.inj (Option.some.inj (hf.symm.trans hg))
      subst Q
      simp only [Heap.field, Heap.setField, Heap.get_set_same, MFields.get_set_same,
        writeMachine, upd_same]
    · have ho := fieldOffset_ne hf hg hn
      simp only [Heap.field, Heap.setField, Heap.get_set_same,
        MFields.get_set_ne _ _ _ _ hn, writeMachine]
      rw [upd_other _ _ (by omega)]
      exact h r hg
  · have hd := hs.separated r q he
    have ho := fieldOffset_bound hf
    have hgo := fieldOffset_bound hg
    simp only [Heap.field, Heap.setField, Heap.get_set_ne hp r q he, writeMachine]
    rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
    exact h q hg

theorem ArrayRepr.structRefWrite {H : HTy} {hp : Heap H} {p : PrimTy} {s f : Name} {R : RefTy}
    {a : HRef H (.array (.prim p))} {r : HRef H (.struct s)}
    {ab rb : Fin W} {m : Machine} (h : ArrayRepr hp a ab m)
    (hf : lookupBy f (structDef s) = some (.ref R))
    (hd : ab.val + 1 + hp.len a .dyn ≤ rb.val ∨ rb.val + (structDef s).length ≤ ab.val)
    (v : HRef H R) (w : Word) :
    ArrayRepr (hp.setField r hf v) a ab
      (writeMachine m (rb.val + fieldOffset (structDef s) f) w) := by
  have he : r.id ≠ a.id := by
    intro he
    have ht := (HRef.heq_of_id r a he).1
    cases ht
  have ho := fieldOffset_bound hf
  refine ⟨?_, ?_, ?_⟩
  · simpa only [arrayLen_setRefField] using h.space
  · change upd m.mem (rb.val + fieldOffset (structDef s) f) w ab.val = _
    rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
    simpa only [arrayLen_setRefField] using h.length
  · intro i x hx
    rw [Heap.setField, Heap.get_set_ne hp r a he] at hx
    have hi : i < hp.len a .dyn := (List.getElem?_eq_some_iff.mp hx).1
    change ReprV p x (upd m.mem (rb.val + fieldOffset (structDef s) f) w (ab.val + 1 + i))
    rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
    exact h.elements i x hx

theorem HeapRepr.structRefWrite {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : HeapRepr hp base frame m)
    (hd : StructArraySeparated hp base) {s f : Name} {R : RefTy}
    (r : HRef H (.struct s)) (hf : lookupBy f (structDef s) = some (.ref R))
    (v : HRef H R) (w : Word) :
    HeapRepr (hp.setField r hf v) base frame
      (writeMachine m ((base r.id).val + fieldOffset (structDef s) f) w) := by
  refine ⟨fun a => (h.arrays a).structRefWrite hf (hd a r) v w, h.above, ?_⟩
  intro p q a b hn
  simpa only [arrayLen_setRefField] using h.separated a b hn

theorem StructArraySeparated.setReference {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    (h : StructArraySeparated hp base) {s f : Name} {R : RefTy}
    (r : HRef H (.struct s)) (hf : lookupBy f (structDef s) = some (.ref R)) (v : HRef H R) :
    StructArraySeparated (hp.setField r hf v) base := by
  intro p t a q
  simpa only [arrayLen_setRefField] using h a q

theorem StructAllocatorRepr.setReference {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : StructAllocatorRepr hp base frame cursor m) {s f : Name} {R : RefTy}
    (r : HRef H (.struct s)) (hf : lookupBy f (structDef s) = some (.ref R)) (v : HRef H R) :
    StructAllocatorRepr (hp.setField r hf v) base frame cursor
      (writeMachine m ((base r.id).val + fieldOffset (structDef s) f) (.val (base v.id))) := by
  have ho := fieldOffset_bound hf
  have hl := h.live r
  have hb := h.structs.above r
  have hz := h.arrays.free.reserved
  refine ⟨⟨h.arrays.heap.structRefWrite h.separated r hf v _, ?_, ?_⟩,
    h.structs.setReference r hf v _, StructArraySeparated.setReference h.separated r hf v, h.live⟩
  · refine ⟨h.arrays.free.reserved, h.arrays.free.above, ?_, ?_⟩
    · change upd m.mem _ _ 0 = .val cursor
      rw [upd_other _ _ (by omega)]
      exact h.arrays.free.cell
    · intro addr ha
      change upd m.mem _ _ addr = w[0]
      rw [upd_other _ _ (by omega)]
      exact h.arrays.free.zero addr ha
  · intro p a
    simpa only [arrayLen_setRefField] using h.arrays.live a

theorem StateRepr.setReference {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {s f : Name} {R : RefTy}
    (r : HRef σ.H (.struct s)) (hf : lookupBy f (structDef s) = some (.ref R)) (v : HRef σ.H R) :
    StateRepr L b frame F (σ.withHeap (σ.heap.setField r hf v)) base
      (writeMachine m ((base r.id).val + fieldOffset (structDef s) f) (.val (base v.id))) := by
  have hm : ∀ l, l < frame →
      (writeMachine m ((base r.id).val + fieldOffset (structDef s) f) (.val (base v.id))).mem l = m.mem l := by
    intro l hl
    have hb := h.structs.above r
    exact upd_other _ _ (by omega)
  have hc := h.core.congrMem (fun l _ hl => hm l (Nat.lt_of_lt_of_le hl h.locals))
  refine ⟨⟨hc.store, hc.vals, hc.aliases, hc.net, hc.netSelf, hc.bound,
      hc.fragile, hc.env, hc.funds, hc.oracle⟩,
    h.heap.structRefWrite h.separated r hf v _, ?_, h.locals,
    h.structs.setReference r hf v _, StructArraySeparated.setReference h.separated r hf v,
    RefFieldsRepr.setReference h.refs h.structs r hf v⟩
  intro Q i
  obtain ⟨q, hq, hi⟩ := h.pointers i
  refine ⟨q, hq, ?_⟩
  rw [hm _ (Nat.lt_of_lt_of_le (lvl_lt b i) h.locals)]
  exact hi

theorem writeFieldWord_run (m : Machine) (base : Fin W) (offset : Nat) (w : Word)
    (hb : base.val + offset < W) :
    run (writeFieldCode offset) ((m.push w).push (.val base)) =
      .ok (writeMachine m (base.val + offset) w) 0 := by
  rw [writeFieldCode, run_append_ok (fieldAddr_run (m.push w) base offset)]
  simp only [run, Machine.push, exec_cons_zero, Instr.step, wmod_of_lt hb,
    Out.ok_bind, exec_nil, writeMachine]

theorem writeReference_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {s f : Name} {R : RefTy}
    {dst : MPath C Γ (.ref (.struct s))} {src : MPath C Γ (.ref R)}
    {pointer value : List Instr} (hd : PtrFrag b dst pointer) (hs : PtrFrag b src value)
    (hf : C.fieldType s f = some (.ref R)) :
    ResultRepr L b frame F σ base m (TRun.assignMem (.field dst f hf) (.ref src) σ)
      (run (value ++ pointer ++ writeFieldCode (fieldOffset (structDef s) f)) m) := by
  obtain ⟨v, hv, hcv⟩ := hs.correct h
  obtain ⟨r, hr, _⟩ := hd.correct h
  have hb : (base r.id).val + fieldOffset (structDef s) f < W := by
    have ho := fieldOffset_bound hf
    have he := (h.structs.objects r).space
    omega
  refine .inl ⟨⟨σ.withHeap (σ.heap.setField r hf v), List.prefix_refl _⟩, _, ?_, ?_,
    h.setReference r hf v, rfl, fun _ _ ha => ha.setReference r hf v⟩
  · simp only [TRun.assignMem, MSrc.mvalT, MLoc.addrT, hv, hr, bind, Except.bind,
      pure, Except.pure, Heap.writeAddr, TRes.ofOpt]
  · rw [List.append_assoc, run_append_ok hcv,
      run_append_ok (hd.run_of_eval (h.push (.val (base v.id))) hr)]
    exact writeFieldWord_run m (base r.id) _ _ hb

end Solidity.Evm.Memory
