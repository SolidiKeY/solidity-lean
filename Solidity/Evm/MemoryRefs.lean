import Solidity.Evm.MemoryStructGrow

/-!+# Reference words in memory structs

Primitive-field representation does not constrain a reference member's word.
This separate relation records that word's actual typed heap identity. It
uses the shared address map, so aliases and nested paths can follow pointers
without erasing their endpoint types. The ordinary interval ownership still
frames each pointer cell against local, array and primitive-member writes.
-/
namespace Solidity.Evm.Memory
open Semantics

def RefFieldsRepr {H : HTy} (hp : Heap H) (base : Nat → Fin W) (m : Machine) : Prop :=
  ∀ {s f : Name} {R : RefTy} (r : HRef H (.struct s))
    (hf : lookupBy f (structDef s) = some (.ref R)),
    m.mem ((base r.id).val + fieldOffset (structDef s) f) = .val (base (hp.field r hf).id)

theorem RefFieldsRepr.withoutStructs {H : HTy} (hp : Heap H) (base : Nat → Fin W) (m : Machine)
    (hn : ∀ {s : Name}, HRef H (.struct s) → False) : RefFieldsRepr hp base m := by
  intro s f R r hf
  exact (hn r).elim

theorem RefFieldsRepr.mem_eq {H : HTy} {hp : Heap H} {base : Nat → Fin W} {m m' : Machine}
    (h : RefFieldsRepr hp base m) (hm : m'.mem = m.mem) : RefFieldsRepr hp base m' := by
  intro s f R r hf
  rw [hm]
  exact h r hf

theorem RefFieldsRepr.localWrite {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : RefFieldsRepr hp base m)
    (hs : StructHeapRepr hp base frame m) (l : Nat) (hl : l < frame) (w : Word) :
    RefFieldsRepr hp base (writeMachine m l w) := by
  intro s f R r hf
  have hb : frame ≤ (base r.id).val := hs.above r
  change upd m.mem l w _ = _
  rw [upd_other _ _ (by omega)]
  exact h r hf

/-- Different typed member sorts force different labels in the same struct. -/
theorem primitive_reference_fields_ne {s f g : Name} {p : PrimTy} {R : RefTy}
    (hf : lookupBy f (structDef s) = some (.prim p))
    (hg : lookupBy g (structDef s) = some (.ref R)) : f ≠ g := by
  intro he
  subst g
  cases Option.some.inj (hf.symm.trans hg)

/-- Updating a primitive member cannot change a reference-valued member. -/
theorem refField_setPrimitive {H : HTy} (hp : Heap H) {s t f g : Name} {p : PrimTy} {R : RefTy}
    (r : HRef H (.struct s)) (q : HRef H (.struct t))
    (hf : lookupBy f (structDef s) = some (.prim p))
    (hg : lookupBy g (structDef t) = some (.ref R)) (v : p.Denote) :
    (hp.setField r hf v).field q hg = hp.field q hg := by
  by_cases he : r.id = q.id
  · obtain ⟨ht, hr⟩ := HRef.heq_of_id r q he
    cases ht
    cases hr
    simp only [Heap.field, Heap.setField, Heap.get_set_same,
      MFields.get_set_ne _ _ _ _ (primitive_reference_fields_ne hf hg)]
  · simp only [Heap.field, Heap.setField, Heap.get_set_ne hp r q he]

theorem RefFieldsRepr.setPrimitive {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : RefFieldsRepr hp base m)
    (hs : StructHeapRepr hp base frame m) {s f : Name} {p : PrimTy}
    (r : HRef H (.struct s)) (hf : lookupBy f (structDef s) = some (.prim p))
    (v : p.Denote) (w : Word) :
    RefFieldsRepr (hp.setField r hf v) base
      (writeMachine m ((base r.id).val + fieldOffset (structDef s) f) w) := by
  intro t g R q hg
  rw [refField_setPrimitive hp r q hf hg v]
  change upd m.mem _ w _ = _
  by_cases he : r.id = q.id
  · obtain ⟨ht, hr⟩ := HRef.heq_of_id r q he
    cases ht
    cases hr
    have hn := fieldOffset_ne hf hg (primitive_reference_fields_ne hf hg)
    rw [upd_other _ _ (by omega)]
    exact h r hg
  · have hd := hs.separated r q he
    have hfo := fieldOffset_bound hf
    have hgo := fieldOffset_bound hg
    rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
    exact h q hg

theorem RefFieldsRepr.arraySet {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {m : Machine} (h : RefFieldsRepr hp base m) (hd : StructArraySeparated hp base)
    {p : PrimTy} (a : HRef H (.array (.prim p))) (i : Nat) (hi : i < hp.len a .dyn)
    (v : p.Denote) (w : Word) :
    RefFieldsRepr (hp.set a (MObj.setElem .dyn (hp.get a) i v)) base
      (writeMachine m ((base a.id).val + 1 + i) w) := by
  intro s f R r hf
  have he : a.id ≠ r.id := by
    intro he
    have ht := (HRef.heq_of_id a r he).1
    cases ht
  simp only [Heap.field, Heap.get_set_ne hp a r he]
  have ho := fieldOffset_bound hf
  have hs := hd a r
  change upd m.mem _ w _ = _
  rw [upd_other _ _ (by rcases hs with hs | hs <;> omega)]
  exact h r hf

/-- Pointer reads preserve the stack below the returned, identity-indexed word. -/
theorem RefFieldsRepr.readField {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : RefFieldsRepr hp base m)
    (hs : StructHeapRepr hp base frame m) {s f : Name} {R : RefTy}
    (r : HRef H (.struct s)) (hf : lookupBy f (structDef s) = some (.ref R)) :
    run (readFieldCode (fieldOffset (structDef s) f)) (m.push (.val (base r.id))) =
      .ok (m.push (.val (base (hp.field r hf).id))) 0 := by
  have hb : (base r.id).val + fieldOffset (structDef s) f < W := by
    have ho := fieldOffset_bound hf
    have hs := (hs.objects r).space
    omega
  rw [readFieldCode, run_append_ok (fieldAddr_run m _ _)]
  simp only [run, Machine.push, exec_cons_zero, Instr.step, Machine.next,
    wmod_of_lt hb, Out.ok_bind, exec_nil, h r hf]

private theorem allocRef_cases {H : HTy} {T R : RefTy} (hp : Heap H) (o : MObj H T)
    (r : HRef (H ++ [T]) R) :
    (∃ q : HRef H R, q.wk (List.prefix_append H [T]) = r) ∨
      (R = T ∧ HEq r (hp.alloc o).2) := by
  by_cases hi : r.id < H.length
  · let q : HRef H R := ⟨r.id, by simpa only [List.getElem?_append_left hi] using r.get?⟩
    have he : q.wk (List.prefix_append H [T]) = r := by cases r; rfl
    exact .inl ⟨q, he⟩
  · have hr : r.id = H.length := by
      have hl : r.id < (H ++ [T]).length := r.id_lt
      simp only [List.length_append, List.length_singleton] at hl
      omega
    exact .inr (HRef.heq_of_id r (hp.alloc o).2 hr)

/-- Growing by an object without reference fields retains all older pointer words. -/
theorem RefFieldsRepr.alloc {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {m m' : Machine} (h : RefFieldsRepr hp base m) {T : RefTy} (o : MObj H T)
    (cursor : Fin W)
    (hm : ∀ {s f : Name} {R : RefTy} (r : HRef H (.struct s))
      (_hf : lookupBy f (structDef s) = some (.ref R)),
      m'.mem ((base r.id).val + fieldOffset (structDef s) f) =
        m.mem ((base r.id).val + fieldOffset (structDef s) f))
    (hn : ∀ {s f : Name} {R : RefTy}, T = .struct s →
      lookupBy f (structDef s) = some (.ref R) → False) :
    RefFieldsRepr (hp.alloc o).1 (upd base H.length cursor) m' := by
  intro s f R r hf
  rcases allocRef_cases hp o r with ⟨q, rfl⟩ | ⟨ht, _⟩
  · have he : (hp.alloc o).1.field (q.wk (List.prefix_append H [T])) hf =
        (hp.field q hf).wk (List.prefix_append H [T]) := by
      simp only [Heap.field, Heap.keeps_alloc hp o q, MObj.wk, MFields.get_wk]
    rw [he]
    simpa only [MVal.wk, HRef.wk, allocationBase_old base cursor q,
      allocationBase_old base cursor (hp.field q hf)] using (hm q hf).trans (h q hf)
  · exact (hn ht.symm hf).elim

theorem RefFieldsRepr.allocateArray {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine} (h : RefFieldsRepr hp base m)
    (ha : StructAllocatorRepr hp base frame cursor m) (p : PrimTy) (size : Fin W) :
    RefFieldsRepr (hp.alloc (defaultArray p size)).1 (upd base H.length cursor)
      (allocateMachine m cursor size) := by
  apply h.alloc (defaultArray p size) cursor
  · intro s f R r hf
    have ho := fieldOffset_bound hf
    have hl := ha.live r
    have hb := ha.structs.above r
    have hz := ha.arrays.free.reserved
    exact allocateMachine_other m cursor size _ (by omega) (by omega)
  · intro s f R he
    cases he

theorem RefFieldsRepr.allocateStruct {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine} (h : RefFieldsRepr hp base m)
    (ha : StructAllocatorRepr hp base frame cursor m) {s : Name} (o : MObj H (.struct s))
    (hn : ∀ {f : Name} {R : RefTy}, lookupBy f (structDef s) = some (.ref R) → False)
    (n : Nat) :
    RefFieldsRepr (hp.alloc o).1 (upd base H.length cursor)
      (allocateStructMachine m cursor n) := by
  apply h.alloc o cursor
  · intro t f R r hf
    have hb := ha.structs.above r
    have hz := ha.arrays.free.reserved
    exact allocateStructMachine_other m cursor n _ (by omega)
  · intro t f R he hf
    cases he
    exact hn hf

end Solidity.Evm.Memory
