import Solidity.Evm.MemoryStruct
import Solidity.Evm.MemoryHeap

/-!
# Framing primitive struct fields

All aliases use a single address map. Struct intervals reserve every member
cell, so primitive writes preserve other structs and reserved local frames.
The cross-relation separates these intervals from primitive dynamic arrays.
It allows the struct and array simulation layers to share one target heap.
-/
namespace Solidity.Evm.Memory
open Semantics

structure StructHeapRepr {H : HTy} (hp : Heap H) (base : Nat → Fin W)
    (frame : Nat) (m : Machine) : Prop where
  objects : ∀ {s : Name} (r : HRef H (.struct s)), StructRepr hp r (base r.id) m
  above : ∀ {s : Name} (r : HRef H (.struct s)), frame ≤ (base r.id).val
  separated : ∀ {s t : Name} (r : HRef H (.struct s)) (q : HRef H (.struct t)), r.id ≠ q.id →
    (base r.id).val + (structDef s).length ≤ (base q.id).val ∨
    (base q.id).val + (structDef t).length ≤ (base r.id).val

/-- Array headers and all live elements lie outside every struct interval. -/
def StructArraySeparated {H : HTy} (hp : Heap H) (base : Nat → Fin W) : Prop :=
  ∀ {p : PrimTy} {s : Name} (a : HRef H (.array (.prim p))) (r : HRef H (.struct s)),
    (base a.id).val + 1 + hp.len a .dyn ≤ (base r.id).val ∨
    (base r.id).val + (structDef s).length ≤ (base a.id).val

theorem StructHeapRepr.stack {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : StructHeapRepr hp base frame m) (st : List Word) :
    StructHeapRepr hp base frame {m with stack := st} :=
  ⟨fun r => (h.objects r).stack st, h.above, h.separated⟩

theorem StructHeapRepr.write_below {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : StructHeapRepr hp base frame m)
    {s f : Name} {p : PrimTy} (r : HRef H (.struct s))
    (_hf : lookupBy f (structDef s) = some (.prim p)) (w : Word) (l : Nat) (hl : l < frame) :
    (writeMachine m ((base r.id).val + fieldOffset (structDef s) f) w).mem l = m.mem l := by
  have hb : frame ≤ (base r.id).val := h.above r
  exact upd_other _ _ (by omega)

/-- Local writes preserve every represented struct member. -/
theorem StructHeapRepr.localWrite {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : StructHeapRepr hp base frame m)
    (l : Nat) (hl : l < frame) (w : Word) :
    StructHeapRepr hp base frame (writeMachine m l w) := by
  refine ⟨?_, h.above, h.separated⟩
  intro s r
  refine ⟨(h.objects r).space, ?_⟩
  intro f p hf
  have hb : frame ≤ (base r.id).val := h.above r
  change ReprV p (hp.field r hf) (upd m.mem l w ((base r.id).val + fieldOffset (structDef s) f))
  rw [upd_other _ _ (by omega)]
  exact (h.objects r).fields hf

/-- Aliases observe the write; distinct represented structs retain their fields. -/
theorem StructHeapRepr.set {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : StructHeapRepr hp base frame m)
    {s f : Name} {p : PrimTy} (r : HRef H (.struct s))
    (hf : lookupBy f (structDef s) = some (.prim p))
    (v : p.Denote) (w : Word) (hw : ReprV p v w) :
    StructHeapRepr (hp.setField r hf v) base frame
      (writeMachine m ((base r.id).val + fieldOffset (structDef s) f) w) := by
  refine ⟨?_, h.above, h.separated⟩
  intro t q
  by_cases he : r.id = q.id
  · obtain ⟨ht, hr⟩ := HRef.heq_of_id r q he
    cases ht
    cases hr
    exact (h.objects r).set hf v w hw
  · refine ⟨(h.objects q).space, ?_⟩
    intro g u hg
    have hd := h.separated r q he
    have hfo : fieldOffset (structDef s) f < (structDef s).length := fieldOffset_bound hf
    have hgo : fieldOffset (structDef t) g < (structDef t).length := fieldOffset_bound hg
    simp only [Heap.field, Heap.setField, Heap.get_set_ne hp r q he, writeMachine]
    rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
    exact (h.objects q).fields hg

/-- A struct field write preserves an array in a disjoint interval. -/
theorem ArrayRepr.structWrite {H : HTy} {hp : Heap H} {p q : PrimTy} {s f : Name}
    {a : HRef H (.array (.prim p))} {r : HRef H (.struct s)}
    {ab rb : Fin W} {m : Machine} (h : ArrayRepr hp a ab m)
    (hf : lookupBy f (structDef s) = some (.prim q))
    (hd : ab.val + 1 + hp.len a .dyn ≤ rb.val ∨
      rb.val + (structDef s).length ≤ ab.val) (v : q.Denote) (w : Word) :
    ArrayRepr (hp.setField r hf v) a ab
      (writeMachine m (rb.val + fieldOffset (structDef s) f) w) := by
  have he : r.id ≠ a.id := by
    intro he
    have ht : RefTy.struct s = RefTy.array (.prim p) := (HRef.heq_of_id r a he).1
    cases ht
  have ho : fieldOffset (structDef s) f < (structDef s).length := fieldOffset_bound hf
  constructor
  · simpa only [Heap.len, Heap.setField, Heap.get_set_ne hp r a he] using h.space
  · change upd m.mem (rb.val + fieldOffset (structDef s) f) w ab.val = _
    rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
    simpa only [Heap.len, Heap.setField, Heap.get_set_ne hp r a he] using h.length
  · intro i x hx
    rw [Heap.setField, Heap.get_set_ne hp r a he] at hx
    have hi : i < hp.len a .dyn := (List.getElem?_eq_some_iff.mp hx).1
    change ReprV p x (upd m.mem (rb.val + fieldOffset (structDef s) f) w (ab.val + 1 + i))
    rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
    exact h.elements i x hx

/-- An array element write preserves a struct in a disjoint interval. -/
theorem StructRepr.arrayWrite {H : HTy} {hp : Heap H} {p : PrimTy} {s : Name}
    {a : HRef H (.array (.prim p))} {r : HRef H (.struct s)}
    {ab rb : Fin W} {m : Machine} (h : StructRepr hp r rb m)
    (hd : ab.val + 1 + hp.len a .dyn ≤ rb.val ∨
      rb.val + (structDef s).length ≤ ab.val)
    (i : Nat) (hi : i < hp.len a .dyn) (v : p.Denote) (w : Word) :
    StructRepr (hp.set a (MObj.setElem .dyn (hp.get a) i v)) r rb
      (writeMachine m (ab.val + 1 + i) w) := by
  have he : a.id ≠ r.id := by
    intro he
    have ht : RefTy.array (.prim p) = RefTy.struct s := (HRef.heq_of_id a r he).1
    cases ht
  refine ⟨h.space, ?_⟩
  intro f q hf
  have ho : fieldOffset (structDef s) f < (structDef s).length := fieldOffset_bound hf
  simp only [Heap.field, Heap.get_set_ne hp a r he, writeMachine]
  rw [upd_other _ _ (by rcases hd with hd | hd <;> omega)]
  exact h.fields hf

theorem arrayLen_setField {H : HTy} {hp : Heap H} {p q : PrimTy} {s f : Name}
    (a : HRef H (.array (.prim p))) (r : HRef H (.struct s))
    (hf : lookupBy f (structDef s) = some (.prim q)) (v : q.Denote) :
    (hp.setField r hf v).len a .dyn = hp.len a .dyn := by
  have he : r.id ≠ a.id := by
    intro he
    have ht : RefTy.struct s = RefTy.array (.prim p) := (HRef.heq_of_id r a he).1
    cases ht
  simp only [Heap.len, Heap.setField, Heap.get_set_ne hp r a he]

theorem HeapRepr.structWrite {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : HeapRepr hp base frame m)
    (hd : StructArraySeparated hp base) {s f : Name} {p : PrimTy}
    (r : HRef H (.struct s)) (hf : lookupBy f (structDef s) = some (.prim p))
    (v : p.Denote) (w : Word) :
    HeapRepr (hp.setField r hf v) base frame
      (writeMachine m ((base r.id).val + fieldOffset (structDef s) f) w) := by
  refine ⟨fun a => (h.arrays a).structWrite hf (hd a r) v w, h.above, ?_⟩
  intro q u a b hn
  simpa only [arrayLen_setField] using h.separated a b hn

theorem StructHeapRepr.arraySet {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : StructHeapRepr hp base frame m)
    (hd : StructArraySeparated hp base) {p : PrimTy} (a : HRef H (.array (.prim p)))
    (i : Nat) (hi : i < hp.len a .dyn) (v : p.Denote) (w : Word) :
    StructHeapRepr (hp.set a (MObj.setElem .dyn (hp.get a) i v)) base frame
      (writeMachine m ((base a.id).val + 1 + i) w) :=
  ⟨fun r => (h.objects r).arrayWrite (hd a r) i hi v w, h.above, h.separated⟩

theorem StructArraySeparated.setStruct {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    (h : StructArraySeparated hp base) {s f : Name} {p : PrimTy}
    (r : HRef H (.struct s)) (hf : lookupBy f (structDef s) = some (.prim p))
    (v : p.Denote) : StructArraySeparated (hp.setField r hf v) base := by
  intro q t a b
  simpa only [arrayLen_setField] using h a b

theorem StructArraySeparated.setArray {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    (h : StructArraySeparated hp base) {p : PrimTy} (a : HRef H (.array (.prim p)))
    (i : Nat) (v : p.Denote) :
    StructArraySeparated (hp.set a (MObj.setElem .dyn (hp.get a) i v)) base := by
  intro q t b r
  simpa only [arrayLen_set] using h b r

end Solidity.Evm.Memory
