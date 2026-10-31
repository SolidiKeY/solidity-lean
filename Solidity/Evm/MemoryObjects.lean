import Solidity.Evm.MemoryRefArrayState

/-!
# Typed ownership of every represented memory object

Dynamic arrays have a header; fixed arrays are headerless. Both keep one
word per element, interpreting a reference word by its actual typed child
identity. Positive reservations also cover empty fixed arrays and structs.
This additive relation is for compiler paths that need these layouts; the
existing primitive and nonallocating reference-array inputs are unchanged.
-/
namespace Solidity.Evm.Memory.Objects
open Semantics

/-- A represented word retains its source type, including a reference endpoint. -/
def ValueRepr {H : HTy} (base : Nat → Fin W) : (T : Ty) → MVal H T → Word → Prop
  | .prim p, v, w => ReprV p v w
  | .ref _, v, w => w = .val (base v.id)

/-- Only dynamic arrays have a length cell. The recursor generalizes both indices. -/
def header {A : RefTy} {E : Ty} (a : ArrTy A E) : Nat :=
  @ArrTy.casesOn (fun _ _ _ => Nat) A E a (fun {_} => 1) (fun {_} {_} => 0)

/-- Every live object reserves a positive interval, including empty objects. -/
def cells {H : HTy} (hp : Heap H) : {R : RefTy} → HRef H R → Nat
  | .array _, r => 1 + hp.len r .dyn
  | .fixed _ n, _ => max 1 n
  | .struct s, _ => max 1 (structDef s).length
  | .mapping .., _ => 1

theorem cells_pos {H : HTy} (hp : Heap H) {R : RefTy} (r : HRef H R) :
    0 < cells hp r := by
  cases R <;> simp only [cells] <;> omega

theorem header_len_le_cells {H : HTy} (hp : Heap H) {A : RefTy} {E : Ty}
    (a : ArrTy A E) (r : HRef H A) : header a + hp.len r a ≤ cells hp r := by
  cases a with
  | dyn => simp only [header, cells]; omega
  | @fixed E n =>
    have hn : hp.len r .fixed = n := by
      change (MObj.elems .fixed (hp.get r)).length = n
      rw [MObj.elems_fixed]
      exact (hp.get r).property
    simp only [header, cells, hn, Nat.zero_add]
    exact Nat.le_max_right _ _

/-- Ownership does not depend on the machine stack or on a choice of alias. -/
structure Ownership {H : HTy} (hp : Heap H) (base : Nat → Fin W) (frame : Nat) : Prop where
  above : ∀ {R : RefTy} (r : HRef H R), frame ≤ (base r.id).val
  space : ∀ {R : RefTy} (r : HRef H R), (base r.id).val + cells hp r ≤ W
  separated : ∀ {R Q : RefTy} (r : HRef H R) (q : HRef H Q), r.id ≠ q.id →
    (base r.id).val + cells hp r ≤ (base q.id).val ∨
    (base q.id).val + cells hp q ≤ (base r.id).val

/-- Dynamic and fixed arrays share typed element words, but not their headers. -/
structure ArrayRepr {H : HTy} {A : RefTy} {E : Ty} (hp : Heap H)
    (r : HRef H A) (a : ArrTy A E) (base : Nat → Fin W) (m : Machine) : Prop where
  space : (base r.id).val + cells hp r ≤ W
  length : header a = 1 → m.mem (base r.id).val = .val (wmod (hp.len r a))
  elements : ∀ i v, (MObj.elems a (hp.get r))[i]? = some v →
    ValueRepr base E v (m.mem ((base r.id).val + header a + i))

theorem ArrayRepr.stack {H : HTy} {A : RefTy} {E : Ty} {hp : Heap H}
    {r : HRef H A} {a : ArrTy A E} {base : Nat → Fin W} {m : Machine}
    (h : ArrayRepr hp r a base m) (st : List Word) :
    ArrayRepr hp r a base {m with stack := st} := ⟨h.space, h.length, h.elements⟩

theorem ArrayRepr.primitive {H : HTy} {p : PrimTy} {hp : Heap H}
    {r : HRef H (.array (.prim p))} {base : Nat → Fin W} {m : Machine}
    (h : ArrayRepr hp r .dyn base m) :
    Solidity.Evm.Memory.ArrayRepr hp r (base r.id) m := by
  refine ⟨?_, h.length rfl, h.elements⟩
  have hs := h.space
  simp only [cells] at hs
  omega

theorem ArrayRepr.reference {H : HTy} {R : RefTy} {hp : Heap H}
    {r : HRef H (.array (.ref R))} {base : Nat → Fin W} {m : Machine}
    (h : ArrayRepr hp r .dyn base m) : RefArrayRepr hp r base m := by
  refine ⟨?_, h.length rfl, h.elements⟩
  have hs := h.space
  simp only [cells] at hs
  omega

/-- The old struct relations are reused alongside both kinds of arrays. -/
structure HeapRepr {H : HTy} (hp : Heap H) (base : Nat → Fin W)
    (frame : Nat) (m : Machine) : Prop where
  owner : Ownership hp base frame
  arrays : ∀ {A : RefTy} {E : Ty} (a : ArrTy A E) (r : HRef H A), ArrayRepr hp r a base m
  structs : ∀ {s : Name} (r : HRef H (.struct s)), StructRepr hp r (base r.id) m
  refs : RefFieldsRepr hp base m

theorem HeapRepr.primitive {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : HeapRepr hp base frame m) :
    Solidity.Evm.Memory.HeapRepr hp base frame m := by
  refine ⟨fun r => (h.arrays .dyn r).primitive, h.owner.above, ?_⟩
  intro p q r s hn
  simpa only [cells, Nat.add_assoc] using h.owner.separated r s hn

theorem HeapRepr.structHeap {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : HeapRepr hp base frame m) :
    StructHeapRepr hp base frame m := by
  refine ⟨h.structs, h.owner.above, ?_⟩
  intro s t r q hn
  have hd := h.owner.separated r q hn
  have hs : (structDef s).length ≤ max 1 (structDef s).length := Nat.le_max_right _ _
  have ht : (structDef t).length ≤ max 1 (structDef t).length := Nat.le_max_right _ _
  simp only [cells] at hd
  rcases hd with hd | hd <;> omega

theorem HeapRepr.referenceArrays {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : HeapRepr hp base frame m) :
    RefArrayHeapRepr hp base frame m := by
  refine ⟨fun r => (h.arrays .dyn r).reference, h.owner.above, ?_, ?_, ?_⟩
  · intro R Q r q hn
    simpa only [cells, Nat.add_assoc] using h.owner.separated r q hn
  · intro R p r q
    have hn : r.id ≠ q.id := by intro he; cases (HRef.heq_of_id r q he).1
    simpa only [cells, Nat.add_assoc] using h.owner.separated r q hn
  · intro R s r q
    have hn : r.id ≠ q.id := by intro he; cases (HRef.heq_of_id r q he).1
    have hd := h.owner.separated r q hn
    have hs : (structDef s).length ≤ max 1 (structDef s).length := Nat.le_max_right _ _
    simp only [cells] at hd
    rcases hd with hd | hd <;> omega

theorem HeapRepr.structArraySeparated {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : HeapRepr hp base frame m) :
    StructArraySeparated hp base := by
  intro p s r q
  have hn : r.id ≠ q.id := by intro he; cases (HRef.heq_of_id r q he).1
  have hd := h.owner.separated r q hn
  have hs : (structDef s).length ≤ max 1 (structDef s).length := Nat.le_max_right _ _
  simp only [cells] at hd
  rcases hd with hd | hd <;> omega

theorem HeapRepr.stack {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : HeapRepr hp base frame m) (st : List Word) :
    HeapRepr hp base frame {m with stack := st} :=
  ⟨h.owner, fun a r => (h.arrays a r).stack st, fun r => (h.structs r).stack st,
    RefFieldsRepr.mem_eq h.refs rfl⟩

/-- Local stores cannot touch any object, including headerless fixed arrays. -/
theorem HeapRepr.localWrite {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m : Machine} (h : HeapRepr hp base frame m)
    (l : Nat) (hl : l < frame) (w : Word) :
    HeapRepr hp base frame (writeMachine m l w) := by
  refine ⟨h.owner, ?_, ?_, RefFieldsRepr.localWrite h.refs h.structHeap l hl w⟩
  · intro A E a r
    have hb := h.owner.above r
    refine ⟨(h.arrays a r).space, ?_, ?_⟩
    · intro ha
      exact (upd_other _ _ (by omega)).trans ((h.arrays a r).length ha)
    · intro i v hv
      change ValueRepr base E v (upd m.mem l w _)
      rw [upd_other _ _ (by omega)]
      exact (h.arrays a r).elements i v hv
  · intro s r
    have hb := h.owner.above r
    refine ⟨(h.structs r).space, ?_⟩
    intro f p hf
    change ReprV p _ (upd m.mem l w _)
    rw [upd_other _ _ (by omega)]
    exact (h.structs r).fields hf

variable {C : Contract}

/-- A stronger, additive input for newly compiled object layouts. -/
structure StateRepr (L b frame : Nat) {Γ : Ctx} (F : Frag Γ)
    (σ : State C Γ) (base : Nat → Fin W) (m : Machine) : Prop where
  core : Sim C L b F σ m
  heap : HeapRepr σ.heap base frame m
  pointers : PointerRepr σ base b m
  locals : b + Γ.length ≤ frame

theorem StateRepr.legacy {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) :
    Solidity.Evm.Memory.StateRepr L b frame F σ base m :=
  ⟨h.core, h.heap.primitive, h.pointers, h.locals, h.heap.structHeap,
    h.heap.structArraySeparated, h.heap.refs⟩

theorem StateRepr.reference {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) : RefArrayStateRepr L b frame F σ base m :=
  ⟨h.legacy, h.heap.referenceArrays⟩

theorem StateRepr.push {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) (w : Word) :
    StateRepr L b frame F σ base (m.push w) :=
  ⟨h.core.push w, h.heap.stack _, h.pointers, h.locals⟩

end Solidity.Evm.Memory.Objects
