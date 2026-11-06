import Solidity.Evm.MemoryStructCopyAlloc

/-!
# Allocating a struct with initialized reference members

This construction boundary accepts the actual pointer words of the fresh
parent. It preserves every older object, local pointer, interval and zeroed
free region. Children must already exist in the typed heap; recursive default
construction can compose this boundary after its child allocations.
-/
namespace Solidity.Evm.Memory
open Semantics
variable {C : Contract}

private theorem freshOrOld {H : HTy} {R T : RefTy} (hp : Heap H) (o : MObj H R)
    (r : HRef (H ++ [R]) T) :
    (∃ q : HRef H T, q.wk (List.prefix_append H [R]) = r) ∨
      (T = R ∧ HEq r (hp.alloc o).2) := by
  by_cases hi : r.id < H.length
  · let q : HRef H T := ⟨r.id, by simpa only [List.getElem?_append_left hi] using r.get?⟩
    exact .inl ⟨q, by cases r; rfl⟩
  · have hr : r.id = H.length := by
      have hl := r.id_lt
      simp only [List.length_append, List.length_singleton] at hl
      omega
    exact .inr (HRef.heq_of_id r (hp.alloc o).2 hr)

private theorem allocatedArray {H : HTy} {s : Name} {p : PrimTy} (hp : Heap H)
    (o : MObj H (.struct s)) (r : HRef (H ++ [.struct s]) (.array (.prim p))) :
    ∃ q : HRef H (.array (.prim p)), q.wk (List.prefix_append H [.struct s]) = r := by
  rcases freshOrOld hp o r with h | ⟨ht, _⟩
  · exact h
  · cases ht

private theorem oldLength {H : HTy} {s : Name} {p : PrimTy} (hp : Heap H)
    (o : MObj H (.struct s)) (a : HRef H (.array (.prim p))) :
    (hp.alloc o).1.len (a.wk (List.prefix_append H [.struct s])) .dyn = hp.len a .dyn := by
  simp only [Heap.len, Heap.keeps_alloc hp o a, MObj.elems_dyn, MObj.wk, List.length_map]

/-- A fresh parent may contain references to any already represented children.
The new object's pointer words must be initialized before the full relation holds. -/
theorem RefFieldsRepr.allocInitialized {H : HTy} {hp : Heap H}
    {base : Nat → Fin W} {m m' : Machine} (h : RefFieldsRepr hp base m)
    {s : Name} (o : MObj H (.struct s)) (cursor : Fin W)
    (hold : ∀ {t f : Name} {R : RefTy} (r : HRef H (.struct t))
      (_hf : lookupBy f (structDef t) = some (.ref R)),
      m'.mem ((base r.id).val + fieldOffset (structDef t) f) =
        m.mem ((base r.id).val + fieldOffset (structDef t) f))
    (hfresh : ∀ {f : Name} {R : RefTy}
      (hf : lookupBy f (structDef s) = some (.ref R)),
      m'.mem (cursor.val + fieldOffset (structDef s) f) =
        .val (base (MFields.get (structDef s) o hf).id)) :
    RefFieldsRepr (hp.alloc o).1 (upd base H.length cursor) m' := by
  intro t f R r hf
  rcases freshOrOld hp o r with ⟨q, rfl⟩ | ⟨ht, he⟩
  · have he : (hp.alloc o).1.field (q.wk (List.prefix_append H [.struct s])) hf =
        (hp.field q hf).wk (List.prefix_append H [.struct s]) := by
      simp only [Heap.field, Heap.keeps_alloc hp o q, MObj.wk, MFields.get_wk]
    rw [he]
    simpa only [MVal.wk, HRef.wk, allocationBase_old base cursor q,
      allocationBase_old base cursor (hp.field q hf)] using (hold q hf).trans (h q hf)
  · cases ht
    cases he
    change m'.mem ((upd base H.length cursor H.length).val + fieldOffset (structDef s) f) =
      .val (upd base H.length cursor ((hp.alloc o).1.field (hp.alloc o).2 hf).id)
    have hv : (hp.alloc o).1.field (hp.alloc o).2 hf =
        (MFields.get (structDef s) o hf).wk (List.prefix_append H [.struct s]) := by
      simp only [Heap.field, Heap.get_alloc, MObj.wk, MFields.get_wk]
    rw [hv]
    change m'.mem ((upd base H.length cursor H.length).val + fieldOffset (structDef s) f) =
      .val (upd base H.length cursor (MFields.get (structDef s) o hf).id)
    rw [upd_same, allocationBase_old base cursor (MFields.get (structDef s) o hf)]
    exact hfresh hf

/-- Initializing a fresh reference-bearing parent preserves the complete state and ownership. -/
theorem StateRepr.reserveInitializedStruct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor next : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : StructAllocatorRepr σ.heap base frame cursor m)
    (hb : 0 < b) {s : Name} (o : MObj σ.H (.struct s))
    (hn : cursor.val + (structDef s).length ≤ next.val)
    (mem : Nat → Word)
    (hold : ∀ addr, 0 < addr → addr < cursor.val → mem addr = m.mem addr)
    (hcell : mem 0 = .val next)
    (hzero : ∀ addr, next.val ≤ addr → mem addr = w[0])
    (hrefs : ∀ {f : Name} {R : RefTy}
      (hf : lookupBy f (structDef s) = some (.ref R)),
      mem (cursor.val + fieldOffset (structDef s) f) =
        .val (base (MFields.get (structDef s) o hf).id))
    (hfresh : StructRepr (σ.heap.alloc o).1 (σ.heap.alloc o).2 cursor {m with mem := mem}) :
    StateRepr L b frame F (σ.alloc o).1 (upd base σ.H.length cursor) {m with mem := mem} ∧
      StructAllocatorRepr (σ.alloc o).1.heap (upd base σ.H.length cursor) frame next {m with mem := mem} := by
  have hz : 0 < frame := ha.arrays.free.reserved
  have hc : frame ≤ cursor.val := ha.arrays.free.above
  have hlocals : b + Γ.length ≤ frame := h.locals
  have ha' : HeapRepr (σ.heap.alloc o).1 (upd base σ.H.length cursor) frame {m with mem := mem} := by
    refine ⟨?_, ?_, ?_⟩
    · intro p a
      obtain ⟨a, rfl⟩ := allocatedArray σ.heap o a
      simp only [HRef.wk, allocationBase_old base cursor a]
      refine ArrayRepr.keeps (hp := σ.heap) ?_ (List.prefix_append σ.H [.struct s])
        (Heap.keeps_alloc σ.heap o)
      have hr := ha.arrays.heap.arrays a
      have hl := ha.arrays.live a
      have hab := ha.arrays.heap.above a
      refine ⟨hr.space, ?_, ?_⟩
      · change mem (base a.id).val = _
        rw [hold _ (by omega) (by omega)]
        exact hr.length
      · intro i v hv
        have hi : i < σ.heap.len a .dyn := (List.getElem?_eq_some_iff.mp hv).1
        change ReprV p v (mem ((base a.id).val + 1 + i))
        rw [hold _ (by omega) (by omega)]
        exact hr.elements i v hv
    · intro p a
      obtain ⟨a, rfl⟩ := allocatedArray σ.heap o a
      simpa only [HRef.wk, allocationBase_old base cursor a] using ha.arrays.heap.above a
    · intro p q a d hne
      obtain ⟨a, rfl⟩ := allocatedArray σ.heap o a
      obtain ⟨d, rfl⟩ := allocatedArray σ.heap o d
      rw [oldLength σ.heap o a, oldLength σ.heap o d]
      simpa only [HRef.wk, allocationBase_old base cursor a, allocationBase_old base cursor d]
        using ha.arrays.heap.separated a d hne
  have hs' : StructHeapRepr (σ.heap.alloc o).1 (upd base σ.H.length cursor) frame {m with mem := mem} := by
    refine ⟨?_, ?_, ?_⟩
    · intro t r
      rcases freshOrOld σ.heap o r with ⟨r, rfl⟩ | ⟨ht, he⟩
      · simp only [HRef.wk, allocationBase_old base cursor r]
        refine StructRepr.keeps (hp := σ.heap) ?_ (List.prefix_append σ.H [.struct s])
          (Heap.keeps_alloc σ.heap o)
        refine ⟨(ha.structs.objects r).space, ?_⟩
        intro f p hf
        have ho := fieldOffset_bound hf
        have hl := ha.live r
        have hab := ha.structs.above r
        change ReprV p (σ.heap.field r hf) (mem ((base r.id).val + fieldOffset (structDef t) f))
        rw [hold _ (by omega) (by omega)]
        exact (ha.structs.objects r).fields hf
      · cases ht
        cases he
        simpa only [Heap.alloc, upd_same] using hfresh
    · intro t r
      rcases freshOrOld σ.heap o r with ⟨r, rfl⟩ | ⟨ht, he⟩
      · simpa only [HRef.wk, allocationBase_old base cursor r] using ha.structs.above r
      · cases ht; cases he
        simpa only [Heap.alloc, upd_same] using hc
    · intro t u r q hne
      rcases freshOrOld σ.heap o r with ⟨r, rfl⟩ | ⟨ht, he⟩
      · rcases freshOrOld σ.heap o q with ⟨q, rfl⟩ | ⟨ht, he⟩
        · simpa only [HRef.wk, allocationBase_old base cursor r, allocationBase_old base cursor q]
            using ha.structs.separated r q hne
        · cases ht; cases he
          exact .inl (by simpa only [HRef.wk, Heap.alloc, allocationBase_old base cursor r, upd_same] using ha.live r)
      · cases ht; cases he
        rcases freshOrOld σ.heap o q with ⟨q, rfl⟩ | ⟨ht, he⟩
        · exact .inr (by simpa only [HRef.wk, Heap.alloc, allocationBase_old base cursor q, upd_same] using ha.live q)
        · cases ht; cases he; exact (hne rfl).elim
  have hx : StructArraySeparated (σ.heap.alloc o).1 (upd base σ.H.length cursor) :=
    StructArraySeparated.allocStruct ha.separated ha.arrays.live o
  refine ⟨⟨?_, ha', ?_, h.locals, hs', hx, ?_⟩,
    ⟨⟨ha', ⟨hz, by omega, hcell, hzero⟩, ?_⟩, hs', hx, ?_⟩⟩
  · have hm : ∀ l, b ≤ l → l < b + Γ.length → mem (cell l) = m.mem (cell l) := by
      intro l hl hu
      exact hold l (by omega) (by omega)
    have hcore := (h.core.congrMem hm).congrLook
      (fun i => Look.ofTEnv_wk (List.prefix_append σ.H [.struct s]) σ.env i)
    exact ⟨hcore.store, hcore.vals, hcore.aliases, hcore.net, hcore.netSelf, hcore.bound,
      hcore.fragile, hcore.env, hcore.funds, hcore.oracle⟩
  · intro R i
    obtain ⟨r, hr, hm⟩ := h.pointers i
    refine ⟨r.wk (List.prefix_append _ _), ?_, ?_⟩
    · change TEnv.get i (TEnv.wk _ Γ σ.env) = _
      rw [TEnv.get_wk, hr]; rfl
    · change mem (cell (lvl b i)) = .val (upd base σ.H.length cursor r.id)
      change mem (lvl b i) = .val (upd base σ.H.length cursor r.id)
      rw [hold _ (by have hi := le_lvl b i; omega)
        (by have hi := lvl_lt b i; omega), allocationBase_old base cursor r]
      exact hm
  · apply RefFieldsRepr.allocInitialized h.refs o cursor
    · intro t f R r hf
      have ho := fieldOffset_bound hf
      have hl := ha.live r
      have hab := ha.structs.above r
      exact hold _ (by omega) (by omega)
    · exact hrefs
  · intro p a
    obtain ⟨a, rfl⟩ := allocatedArray σ.heap o a
    change (upd base σ.H.length cursor (a.wk (List.prefix_append _ _)).id).val + 1 +
      (σ.heap.alloc o).1.len (a.wk (List.prefix_append _ _)) .dyn ≤ next.val
    rw [oldLength σ.heap o a]
    simp only [HRef.wk, allocationBase_old base cursor a]
    exact Nat.le_trans (ha.arrays.live a) (by omega)
  · intro t r
    rcases freshOrOld σ.heap o r with ⟨r, rfl⟩ | ⟨ht, he⟩
    · simp only [HRef.wk, allocationBase_old base cursor r]
      exact Nat.le_trans (ha.live r) (by omega)
    · cases ht; cases he
      simpa only [Heap.alloc, upd_same] using hn

end Solidity.Evm.Memory
