import Solidity.Evm.MemoryStructAlloc

/-!
# Allocation with live structs

Both the primitive-array allocator and a headerless struct allocator preserve
the combined ownership relation. Growing the typed heap retains old field
values and addresses; live-interval bounds keep the allocation writes outside
old objects. Struct allocation interprets primitive defaults and reserves
reference member cells; source-level recursive construction remains separate.
-/
namespace Solidity.Evm.Memory
open Semantics

/-- Every identity after one typed allocation is either old or its fresh one. -/
private theorem allocRef_split {H : HTy} {R T : RefTy} (hp : Heap H) (o : MObj H R)
    (r : HRef (H ++ [R]) T) :
    (∃ q : HRef H T, q.wk (List.prefix_append H [R]) = r) ∨
      (T = R ∧ HEq r (hp.alloc o).2) := by
  by_cases hi : r.id < H.length
  · let q : HRef H T := ⟨r.id, by simpa only [List.getElem?_append_left hi] using r.get?⟩
    have he : q.wk (List.prefix_append H [R]) = r := by cases r; rfl
    exact .inl ⟨q, he⟩
  · have hr : r.id = H.length := by
      have hl : r.id < (H ++ [R]).length := r.id_lt
      simp only [List.length_append, List.length_singleton] at hl
      omega
    exact .inr (HRef.heq_of_id r (hp.alloc o).2 hr)

/-- Weakening a heap preserves its older primitive struct fields. -/
theorem StructRepr.keeps {H H' : HTy} {hp : Heap H} {hp' : Heap H'}
    {s : Name} {r : HRef H (.struct s)} {base : Fin W} {m : Machine}
    (h : StructRepr hp r base m) (e : H <+: H') (hk : Heap.Keeps e hp hp') :
    StructRepr hp' (r.wk e) base m := by
  refine ⟨h.space, ?_⟩
  intro f p hf
  simpa only [Heap.field, hk r, MObj.wk, MFields.get_wk, MVal.wk] using h.fields hf

/-- An allocation cannot introduce an identity at a different reference type. -/
private theorem beforeAlloc {H : HTy} {R T : RefTy} (hp : Heap H) (o : MObj H R)
    (hne : T ≠ R) (r : HRef (H ++ [R]) T) :
    ∃ q : HRef H T, q.wk (List.prefix_append H [R]) = r := by
  rcases allocRef_split hp o r with h | ⟨ht, _⟩
  · exact h
  · exact (hne ht).elim

/-- Array allocation's two writes leave all owned struct fields unchanged. -/
theorem StructHeapRepr.allocateArray {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : StructHeapRepr hp base frame m) (hf : FreeMemory frame cursor m)
    (hlive : ∀ {s : Name} (r : HRef H (.struct s)),
      (base r.id).val + (structDef s).length ≤ cursor.val) (size : Fin W) :
    StructHeapRepr hp base frame (allocateMachine m cursor size) := by
  refine ⟨?_, h.above, h.separated⟩
  intro s r
  refine ⟨(h.objects r).space, ?_⟩
  intro f p hfield
  have ho : fieldOffset (structDef s) f < (structDef s).length := fieldOffset_bound hfield
  have he : (base r.id).val + (structDef s).length ≤ cursor.val := hlive r
  have hb : frame ≤ (base r.id).val := h.above r
  have hz : 0 < frame := hf.reserved
  rw [allocateMachine_other m cursor size _ (by omega) (by omega)]
  exact (h.objects r).fields hfield

/-- Growing by an array retains exactly the older struct identities and bases. -/
theorem StructHeapRepr.allocArray {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : StructHeapRepr hp base frame m) (hf : FreeMemory frame cursor m)
    (hlive : ∀ {s : Name} (r : HRef H (.struct s)),
      (base r.id).val + (structDef s).length ≤ cursor.val)
    (p : PrimTy) (size : Fin W) :
    StructHeapRepr (hp.alloc (defaultArray p size)).1 (upd base H.length cursor)
      frame (allocateMachine m cursor size) := by
  have hold {s : Name} (r : HRef (H ++ [.array (.prim p)]) (.struct s)) :
      ∃ q : HRef H (.struct s), q.wk (List.prefix_append H [.array (.prim p)]) = r :=
    beforeAlloc hp (defaultArray p size) (by intro he; cases he) r
  refine ⟨?_, ?_, ?_⟩
  · intro s r
    obtain ⟨q, rfl⟩ := hold r
    simp only [HRef.wk, allocationBase_old base cursor q]
    exact ((h.allocateArray hf hlive size).objects q).keeps _ (Heap.keeps_alloc hp _)
  · intro s r
    obtain ⟨q, rfl⟩ := hold r
    simp only [HRef.wk, allocationBase_old base cursor q]
    exact h.above q
  · intro s t r q hne
    obtain ⟨r, rfl⟩ := hold r
    obtain ⟨q, rfl⟩ := hold q
    simpa only [HRef.wk, allocationBase_old base cursor r, allocationBase_old base cursor q]
      using h.separated r q hne

/-- The fresh array is above every live struct; old cross-separation remains. -/
theorem StructArraySeparated.allocArray {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {cursor : Fin W} (h : StructArraySeparated hp base)
    (hlive : ∀ {s : Name} (r : HRef H (.struct s)),
      (base r.id).val + (structDef s).length ≤ cursor.val) (p : PrimTy) (size : Fin W) :
    StructArraySeparated (hp.alloc (defaultArray p size)).1 (upd base H.length cursor) := by
  intro q s a r
  obtain ⟨r, rfl⟩ := beforeAlloc hp (defaultArray p size) (by intro he; cases he) r
  rcases allocRef_split hp (defaultArray p size) a with ⟨a, rfl⟩ | ⟨ht, he⟩
  · have hlen : (hp.alloc (defaultArray p size)).1.len
        (a.wk (List.prefix_append _ _)) .dyn = hp.len a .dyn := by
      simp only [Heap.len, Heap.keeps_alloc hp (defaultArray p size) a,
        MObj.elems_dyn, MObj.wk, List.length_map]
    rw [hlen]
    simpa only [HRef.wk, allocationBase_old base cursor a, allocationBase_old base cursor r]
      using h a r
  · cases ht
    cases he
    apply Or.inr
    simpa only [HRef.wk, Heap.alloc, allocationBase_old base cursor r, upd_same]
      using hlive r

/-- Array allocation preserves the combined ownership invariant. -/
theorem StructAllocatorRepr.allocateArray {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : StructAllocatorRepr hp base frame cursor m) (p : PrimTy) (size : Fin W)
    (hspace : cursor.val + size.val + 1 < W) :
    StructAllocatorRepr (hp.alloc (defaultArray p size)).1 (upd base H.length cursor)
      frame ⟨cursor.val + size.val + 1, hspace⟩ (allocateMachine m cursor size) := by
  refine ⟨h.arrays.allocate p size hspace,
    h.structs.allocArray h.arrays.free h.live p size,
    StructArraySeparated.allocArray h.separated h.live p size, ?_⟩
  intro s r
  obtain ⟨q, rfl⟩ := beforeAlloc hp (defaultArray p size) (by intro he; cases he) r
  simp only [HRef.wk, allocationBase_old base cursor q]
  have hl : (base q.id).val + (structDef s).length ≤ cursor.val := h.live q
  omega

/-- Reserve member cells without an array header, returning the old cursor. -/
def allocateStructCode (size : Nat) : List Instr :=
  [.mload 0, .dup 1, .push (.val (wmod size)), .add, .mstore 0]

def allocateStructMachine (m : Machine) (cursor : Fin W) (size : Nat) : Machine :=
  writeMachine m 0 (.val (wmod (cursor.val + size)))

theorem allocateStruct_run (m : Machine) (cursor : Fin W) (size : Nat)
    (hc : m.mem 0 = .val cursor) :
    run (allocateStructCode size) m =
      .ok ((allocateStructMachine m cursor size).push (.val cursor)) 0 := by
  simp only [run, allocateStructCode, allocateStructMachine, writeMachine, Machine.push,
    exec_cons_zero, Instr.step, Machine.next, Out.ok_bind, hc, wmod_def,
    List.getElem?_cons_zero, Nat.reduceSub,
    exec_nil, Nat.add_mod, Nat.mod_mod, Nat.add_comm]

/-- Struct allocation writes only the reserved cursor cell. -/
theorem allocateStructMachine_other (m : Machine) (cursor : Fin W) (size addr : Nat)
    (hz : addr ≠ 0) : (allocateStructMachine m cursor size).mem addr = m.mem addr :=
  upd_other _ _ hz

theorem FreeMemory.allocateStruct {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : FreeMemory frame cursor m) (size : Nat) (hspace : cursor.val + size < W) :
    FreeMemory frame ⟨cursor.val + size, hspace⟩ (allocateStructMachine m cursor size) := by
  refine ⟨h.reserved, ?_, ?_, ?_⟩
  · change frame ≤ cursor.val + size
    have hb : frame ≤ cursor.val := h.above
    omega
  · simp only [allocateStructMachine, writeMachine, upd_same, wmod_def, Nat.mod_eq_of_lt hspace]
  · intro a ha
    have hb : frame ≤ cursor.val := h.above
    have hz : 0 < frame := h.reserved
    change cursor.val + size ≤ a at ha
    rw [allocateStructMachine_other m cursor size a (by omega)]
    exact h.zero a (by omega)

/-- Only primitive fields are interpreted; reference member cells are reserved. -/
def StructDefaults {H : HTy} {s : Name} (o : MObj H (.struct s)) : Prop :=
  ∀ {f : Name} {p : PrimTy} (hf : lookupBy f (structDef s) = some (.prim p)),
    MFields.get (structDef s) o hf = p.dflt

/-- A zero tail represents the fresh object's actual primitive defaults. -/
theorem FreeMemory.struct {H : HTy} {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : FreeMemory frame cursor m) (hp : Heap H) {s : Name} (o : MObj H (.struct s))
    (hd : StructDefaults o) (hspace : cursor.val + (structDef s).length < W) :
    StructRepr (hp.alloc o).1 (hp.alloc o).2 cursor
      (allocateStructMachine m cursor (structDef s).length) := by
  refine ⟨by omega, ?_⟩
  intro f p hf
  have ho : fieldOffset (structDef s) f < (structDef s).length := fieldOffset_bound hf
  have hb : frame ≤ cursor.val := h.above
  have hz : 0 < frame := h.reserved
  rw [Heap.field, Heap.get_alloc, MObj.wk, MFields.get_wk]
  change ReprV p (MFields.get (structDef s) o hf) _
  rw [hd hf, allocateStructMachine_other m cursor _ _ (by omega), h.zero _ (by omega)]
  exact ReprV.dflt_zero p

private theorem allocLen_old {H : HTy} {R : RefTy} {p : PrimTy}
    (hp : Heap H) (o : MObj H R) (a : HRef H (.array (.prim p))) :
    (hp.alloc o).1.len (a.wk (List.prefix_append H [R])) .dyn = hp.len a .dyn := by
  simp only [Heap.len, Heap.keeps_alloc hp o a, MObj.elems_dyn, MObj.wk, List.length_map]

/-- Adding a struct changes neither old array values nor their target regions. -/
theorem HeapRepr.allocStruct {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine} (h : HeapRepr hp base frame m)
    (hz : 0 < frame) {s : Name} (o : MObj H (.struct s)) :
    HeapRepr (hp.alloc o).1 (upd base H.length cursor) frame
      (allocateStructMachine m cursor (structDef s).length) := by
  have hold {p : PrimTy} (a : HRef (H ++ [.struct s]) (.array (.prim p))) :
      ∃ q : HRef H (.array (.prim p)), q.wk (List.prefix_append H [.struct s]) = a :=
    beforeAlloc hp o (by intro he; cases he) a
  refine ⟨?_, ?_, ?_⟩
  · intro p a
    obtain ⟨a, rfl⟩ := hold a
    simp only [HRef.wk, allocationBase_old base cursor a]
    exact ((h.localWrite 0 hz _).arrays a).keeps _ (Heap.keeps_alloc hp o)
  · intro p a
    obtain ⟨a, rfl⟩ := hold a
    simpa only [HRef.wk, allocationBase_old base cursor a] using h.above a
  · intro p q a r hne
    obtain ⟨a, rfl⟩ := hold a
    obtain ⟨r, rfl⟩ := hold r
    rw [allocLen_old hp o a, allocLen_old hp o r]
    simpa only [HRef.wk, allocationBase_old base cursor a, allocationBase_old base cursor r]
      using h.separated a r hne

/-- Fresh and older structs stay disjoint and represent their typed fields. -/
theorem StructHeapRepr.allocStruct {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : StructHeapRepr hp base frame m) (hf : FreeMemory frame cursor m)
    (hlive : ∀ {t : Name} (r : HRef H (.struct t)),
      (base r.id).val + (structDef t).length ≤ cursor.val)
    {s : Name} (o : MObj H (.struct s)) (hd : StructDefaults o)
    (hspace : cursor.val + (structDef s).length < W) :
    StructHeapRepr (hp.alloc o).1 (upd base H.length cursor) frame
      (allocateStructMachine m cursor (structDef s).length) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t r
    rcases allocRef_split hp o r with ⟨r, rfl⟩ | ⟨ht, he⟩
    · simp only [HRef.wk, allocationBase_old base cursor r]
      exact ((h.localWrite 0 hf.reserved _).objects r).keeps _ (Heap.keeps_alloc hp o)
    · cases ht
      cases he
      change StructRepr (hp.alloc o).1 (hp.alloc o).2 (upd base H.length cursor H.length) _
      rw [upd_same]
      exact hf.struct hp o hd hspace
  · intro t r
    rcases allocRef_split hp o r with ⟨r, rfl⟩ | ⟨ht, he⟩
    · simpa only [HRef.wk, allocationBase_old base cursor r] using h.above r
    · cases ht
      cases he
      simpa only [Heap.alloc, upd_same] using hf.above
  · intro t u r q hne
    rcases allocRef_split hp o r with ⟨r, rfl⟩ | ⟨ht, he⟩
    · rcases allocRef_split hp o q with ⟨q, rfl⟩ | ⟨ht, he⟩
      · simpa only [HRef.wk, allocationBase_old base cursor r, allocationBase_old base cursor q]
          using h.separated r q hne
      · cases ht
        cases he
        apply Or.inl
        simpa only [HRef.wk, Heap.alloc, allocationBase_old base cursor r, upd_same] using hlive r
    · cases ht
      cases he
      rcases allocRef_split hp o q with ⟨q, rfl⟩ | ⟨ht, he⟩
      · apply Or.inr
        simpa only [HRef.wk, Heap.alloc, allocationBase_old base cursor q, upd_same] using hlive q
      · cases ht
        cases he
        exact (hne rfl).elim

/-- Every live array is below a freshly reserved struct interval. -/
theorem StructArraySeparated.allocStruct {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {cursor : Fin W} (h : StructArraySeparated hp base)
    (hlive : ∀ {p : PrimTy} (a : HRef H (.array (.prim p))),
      (base a.id).val + 1 + hp.len a .dyn ≤ cursor.val) {s : Name} (o : MObj H (.struct s)) :
    StructArraySeparated (hp.alloc o).1 (upd base H.length cursor) := by
  intro p t a r
  obtain ⟨a, rfl⟩ := beforeAlloc hp o (by intro he; cases he) a
  rw [allocLen_old hp o a]
  rcases allocRef_split hp o r with ⟨r, rfl⟩ | ⟨ht, he⟩
  · simpa only [HRef.wk, allocationBase_old base cursor a, allocationBase_old base cursor r]
      using h a r
  · cases ht
    cases he
    apply Or.inl
    simpa only [HRef.wk, Heap.alloc, allocationBase_old base cursor a, upd_same] using hlive a

/-- Headerless struct allocation preserves arrays, old aliases and the zero tail. -/
theorem StructAllocatorRepr.allocateStruct {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : StructAllocatorRepr hp base frame cursor m) {s : Name} (o : MObj H (.struct s))
    (hd : StructDefaults o) (hspace : cursor.val + (structDef s).length < W) :
    StructAllocatorRepr (hp.alloc o).1 (upd base H.length cursor) frame
      ⟨cursor.val + (structDef s).length, hspace⟩
      (allocateStructMachine m cursor (structDef s).length) := by
  refine ⟨⟨h.arrays.heap.allocStruct h.arrays.free.reserved o,
      h.arrays.free.allocateStruct _ hspace, ?_⟩,
    h.structs.allocStruct h.arrays.free h.live o hd hspace,
    StructArraySeparated.allocStruct h.separated h.arrays.live o, ?_⟩
  · intro p a
    obtain ⟨a, rfl⟩ := beforeAlloc hp o (by intro he; cases he) a
    rw [allocLen_old hp o a]
    simp only [HRef.wk, allocationBase_old base cursor a]
    have hl : (base a.id).val + 1 + hp.len a .dyn ≤ cursor.val := h.arrays.live a
    omega
  · intro t r
    rcases allocRef_split hp o r with ⟨r, rfl⟩ | ⟨ht, he⟩
    · simp only [HRef.wk, allocationBase_old base cursor r]
      have hl : (base r.id).val + (structDef t).length ≤ cursor.val := h.live r
      omega
    · cases ht
      cases he
      simp only [Heap.alloc, upd_same, Nat.le_refl]

/-- Reserving an additional zero interval preserves every live object. -/
theorem StructAllocatorRepr.advance {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : StructAllocatorRepr hp base frame cursor m) (next : Fin W) (hn : cursor.val ≤ next.val) :
    StructAllocatorRepr hp base frame next (writeMachine m 0 (.val next)) := by
  refine ⟨⟨h.arrays.heap.localWrite 0 h.arrays.free.reserved _, ?_, ?_⟩,
    h.structs.localWrite 0 h.arrays.free.reserved _, h.separated, ?_⟩
  · refine ⟨h.arrays.free.reserved, Nat.le_trans h.arrays.free.above hn, rfl, ?_⟩
    intro a ha
    have hz : 0 < frame := h.arrays.free.reserved
    have hb : frame ≤ cursor.val := h.arrays.free.above
    change upd m.mem 0 (.val next) a = w[0]
    rw [upd_other _ _ (by omega)]
    exact h.arrays.free.zero a (by omega)
  · intro p a
    exact Nat.le_trans (h.arrays.live a) hn
  · intro s r
    exact Nat.le_trans (h.live r) hn

/-- A reservation may pad the tail after the actual member cells. -/
theorem StructAllocatorRepr.reserveStruct {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : StructAllocatorRepr hp base frame cursor m) {s : Name} (o : MObj H (.struct s))
    (hd : StructDefaults o) (size : Nat) (hn : (structDef s).length ≤ size)
    (hspace : cursor.val + size < W) :
    StructAllocatorRepr (hp.alloc o).1 (upd base H.length cursor) frame
      ⟨cursor.val + size, hspace⟩ (allocateStructMachine m cursor size) := by
  have hs : cursor.val + (structDef s).length < W := by omega
  have hg := (h.allocateStruct o hd hs).advance ⟨cursor.val + size, hspace⟩ (by simp only; omega)
  apply hg.mem_eq
  funext a
  by_cases hz : a = 0
  · subst a
    simp only [allocateStructMachine, writeMachine, upd_same, wmod_of_lt hspace]
  · simp only [allocateStructMachine, writeMachine, upd_other _ _ hz]

end Solidity.Evm.Memory
