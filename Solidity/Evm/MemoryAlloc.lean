import Solidity.Evm.MemoryHeap

/-!
# Bump allocation in word memory

Cell zero holds the next free array base. Local frames and live arrays must
be strictly above that cell and below the cursor. Unused memory is zero,
so allocating a primitive array writes only its length and advances the
cursor; its elements already have their default representation.

These target lemmas precede the source-heap growth and compiler integration.
A capacity premise prevents word-address wrap; allocation is not yet a
clause of the public compiler.
-/
namespace Solidity.Evm.Memory

/-- Consume a length, write the header, return its base and advance cell zero. -/
def allocateArrayCode : List Instr :=
  [.mload 0, .dup 2, .dup 2, .mstoreAt, .swap 1, .dup 2, .add,
    .push w[1], .add, .mstore 0]

/-- The two memory writes of array allocation; all other machine fields stay. -/
def allocateMachine (m : Machine) (cursor size : Fin W) : Machine :=
  writeMachine (writeMachine m cursor.val (.val size)) 0
    (.val (wmod (cursor.val + size.val + 1)))

/-- The instruction sequence returns the old cursor and performs exactly its
header and cursor writes, including its word arithmetic. -/
theorem allocateArray_run (m : Machine) (cursor size : Fin W)
    (hc : m.mem 0 = .val cursor) :
    run allocateArrayCode (m.push (.val size)) =
      .ok ((allocateMachine m cursor size).push (.val cursor)) 0 := by
  simp only [run, allocateArrayCode, allocateMachine, writeMachine, Machine.push,
    exec_cons_zero, Instr.step, Machine.next, Out.ok_bind, hc, wmod_def,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceSub,
    List.set_cons_zero, exec_nil, Nat.add_mod, Nat.mod_mod, Nat.add_comm]

/-- The allocator's cursor cell, reserved frame and zeroed unused region. -/
structure FreeMemory (frame : Nat) (cursor : Fin W) (m : Machine) : Prop where
  reserved : 0 < frame
  above : frame ≤ cursor.val
  cell : m.mem 0 = .val cursor
  zero : ∀ addr : Nat, cursor.val ≤ addr → m.mem addr = w[0]

/-- Allocation preserves every cell except its header and the cursor cell. -/
theorem allocateMachine_other (m : Machine) (cursor size : Fin W) (addr : Nat)
    (ha : addr ≠ cursor.val) (hz : addr ≠ 0) :
    (allocateMachine m cursor size).mem addr = m.mem addr :=
  (upd_other _ _ hz).trans (upd_other _ _ ha)

/-- The header is the requested length when the cursor cell is reserved. -/
theorem allocateMachine_header (m : Machine) (cursor size : Fin W) (hc : cursor.val ≠ 0) :
    (allocateMachine m cursor size).mem cursor.val = .val size :=
  (upd_other _ _ hc).trans (upd_same _ _ _)

/-- Advancing a non-wrapping cursor leaves a zeroed free tail. -/
theorem FreeMemory.allocate {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : FreeMemory frame cursor m) (size : Fin W)
    (hspace : cursor.val + size.val + 1 < W) :
    FreeMemory frame ⟨cursor.val + size.val + 1, hspace⟩ (allocateMachine m cursor size) := by
  refine ⟨h.reserved, ?_, ?_, ?_⟩
  · change frame ≤ cursor.val + size.val + 1
    have habove : frame ≤ cursor.val := h.above
    omega
  · simp only [allocateMachine, writeMachine, upd_same, wmod_def, Nat.mod_eq_of_lt hspace]
  · intro addr ha
    change cursor.val + size.val + 1 ≤ addr at ha
    rw [allocateMachine_other m cursor size addr (by omega) (by omega)]
    exact h.zero addr (by omega)

/-- A newly allocated primitive source array contains its type's defaults. -/
def defaultArray {H : HTy} (p : PrimTy) (size : Fin W) : MObj H (.array (.prim p)) :=
  ⟨List.replicate size.val p.dflt, (List.length_replicate ..).symm ▸ size.isLt⟩

/-- The allocation code represents the actual fresh typed heap object. -/
theorem FreeMemory.array {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : FreeMemory frame cursor m) (size : Fin W)
    (hspace : cursor.val + size.val + 1 < W) {H : HTy} (hp : Heap H) (p : PrimTy) :
    ArrayRepr (hp.alloc (defaultArray p size)).1 (hp.alloc (defaultArray p size)).2
      cursor (allocateMachine m cursor size) := by
  have hlen : (hp.alloc (defaultArray p size)).1.len (hp.alloc (defaultArray p size)).2 .dyn = size.val := by
    simp only [Heap.len, Heap.get_alloc, MObj.elems_dyn, MObj.wk, defaultArray,
      List.length_map, List.length_replicate]
  constructor
  · rw [hlen]
    omega
  · rw [hlen, allocateMachine_header m cursor size (by have := h.reserved; have := h.above; omega)]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt size.isLt).symm
  · intro i v hv
    simp only [Heap.get_alloc, MObj.elems_dyn, MObj.wk, defaultArray, List.map_replicate] at hv
    obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hv
    simp only [List.getElem_replicate, MVal.wk] at he
    subst v
    rw [allocateMachine_other m cursor size _ (by omega) (by omega), h.zero _ (by omega)]
    exact ReprV.dflt_zero p

/-- Reserving a fresh array preserves all existing represented objects. -/
theorem HeapRepr.allocate {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : HeapRepr hp base frame m) (hf : FreeMemory frame cursor m)
    (hlive : ∀ {p : PrimTy} (r : HRef H (.array (.prim p))),
      (base r.id).val + 1 + hp.len r .dyn ≤ cursor.val) (size : Fin W) :
    HeapRepr hp base frame (allocateMachine m cursor size) := by
  refine ⟨?_, h.above, h.separated⟩
  intro p r
  have hr : ArrayRepr hp r (base r.id) m := h.arrays r
  have hb : frame ≤ (base r.id).val := h.above r
  have he : (base r.id).val + 1 + hp.len r .dyn ≤ cursor.val := hlive r
  have hf' : 0 < frame := hf.reserved
  refine ⟨hr.space, ?_, ?_⟩
  · rw [allocateMachine_other m cursor size _ (by omega) (by omega)]
    exact hr.length
  · intro i v hv
    have hi : i < hp.len r .dyn := (List.getElem?_eq_some_iff.mp hv).1
    rw [allocateMachine_other m cursor size _ (by omega) (by omega)]
    exact hr.elements i v hv

/-- Growing the typed heap preserves an older primitive array's representation. -/
theorem ArrayRepr.keeps {H H' : HTy} {hp : Heap H} {hp' : Heap H'}
    {p : PrimTy} {r : HRef H (.array (.prim p))} {base : Fin W} {m : Machine}
    (h : ArrayRepr hp r base m) (e : H <+: H') (hk : Heap.Keeps e hp hp') :
    ArrayRepr hp' (r.wk e) base m := by
  have hlen : hp'.len (r.wk e) .dyn = hp.len r .dyn := by
    simp only [Heap.len, hk r, MObj.elems_dyn, MObj.wk, List.length_map]
  refine ⟨by simpa only [hlen] using h.space, by simpa only [hlen] using h.length, ?_⟩
  intro i v hv
  rw [hk r] at hv
  simp only [MObj.elems_dyn, MObj.wk] at hv
  have hm : (List.map (MVal.wk e (.prim p)) (hp.get r).val : List p.Denote) =
      (hp.get r).val := List.map_id _
  rw [hm] at hv
  exact h.elements i v (by simpa only [MObj.elems_dyn] using hv)

/-- Every primitive-array reference after one allocation is old or fresh. -/
private theorem arrayRef_cases {H : HTy} (hp : Heap H) (p : PrimTy) (size : Fin W)
    (P : (q : PrimTy) → HRef (H ++ [.array (.prim p)]) (.array (.prim q)) → Prop)
    (hold : ∀ (q : PrimTy) (r : HRef H (.array (.prim q))),
      P q (r.wk (List.prefix_append _ _)))
    (hfresh : P p (hp.alloc (defaultArray p size)).2)
    (q : PrimTy) (r : HRef (H ++ [.array (.prim p)]) (.array (.prim q))) : P q r := by
  by_cases hi : r.id < H.length
  · let s : HRef H (.array (.prim q)) := ⟨r.id, by simpa only [List.getElem?_append_left hi] using r.get?⟩
    have he : s.wk (List.prefix_append H [.array (.prim p)]) = r := by cases r; rfl
    rw [← he]
    exact hold q s
  · have hr : r.id = H.length := by
      have hl : r.id < (H ++ [RefTy.array (.prim p)]).length := r.id_lt
      simp only [List.length_append, List.length_singleton] at hl
      omega
    obtain ⟨ht, he⟩ := HRef.heq_of_id r (hp.alloc (defaultArray p size)).2 hr
    cases ht
    cases he
    exact hfresh

/-- One fresh identity is mapped to the old cursor; all older aliases retain
one address and every old/new primitive array remains separated. -/
theorem HeapRepr.alloc {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : HeapRepr hp base frame m) (hf : FreeMemory frame cursor m)
    (hlive : ∀ {p : PrimTy} (r : HRef H (.array (.prim p))),
      (base r.id).val + 1 + hp.len r .dyn ≤ cursor.val)
    (p : PrimTy) (size : Fin W) (hspace : cursor.val + size.val + 1 < W) :
    HeapRepr (hp.alloc (defaultArray p size)).1 (upd base H.length cursor) frame
      (allocateMachine m cursor size) := by
  constructor
  · intro q r
    refine arrayRef_cases hp p size
      (fun q r => ArrayRepr (hp.alloc (defaultArray p size)).1 r
        (upd base H.length cursor r.id) (allocateMachine m cursor size)) ?_ ?_ q r
    · intro q s
      change ArrayRepr (hp.alloc (defaultArray p size)).1 (s.wk (List.prefix_append _ _))
        (upd base H.length cursor s.id) (allocateMachine m cursor size)
      rw [upd_other base cursor (Nat.ne_of_lt s.id_lt)]
      exact ((h.allocate hf hlive size).arrays s).keeps _ (Heap.keeps_alloc hp _)
    · change ArrayRepr (hp.alloc (defaultArray p size)).1 (hp.alloc (defaultArray p size)).2
        (upd base H.length cursor H.length) (allocateMachine m cursor size)
      rw [upd_same]
      exact hf.array size hspace hp p
  · intro q r
    refine arrayRef_cases hp p size
      (fun _ r => frame ≤ (upd base H.length cursor r.id).val) ?_ ?_ q r
    · intro q s
      change frame ≤ (upd base H.length cursor s.id).val
      rw [upd_other base cursor (Nat.ne_of_lt s.id_lt)]
      exact h.above s
    · change frame ≤ (upd base H.length cursor H.length).val
      rw [upd_same]
      exact hf.above
  · have hbase {q : PrimTy} (r : HRef H (.array (.prim q))) :
        upd base H.length cursor (r.wk (List.prefix_append H [.array (.prim p)])).id = base r.id :=
      upd_other _ _ (Nat.ne_of_lt r.id_lt)
    have hnew : upd base H.length cursor (hp.alloc (defaultArray p size)).2.id = cursor :=
      upd_same _ _ _
    have hlen {q : PrimTy} (r : HRef H (.array (.prim q))) :
        (hp.alloc (defaultArray p size)).1.len (r.wk (List.prefix_append _ _)) .dyn = hp.len r .dyn := by
      simp only [Heap.len, Heap.keeps_alloc hp (defaultArray p size) r,
        MObj.elems_dyn, MObj.wk, List.length_map]
    intro q t r s hne
    induction q, r using arrayRef_cases hp p size generalizing t s with
    | hold q r =>
      induction t, s using arrayRef_cases hp p size with
      | hold t s =>
        simpa only [hbase r, hbase s, hlen r, hlen s] using h.separated r s hne
      | hfresh =>
        apply Or.inl
        simpa only [hbase r, hnew, hlen r] using hlive r
    | hfresh =>
      induction t, s using arrayRef_cases hp p size with
      | hold t s =>
        apply Or.inr
        simpa only [hnew, hbase s, hlen s] using hlive s
      | hfresh => exact (hne rfl).elim

/-- The global heap, cursor and zero tail needed for repeatable allocation. -/
structure AllocatorRepr {H : HTy} (hp : Heap H) (base : Nat → Fin W)
    (frame : Nat) (cursor : Fin W) (m : Machine) : Prop where
  heap : HeapRepr hp base frame m
  free : FreeMemory frame cursor m
  live : ∀ {p : PrimTy} (r : HRef H (.array (.prim p))),
    (base r.id).val + 1 + hp.len r .dyn ≤ cursor.val

/-- Allocator invariants observe memory only, not the stack or storage. -/
theorem AllocatorRepr.mem_eq {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m m' : Machine}
    (h : AllocatorRepr hp base frame cursor m) (hm : m'.mem = m.mem) :
    AllocatorRepr hp base frame cursor m' := by
  refine ⟨⟨?_, h.heap.above, h.heap.separated⟩, ?_, h.live⟩
  · intro p r
    have hr := h.heap.arrays r
    exact ⟨hr.space, hm ▸ hr.length, fun i v hv => hm ▸ hr.elements i v hv⟩
  · exact ⟨h.free.reserved, h.free.above, hm ▸ h.free.cell,
      fun a ha => hm ▸ h.free.zero a ha⟩

/-- A nonzero reserved local cell lies below both live arrays and the free tail. -/
theorem AllocatorRepr.localWrite {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : AllocatorRepr hp base frame cursor m) (addr : Nat)
    (hz : 0 < addr) (hl : addr < frame) (w : Word) :
    AllocatorRepr hp base frame cursor (writeMachine m addr w) := by
  refine ⟨h.heap.localWrite addr hl w, ?_, h.live⟩
  refine ⟨h.free.reserved, h.free.above, ?_, ?_⟩
  · exact (upd_other m.mem w (Nat.ne_of_lt hz)).trans h.free.cell
  · intro a ha
    have hc : frame ≤ cursor.val := h.free.above
    exact (upd_other m.mem w (by omega)).trans (h.free.zero a ha)

/-- Older identities keep their runtime addresses when one address is added. -/
theorem allocationBase_old {H : HTy} {R : RefTy} (base : Nat → Fin W)
    (cursor : Fin W) (r : HRef H R) :
    upd base H.length cursor r.id = base r.id :=
  upd_other _ _ (Nat.ne_of_lt r.id_lt)

/-- Every allocated array remains below the next allocation's cursor. -/
theorem AllocatorRepr.live_alloc {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : AllocatorRepr hp base frame cursor m) (p : PrimTy) (size : Fin W)
    {q : PrimTy} (r : HRef (H ++ [.array (.prim p)]) (.array (.prim q))) :
    (upd base H.length cursor r.id).val + 1 + (hp.alloc (defaultArray p size)).1.len r .dyn ≤
      cursor.val + size.val + 1 := by
  induction q, r using arrayRef_cases hp p size with
  | hold q r =>
    change (upd base H.length cursor r.id).val + 1 +
      (hp.alloc (defaultArray p size)).1.len (r.wk (List.prefix_append _ _)) .dyn ≤ _
    rw [allocationBase_old base cursor r]
    have he : (hp.alloc (defaultArray p size)).1.len
        (r.wk (List.prefix_append _ _)) .dyn = hp.len r .dyn := by
      simp only [Heap.len, Heap.keeps_alloc hp (defaultArray p size) r,
        MObj.elems_dyn, MObj.wk, List.length_map]
    rw [he]
    have hl : (base r.id).val + 1 + hp.len r .dyn ≤ cursor.val := h.live r
    omega
  | hfresh =>
    change (upd base H.length cursor H.length).val + 1 +
      (hp.alloc (defaultArray p size)).1.len (hp.alloc (defaultArray p size)).2 .dyn ≤ _
    simp only [upd_same, Heap.len, Heap.get_alloc, MObj.elems_dyn, MObj.wk,
      defaultArray, List.length_map, List.length_replicate]
    omega

/-- Array allocation preserves all allocator invariants and extends the
identity map at exactly the fresh source identity. -/
theorem AllocatorRepr.allocate {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : AllocatorRepr hp base frame cursor m) (p : PrimTy) (size : Fin W)
    (hspace : cursor.val + size.val + 1 < W) :
    AllocatorRepr (hp.alloc (defaultArray p size)).1 (upd base H.length cursor)
      frame ⟨cursor.val + size.val + 1, hspace⟩ (allocateMachine m cursor size) :=
  ⟨h.heap.alloc h.free h.live p size hspace, h.free.allocate size hspace,
    fun r => h.live_alloc p size r⟩

/-- Writing a live array keeps the cursor and unused memory suitable for a
later allocation, as well as preserving every other represented object. -/
theorem AllocatorRepr.set {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : AllocatorRepr hp base frame cursor m) {p : PrimTy}
    (r : HRef H (.array (.prim p))) (i : Nat) (hi : i < hp.len r .dyn)
    (v : p.Denote) (w : Word) (hw : ReprV p v w) :
    AllocatorRepr (hp.set r (MObj.setElem .dyn (hp.get r) i v)) base frame cursor
      (writeMachine m ((base r.id).val + 1 + i) w) := by
  have he : (base r.id).val + 1 + i < cursor.val := by
    have hl : (base r.id).val + 1 + hp.len r .dyn ≤ cursor.val := h.live r
    omega
  have hz : 0 < (base r.id).val + 1 + i := by omega
  refine ⟨h.heap.set r i hi v w hw, ?_, ?_⟩
  · refine ⟨h.free.reserved, h.free.above, ?_, ?_⟩
    · change upd m.mem ((base r.id).val + 1 + i) w 0 = .val cursor
      rw [upd_other _ _ (by omega)]
      exact h.free.cell
    · intro addr ha
      change upd m.mem ((base r.id).val + 1 + i) w addr = w[0]
      rw [upd_other _ _ (by omega)]
      exact h.free.zero addr ha
  · intro q s
    simpa only [arrayLen_set] using h.live s

end Solidity.Evm.Memory
