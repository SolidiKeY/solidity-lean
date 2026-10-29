import Solidity.Evm.MemoryObjectChildrenSim

/-! Allocation of a dynamic array whose elements default to distinct empty
dynamic arrays. The source allocates children before the parent; the target
reserves the parent first. Both use the same finite typed heap identities. -/
namespace Solidity.Evm.Memory.Objects

def nestedCopy {H : HTy} (hp : Heap H) (E : Ty)
    (hm : (Ty.ref (.array E)).mapFree = true) (size : Fin W) :
    Grown H (MVal · (.ref (.array (.ref (.array E))))) :=
  let g := childrenCopy hp E hm size.val
  Grown.alloc ⟨g.ext, g.heap, ⟨g.val.1, by
    rw [g.val.2, List.length_replicate]
    exact size.isLt⟩⟩

theorem nestedCopy_source {H : HTy} (hp : Heap H) (E : Ty) (size : Fin W)
    (hn : (RefTy.array (.ref (.array E))).newArrOk = true)
    (hm : (Ty.ref (.array E)).mapFree = true) :
    (newArrT (.array (.ref (.array E))) (indexValue size) hn).copyStToM hp
      (RefTy.mapFree_of_newArrOk hn) = nestedCopy hp E hm size := by
  rw [newArrT, SVal.copyStToM_array]
  simp only [indexValue, Int.toNat_natCast]
  rfl

def nestedPrefix : List Instr := [.dup 1] ++ allocateArrayCode ++ [.swap 1, .push w[0]]
def nestedCode : List Instr := nestedPrefix ++ [.loop childrenCondition childrenBody, .pop, .pop]

theorem nestedPrefix_run (m : Machine) (cursor size : Fin W)
    (hc : m.mem 0 = .val cursor) :
    run nestedPrefix (m.push (.val size)) =
      .ok (control (allocateMachine m cursor size) cursor size (wmod 0)) 0 := by
  have hd : run [.dup 1] (m.push (.val size)) = .ok ((m.push (.val size)).push (.val size)) 0 := rfl
  rw [nestedPrefix, List.append_assoc, run_append_ok hd,
    run_append_ok (allocateArray_run (m.push (.val size)) cursor size hc)]
  change _ = Out.ok (control (allocateMachine m cursor size) cursor size ⟨0, W_pos⟩) 0
  rfl

private theorem runLoop_exit {cond body : List Instr} {m m' : Machine} {k : Nat}
    (h : loopIterN (run cond) (run body) k m = .inr (.ok m' 0)) :
    run [.loop cond body, .pop, .pop] m = run [.pop, .pop] m' := by
  change (loopRun (run cond) (run body) m).bind _ = _
  rw [loopRun_of_iterN h]
  rfl

/-- Full typed layout, actual source copying and target execution are related;
capacity accounts for the parent and all separately allocated children. -/
theorem nested_correct {H : HTy} (hp : Heap H) (E : Ty)
    (hm : (Ty.ref (.array E)).mapFree = true) (size : Fin W)
    (base : Nat → Fin W) (frame : Nat) (m : Machine) (cursor : Fin W)
    (ha : AllocatorRepr hp base frame cursor m)
    (hs : cursor.val + size.val + 1 + size.val < W) :
    let g := nestedCopy hp E hm size
    ∃ base' m', run nestedCode (m.push (.val size)) = .ok (m'.push (.val cursor)) 0 ∧
      AllocatorRepr g.heap base' frame ⟨cursor.val + size.val + 1 + size.val, hs⟩ m' ∧
      base' g.val.id = cursor ∧ BaseExtends H base base' ∧
      m'.stack = m.stack ∧ m' = {m with mem := m'.mem} ∧
      (∀ addr, 0 < addr → addr < frame → m'.mem addr = m.mem addr) := by
  have hs₀ : cursor.val + size.val + 1 < W := by omega
  let start := allocateMachine m cursor size
  let cc : Fin W := ⟨cursor.val + size.val + 1, hs₀⟩
  have hr := ha.reserveArray size hs₀
  have hg : Gap hp base cursor.val (cursor.val + 1 + size.val) := by
    intro R r
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr.2 r
  obtain ⟨base₁, m', hloop, ha₁, hg₁, hb₁, helems, hstack, hprefix, hframe⟩ :=
    children_sim hp E hm size.val base frame start cursor size (wmod 0) cc hr.1 hg
      ha.free.above (by change cursor.val + 1 + size.val ≤ cursor.val + size.val + 1; omega)
      (by change 0 + size.val = size.val; omega)
      (by change cursor.val + size.val + 1 + size.val < W; exact hs)
  let g := childrenCopy hp E hm size.val
  let o : MObj g.H' (.array (.ref (.array E))) := ⟨g.val.1, by
    rw [g.val.2, List.length_replicate]
    exact size.isLt⟩
  let base' := upd base₁ g.H'.length cursor
  let e := List.prefix_append g.H' [.array (.ref (.array E))]
  have hlen : (g.heap.alloc o).1.len (g.heap.alloc o).2 .dyn = size.val := by
    simp only [Heap.len, Heap.get_alloc, MObj.elems_dyn, MObj.wk, o, List.length_map]
    exact g.val.2.trans (List.length_replicate ..)
  have hcells : cells (g.heap.alloc o).1 (g.heap.alloc o).2 = 1 + size.val := by
    simp only [cells, hlen]
  have hz : 0 < cursor.val := Nat.lt_of_lt_of_le ha.free.reserved ha.free.above
  have fresh : ArrayRepr (g.heap.alloc o).1 (g.heap.alloc o).2 .dyn base' m' := by
    refine ⟨?_, ?_, ?_⟩
    · change (upd base₁ g.H'.length cursor g.H'.length).val + cells (g.heap.alloc o).1 (g.heap.alloc o).2 ≤ W
      rw [upd_same, hcells]
      omega
    · intro hh
      change m'.mem (upd base₁ g.H'.length cursor g.H'.length).val = _
      rw [upd_same, hlen, hprefix _ hz (by change cursor.val < cursor.val + 1 + 0; omega)]
      rw [allocateMachine_header m cursor size (by omega)]
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt size.isLt).symm
    · intro j v hv
      simp only [Heap.get_alloc, MObj.elems_dyn, MObj.wk, o, List.getElem?_map] at hv
      cases hx : g.val.1[j]? with
      | none => simp only [hx, Option.map_none] at hv; cases hv
      | some x =>
        simp only [hx, Option.map_some, Option.some.injEq] at hv
        subst v
        change m'.mem ((upd base₁ g.H'.length cursor g.H'.length).val + 1 + j) =
          .val (upd base₁ g.H'.length cursor x.id)
        rw [upd_same, upd_other base₁ cursor (Nat.ne_of_lt x.id_lt)]
        have he := helems j x hx
        simpa only [show (wmod 0).val = 0 from rfl, Nat.add_zero] using he
  have haf : AllocatorRepr (nestedCopy hp E hm size).heap base' frame
      ⟨cursor.val + size.val + 1 + size.val, hs⟩ m' := by
    apply ha₁.adoptReservedArray .dyn o cursor ha.free.above fresh
    · change cursor.val + cells (g.heap.alloc o).1 (g.heap.alloc o).2 ≤ cc.val + size.val
      rw [hcells]
      change cursor.val + (1 + size.val) ≤ cursor.val + size.val + 1 + size.val
      omega
    · intro R r
      change (base₁ r.id).val + cells g.heap r ≤ cursor.val ∨
        cursor.val + cells (g.heap.alloc o).1 (g.heap.alloc o).2 ≤ (base₁ r.id).val
      rw [hcells]
      simpa only [Nat.add_assoc] using hg₁ r
  refine ⟨base', m', ?_, haf, upd_same base₁ g.H'.length cursor, ?_,
    hstack, ?_, ?_⟩
  · rw [nestedCode, run_append_ok (nestedPrefix_run m cursor size ha.free.cell), runLoop_exit hloop]
    rfl
  · apply BaseExtends.trans g.ext hb₁
    intro R r
    exact upd_other base₁ cursor (Nat.ne_of_lt r.id_lt)
  · calc
      m' = {start with mem := m'.mem} := hframe
      _ = {m with mem := m'.mem} := rfl
  · intro addr hz' hl
    rw [hprefix addr hz' (by
      have hf := ha.free.above
      change addr < cursor.val + 1 + 0
      omega)]
    exact allocateMachine_other m cursor size addr (by have hf := ha.free.above; omega) (by omega)

end Solidity.Evm.Memory.Objects
