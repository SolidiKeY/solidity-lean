import Solidity.Evm.MemoryObjectConstructionSource

/-! Existing primitive array allocation under complete object ownership, so a
reference-array program may allocate its primitive children without losing old
reference or fixed-array reservations. -/
namespace Solidity.Evm.Memory.Objects

theorem AllocatorRepr.allocatePrimitive {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : AllocatorRepr hp base frame cursor m) (p : PrimTy) (size : Fin W)
    (hs : cursor.val + size.val + 1 < W) :
    AllocatorRepr (hp.alloc (defaultArray p size)).1 (upd base H.length cursor) frame
      ⟨cursor.val + size.val + 1, hs⟩ (allocateMachine m cursor size) := by
  let o := defaultArray (H := H) p size
  let e := List.prefix_append H [.array (.prim p)]
  have hk : Heap.Keeps e hp (hp.alloc o).1 := fun r => Heap.keeps_alloc hp o r
  have hold := h.free.array size hs hp p
  have hlen : (hp.alloc o).1.len (hp.alloc o).2 .dyn = size.val := by
    simp only [Heap.len, Heap.get_alloc, MObj.elems_dyn, MObj.wk, o, defaultArray,
      List.length_map, List.length_replicate]
  have hc : cells (hp.alloc o).1 (hp.alloc o).2 = 1 + size.val := by
    simp only [cells, hlen]
  have hf : ArrayRepr (hp.alloc o).1 (hp.alloc o).2 .dyn (upd base H.length cursor)
      (allocateMachine m cursor size) := by
    refine ⟨?_, ?_, ?_⟩
    · change (upd base H.length cursor H.length).val + cells (hp.alloc o).1 (hp.alloc o).2 ≤ W
      rw [upd_same, hc]
      omega
    · intro hh
      simpa only [Heap.alloc, HRef.id, upd_same] using hold.length
    · intro i v hv
      simpa only [Heap.alloc, HRef.id, upd_same] using hold.elements i v hv
  refine ⟨(h.headerOutside size).adoptArray .dyn o cursor h.free.above hf
    (fun r => .inl (h.live r)), h.free.allocate size hs, ?_⟩
  intro R r
  rcases allocRef_split hp o r with ⟨q, rfl⟩ | ⟨ht, he⟩
  · change (upd base H.length cursor q.id).val + cells (hp.alloc o).1 (q.wk e) ≤ cursor.val + size.val + 1
    rw [upd_other base cursor (Nat.ne_of_lt q.id_lt), cells_keeps e hk]
    exact Nat.le_trans (h.live q) (by omega)
  · cases ht; cases he
    change (upd base H.length cursor H.length).val + cells (hp.alloc o).1 (hp.alloc o).2 ≤ cursor.val + size.val + 1
    rw [upd_same, hc]
    omega

variable {C : Contract}

theorem StateRepr.allocatePrimitive {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : AllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    (p : PrimTy) (size : Fin W) (hs : cursor.val + size.val + 1 < W) :
    StateRepr L b frame F (σ.alloc (defaultArray p size)).1
      (upd base σ.H.length cursor) (allocateMachine m cursor size) := by
  apply h.adopt (Grown.alloc ⟨List.prefix_refl _, σ.heap, defaultArray p size⟩)
    (ha.allocatePrimitive p size hs).heap (fun r => allocationBase_old base cursor r) rfl
  intro l hl hu
  have hf := ha.free.above
  have hh := h.locals
  exact allocateMachine_other m cursor size l (by omega) (by omega)

theorem primitiveDeclare_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : AllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    (p : PrimTy) (n : Simple C Γ .uint) (hn : simpleIn n = true)
    (size : Fin W) (hs : n.evalT σ = indexValue size)
    (hspace : cursor.val + size.val + 1 < W) (hcap : b + (Γ.length + 1) ≤ frame) :
    let σ' := σ.allocPush (defaultArray p size)
    let base' := upd base σ.H.length cursor
    let m' := writeMachine (allocateMachine m cursor size)
      (cell (b + Γ.length)) (.val cursor)
    TRun.declMem (.array (.prim p)) (some (.newArr n rfl)) rfl σ =
        .ok ⟨σ', List.prefix_append _ _⟩ ∧
      run (declareNewCode b n) m = .ok m' 0 ∧
      StateRepr L b frame (F.push (.mem (.array (.prim p))) .ok) σ' base' m' ∧
      AllocatorRepr σ'.heap base' frame ⟨cursor.val + size.val + 1, hspace⟩ m' ∧
      m'.stack = m.stack := by
  refine ⟨newArray_decl σ p n size hs, ?_, ?_, ?_, rfl⟩
  · obtain ⟨w, hw, hr⟩ := simple_sim h.core n hn
    rw [hs] at hw
    obtain ⟨a, rfl, he⟩ := hw
    have he' : a = size := Fin.ext (Int.ofNat_inj.mp he.symm)
    subst a
    rw [declareNewCode, List.append_assoc, run_append_ok hr,
      run_append_ok (allocateArray_run m cursor size ha.free.cell)]
    rfl
  · have hid : (σ.alloc (defaultArray p size)).2.id = σ.H.length := rfl
    simpa only [hid, upd_same] using
      (h.allocatePrimitive ha hb p size hspace).consMem (σ.alloc (defaultArray p size)).2 hcap
  · exact (ha.allocatePrimitive p size hspace).localWrite (b + Γ.length)
      (by omega) (by omega) (.val cursor)

theorem primitiveRebind_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : AllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    (p : PrimTy) (dst : Idx Γ (.mem (.array (.prim p))))
    (n : Simple C Γ .uint) (hn : simpleIn n = true)
    (size : Fin W) (hs : n.evalT σ = indexValue size)
    (hspace : cursor.val + size.val + 1 < W) :
    let σ' := (σ.alloc (defaultArray p size)).1.setLocal dst
      (some (σ.alloc (defaultArray p size)).2)
    let base' := upd base σ.H.length cursor
    let m' := writeMachine (allocateMachine m cursor size) (cellOf b dst) (.val cursor)
    TRun.rebindMem dst (.newArr n rfl) σ = .ok ⟨σ', List.prefix_append _ _⟩ ∧
      run (rebindNewCode b dst n) m = .ok m' 0 ∧
      StateRepr L b frame F σ' base' m' ∧
      AllocatorRepr σ'.heap base' frame ⟨cursor.val + size.val + 1, hspace⟩ m' ∧
      m'.stack = m.stack := by
  refine ⟨newArray_rebind σ p dst n size hs, ?_, ?_, ?_, rfl⟩
  · obtain ⟨w, hw, hr⟩ := simple_sim h.core n hn
    rw [hs] at hw
    obtain ⟨a, rfl, he⟩ := hw
    have he' : a = size := Fin.ext (Int.ofNat_inj.mp he.symm)
    subst a
    rw [rebindNewCode, List.append_assoc, run_append_ok hr,
      run_append_ok (allocateArray_run m cursor size ha.free.cell)]
    rfl
  · have hid : (σ.alloc (defaultArray p size)).2.id = σ.H.length := rfl
    simpa only [hid, upd_same] using
      (h.allocatePrimitive ha hb p size hspace).setMem dst (σ.alloc (defaultArray p size)).2
  · exact (ha.allocatePrimitive p size hspace).localWrite (cellOf b dst)
      (Nat.lt_of_lt_of_le hb (le_lvl b dst))
      (Nat.lt_of_lt_of_le (lvl_lt b dst) h.locals) (.val cursor)

end Solidity.Evm.Memory.Objects
