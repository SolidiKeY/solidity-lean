import Solidity.Evm.MemoryObjectChildrenCopy

/-! A finite kernel-checked loop simulation for the actual source child-copy fold. -/
namespace Solidity.Evm.Memory.Objects

theorem storeChildMachine_eq (m : Machine) (parent index child : Fin W)
    (hs : parent.val + 1 + index.val < W) :
    storeChildMachine m parent index child =
      writeMachine m (parent.val + 1 + index.val) (.val child) := by
  unfold storeChildMachine
  have ha : parent.val + index.val + 1 < W := by omega
  rw [wmod_of_lt ha]
  congr 1
  change parent.val + index.val + 1 = parent.val + 1 + index.val
  omega

/-- Copying `k` actual defaults allocates distinct typed children, fills the
corresponding parent segment, and terminates the target loop in `k+1` turns. -/
theorem children_sim {H : HTy} (hp : Heap H) (E : Ty)
    (hm : (Ty.ref (.array E)).mapFree = true) (k : Nat)
    (base : Nat → Fin W) (frame : Nat) (m : Machine)
    (parent total index cursor : Fin W)
    (ha : AllocatorRepr hp base frame cursor m)
    (hg : Gap hp base parent.val (parent.val + 1 + total.val))
    (hpframe : frame ≤ parent.val) (hgap : parent.val + 1 + total.val ≤ cursor.val)
    (hi : index.val + k = total.val) (hs : cursor.val + k < W) :
    let g := childrenCopy hp E hm k
    ∃ base' m',
      loopIterN (run childrenCondition) (run childrenBody) (k + 1)
        (control m parent total index) = .inr (.ok (control m' parent total total) 0) ∧
      AllocatorRepr g.heap base' frame ⟨cursor.val + k, hs⟩ m' ∧
      Gap g.heap base' parent.val (parent.val + 1 + total.val) ∧
      BaseExtends H base base' ∧
      (∀ j v, g.val.1[j]? = some v →
        m'.mem (parent.val + 1 + index.val + j) = .val (base' v.id)) ∧
      m'.stack = m.stack ∧
      (∀ addr, 0 < addr → addr < parent.val + 1 + index.val → m'.mem addr = m.mem addr) ∧ m' = {m with mem := m'.mem} := by
  induction k generalizing H hp base m index cursor with
  | zero =>
    have he : index = total := Fin.ext (by omega)
    subst index
    rw [childrenCopy_zero]
    refine ⟨base, m, ?_, ?_, hg, BaseExtends.refl base, ?_, rfl, (fun _ _ _ => rfl), rfl⟩
    · rw [loopIterN, childrenTurn_done]
    · simpa only [Nat.add_zero] using ha
    · intro j v hv
      cases hv
  | succ k ih =>
    have himore : index.val < total.val := by omega
    have hi' : index.val + 1 < W := Nat.lt_of_le_of_lt (by omega) total.isLt
    have hc' : cursor.val + 1 < W := by omega
    let index' : Fin W := ⟨index.val + 1, hi'⟩
    let cursor' : Fin W := ⟨cursor.val + 1, hc'⟩
    let o : MObj H (.array E) := emptyArray E
    let hp₁ := (hp.alloc o).1
    let base₁ := upd base H.length cursor
    let m₁ := storeChildMachine (allocateMachine m cursor (wmod 0)) parent index cursor
    let e := List.prefix_append H [.array E]
    have haddr : parent.val + 1 + index.val < W := by omega
    have hz : 0 < parent.val + 1 + index.val := by omega
    have hg₁ : Gap hp₁ base₁ parent.val (parent.val + 1 + total.val) :=
      hg.allocateEmpty E cursor hgap
    have ha₁ : AllocatorRepr hp₁ base₁ frame cursor' m₁ := by
      dsimp only [m₁]
      rw [storeChildMachine_eq _ _ _ _ haddr]
      exact (ha.allocateEmpty E hc').writeGap hg₁ (by omega) (by omega) hz (by
        change parent.val + 1 + total.val ≤ cursor.val + 1
        omega) _
    have hrest : index'.val + k = total.val := by change index.val + 1 + k = total.val; omega
    have hsrest : cursor'.val + k < W := by change cursor.val + 1 + k < W; omega
    obtain ⟨base', m', hloop, ha', hg', hb', helem, hstack, hprefix, hframe⟩ :=
      ih hp₁ base₁ m₁ index' cursor' ha₁ hg₁ (by
        change parent.val + 1 + total.val ≤ cursor.val + 1
        omega) hrest hsrest
    rw [childrenCopy_succ]
    refine ⟨base', m', ?_, ?_, hg', ?_, ?_, hstack.trans rfl, ?_, ?_⟩
    · have hnext : wmod (index.val + 1) = index' := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hi'
      rw [loopIterN, childrenTurn_more m parent total index cursor ha.free.cell himore, hnext]
      exact hloop
    · have heq : cursor'.val + k = cursor.val + (k + 1) := by
        change cursor.val + 1 + k = cursor.val + (k + 1)
        omega
      simpa only [heq] using ha'
    · exact BaseExtends.trans e (fun r => allocationBase_old base cursor r) hb'
    · intro j v hv
      cases j with
      | zero =>
        change ((hp.alloc o).2.wk (childrenCopy hp₁ E hm k).ext ::
          (childrenCopy hp₁ E hm k).val.1)[0]? = some v at hv
        cases hv
        have hbase : base' (hp.alloc o).2.id = cursor := by
          exact (hb' (hp.alloc o).2).trans (upd_same base H.length cursor)
        change m'.mem (parent.val + 1 + index.val + 0) = .val (base' (hp.alloc o).2.id)
        rw [Nat.add_zero, hbase, hprefix _ hz (by
          change parent.val + 1 + index.val < parent.val + 1 + (index.val + 1)
          omega)]
        dsimp only [m₁]
        rw [storeChildMachine_eq _ _ _ _ haddr]
        exact upd_same _ _ _
      | succ j =>
        change ((hp.alloc o).2.wk (childrenCopy hp₁ E hm k).ext ::
          (childrenCopy hp₁ E hm k).val.1)[j + 1]? = some v at hv
        change (childrenCopy hp₁ E hm k).val.1[j]? = some v at hv
        have hh := helem j v hv
        change m'.mem (parent.val + 1 + (index.val + 1) + j) = _ at hh
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    · intro addr hz haddr'
      rw [hprefix addr hz (by
        change addr < parent.val + 1 + (index.val + 1)
        omega)]
      dsimp only [m₁]
      rw [storeChildMachine_eq _ _ _ _ haddr]
      exact (upd_other _ _ (by omega)).trans
        (allocateMachine_other m cursor (wmod 0) addr (by omega) (by omega))

    · calc
        m' = {m₁ with mem := m'.mem} := hframe
        _ = {m with mem := m'.mem} := rfl

end Solidity.Evm.Memory.Objects
