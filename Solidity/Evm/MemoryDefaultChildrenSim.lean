import Solidity.Evm.MemoryDefaultChildren

/-! A typed child builder may itself allocate several nested objects. This
simulation threads its actual source heap extension and positive exact cost. -/
namespace Solidity.Evm.Memory.Objects

theorem defaultChildren_sim {R : RefTy} {hm : (Ty.ref R).mapFree = true} {count : Nat}
    (builder : DefaultBuilder R hm count) {H : HTy} (hp : Heap H) (k : Nat)
    (base : Nat → Fin W) (frame : Nat) (m : Machine)
    (parent total index cursor : Fin W) (offset finish : Nat)
    (ha : AllocatorRepr hp base frame cursor m) (hg : Gap hp base parent.val finish)
    (hpframe : frame ≤ parent.val) (hspan : parent.val + offset + total.val ≤ finish)
    (hgap : finish ≤ cursor.val) (hi : index.val + k = total.val)
    (hs : cursor.val + k * count < W) :
    let g := defaultChildrenCopy hp R hm k
    ∃ base' m',
      loopIterN (run childrenCondition) (run (defaultChildrenBody offset builder.code)) (k + 1)
        (control m parent total index) = .inr (.ok (control m' parent total total) 0) ∧
      AllocatorRepr g.heap base' frame ⟨cursor.val + k * count, hs⟩ m' ∧
      Gap g.heap base' parent.val finish ∧ BaseExtends H base base' ∧
      (∀ j v, g.val.1[j]? = some v →
        m'.mem (parent.val + offset + index.val + j) = .val (base' v.id)) ∧
      m'.stack = m.stack ∧
      (∀ addr, 0 < addr → addr < parent.val + offset + index.val → m'.mem addr = m.mem addr) ∧
      m' = {m with mem := m'.mem} ∧
      (∀ lo hi, Gap hp base lo hi → hi ≤ cursor.val → Gap g.heap base' lo hi) := by
  induction k generalizing H hp base m index cursor with
  | zero =>
    have he : index = total := Fin.ext (by omega)
    subst index
    rw [defaultChildrenCopy_zero]
    refine ⟨base, m, ?_, ?_, hg, BaseExtends.refl base, ?_, rfl, (fun _ _ _ => rfl), rfl, (fun _ _ hg _ => hg)⟩
    · rw [loopIterN, defaultTurn_done]
    · simpa only [Nat.zero_mul, Nat.add_zero] using ha
    · intro j v hv
      cases hv
  | succ k ih =>
    have himore : index.val < total.val := by omega
    have hi' : index.val + 1 < W := Nat.lt_of_le_of_lt (by omega) total.isLt
    have hcost : cursor.val + count < W := by
      rw [Nat.succ_mul] at hs
      omega
    let index' : Fin W := ⟨index.val + 1, hi'⟩
    let cursor' : Fin W := ⟨cursor.val + count, hcost⟩
    let g₁ := hp.allocDefault R hm
    have hcinput : AllocatorRepr hp base frame cursor (control m parent total index) :=
      ha.stack _
    obtain ⟨base₁, controlled, hrun, ha₁, hroot, hbase, hcontrolled, hlow, hpreserve⟩ :=
      builder.correct hp base frame cursor (control m parent total index) hcinput hcost
    let childMachine : Machine := {m with mem := controlled.mem}
    have hcontrol : controlled = control childMachine parent total index := hcontrolled
    have hachild : AllocatorRepr g₁.heap base₁ frame cursor' childMachine := ha₁.mem_eq rfl
    let m₁ := defaultStoreMachine childMachine parent index cursor offset
    have haddr : parent.val + offset + index.val < W := by omega
    have hpzero : 0 < parent.val := Nat.lt_of_lt_of_le ha.free.reserved hpframe
    have hz : 0 < parent.val + offset + index.val := by omega
    have hg₁ : Gap g₁.heap base₁ parent.val finish := hpreserve _ _ hg hgap
    have halloc₁ : AllocatorRepr g₁.heap base₁ frame cursor' m₁ := by
      dsimp only [m₁]
      rw [defaultStoreMachine_eq _ _ _ _ _ haddr]
      exact hachild.writeGap hg₁ (by omega) (by omega) hz (by
        change finish ≤ cursor.val + count
        omega) _
    have hbody : run (defaultChildrenBody offset builder.code) (control m parent total index) =
        .ok (control m₁ parent total (wmod (index.val + 1))) 0 := by
      rw [defaultChildrenBody, run_append_ok hrun, hcontrol]
      exact defaultStoreStep_run childMachine parent total index cursor offset
    have hrest : index'.val + k = total.val := by change index.val + 1 + k = total.val; omega
    have hsrest : cursor'.val + k * count < W := by
      change cursor.val + count + k * count < W
      rw [Nat.succ_mul] at hs
      omega
    obtain ⟨base', m', hloop, ha', hg', hb', helem, hstack, hprefix, hframe, hallgaps⟩ :=
      ih g₁.heap base₁ m₁ index' cursor' halloc₁ hg₁ (by
        change finish ≤ cursor.val + count
        omega) hrest hsrest
    rw [defaultChildrenCopy_succ]
    refine ⟨base', m', ?_, ?_, hg', BaseExtends.trans g₁.ext hbase hb', ?_,
      hstack.trans rfl, ?_, ?_, ?_⟩
    · have hnext : wmod (index.val + 1) = index' := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hi'
      rw [loopIterN, defaultTurn_more himore hbody, hnext]
      exact hloop
    · have heq : cursor'.val + k * count = cursor.val + (k + 1) * count := by
        change cursor.val + count + k * count = cursor.val + (k + 1) * count
        rw [Nat.succ_mul]
        omega
      simpa only [heq] using ha'
    · intro j v hv
      cases j with
      | zero =>
        change (HRef.wk (defaultChildrenCopy g₁.heap R hm k).ext g₁.val ::
          (defaultChildrenCopy g₁.heap R hm k).val.1)[0]? = some v at hv
        cases hv
        have hbroot : base' g₁.val.id = cursor := (hb' g₁.val).trans hroot
        change m'.mem (parent.val + offset + index.val + 0) = .val (base' g₁.val.id)
        rw [Nat.add_zero, hbroot, hprefix _ hz (by
          change parent.val + offset + index.val < parent.val + offset + (index.val + 1)
          omega)]
        dsimp only [m₁]
        rw [defaultStoreMachine_eq _ _ _ _ _ haddr]
        exact upd_same _ _ _
      | succ j =>
        change (HRef.wk (defaultChildrenCopy g₁.heap R hm k).ext g₁.val ::
          (defaultChildrenCopy g₁.heap R hm k).val.1)[j + 1]? = some v at hv
        change (defaultChildrenCopy g₁.heap R hm k).val.1[j]? = some v at hv
        have hh := helem j v hv
        change m'.mem (parent.val + offset + (index.val + 1) + j) = _ at hh
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    · intro addr hz' hl
      rw [hprefix addr hz' (by
        change addr < parent.val + offset + (index.val + 1)
        omega)]
      dsimp only [m₁]
      rw [defaultStoreMachine_eq _ _ _ _ _ haddr]
      exact (upd_other _ _ (by omega)).trans (hlow addr hz' (by omega))
    · calc
        m' = {m₁ with mem := m'.mem} := hframe
        _ = {m with mem := m'.mem} := rfl

    · intro lo hi hg₀ hh
      exact hallgaps lo hi (hpreserve lo hi hg₀ hh) (by
        change hi ≤ cursor.val + count
        omega)

end Solidity.Evm.Memory.Objects
