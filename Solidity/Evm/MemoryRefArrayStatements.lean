import Solidity.Evm.MemoryRefArrayPaths

/-! Source statements using fallible reference-array pointers. -/
namespace Solidity.Evm.Memory
open Semantics
variable {C : Contract}

def RefArrayResultRepr {Γ Δ : Ctx} (L b frame : Nat) (F : Frag Δ) (σ : State C Γ)
    (base : Nat → Fin W) (m : Machine) (res : TRes (Solidity.Out C σ.H Δ)) (out : Out) : Prop :=
  (∃ o m', res = .ok o ∧ out = .ok m' 0 ∧ RefArrayStateRepr L b frame F o.st base m' ∧
    m'.stack = m.stack) ∨ (res = .error .revert ∧ out = .revert)

theorem RefPtrFrag.run_of_eval {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : RefArrayStateRepr L b frame F σ base m) {R : RefTy}
    {src : MPath C Γ (.ref R)} {code : List Instr} (hs : RefPtrFrag b F src code)
    {r : HRef σ.H R} (hr : src.mvalT σ = .ok r) :
    run code m = .ok (m.push (.val (base r.id))) 0 := by
  rcases hs.correct h with ⟨q, hq, hc⟩ | ⟨hq, _⟩
  · cases Except.ok.inj (hq.symm.trans hr)
    exact hc
  · cases hq.symm.trans hr

theorem RefPtrFrag.rebind {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : RefArrayStateRepr L b frame F σ base m) {R : RefTy}
    {src : MPath C Γ (.ref R)} {code : List Instr} (hs : RefPtrFrag b F src code)
    (dst : Idx Γ (.mem R)) :
    RefArrayResultRepr L b frame F σ base m (TRun.rebindMem dst (.alias src) σ)
      (run (code ++ [.mstore (cellOf b dst)]) m) := by
  rcases hs.correct h with ⟨r, hr, hc⟩ | ⟨hr, hc⟩
  · refine .inl ⟨⟨σ.setLocal dst (some r), List.prefix_refl _⟩, _, ?_, ?_, h.setMem dst r, rfl⟩
    · simp only [TRun.rebindMem, MRhs.evalT, hr, bind, Except.bind, pure, Except.pure]
    · rw [run_append_ok hc]
      rfl
  · refine .inr ⟨?_, run_append_revert hc⟩
    simp only [TRun.rebindMem, MRhs.evalT, hr, bind, Except.bind]

theorem RefPtrFrag.writeReference {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : RefArrayStateRepr L b frame F σ base m) {R : RefTy}
    {dst : MPath C Γ (.ref (.array (.ref R)))} {src : MPath C Γ (.ref R)}
    {pointer value : List Instr} (hd : RefPtrFrag b F dst pointer) (hs : RefPtrFrag b F src value)
    (i : Val C Γ .uint) (hi : valIn F i = true) :
    RefArrayResultRepr L b frame F σ base m
      (TRun.assignMem (.index .dyn dst i) (.ref src) σ)
      (run (value ++ pointer ++ compileVal b i ++ writeArrayStackCode) m) := by
  simp only [RefArrayResultRepr, TRun.assignMem, MSrc.mvalT, bind, Except.bind]
  rw [List.append_assoc, List.append_assoc]
  rcases hs.correct h with ⟨v, hv, hcv⟩ | ⟨hv, hcv⟩
  · rw [hv, run_append_ok hcv]
    rcases hd.correct (h.push (.val (base v.id))) with ⟨r, hr, hcr⟩ | ⟨hr, hcr⟩
    · simp only [MLoc.addrT, hr, bind, Except.bind]
      rw [run_append_ok hcr]
      have harr := h.arrays.arrays r
      rcases val_sim i ((h.state.push (.val (base v.id))).push (.val (base r.id))).core hi with
        ⟨iv, iw, hiv, hiw, hic⟩ | ⟨hiv, hic⟩
      · obtain ⟨a, ha, hva, rfl⟩ := hiw.uint_inv
        have he : iv = indexValue ⟨a, ha⟩ := Subtype.ext hva
        subst iv
        rw [hiv, run_append_ok hic, writeArrayStackCode,
          arrayStack_append_eq (m.push (.val (base v.id))) (base r.id) ⟨a, ha⟩ _
            (σ.heap.len_dyn_lt r) harr.length, ← writeArrayCode]
        simp only [pure, Except.pure]
        rcases harr.write ⟨a, ha⟩ v with ⟨hp', hpwrite, hrun, _⟩ | ⟨hpwrite, hrun⟩
        · rw [hpwrite, hrun]
          have hin : a < (MObj.elems .dyn (σ.heap.get r)).length := by
            by_cases hn : a < (MObj.elems .dyn (σ.heap.get r)).length
            · exact hn
            · simp only [Heap.writeAddr, Heap.setIndex, indexValue, Int.toNat_natCast,
                if_neg hn] at hpwrite
              cases hpwrite
          have he : hp' = σ.heap.set r (MObj.setElem .dyn (σ.heap.get r) a v) := by
            simpa only [Heap.writeAddr, Heap.setIndex, indexValue, Int.toNat_natCast,
              if_pos hin, Option.some.injEq] using hpwrite.symm
          subst hp'
          exact .inl ⟨⟨σ.withHeap (σ.heap.set r (MObj.setElem .dyn (σ.heap.get r) a v)), List.prefix_refl _⟩, _, rfl, rfl, h.setReference r a hin v, rfl⟩
        · rw [hpwrite, hrun]
          exact .inr ⟨rfl, rfl⟩
      · rw [hiv, run_append_revert hic]
        exact .inr ⟨rfl, rfl⟩
    · refine .inr ⟨?_, run_append_revert hcr⟩
      simp only [MLoc.addrT, hr, bind, Except.bind]
  · rw [hv, run_append_revert hcv]
    exact .inr ⟨rfl, rfl⟩

theorem RefPtrFrag.writePrimitive {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : RefArrayStateRepr L b frame F σ base m) {p : PrimTy}
    {dst : MPath C Γ (.ref (.array (.prim p)))} {pointer : List Instr}
    (hd : RefPtrFrag b F dst pointer) (v : Val C Γ p) (hv : valIn F v = true)
    (i : Val C Γ .uint) (hi : valIn F i = true) :
    RefArrayResultRepr L b frame F σ base m
      (TRun.assignMem (.index .dyn dst i) (.val v) σ)
      (run (compileVal b v ++ pointer ++ compileVal b i ++ writeArrayStackCode) m) := by
  simp only [RefArrayResultRepr, TRun.assignMem, MSrc.mvalT, bind, Except.bind]
  rw [List.append_assoc, List.append_assoc]
  rcases val_sim v h.state.core hv with ⟨x, w, hx, hw, hcv⟩ | ⟨hx, hcv⟩
  · rw [hx, run_append_ok hcv]
    rcases hd.correct (h.push w) with ⟨r, hr, hcr⟩ | ⟨hr, hcr⟩
    · simp only [MLoc.addrT, hr, bind, Except.bind]
      rw [run_append_ok hcr]
      have harr := h.state.heap.arrays r
      rcases val_sim i ((h.state.push w).push (.val (base r.id))).core hi with
        ⟨iv, iw, hiv, hiw, hic⟩ | ⟨hiv, hic⟩
      · obtain ⟨a, ha, hva, rfl⟩ := hiw.uint_inv
        have he : iv = indexValue ⟨a, ha⟩ := Subtype.ext hva
        subst iv
        rw [hiv, run_append_ok hic, writeArrayStackCode,
          arrayStack_append_eq (m.push w) (base r.id) ⟨a, ha⟩ _
            (σ.heap.len_dyn_lt r) harr.length, ← writeArrayCode]
        simp only [pure, Except.pure]
        rcases writeArray_correct harr ⟨a, ha⟩ x w hw with
          ⟨hp', hpwrite, hrun, _⟩ | ⟨hpwrite, hrun⟩
        · rw [hpwrite, hrun]
          have hin : a < (MObj.elems .dyn (σ.heap.get r)).length := by
            by_cases hn : a < (MObj.elems .dyn (σ.heap.get r)).length
            · exact hn
            · simp only [Heap.writeAddr, Heap.setIndex, indexValue, Int.toNat_natCast,
                if_neg hn] at hpwrite
              cases hpwrite
          have he : hp' = σ.heap.set r (MObj.setElem .dyn (σ.heap.get r) a x) := by
            simpa only [Heap.writeAddr, Heap.setIndex, indexValue, Int.toNat_natCast,
              if_pos hin, Option.some.injEq] using hpwrite.symm
          subst hp'
          exact .inl ⟨⟨σ.withHeap (σ.heap.set r (MObj.setElem .dyn (σ.heap.get r) a x)),
            List.prefix_refl _⟩, _, rfl, rfl, h.setPrimitive r a hin x w hw, rfl⟩
        · rw [hpwrite, hrun]
          exact .inr ⟨rfl, rfl⟩
      · rw [hiv, run_append_revert hic]
        exact .inr ⟨rfl, rfl⟩
    · refine .inr ⟨?_, run_append_revert hcr⟩
      simp only [MLoc.addrT, hr, bind, Except.bind]
  · rw [hx, run_append_revert hcv]
    exact .inr ⟨rfl, rfl⟩

end Solidity.Evm.Memory
