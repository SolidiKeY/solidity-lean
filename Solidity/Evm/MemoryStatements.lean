import Solidity.Evm.MemoryLocals

/-!
# Memory programs with guards and primitive storage writes

The heap representation survives a primitive storage write because target
memory and source heap are unchanged. Storage aliases retain their validity
through the existing length-preservation lemma. A guard consumes its Boolean
value and either preserves the complete state relation or reverts.
-/
namespace Solidity.Evm.Memory

variable {C : Contract}

theorem StateRepr.store {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {stor : Storage C} {st : WordStore}
    (hs : ReprStore C L st stor) (hlen : ∀ x, LenSlot C x → m.store x ≤ st x) :
    StateRepr L b frame F (σ.withStorage stor) base {m with store := st} := by
  have hc := h.core.store' hs hlen
  exact ⟨⟨hc.store, hc.vals, hc.aliases, hc.net, hc.netSelf, hc.bound,
    hc.fragile, hc.env, hc.funds, hc.oracle⟩,
    ⟨fun r => ⟨(h.heap.arrays r).space, (h.heap.arrays r).length, (h.heap.arrays r).elements⟩,
      h.heap.above, h.heap.separated⟩, h.pointers, h.locals,
    ⟨fun r => ⟨(h.structs.objects r).space, (h.structs.objects r).fields⟩,
      h.structs.above, h.structs.separated⟩, h.separated, RefFieldsRepr.mem_eq h.refs rfl⟩

def storageAssignCode {Γ : Ctx} {p : PrimTy} (b : Nat)
    (l : Loc C Γ (.prim p)) (value : List Instr) : List Instr :=
  value ++ Evm.compileLoc b l ++ [.sstore]

theorem storageAssign_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy}
    (l : Loc C Γ (.prim p)) (v : Val C Γ p) (code : List Instr)
    (hl : locIn F false l = true) (hv : ValOutT p (v.evalT σ) (run code m) m) :
    ResultRepr L b frame F σ base m (TRun.assign l (.val v) σ)
      (run (storageAssignCode b l code) m) := by
  simp only [storageAssignCode, List.append_assoc]
  rcases hv with ⟨vv, w, hvv, hrv, hrun⟩ | ⟨hvv, hrun⟩
  · rw [run_append_ok hrun]
    rcases loc_sim l (h.core.push w) hl with ⟨r, s, sv, hres, hsv, hps, _, hrunl⟩ | ⟨hres, hrunl⟩
    · rw [run_append_ok hrunl]
      obtain ⟨a, rfl, hnew⟩ := repr_write (L := L) hrv m.store s
      obtain ⟨st', hst', hrep⟩ := save_repr h.core.store hps ⟨sv, hsv⟩ hnew
        (fun x hx => WordStore.write_other _ _ fun he => hx (he ▸ Occ.prim))
      refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩, {m with store := WordStore.write m.store s a},
        ?_, rfl, h.store hrep (upd_len hps a), rfl, ?_⟩
      · simp only [TRun.assign, Src.valueT, hvv, hres, bind, Except.bind, pure, Except.pure,
          Storage.write, SVal.isPrim, Ty.isPrimitive, ↓reduceIte, hst', TRes.ofOpt]
      · exact fun _ _ ha => ha.mem_eq rfl
    · exact .inr ⟨by simp only [TRun.assign, Src.valueT, hvv, hres,
        bind, Except.bind, pure, Except.pure], run_append_revert hrunl⟩
  · exact .inr ⟨by simp only [TRun.assign, Src.valueT, hvv, bind, Except.bind],
      run_append_revert hrun⟩

theorem requireValue_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) (c : Val C Γ .bool) (code : List Instr)
    (hc : ValOutT .bool (c.evalT σ) (run code m) m) :
    ResultRepr L b frame F σ base m (TRun.require c σ) (run (code ++ assertTop) m) := by
  rcases hc with ⟨vc, wc, hvc, hrc, hrunc⟩ | ⟨hvc, hrunc⟩
  · obtain rfl := hrc.bool_inv
    cases vc
    · exact .inr ⟨by simp only [TRun.require, hvc, bind, Except.bind,
        Solidity.boolT, Bool.false_eq_true, ↓reduceIte], by rw [run_append_skip hrunc]; rfl⟩
    · exact .inl ⟨⟨σ, List.prefix_refl _⟩, m,
        by simp only [TRun.require, hvc, bind, Except.bind, Solidity.boolT, ↓reduceIte, pure, Except.pure],
        by rw [run_append_skip hrunc]; rfl, h, rfl, fun _ _ ha => ha⟩
  · exact .inr ⟨by simp only [TRun.require, hvc, bind, Except.bind], run_append_revert hrunc⟩

end Solidity.Evm.Memory
