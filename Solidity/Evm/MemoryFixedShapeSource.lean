import Solidity.Evm.MemoryFixedShapeLaws

/-! Actual fixed-source assignment simulations, including destination failure. -/
namespace Solidity.Evm.Memory
open Semantics

theorem FixedStateRepr.storeDrop {L b frame : Nat} {C : Contract} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : FixedStateRepr L b frame F σ base m) {stor : Storage C} {st : WordStore}
    (hs : ReprStore C L st stor) :
    FixedStateRepr L b frame F.dropFragile (σ.withStorage stor) base {m with store := st} :=
  ⟨h.legacy.storeDrop hs, h.fixed.mem_eq rfl⟩

def assignFixedDynamicCode {C : Contract} {Γ : Ctx} {p : PrimTy} (b n : Nat)
    (dst : Loc C Γ (.ref (.array (.prim p)))) (pointer : List Instr) : List Instr :=
  pointer ++ Evm.compileLoc b dst ++ memoryFixedDynamicCode n

def assignFixedPadCode {C : Contract} {Γ : Ctx} {p : PrimTy} {k : Nat} (b n : Nat)
    (dst : Loc C Γ (.ref (.fixed (.prim p) k))) (pointer : List Instr) : List Instr :=
  pointer ++ Evm.compileLoc b dst ++ memoryFixedPadCode n k

attribute [local irreducible] run exec Instr.step loopRun

theorem assignFixedDynamic_correct {C : Contract} {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : FixedStateRepr L b frame F σ base m) {p : PrimTy} {n : Nat}
    (dst : Loc C Γ (.ref (.array (.prim p)))) (src : MPath C Γ (.ref (.fixed (.prim p) n)))
    (pointer : List Instr) (hp : PtrFrag b src pointer) (hl : locIn F false dst = true)
    (hn : n < W) (hbound : ∀ r sr, src.mvalT σ = .ok r → dst.resolveT σ = .ok sr → n < L) :
    FixedResult L b frame F.dropFragile σ base m
      (TRun.assign dst (.fixedCopyMem src (.dynamic hn)) σ)
      (run (assignFixedDynamicCode b n dst pointer) m) := by
  obtain ⟨r, hr, hptr⟩ := hp.correct h.legacy
  let words := fun i => payloadWord (m.mem ((base r.id).val + i))
  have harr := h.fixed.objects r
  rw [assignFixedDynamicCode, List.append_assoc, run_append_ok hptr]
  rcases loc_sim dst (h.legacy.core.push (.val (base r.id))) hl with
    ⟨sr, slot, old, hres, hold, hpath, _, hloc⟩ | ⟨hres, hloc⟩
  · rw [run_append_ok hloc, memoryFixedDynamic_run m (base r.id) slot n words hn harr.space harr.payloads]
    have hnew := primitiveFixed_dynamic_repr harr m.store slot L hn (hbound r sr hr hres) old
    obtain ⟨st', hsave, hrep⟩ := save_repr h.legacy.core.store hpath ⟨old, hold⟩ hnew
      (fun x hx => arrayCopyStore_other (p := p) m.store slot n words x hx)
    have hwrite : σ.storage.write sr ((FixedCopy.dynamic hn).apply (MVal.copyMToSt σ.heap r)) = some st' := by
      rw [write_ref _ _ _ (Sto.find_of_findLive hold)]
      exact hsave
    refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩,
      {m with store := arrayCopyStore m.store slot n words}, ?_, rfl,
      h.storeDrop hrep, rfl, rfl, rfl, HEq.rfl⟩
    simp only [TRun.assign, Src.valueT, hr, hres, hwrite, bind, Except.bind, TRes.ofOpt, pure, Except.pure]
  · exact .inr ⟨by simp only [TRun.assign, Src.valueT, hr, hres, bind, Except.bind, pure, Except.pure], run_append_revert hloc⟩

theorem assignFixedPad_correct {C : Contract} {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : FixedStateRepr L b frame F σ base m) {p : PrimTy} {n k : Nat}
    (dst : Loc C Γ (.ref (.fixed (.prim p) k))) (src : MPath C Γ (.ref (.fixed (.prim p) n)))
    (pointer : List Instr) (hp : PtrFrag b src pointer) (hl : locIn F false dst = true)
    (hfit : n ≤ k) (hk : k < W) :
    FixedResult L b frame F σ base m
      (TRun.assign dst (.fixedCopyMem src (.fixed k hfit)) σ)
      (run (assignFixedPadCode b n dst pointer) m) := by
  obtain ⟨r, hr, hptr⟩ := hp.correct h.legacy
  let words := fun i => payloadWord (m.mem ((base r.id).val + i))
  have harr := h.fixed.objects r
  rw [assignFixedPadCode, List.append_assoc, run_append_ok hptr]
  rcases loc_sim dst (h.legacy.core.push (.val (base r.id))) hl with
    ⟨sr, slot, old, hres, hold, hpath, _, hloc⟩ | ⟨hres, hloc⟩
  · rw [run_append_ok hloc, memoryFixedPad_run m (base r.id) slot n k words (by omega) hk harr.space harr.payloads]
    let copied := fixedPadStore m.store slot n k words
    have hsnap := primitiveFixed_pad_repr harr m.store slot L hfit
    have hnew := (overlay_repr hsnap _ (Nat.lt_succ_self _) (by rfl)).2 old
    obtain ⟨st', hsave, hrep⟩ := save_repr h.legacy.core.store hpath ⟨old, hold⟩ hnew
      (fun x hx => fixedPadStore_other (p := p) m.store slot n k words hfit x hx)
    have hwrite : σ.storage.write sr ((FixedCopy.fixed k hfit).apply (MVal.copyMToSt σ.heap r)) = some st' := by
      rw [write_ref _ _ _ (Sto.find_of_findLive hold)]
      exact hsave
    have hlen : ∀ x, LenSlot C x → m.store x ≤ copied x := by
      intro x hx
      have hout : ∀ i, i < k → x ≠ slot.add i := by
        intro i hi he
        have hoc : OccAt true (.ref (.fixed (.prim p) k)) slot (slot.add i) := by
          simpa only [size_prim, Nat.mul_one] using
            (OccAt.felem i hi (E := .prim p) (s := slot) OccAt.prim)
        obtain ⟨T, ht, hp⟩ := hpath.occAt hoc
        exact len_prim_disjoint hx ⟨sr.root, T, ht, he ▸ hp⟩
      have he : copied x = m.store x := by
        unfold copied fixedPadStore
        have hz : (fun i st => WordStore.write st (slot.add i) 0) =
          (fun i st => WordStore.write st (slot.add i) ((fun _ => wmod 0) i).val) := rfl
        rw [hz, rangeStore_other slot (fun _ => wmod 0) x _ _ _ (by
          intro i _ hi; exact hout i (by omega))]
        exact rangeStore_other slot words x n 0 m.store (by intro i _ hi; exact hout i (by omega))
      rw [he]
      exact Nat.le_refl _
    refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩, {m with store := copied},
      ?_, rfl, h.store hrep hlen, rfl, rfl, rfl, HEq.rfl⟩
    simp only [TRun.assign, Src.valueT, hr, hres, hwrite, bind, Except.bind, TRes.ofOpt, pure, Except.pure]
  · exact .inr ⟨by simp only [TRun.assign, Src.valueT, hr, hres, bind, Except.bind, pure, Except.pure], run_append_revert hloc⟩

end Solidity.Evm.Memory
