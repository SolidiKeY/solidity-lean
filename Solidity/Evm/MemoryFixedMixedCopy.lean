import Solidity.Evm.MemoryFixedShapeSource

/-! Dynamic-array and primitive-struct copies preserve the additive fixed
payload relation, so all supported copy families compose in one read-only route. -/
namespace Solidity.Evm.Memory
open Semantics
variable {C : Contract}
attribute [local irreducible] run exec Instr.step loopRun

theorem assignFixedAwareArray_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : FixedStateRepr L b frame F σ base m) {p : PrimTy}
    (dst : Loc C Γ (.ref (.array (.prim p)))) (src : MPath C Γ (.ref (.array (.prim p))))
    (pointer : List Instr) (hp : PtrFrag b src pointer) (hl : locIn F false dst = true)
    (hbound : ∀ r sr, src.mvalT σ = .ok r → dst.resolveT σ = .ok sr → σ.heap.len r .dyn < L) :
    FixedResult L b frame F.dropFragile σ base m (TRun.assignFromMem dst src σ)
      (run (assignMemoryArrayCode b dst pointer) m) := by
  obtain ⟨r, hr, hptr⟩ := hp.correct h.legacy
  let n := σ.heap.len r .dyn
  let words := fun i => payloadWord (m.mem ((base r.id).val + 1 + i))
  have harr := h.legacy.heap.arrays r
  have hw : ∀ i, i < n → m.mem ((base r.id).val + 1 + i) = .val (words i) := by
    intro i hi
    let v := (MObj.elems .dyn (σ.heap.get r))[i]'hi
    exact ReprV.payload (harr.elements i v (getElem?_pos _ i hi))
  rw [assignMemoryArrayCode, List.append_assoc, run_append_ok hptr]
  rcases loc_sim dst (h.legacy.core.push (.val (base r.id))) hl with
    ⟨sr, slot, old, hres, hold, hpath, _, hloc⟩ | ⟨hres, hloc⟩
  · rw [run_append_ok hloc]
    have hrun := memoryArrayCopy_run m (base r.id) slot n words
      (σ.heap.len_dyn_lt r) harr.space harr.length hw
    rw [hrun]
    have hnew := primitiveArray_copy_repr harr m.store slot L (hbound r sr hr hres) old
    obtain ⟨st', hsave, hrep⟩ := save_repr h.legacy.core.store hpath ⟨old, hold⟩ hnew
      (fun x hx => arrayCopyStore_other (p := p) m.store slot n words x hx)
    have hwrite : σ.storage.write sr (MVal.copyMToSt σ.heap (T := .ref (.array (.prim p))) r) = some st' := by
      rw [write_ref _ _ _ (Sto.find_of_findLive hold)]
      exact hsave
    refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩,
      {m with store := arrayCopyStore m.store slot n words}, ?_, rfl,
      h.storeDrop hrep, rfl, rfl, rfl, HEq.rfl⟩
    simp only [TRun.assignFromMem, hr, hres, hwrite, bind, Except.bind, TRes.ofOpt, pure, Except.pure]
  · exact .inr ⟨by simp only [TRun.assignFromMem, hr, hres, bind, Except.bind], run_append_revert hloc⟩


theorem assignFixedAwareStruct_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : FixedStateRepr L b frame F σ base m) {s : Name}
    (dst : Loc C Γ (.ref (.struct s))) (src : MPath C Γ (.ref (.struct s)))
    (pointer : List Instr) (hp : PtrFrag b src pointer) (hl : locIn F false dst = true)
    (hprim : primitiveMembers (structDef s) = true)
    (hst : static (.ref (.struct s)) = true) (hfit : (structDef s).length < W) :
    FixedResult L b frame F σ base m (TRun.assignFromMem dst src σ)
      (run (assignMemoryStructCode b dst pointer) m) := by
  obtain ⟨r, hr, hptr⟩ := hp.correct h.legacy
  let n := (structDef s).length
  let words := fun i => payloadWord (m.mem ((base r.id).val + i))
  have hs := h.legacy.structs.objects r
  rw [assignMemoryStructCode, List.append_assoc, run_append_ok hptr]
  rcases loc_sim dst (h.legacy.core.push (.val (base r.id))) hl with
    ⟨sr, slot, old, hres, hold, hpath, _, hloc⟩ | ⟨hres, hloc⟩
  · rw [run_append_ok hloc]
    have hrun := memoryStructCopy_run m (base r.id) slot n words hfit hs.space (hs.payloads hprim)
    rw [hrun]
    let copied := rangeStore (fun i st => WordStore.write st (slot.add i) (words i).val) 0 n m.store
    have hn := primitiveStruct_copy_repr hs hprim m.store slot L
    have hnew := (overlay_repr hn _ (Nat.lt_succ_self _) hst).2 old
    obtain ⟨st', hsave, hrep⟩ := save_repr h.legacy.core.store hpath ⟨old, hold⟩ hnew
      (fun x hx => primitiveStruct_copy_other hprim m.store slot words x hx)
    have hwrite : σ.storage.write sr (MVal.copyMToSt σ.heap (T := .ref (.struct s)) r) = some st' := by
      rw [write_ref _ _ _ (Sto.find_of_findLive hold)]
      exact hsave
    have hlen : ∀ x, LenSlot C x → m.store x ≤ copied x := by
      intro x hx
      have he : copied x = m.store x := rangeStore_other slot words x n 0 m.store (by
        intro i _ hi he
        obtain ⟨f, p, hf, ho⟩ := primitiveField_at hprim (structDef_nodup s) i (by omega)
        have hoc : OccAt true (.ref (.struct s)) slot (slot.add i) := by
          rw [← ho, ← primitiveField_offset hprim f]
          exact .field hf .prim
        obtain ⟨T, ht, hp⟩ := hpath.occAt hoc
        exact len_prim_disjoint hx ⟨sr.root, T, ht, he ▸ hp⟩)
      rw [he]
      exact Nat.le_refl _
    refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩, {m with store := copied}, ?_, rfl,
      h.store hrep hlen, rfl, rfl, rfl, HEq.rfl⟩
    simp only [TRun.assignFromMem, hr, hres, hwrite, bind, Except.bind, TRes.ofOpt, pure, Except.pure]
  · exact .inr ⟨by simp only [TRun.assignFromMem, hr, hres, bind, Except.bind], run_append_revert hloc⟩

end Solidity.Evm.Memory
