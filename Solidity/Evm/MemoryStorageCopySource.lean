import Solidity.Evm.MemoryStorageCopyLaws
import Solidity.Evm.MemoryStatements

/-!
# Source simulation of runtime-length memory-to-storage copies

Source pointers are evaluated before destination paths. Destination failure
reverts before any store. Successful copies keep every memory object and
allocator cell, and discard fragile storage aliases because length can shrink.
-/
namespace Solidity.Evm.Memory
open Semantics
variable {C : Contract}

theorem StateRepr.storeDrop {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {stor : Storage C} {st : WordStore}
    (hs : ReprStore C L st stor) :
    StateRepr L b frame F.dropFragile (σ.withStorage stor) base {m with store := st} := by
  have hc := h.core.storeDrop hs
  exact ⟨⟨hc.store, hc.vals, hc.aliases, hc.net, hc.netSelf, hc.bound,
    hc.fragile, hc.env, hc.funds, hc.oracle⟩,
    ⟨fun r => ⟨(h.heap.arrays r).space, (h.heap.arrays r).length, (h.heap.arrays r).elements⟩,
      h.heap.above, h.heap.separated⟩, h.pointers, h.locals,
    ⟨fun r => ⟨(h.structs.objects r).space, (h.structs.objects r).fields⟩,
      h.structs.above, h.structs.separated⟩, h.separated, RefFieldsRepr.mem_eq h.refs rfl⟩

def assignMemoryArrayCode {Γ : Ctx} {p : PrimTy} (b : Nat)
    (dst : Loc C Γ (.ref (.array (.prim p)))) (pointer : List Instr) : List Instr :=
  pointer ++ Evm.compileLoc b dst ++ memoryArrayCopyCode

attribute [local irreducible] run exec Instr.step loopRun

/-- General typed source/machine simulation, including destination bounds
failure, arbitrary represented payloads and exact source deep-copy semantics. -/
theorem assignMemoryArray_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) {p : PrimTy}
    (dst : Loc C Γ (.ref (.array (.prim p)))) (src : MPath C Γ (.ref (.array (.prim p))))
    (pointer : List Instr) (hp : PtrFrag b src pointer) (hl : locIn F false dst = true)
    (hbound : ∀ r sr, src.mvalT σ = .ok r → dst.resolveT σ = .ok sr → σ.heap.len r .dyn < L) :
    ResultRepr L b frame F.dropFragile σ base m (TRun.assignFromMem dst src σ)
      (run (assignMemoryArrayCode b dst pointer) m) := by
  obtain ⟨r, hr, hptr⟩ := hp.correct h
  let n := σ.heap.len r .dyn
  let words := fun i => payloadWord (m.mem ((base r.id).val + 1 + i))
  have harr := h.heap.arrays r
  have hw : ∀ i, i < n → m.mem ((base r.id).val + 1 + i) = .val (words i) := by
    intro i hi
    let v := (MObj.elems .dyn (σ.heap.get r))[i]'hi
    exact ReprV.payload (harr.elements i v (getElem?_pos _ i hi))
  rw [assignMemoryArrayCode, List.append_assoc, run_append_ok hptr]
  rcases loc_sim dst (h.core.push (.val (base r.id))) hl with
    ⟨sr, slot, old, hres, hold, hpath, _, hloc⟩ | ⟨hres, hloc⟩
  · rw [run_append_ok hloc]
    have hrun := memoryArrayCopy_run m (base r.id) slot n words
      (σ.heap.len_dyn_lt r) harr.space harr.length hw
    rw [hrun]
    have hnew := primitiveArray_copy_repr harr m.store slot L (hbound r sr hr hres) old
    obtain ⟨st', hsave, hrep⟩ := save_repr h.core.store hpath ⟨old, hold⟩ hnew
      (fun x hx => arrayCopyStore_other (p := p) m.store slot n words x hx)
    have hwrite : σ.storage.write sr (MVal.copyMToSt σ.heap (T := .ref (.array (.prim p))) r) = some st' := by
      rw [write_ref _ _ _ (Sto.find_of_findLive hold)]
      exact hsave
    refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩,
      {m with store := arrayCopyStore m.store slot n words}, ?_, rfl,
      h.storeDrop hrep, rfl, fun _ _ ha => ha.mem_eq rfl⟩
    simp only [TRun.assignFromMem, hr, hres, hwrite, bind, Except.bind, TRes.ofOpt, pure, Except.pure]
  · exact .inr ⟨by simp only [TRun.assignFromMem, hr, hres, bind, Except.bind], run_append_revert hloc⟩

end Solidity.Evm.Memory
