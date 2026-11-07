import Solidity.Evm.MemoryStorageStructCopy

/-!
# Primitive fixed memory payloads copied to inline storage

Fixed arrays have no length header. This additive payload relation leaves the
legacy `StateRepr` and all its existing input claims unchanged. The code uses
the already-proved finite word loop, starting at the inline destination slot.
-/
-- Retain the existing typed payload proof reductions on Lean 4.35.
set_option backward.isDefEq.respectTransparency false

namespace Solidity.Evm.Memory
open Semantics

/-- The actual typed fixed-array heap payload occupies exactly `n` words. -/
structure FixedArrayRepr {H : HTy} {p : PrimTy} {n : Nat} (hp : Heap H)
    (r : HRef H (.fixed (.prim p) n)) (base : Fin W) (m : Machine) : Prop where
  space : base.val + n ≤ W
  elements : ∀ i v, (hp.get r).val[i]? = some v →
    ReprV p v (m.mem (base.val + i))

/-- Fixed payloads above the local frame; no source mutation is assumed. -/
structure FixedHeapRepr {H : HTy} (hp : Heap H) (base : Nat → Fin W)
    (frame : Nat) (m : Machine) : Prop where
  objects : ∀ {p : PrimTy} {n : Nat} (r : HRef H (.fixed (.prim p) n)),
    FixedArrayRepr hp r (base r.id) m
  above : ∀ {p : PrimTy} {n : Nat} (r : HRef H (.fixed (.prim p) n)), frame ≤ (base r.id).val

/-- A separate refinement: existing dynamic-array/struct inputs do not change. -/
structure FixedStateRepr (L b frame : Nat) {C : Contract} {Γ : Ctx} (F : Frag Γ)
    (σ : State C Γ) (base : Nat → Fin W) (m : Machine) : Prop where
  legacy : StateRepr L b frame F σ base m
  fixed : FixedHeapRepr σ.heap base frame m

theorem FixedArrayRepr.mem_eq {H : HTy} {p : PrimTy} {n : Nat} {hp : Heap H}
    {r : HRef H (.fixed (.prim p) n)} {base : Fin W} {m m' : Machine}
    (h : FixedArrayRepr hp r base m) (hm : m'.mem = m.mem) : FixedArrayRepr hp r base m' :=
  ⟨h.space, fun i v hv => by rw [hm]; exact h.elements i v hv⟩

theorem FixedHeapRepr.mem_eq {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {m m' : Machine} (h : FixedHeapRepr hp base frame m)
    (hm : m'.mem = m.mem) : FixedHeapRepr hp base frame m' :=
  ⟨fun r => (h.objects r).mem_eq hm, h.above⟩

theorem FixedArrayRepr.payloads {H : HTy} {p : PrimTy} {n : Nat} {hp : Heap H}
    {r : HRef H (.fixed (.prim p) n)} {base : Fin W} {m : Machine}
    (h : FixedArrayRepr hp r base m) :
    ∀ i, i < n → m.mem (base.val + i) = .val (payloadWord (m.mem (base.val + i))) := by
  intro i hi
  have hi' : i < (hp.get r).val.length := by rw [(hp.get r).property]; exact hi
  exact ReprV.payload (h.elements i ((hp.get r).val[i]'hi') (getElem?_pos _ i hi'))

/-- This is the actual shared structured word loop, not an unrolled sample. -/
def memoryFixedCopyCode (n : Nat) : List Instr := memoryStructCopyCode n

def fixedCopyStore (st : WordStore) (dst : Slot) (n : Nat) (words : Nat → Fin W) : WordStore :=
  rangeStore (fun i st => WordStore.write st (dst.add i) (words i).val) 0 n st

theorem memoryFixedCopy_run (m : Machine) (base : Fin W) (dst : Slot) (n : Nat)
    (words : Nat → Fin W) (hn : n < W) (hs : base.val + n ≤ W)
    (hw : ∀ i, i < n → m.mem (base.val + i) = .val (words i)) :
    run (memoryFixedCopyCode n) ((m.push (.val base)).push (.slot dst)) =
      .ok {m with store := fixedCopyStore m.store dst n words} 0 :=
  memoryStructCopy_run m base dst n words hn hs hw

/-- The source operation snapshots the actual fixed heap object. -/
theorem primitiveFixed_snapshot {H : HTy} {p : PrimTy} {n : Nat} (hp : Heap H)
    (r : HRef H (.fixed (.prim p) n)) :
    MVal.copyMToSt hp (T := .ref (.fixed (.prim p) n)) r =
      .fixed (SVec.ofLen SVal.prim n (hp.get r).val (hp.get r).property) := by
  simp only [MVal.copyMToSt, MVal.copyBelow, MVal.copyAt, MVal.copyRefAt]

theorem primitiveFixed_copy_repr {H : HTy} {p : PrimTy} {n : Nat} {hp : Heap H}
    {r : HRef H (.fixed (.prim p) n)} {base : Fin W} {m : Machine}
    (h : FixedArrayRepr hp r base m) (st : WordStore) (dst : Slot) (L : Nat) :
    ReprAt (fixedCopyStore st dst n (fun i => payloadWord (m.mem (base.val + i))))
      L (.ref (.fixed (.prim p) n)) dst (MVal.copyMToSt hp r) := by
  rw [primitiveFixed_snapshot]
  refine .fixed ?_
  intro i x hx
  rw [SVec.toList_ofLen, List.getElem?_map] at hx
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hx
  have hi : i < n := by
    have hl := lt_of_getElem? hv
    rwa [(hp.get r).property] at hl
  have hr := h.elements i v hv
  have he : (fixedCopyStore st dst n
      (fun i => payloadWord (m.mem (base.val + i)))).cells (dst.add i) =
      payloadWord (m.mem (base.val + i)) :=
    Fin.ext (rangeStore_written dst _ n 0 st i (Nat.zero_le _) (by omega))
  simp only [size_prim, Nat.mul_one]
  exact .prim (by rw [he, ← ReprV.payload hr]; exact hr)

/-- Fixed copies retain every slot outside their inline typed destination. -/
theorem fixedCopyStore_other {p : PrimTy} (st : WordStore) (dst : Slot) (n : Nat)
    (words : Nat → Fin W) (x : Slot) (hx : ¬ Occ (.ref (.fixed (.prim p) n)) dst x) :
    fixedCopyStore st dst n words x = st x := by
  apply rangeStore_other
  intro i _ hi he
  apply hx
  rw [he]
  simpa only [size_prim, Nat.mul_one] using
    (Occ.felem i (by omega) (E := .prim p) (s := dst) Occ.prim)

/-- Preserve all fixed payloads through a storage-only operation. -/
theorem FixedStateRepr.store {L b frame : Nat} {C : Contract} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : FixedStateRepr L b frame F σ base m) {stor : Storage C} {st : WordStore}
    (hs : ReprStore C L st stor) (hlen : ∀ x, LenSlot C x → m.store x ≤ st x) :
    FixedStateRepr L b frame F (σ.withStorage stor) base {m with store := st} :=
  ⟨h.legacy.store hs hlen, h.fixed.mem_eq rfl⟩


/-- Successful read-only copies derive both heap and target-memory preservation.
No heap-equality premise is assumed at entry. -/
def FixedResult {C : Contract} (L b frame : Nat) {Γ Δ : Ctx} (F : Frag Δ)
    (σ : State C Γ) (base : Nat → Fin W) (m : Machine)
    (source : TRes (Solidity.Out C σ.H Δ)) (target : Out) : Prop :=
  (∃ o m', source = .ok o ∧ target = .ok m' 0 ∧
    FixedStateRepr L b frame F o.st base m' ∧ m'.stack = m.stack ∧
    m'.mem = m.mem ∧ o.st.H = σ.H ∧ HEq o.st.heap σ.heap) ∨
  (source = .error .revert ∧ target = .revert)

def assignMemoryFixedCode {C : Contract} {Γ : Ctx} {p : PrimTy} {n : Nat} (b : Nat)
    (dst : Loc C Γ (.ref (.fixed (.prim p) n))) (pointer : List Instr) : List Instr :=
  pointer ++ Evm.compileLoc b dst ++ memoryFixedCopyCode n

attribute [local irreducible] run exec Instr.step loopRun

/-- Same-size primitive fixed-array copies through admitted source/storage paths,
with actual snapshot/write semantics and no length-slot invention. -/
theorem assignMemoryFixed_correct {C : Contract} {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : FixedStateRepr L b frame F σ base m) {p : PrimTy} {n : Nat}
    (dst : Loc C Γ (.ref (.fixed (.prim p) n)))
    (src : MPath C Γ (.ref (.fixed (.prim p) n)))
    (pointer : List Instr) (hp : PtrFrag b src pointer)
    (hl : locIn F false dst = true) (hn : n < W) :
    FixedResult L b frame F σ base m (TRun.assignFromMem dst src σ)
      (run (assignMemoryFixedCode b dst pointer) m) := by
  obtain ⟨r, hr, hptr⟩ := hp.correct h.legacy
  let words := fun i => payloadWord (m.mem ((base r.id).val + i))
  have harr := h.fixed.objects r
  rw [assignMemoryFixedCode, List.append_assoc, run_append_ok hptr]
  rcases loc_sim dst (h.legacy.core.push (.val (base r.id))) hl with
    ⟨sr, slot, old, hres, hold, hpath, _, hloc⟩ | ⟨hres, hloc⟩
  · rw [run_append_ok hloc]
    have hrun := memoryFixedCopy_run m (base r.id) slot n words hn harr.space harr.payloads
    rw [hrun]
    let copied := fixedCopyStore m.store slot n words
    have hsnap := primitiveFixed_copy_repr harr m.store slot L
    have hnew := (overlay_repr hsnap _ (Nat.lt_succ_self _) (by rfl)).2 old
    obtain ⟨st', hsave, hrep⟩ := save_repr h.legacy.core.store hpath ⟨old, hold⟩ hnew
      (fun x hx => fixedCopyStore_other (p := p) m.store slot n words x hx)
    have hwrite : σ.storage.write sr (MVal.copyMToSt σ.heap r) = some st' := by
      rw [write_ref _ _ _ (Sto.find_of_findLive hold)]
      exact hsave
    have hlen : ∀ x, LenSlot C x → m.store x ≤ copied x := by
      intro x hx
      have he : copied x = m.store x := rangeStore_other slot words x n 0 m.store (by
        intro i _ hi he
        have hoc : OccAt true (.ref (.fixed (.prim p) n)) slot (slot.add i) := by
          simpa only [size_prim, Nat.mul_one] using
            (OccAt.felem i (by omega) (E := .prim p) (s := slot) OccAt.prim)
        obtain ⟨T, ht, hp⟩ := hpath.occAt hoc
        exact len_prim_disjoint hx ⟨sr.root, T, ht, he ▸ hp⟩)
      rw [he]
      exact Nat.le_refl _
    refine .inl ⟨⟨σ.withStorage st', List.prefix_refl _⟩, {m with store := copied},
      ?_, rfl, h.store hrep hlen, rfl, rfl, rfl, HEq.rfl⟩
    simp only [TRun.assignFromMem, hr, hres, hwrite, bind, Except.bind, TRes.ofOpt, pure, Except.pure]
  · exact .inr ⟨by simp only [TRun.assignFromMem, hr, hres, bind, Except.bind], run_append_revert hloc⟩

end Solidity.Evm.Memory
