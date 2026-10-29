import Solidity.Evm.MemoryObjectGrow
import Solidity.Typing.Values

/-! Empty reference arrays allocate their own positive object reservation.
No child default is fabricated; their source copy has no child elements. -/
namespace Solidity.Evm.Memory.Objects
open Semantics

def emptyArray {H : HTy} (E : Ty) : MObj H (.array E) := ⟨[], W_pos⟩

theorem emptyArray_copy {H : HTy} (hp : Heap H) (E : Ty)
    (hm : (Ty.ref (.array E)).mapFree = true) :
    hp.allocDefault (.array E) hm =
      Grown.alloc ⟨List.prefix_refl H, hp, emptyArray E⟩ := by
  rw [Heap.allocDefault, SVal.dflt_array, SVal.copyStToM_array, SVec.copyStToM_nil]
  rfl

theorem newEmptyArray_copy {H : HTy} (hp : Heap H) (E : Ty)
    (hm : (Ty.ref (.array E)).mapFree = true) (hn : (RefTy.array E).newArrOk = true) :
    (newArrT (.array E) (indexValue (wmod 0)) hn).copyStToM hp hm =
      Grown.alloc ⟨List.prefix_refl H, hp, emptyArray E⟩ := by
  with_unfolding_all rfl

/-- The complete allocator is retained across real empty-array heap growth. -/
theorem AllocatorRepr.allocateEmpty {H : HTy} {hp : Heap H} {base : Nat → Fin W}
    {frame : Nat} {cursor : Fin W} {m : Machine}
    (h : AllocatorRepr hp base frame cursor m) (E : Ty) (hs : cursor.val + 1 < W) :
    AllocatorRepr (hp.alloc (emptyArray E)).1 (upd base H.length cursor) frame
      ⟨cursor.val + 1, hs⟩ (allocateMachine m cursor (wmod 0)) := by
  let o : MObj H (.array E) := emptyArray E
  let e := List.prefix_append H [.array E]
  have hk : Heap.Keeps e hp (hp.alloc o).1 := fun r => Heap.keeps_alloc hp o r
  have hlen : (hp.alloc o).1.len (hp.alloc o).2 .dyn = 0 := by
    simp only [Heap.len, Heap.get_alloc, MObj.elems_dyn, MObj.wk, o, emptyArray,
      List.map_nil, List.length_nil]
  have hc : cells (hp.alloc o).1 (hp.alloc o).2 = 1 := by
    simp only [cells, hlen, Nat.add_zero]
  have hf : ArrayRepr (hp.alloc o).1 (hp.alloc o).2 .dyn (upd base H.length cursor)
      (allocateMachine m cursor (wmod 0)) := by
    refine ⟨?_, ?_, ?_⟩
    · change (upd base H.length cursor H.length).val + cells (hp.alloc o).1 (hp.alloc o).2 ≤ W
      rw [upd_same, hc]
      omega
    · intro hh
      change (allocateMachine m cursor (wmod 0)).mem (upd base H.length cursor H.length).val = _
      rw [upd_same, hlen, allocateMachine_header]
      have hz := h.free.reserved
      have hb := h.free.above
      omega
    · intro i v hv
      simp only [Heap.get_alloc, MObj.elems_dyn, MObj.wk, o, emptyArray,
        List.map_nil, List.getElem?_nil] at hv
      cases hv
  refine ⟨(h.headerOutside (wmod 0)).adoptArray .dyn o cursor h.free.above hf
    (fun r => .inl (h.live r)), ?_, ?_⟩
  · simpa only [Fin.val_mk, show (wmod 0).val = 0 from rfl, Nat.add_zero] using
      h.free.allocate (wmod 0) (by simpa only [show (wmod 0).val = 0 from rfl, Nat.add_zero] using hs)
  · intro R r
    rcases allocRef_split hp o r with ⟨q, rfl⟩ | ⟨ht, he⟩
    · change (upd base H.length cursor q.id).val + cells (hp.alloc o).1 (q.wk e) ≤ cursor.val + 1
      rw [upd_other base cursor (Nat.ne_of_lt q.id_lt), cells_keeps e hk]
      exact Nat.le_trans (h.live q) (Nat.le_add_right _ _)
    · cases ht; cases he
      change (upd base H.length cursor H.length).val + cells (hp.alloc o).1 (hp.alloc o).2 ≤ cursor.val + 1
      rw [upd_same, hc]
      exact Nat.le_refl _

variable {C : Contract}

theorem defaultEmpty_decl {Γ : Ctx} (σ : State C Γ) (E : Ty)
    (hm : (Ty.ref (.array E)).mapFree = true) :
    TRun.declMem (.array E) none hm σ =
      .ok ⟨σ.allocPush (emptyArray E), List.prefix_append _ _⟩ := by
  have he := emptyArray_copy σ.heap E hm
  simp only [TRun.declMem, State.allocDefaultG, State.grow, pure, Except.pure]
  with_unfolding_all exact State.adopt_push_alloc σ _ _ he _ _

theorem StateRepr.allocateEmpty {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : AllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    (E : Ty) (hs : cursor.val + 1 < W) :
    StateRepr L b frame F (σ.alloc (emptyArray E)).1
      (upd base σ.H.length cursor) (allocateMachine m cursor (wmod 0)) := by
  have hm : ∀ l, b ≤ l → l < b + Γ.length →
      (allocateMachine m cursor (wmod 0)).mem (cell l) = m.mem (cell l) := by
    intro l hl hu
    have hf := ha.free.above
    have hh := h.locals
    exact allocateMachine_other m cursor (wmod 0) l (by omega) (by omega)
  have hc := (h.core.congrMem hm).congrLook
    (fun i => Look.ofTEnv_wk (List.prefix_append σ.H [.array E]) σ.env i)
  refine ⟨⟨hc.store, hc.vals, hc.aliases, hc.net, hc.netSelf, hc.bound,
    hc.fragile, hc.env, hc.funds, hc.oracle⟩, (ha.allocateEmpty E hs).heap, ?_, h.locals⟩
  intro Q i
  obtain ⟨r, hr, hp⟩ := h.pointers i
  refine ⟨r.wk (List.prefix_append _ _), ?_, ?_⟩
  · change TEnv.get i (TEnv.wk _ Γ σ.env) = _
    rw [TEnv.get_wk, hr]
    rfl
  · change (allocateMachine m cursor (wmod 0)).mem (cell (lvl b i)) =
      .val (upd base σ.H.length cursor r.id)
    rw [hm _ (le_lvl b i) (lvl_lt b i), allocationBase_old base cursor r]
    exact hp

/-- Real source default declaration and target allocation retain the full heap. -/
theorem defaultEmpty_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : AllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    (E : Ty) (hm : (Ty.ref (.array E)).mapFree = true)
    (hs : cursor.val + 1 < W) (hcap : b + (Γ.length + 1) ≤ frame) :
    let σ' := σ.allocPush (emptyArray E)
    let base' := upd base σ.H.length cursor
    let m' := writeMachine (allocateMachine m cursor (wmod 0))
      (cell (b + Γ.length)) (.val cursor)
    TRun.declMem (.array E) none hm σ = .ok ⟨σ', List.prefix_append _ _⟩ ∧
      run ([.push w[0]] ++ allocateArrayCode ++ [.mstore (cell (b + Γ.length))]) m = .ok m' 0 ∧
      StateRepr L b frame (F.push (.mem (.array E)) .ok) σ' base' m' ∧
      AllocatorRepr σ'.heap base' frame ⟨cursor.val + 1, hs⟩ m' ∧
      m'.stack = m.stack := by
  refine ⟨defaultEmpty_decl σ E hm, ?_, ?_, ?_, rfl⟩
  · rw [List.append_assoc, run_append_ok (m' := m.push w[0]) rfl,
      show w[0] = Word.val (wmod 0) from congrArg Word.val (Fin.ext rfl),
      run_append_ok (allocateArray_run m cursor (wmod 0) ha.free.cell)]
    rfl
  · have hid : (σ.alloc (emptyArray E)).2.id = σ.H.length := rfl
    simpa only [hid, upd_same] using
      (h.allocateEmpty ha hb E hs).consMem (σ.alloc (emptyArray E)).2 hcap
  · exact (ha.allocateEmpty E hs).localWrite (b + Γ.length) (by omega) (by omega) _

/-- A literal zero allocates no child constructors, at any map-free element type. -/
theorem newEmpty_decl {Γ : Ctx} (σ : State C Γ) (E : Ty)
    (hn : (RefTy.array E).newArrOk = true) (hm : (Ty.ref (.array E)).mapFree = true) :
    TRun.declMem (.array E) (some (.newArr (.lit 0 rfl) hn)) hm σ =
      .ok ⟨σ.allocPush (emptyArray E), List.prefix_append _ _⟩ := by
  have he := newEmptyArray_copy σ.heap E (RefTy.mapFree_of_newArrOk hn) hn
  simp only [TRun.declMem, MRhs.evalT, State.copyStToMG, State.grow,
    bind, Except.bind, pure, Except.pure]
  with_unfolding_all exact State.adopt_push_alloc σ _ _ he _ _

theorem newEmpty_rebind {Γ : Ctx} (σ : State C Γ) (E : Ty)
    (dst : Idx Γ (.mem (.array E))) (hn : (RefTy.array E).newArrOk = true) :
    TRun.rebindMem dst (.newArr (.lit 0 rfl) hn) σ =
      .ok ⟨(σ.alloc (emptyArray E)).1.setLocal dst (some (σ.alloc (emptyArray E)).2),
        List.prefix_append _ _⟩ := by
  have he := newEmptyArray_copy σ.heap E (RefTy.mapFree_of_newArrOk hn) hn
  simp only [TRun.rebindMem, MRhs.evalT, State.copyStToMG, State.grow,
    bind, Except.bind, pure, Except.pure]
  exact congrArg (fun g : Grown σ.H (MVal · (.ref (.array E))) =>
    (Except.ok ⟨(σ.adopt g).1.setLocal dst (some g.val), g.ext⟩ :
      TRes (Solidity.Out C σ.H Γ))) he

theorem newEmpty_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : AllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    (E : Ty) (hn : (RefTy.array E).newArrOk = true) (hm : (Ty.ref (.array E)).mapFree = true)
    (hs : cursor.val + 1 < W) (hcap : b + (Γ.length + 1) ≤ frame) :
    let σ' := σ.allocPush (emptyArray E)
    let base' := upd base σ.H.length cursor
    let m' := writeMachine (allocateMachine m cursor (wmod 0))
      (cell (b + Γ.length)) (.val cursor)
    TRun.declMem (.array E) (some (.newArr (.lit 0 rfl) hn)) hm σ = .ok ⟨σ', List.prefix_append _ _⟩ ∧
      run ([.push w[0]] ++ allocateArrayCode ++ [.mstore (cell (b + Γ.length))]) m = .ok m' 0 ∧
      StateRepr L b frame (F.push (.mem (.array E)) .ok) σ' base' m' ∧
      AllocatorRepr σ'.heap base' frame ⟨cursor.val + 1, hs⟩ m' ∧ m'.stack = m.stack :=
  ⟨newEmpty_decl σ E hn hm, (defaultEmpty_correct h ha hb E hm hs hcap).2⟩

theorem rebindEmpty_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : AllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    (E : Ty) (dst : Idx Γ (.mem (.array E))) (hn : (RefTy.array E).newArrOk = true)
    (hs : cursor.val + 1 < W) :
    let σ' := (σ.alloc (emptyArray E)).1.setLocal dst (some (σ.alloc (emptyArray E)).2)
    let base' := upd base σ.H.length cursor
    let m' := writeMachine (allocateMachine m cursor (wmod 0)) (cellOf b dst) (.val cursor)
    TRun.rebindMem dst (.newArr (.lit 0 rfl) hn) σ = .ok ⟨σ', List.prefix_append _ _⟩ ∧
      run ([.push w[0]] ++ allocateArrayCode ++ [.mstore (cellOf b dst)]) m = .ok m' 0 ∧
      StateRepr L b frame F σ' base' m' ∧
      AllocatorRepr σ'.heap base' frame ⟨cursor.val + 1, hs⟩ m' ∧ m'.stack = m.stack := by
  refine ⟨newEmpty_rebind σ E dst hn, ?_, ?_, ?_, rfl⟩
  · have hz : w[0] = Word.val (wmod 0) := congrArg Word.val (Fin.ext rfl)
    rw [List.append_assoc, run_append_ok (m' := m.push w[0]) rfl, hz,
      run_append_ok (allocateArray_run m cursor (wmod 0) ha.free.cell)]
    rfl
  · have hid : (σ.alloc (emptyArray E)).2.id = σ.H.length := rfl
    simpa only [hid, upd_same] using
      (h.allocateEmpty ha hb E hs).setMem dst (σ.alloc (emptyArray E)).2
  · exact (ha.allocateEmpty E hs).localWrite (cellOf b dst)
      (Nat.lt_of_lt_of_le hb (le_lvl b dst)) (Nat.lt_of_lt_of_le (lvl_lt b dst) h.locals) _

end Solidity.Evm.Memory.Objects
