import Solidity.Evm.MemoryObjectNested
import Solidity.Evm.MemoryObjectCompile

/-! Scoped source integration for nested-array construction. -/
namespace Solidity.Evm.Memory.Objects
variable {C : Contract}

theorem StateRepr.adopt {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base base' : Nat → Fin W} {m m' : Machine}
    (h : StateRepr L b frame F σ base m) {R : RefTy}
    (g : Grown σ.H (MVal · (.ref R))) (hh : HeapRepr g.heap base' frame m')
    (hb : BaseExtends σ.H base base') (hf : m' = {m with mem := m'.mem})
    (hl : ∀ l, b ≤ l → l < b + Γ.length → m'.mem (cell l) = m.mem (cell l)) :
    StateRepr L b frame F (σ.adopt g).1 base' m' := by
  have hc := (h.core.congrMem hl).congrLook (fun i => Look.ofTEnv_wk g.ext σ.env i)
  have hcore := hf.symm ▸ hc
  refine ⟨⟨hcore.store, hcore.vals, hcore.aliases, hcore.net, hcore.netSelf, hcore.bound,
    hcore.fragile, hcore.env, hcore.funds, hcore.oracle⟩, hh, ?_, h.locals⟩
  intro Q i
  obtain ⟨r, hr, hc⟩ := h.pointers i
  refine ⟨r.wk g.ext, ?_, ?_⟩
  · change TEnv.get i (TEnv.wk g.ext Γ σ.env) = _
    rw [TEnv.get_wk, hr]
    rfl
  · change m'.mem (cell (lvl b i)) = .val (base' r.id)
    rw [hl _ (le_lvl b i) (lvl_lt b i), hb r]
    exact hc

theorem nested_decl {Γ : Ctx} (σ : State C Γ) (E : Ty) (n : Simple C Γ .uint)
    (hn : (RefTy.array (.ref (.array E))).newArrOk = true)
    (hm : (Ty.ref (.array E)).mapFree = true) (size : Fin W)
    (hs : n.evalT σ = indexValue size) :
    let g := nestedCopy σ.heap E hm size
    TRun.declMem (.array (.ref (.array E))) (some (.newArr n hn))
      (RefTy.mapFree_of_newArrOk hn) σ =
        .ok ⟨(σ.adopt g).1.push (t := .mem (.array (.ref (.array E)))) (some g.val), g.ext⟩ := by
  have he := nestedCopy_source σ.heap E size hn hm
  rw [← hs] at he
  simp only [TRun.declMem, MRhs.evalT, State.copyStToMG, State.grow,
    bind, Except.bind, pure, Except.pure]
  exact congrArg (fun g : Grown σ.H (MVal · (.ref (.array (.ref (.array E))))) =>
    (Except.ok ⟨(σ.adopt g).1.push (t := .mem (.array (.ref (.array E)))) (some g.val),
      g.ext⟩ : TRes (Solidity.Out C σ.H (.mem (.array (.ref (.array E))) :: Γ)))) he

theorem nested_rebind {Γ : Ctx} (σ : State C Γ) (E : Ty)
    (dst : Idx Γ (.mem (.array (.ref (.array E))))) (n : Simple C Γ .uint)
    (hn : (RefTy.array (.ref (.array E))).newArrOk = true)
    (hm : (Ty.ref (.array E)).mapFree = true) (size : Fin W)
    (hs : n.evalT σ = indexValue size) :
    let g := nestedCopy σ.heap E hm size
    TRun.rebindMem dst (.newArr n hn) σ =
      .ok ⟨(σ.adopt g).1.setLocal dst (some g.val), g.ext⟩ := by
  have he := nestedCopy_source σ.heap E size hn hm
  rw [← hs] at he
  simp only [TRun.rebindMem, MRhs.evalT, State.copyStToMG, State.grow,
    bind, Except.bind, pure, Except.pure]
  exact congrArg (fun g : Grown σ.H (MVal · (.ref (.array (.ref (.array E))))) =>
    (Except.ok ⟨(σ.adopt g).1.setLocal dst (some g.val), g.ext⟩ :
      TRes (Solidity.Out C σ.H Γ))) he

def nestedDeclareCode {Γ : Ctx} (b : Nat) (n : Simple C Γ .uint) : List Instr :=
  compileSimple b n ++ nestedCode ++ [.mstore (cell (b + Γ.length))]
def nestedRebindCode {Γ : Ctx} (b : Nat) {E : Ty}
    (dst : Idx Γ (.mem (.array (.ref (.array E))))) (n : Simple C Γ .uint) : List Instr :=
  compileSimple b n ++ nestedCode ++ [.mstore (cellOf b dst)]

/-- Allocation is integrated with actual scoped declarations, retaining aliases. -/
theorem nestedDeclare_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : AllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    (E : Ty) (n : Simple C Γ .uint) (hns : simpleIn n = true)
    (hn : (RefTy.array (.ref (.array E))).newArrOk = true)
    (hm : (Ty.ref (.array E)).mapFree = true) (size : Fin W)
    (hsize : n.evalT σ = indexValue size)
    (hs : cursor.val + size.val + 1 + size.val < W) (hcap : b + (Γ.length + 1) ≤ frame) :
    let g := nestedCopy σ.heap E hm size
    ∃ base' m',
      TRun.declMem (.array (.ref (.array E))) (some (.newArr n hn))
        (RefTy.mapFree_of_newArrOk hn) σ =
        .ok ⟨(σ.adopt g).1.push (t := .mem (.array (.ref (.array E)))) (some g.val), g.ext⟩ ∧
      run (nestedDeclareCode b n) m = .ok m' 0 ∧
      StateRepr L b frame (F.push (.mem (.array (.ref (.array E)))) .ok)
        ((σ.adopt g).1.push (t := .mem (.array (.ref (.array E)))) (some g.val)) base' m' ∧
      AllocatorRepr g.heap base' frame ⟨cursor.val + size.val + 1 + size.val, hs⟩ m' ∧
      BaseExtends σ.H base base' ∧ m'.stack = m.stack := by
  obtain ⟨base', m₁, hrun, ha₁, href, hbase, hstack, hframe, hmem⟩ :=
    nested_correct σ.heap E hm size base frame m cursor ha hs
  let g := nestedCopy σ.heap E hm size
  let m' := writeMachine m₁ (cell (b + Γ.length)) (.val cursor)
  refine ⟨base', m', nested_decl σ E n hn hm size hsize, ?_, ?_, ?_, hbase, hstack⟩
  · obtain ⟨w, hw, hr⟩ := simple_sim h.core n hns
    rw [hsize] at hw
    obtain ⟨a, rfl, he⟩ := hw
    have he' : a = size := Fin.ext (Int.ofNat_inj.mp he.symm)
    subst a
    rw [nestedDeclareCode, List.append_assoc, run_append_ok hr, run_append_ok hrun]
    rfl
  · have hadopt := h.adopt g ha₁.heap hbase hframe (fun l hl hu =>
      hmem l (Nat.lt_of_lt_of_le hb hl) (Nat.lt_of_lt_of_le hu h.locals))
    have hout := hadopt.consMem g.val hcap
    have href' : base' g.val.id = cursor := href
    simpa only [href'] using hout
  · exact ha₁.localWrite (b + Γ.length) (by omega) (by omega) _

theorem nestedRebind_correct {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : AllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    (E : Ty) (dst : Idx Γ (.mem (.array (.ref (.array E)))))
    (n : Simple C Γ .uint) (hns : simpleIn n = true)
    (hn : (RefTy.array (.ref (.array E))).newArrOk = true)
    (hm : (Ty.ref (.array E)).mapFree = true) (size : Fin W)
    (hsize : n.evalT σ = indexValue size)
    (hs : cursor.val + size.val + 1 + size.val < W) :
    let g := nestedCopy σ.heap E hm size
    ∃ base' m',
      TRun.rebindMem dst (.newArr n hn) σ =
        .ok ⟨(σ.adopt g).1.setLocal dst (some g.val), g.ext⟩ ∧
      run (nestedRebindCode b dst n) m = .ok m' 0 ∧
      StateRepr L b frame F
        ((σ.adopt g).1.setLocal dst (some g.val)) base' m' ∧
      AllocatorRepr g.heap base' frame ⟨cursor.val + size.val + 1 + size.val, hs⟩ m' ∧
      BaseExtends σ.H base base' ∧ m'.stack = m.stack := by
  obtain ⟨base', m₁, hrun, ha₁, href, hbase, hstack, hframe, hmem⟩ :=
    nested_correct σ.heap E hm size base frame m cursor ha hs
  let g := nestedCopy σ.heap E hm size
  let m' := writeMachine m₁ (cellOf b dst) (.val cursor)
  refine ⟨base', m', nested_rebind σ E dst n hn hm size hsize, ?_, ?_, ?_, hbase, hstack⟩
  · obtain ⟨w, hw, hr⟩ := simple_sim h.core n hns
    rw [hsize] at hw
    obtain ⟨a, rfl, he⟩ := hw
    have he' : a = size := Fin.ext (Int.ofNat_inj.mp he.symm)
    subst a
    rw [nestedRebindCode, List.append_assoc, run_append_ok hr, run_append_ok hrun]
    rfl
  · have hadopt := h.adopt g ha₁.heap hbase hframe (fun l hl hu =>
      hmem l (Nat.lt_of_lt_of_le hb hl) (Nat.lt_of_lt_of_le hu h.locals))
    have hout := hadopt.setMem dst g.val
    have href' : base' g.val.id = cursor := href
    simpa only [href'] using hout
  · exact ha₁.localWrite (cellOf b dst) (Nat.lt_of_lt_of_le hb (le_lvl b dst))
      (Nat.lt_of_lt_of_le (lvl_lt b dst) h.locals) _

end Solidity.Evm.Memory.Objects
