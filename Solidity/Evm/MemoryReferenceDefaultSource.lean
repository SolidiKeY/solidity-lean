import Solidity.Evm.MemoryDefaultCompile
import Solidity.Evm.MemoryObjectConstructionSource

namespace Solidity.Evm.Memory.Objects
variable {C : Contract}

theorem reference_decl {Γ : Ctx} (σ : State C Γ) (R : RefTy) (n : Simple C Γ .uint)
    (hn : (RefTy.array (.ref R)).newArrOk = true)
    (hm : (Ty.ref R).mapFree = true) (size : Fin W)
    (hs : n.evalT σ = indexValue size) :
    let g := referenceArrayCopy σ.heap R hm size
    TRun.declMem (.array (.ref R)) (some (.newArr n hn))
      (RefTy.mapFree_of_newArrOk hn) σ =
        .ok ⟨(σ.adopt g).1.push (t := .mem (.array (.ref R))) (some g.val), g.ext⟩ := by
  have he := referenceArrayCopy_source σ.heap R size hn hm
  rw [← hs] at he
  simp only [TRun.declMem, MRhs.evalT, State.copyStToMG, State.grow,
    bind, Except.bind, pure, Except.pure]
  exact congrArg (fun g : Grown σ.H (MVal · (.ref (.array (.ref R)))) =>
    (Except.ok ⟨(σ.adopt g).1.push (t := .mem (.array (.ref R))) (some g.val),
      g.ext⟩ : TRes (Solidity.Out C σ.H (.mem (.array (.ref R)) :: Γ)))) he

theorem reference_rebind {Γ : Ctx} (σ : State C Γ) (R : RefTy)
    (dst : Idx Γ (.mem (.array (.ref R)))) (n : Simple C Γ .uint)
    (hn : (RefTy.array (.ref R)).newArrOk = true)
    (hm : (Ty.ref R).mapFree = true) (size : Fin W)
    (hs : n.evalT σ = indexValue size) :
    let g := referenceArrayCopy σ.heap R hm size
    TRun.rebindMem dst (.newArr n hn) σ =
      .ok ⟨(σ.adopt g).1.setLocal dst (some g.val), g.ext⟩ := by
  have he := referenceArrayCopy_source σ.heap R size hn hm
  rw [← hs] at he
  simp only [TRun.rebindMem, MRhs.evalT, State.copyStToMG, State.grow,
    bind, Except.bind, pure, Except.pure]
  exact congrArg (fun g : Grown σ.H (MVal · (.ref (.array (.ref R)))) =>
    (Except.ok ⟨(σ.adopt g).1.setLocal dst (some g.val), g.ext⟩ :
      TRes (Solidity.Out C σ.H Γ))) he

def referenceDeclareCode {Γ : Ctx} (childCode : List Instr) (b : Nat) (n : Simple C Γ .uint) : List Instr :=
  compileSimple b n ++ referenceArrayCode childCode ++ [.mstore (cell (b + Γ.length))]
def referenceRebindCode {Γ : Ctx} (childCode : List Instr) (b : Nat) {R : RefTy}
    (dst : Idx Γ (.mem (.array (.ref R)))) (n : Simple C Γ .uint) : List Instr :=
  compileSimple b n ++ referenceArrayCode childCode ++ [.mstore (cellOf b dst)]

/-- Allocation is integrated with actual scoped declarations, retaining aliases. -/
theorem referenceDeclare_correct {count : Nat} {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : AllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    (R : RefTy) (n : Simple C Γ .uint) (hns : simpleIn n = true)
    (hn : (RefTy.array (.ref R)).newArrOk = true)
    (hm : (Ty.ref R).mapFree = true) (child : DefaultBuilder R hm count) (size : Fin W)
    (hsize : n.evalT σ = indexValue size)
    (hs : cursor.val + (size.val + 1 + size.val * count) < W) (hcap : b + (Γ.length + 1) ≤ frame) :
    let g := referenceArrayCopy σ.heap R hm size
    ∃ base' m',
      TRun.declMem (.array (.ref R)) (some (.newArr n hn))
        (RefTy.mapFree_of_newArrOk hn) σ =
        .ok ⟨(σ.adopt g).1.push (t := .mem (.array (.ref R))) (some g.val), g.ext⟩ ∧
      run (referenceDeclareCode child.code b n) m = .ok m' 0 ∧
      StateRepr L b frame (F.push (.mem (.array (.ref R))) .ok)
        ((σ.adopt g).1.push (t := .mem (.array (.ref R))) (some g.val)) base' m' ∧
      AllocatorRepr g.heap base' frame ⟨cursor.val + (size.val + 1 + size.val * count), hs⟩ m' ∧
      BaseExtends σ.H base base' ∧ m'.stack = m.stack := by
  obtain ⟨base', m₁, hrun, ha₁, href, hbase, hframe, hmem, _⟩ :=
    referenceArray_correct child σ.heap size base frame m cursor ha hs
  have hstack : m₁.stack = m.stack := by simpa only using congrArg Machine.stack hframe
  let g := referenceArrayCopy σ.heap R hm size
  let m' := writeMachine m₁ (cell (b + Γ.length)) (.val cursor)
  refine ⟨base', m', reference_decl σ R n hn hm size hsize, ?_, ?_, ?_, hbase, hstack⟩
  · obtain ⟨w, hw, hr⟩ := simple_sim h.core n hns
    rw [hsize] at hw
    obtain ⟨a, rfl, he⟩ := hw
    have he' : a = size := Fin.ext (Int.ofNat_inj.mp he.symm)
    subst a
    rw [referenceDeclareCode, List.append_assoc, run_append_ok hr, run_append_ok hrun]
    rfl
  · have hadopt := h.adopt g ha₁.heap hbase hframe (fun l hl hu =>
      hmem l (Nat.lt_of_lt_of_le hb hl) (Nat.lt_of_lt_of_le hu (Nat.le_trans h.locals ha.free.above)))
    have hout := hadopt.consMem g.val hcap
    have href' : base' g.val.id = cursor := href
    simpa only [href'] using hout
  · exact ha₁.localWrite (b + Γ.length) (by omega) (by omega) _

theorem referenceRebind_correct {count : Nat} {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : AllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    (R : RefTy) (dst : Idx Γ (.mem (.array (.ref R))))
    (n : Simple C Γ .uint) (hns : simpleIn n = true)
    (hn : (RefTy.array (.ref R)).newArrOk = true)
    (hm : (Ty.ref R).mapFree = true) (child : DefaultBuilder R hm count) (size : Fin W)
    (hsize : n.evalT σ = indexValue size)
    (hs : cursor.val + (size.val + 1 + size.val * count) < W) :
    let g := referenceArrayCopy σ.heap R hm size
    ∃ base' m',
      TRun.rebindMem dst (.newArr n hn) σ =
        .ok ⟨(σ.adopt g).1.setLocal dst (some g.val), g.ext⟩ ∧
      run (referenceRebindCode child.code b dst n) m = .ok m' 0 ∧
      StateRepr L b frame F
        ((σ.adopt g).1.setLocal dst (some g.val)) base' m' ∧
      AllocatorRepr g.heap base' frame ⟨cursor.val + (size.val + 1 + size.val * count), hs⟩ m' ∧
      BaseExtends σ.H base base' ∧ m'.stack = m.stack := by
  obtain ⟨base', m₁, hrun, ha₁, href, hbase, hframe, hmem, _⟩ :=
    referenceArray_correct child σ.heap size base frame m cursor ha hs
  have hstack : m₁.stack = m.stack := by simpa only using congrArg Machine.stack hframe
  let g := referenceArrayCopy σ.heap R hm size
  let m' := writeMachine m₁ (cellOf b dst) (.val cursor)
  refine ⟨base', m', reference_rebind σ R dst n hn hm size hsize, ?_, ?_, ?_, hbase, hstack⟩
  · obtain ⟨w, hw, hr⟩ := simple_sim h.core n hns
    rw [hsize] at hw
    obtain ⟨a, rfl, he⟩ := hw
    have he' : a = size := Fin.ext (Int.ofNat_inj.mp he.symm)
    subst a
    rw [referenceRebindCode, List.append_assoc, run_append_ok hr, run_append_ok hrun]
    rfl
  · have hadopt := h.adopt g ha₁.heap hbase hframe (fun l hl hu =>
      hmem l (Nat.lt_of_lt_of_le hb hl) (Nat.lt_of_lt_of_le hu (Nat.le_trans h.locals ha.free.above)))
    have hout := hadopt.setMem dst g.val
    have href' : base' g.val.id = cursor := href
    simpa only [href'] using hout
  · exact ha₁.localWrite (cellOf b dst) (Nat.lt_of_lt_of_le hb (le_lvl b dst))
      (Nat.lt_of_lt_of_le (lvl_lt b dst) h.locals) _


def defaultDeclareCode {Γ : Ctx} (code : List Instr) (b : Nat) : List Instr :=
  code ++ [.mstore (cell (b + Γ.length))]

theorem defaultDeclare_correct {count L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {cursor : Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m)
    (ha : AllocatorRepr σ.heap base frame cursor m) (hb : 0 < b)
    (R : RefTy) (hm : (Ty.ref R).mapFree = true) (builder : DefaultBuilder R hm count)
    (hs : cursor.val + count < W) (hcap : b + (Γ.length + 1) ≤ frame) :
    let g := σ.heap.allocDefault R hm
    ∃ base' m',
      TRun.declMem R none hm σ =
        .ok ⟨(σ.adopt g).1.push (t := .mem R) (some g.val), g.ext⟩ ∧
      run (defaultDeclareCode (Γ := Γ) builder.code b) m = .ok m' 0 ∧
      StateRepr L b frame (F.push (.mem R) .ok)
        ((σ.adopt g).1.push (t := .mem R) (some g.val)) base' m' ∧
      AllocatorRepr g.heap base' frame ⟨cursor.val + count, hs⟩ m' ∧
      BaseExtends σ.H base base' ∧ m'.stack = m.stack := by
  obtain ⟨base', m₁, hrun, ha₁, href, hbase, hframe, hmem, _⟩ :=
    builder.correct σ.heap base frame cursor m ha hs
  let g := σ.heap.allocDefault R hm
  let m' := writeMachine m₁ (cell (b + Γ.length)) (.val cursor)
  refine ⟨base', m', rfl, ?_, ?_, ?_, hbase, ?_⟩
  · rw [defaultDeclareCode, run_append_ok hrun]
    rfl
  · have hadopt := h.adopt g ha₁.heap hbase hframe (fun l hl hu =>
      hmem l (Nat.lt_of_lt_of_le hb hl) (Nat.lt_of_lt_of_le hu (Nat.le_trans h.locals ha.free.above)))
    have hout := hadopt.consMem g.val hcap
    have href' : base' g.val.id = cursor := href
    simpa only [href'] using hout
  · exact ha₁.localWrite (b + Γ.length) (by omega) (by omega) _
  · change m₁.stack = m.stack
    simpa only using congrArg Machine.stack hframe

end Solidity.Evm.Memory.Objects
