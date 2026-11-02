import Solidity.Evm.MemoryStructDefaultPlan

/-! # Scoped declarations using certified finite default construction -/
namespace Solidity.Evm.Memory
open Semantics

/-- Bind the constructed root while retaining every older heap identity and alias. -/
theorem DefaultPlan.declare_correct {C : Contract} {R : RefTy} (plan : DefaultPlan R)
    {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) (hb : 0 < b)
    (hm : (Ty.ref R).mapFree = true) (hcap : b + (Γ.length + 1) ≤ frame)
    (ha : AllocationInput b frame plan.cost σ base m) :
    GrowingResult L b frame plan.cost (F.push (.mem R) .ok) σ base m
      (TRun.declMem R none hm σ)
      (run (plan.code ++ [.mstore (cell (b + Γ.length))]) m) := by
  rcases ha with hz | ⟨_, cursor, hal, hspace⟩
  · have hp := plan.root_lt
    omega
  · obtain ⟨base', mem, hst, halloc, hext, hroot, hrun⟩ :=
      plan.sound σ base cursor m hm h hal hb hspace
    let g := σ.heap.allocDefault R hm
    let m₁ : Machine := {m with mem := mem}
    let final := writeMachine m₁ (cell (b + Γ.length)) (.val (base' g.val.id))
    refine .inl ⟨⟨(σ.adopt g).1.push (t := .mem R) (some g.val), g.ext⟩,
      final, base', rfl, ?_, hst.consMem g.val hcap, rfl, hext, ?_⟩
    · rw [run_append_ok hrun]
      rw [← hroot]
      rfl
    · intro c _ hc hcspace
      have he : c = cursor := Word.val.inj (hc.arrays.free.cell.symm.trans hal.arrays.free.cell)
      subst c
      exact halloc.localWrite (b + Γ.length) (by omega) (by omega) (.val (base' g.val.id))

/-- The representation does not constrain the evaluation stack. -/
theorem StateRepr.stack {C : Contract} {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) (st : List Word) :
    StateRepr L b frame F σ base {m with stack := st} :=
  ⟨h.core.stack st, ⟨fun r => (h.heap.arrays r).stack st, h.heap.above, h.heap.separated⟩,
    h.pointers, h.locals, h.structs.stack st, h.separated, RefFieldsRepr.mem_eq h.refs rfl⟩

/-- Rebinding a whole local to its finite fresh default keeps old aliases intact. -/
theorem DefaultPlan.deleteLocal_correct {C : Contract} {R : RefTy} (plan : DefaultPlan R)
    {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) (hb : 0 < b)
    (dst : Idx Γ (.mem R)) (hm : (Ty.ref R).mapFree = true)
    (ha : AllocationInput b frame plan.cost σ base m) :
    GrowingResult L b frame plan.cost F σ base m (TRun.deleteMem (.var dst hm) σ)
      (run (plan.code ++ [.mstore (cellOf b dst)]) m) := by
  rcases ha with hz | ⟨_, cursor, hal, hspace⟩
  · have hp := plan.root_lt; omega
  · obtain ⟨base', mem, hst, halloc, hext, hroot, hrun⟩ :=
      plan.sound σ base cursor m hm h hal hb hspace
    let g := σ.heap.allocDefault R hm
    let m₁ : Machine := {m with mem := mem}
    let final := writeMachine m₁ (cellOf b dst) (.val (base' g.val.id))
    refine .inl ⟨⟨(σ.adopt g).1.setLocal dst (some g.val), g.ext⟩,
      final, base', rfl, ?_, hst.setMem dst g.val, rfl, hext, ?_⟩
    · rw [run_append_ok hrun, ← hroot]; rfl
    · intro c _ hc hcspace
      have he : c = cursor := Word.val.inj (hc.arrays.free.cell.symm.trans hal.arrays.free.cell)
      subst c
      exact halloc.localWrite (cellOf b dst) (Nat.lt_of_lt_of_le hb (le_lvl b dst))
        (Nat.lt_of_lt_of_le (lvl_lt b dst) h.locals) (.val (base' g.val.id))

/-- Clearing a member resolves its parent first, constructs the finite child,
then redirects only that member. Older aliases keep every previous object. -/
theorem DefaultPlan.deleteField_correct {C : Contract} {R : RefTy} (plan : DefaultPlan R)
    {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) (hb : 0 < b)
    {s f : Name} {src : MPath C Γ (.ref (.struct s))} {pointer : List Instr}
    (hs : PtrFrag b src pointer) (r : HRef σ.H (.struct s)) (hr : src.mvalT σ = .ok r)
    (hf : C.fieldType s f = some (.ref R)) (hm : (Ty.ref R).mapFree = true)
    (ha : AllocationInput b frame plan.cost σ base m) :
    GrowingResult L b frame plan.cost F σ base m
      (TRun.deleteMem (.loc (.field src f hf)) σ)
      (run (clearReferenceCode pointer plan.code (fieldOffset (structDef s) f)) m) := by
  rcases ha with hz | ⟨_, cursor, hal, hspace⟩
  · have hp := plan.root_lt; omega
  · obtain ⟨base', mem, hst, halloc, hext, hroot, hrun⟩ :=
      plan.sound σ base cursor (m.push (.val (base r.id))) hm
        (h.push (.val (base r.id))) (hal.stack _) hb hspace
    let g := σ.heap.allocDefault R hm
    let σ₁ := (σ.adopt g).1
    let r₁ := r.wk g.ext
    let m₁ : Machine := {m with mem := mem}
    let final := writeMachine m₁ ((base r.id).val + fieldOffset (structDef s) f)
      (.val (base' g.val.id))
    have hst₁ : StateRepr L b frame F σ₁ base' m₁ := hst.stack m.stack
    have hal₁ : StructAllocatorRepr g.heap base' frame ⟨cursor.val + plan.cost, hspace⟩ m₁ :=
      halloc.stack m.stack
    refine .inl ⟨⟨σ₁.withHeap (σ₁.heap.setField r₁ hf g.val), g.ext⟩,
      final, base', ?_, ?_, ?_, rfl, hext, ?_⟩
    · simp only [TRun.deleteMem, MLoc.addrT, hr, bind, Except.bind, pure, Except.pure,
        TRun.clearT, State.allocDefaultG, State.grow]
      rfl
    · change run (clearReferenceCode pointer plan.code (fieldOffset (structDef s) f)) m =
        .ok (writeMachine m₁ ((base r.id).val + fieldOffset (structDef s) f)
          (.val (base' g.val.id))) 0
      rw [hroot]
      apply clearReference_run m m₁ (base r.id) (wmod (cursor.val + plan.root))
        _ pointer plan.code (hs.run_of_eval h hr) hrun
      have ho := fieldOffset_bound hf
      have hbnd := (h.structs.objects r).space
      omega
    · simpa only [r₁, HRef.wk, hext r] using hst₁.setReference r₁ hf g.val
    · intro c _ hc hcspace
      have he : c = cursor := Word.val.inj (hc.arrays.free.cell.symm.trans hal.arrays.free.cell)
      subst c
      simpa only [r₁, HRef.wk, hext r] using hal₁.setReference r₁ hf g.val

end Solidity.Evm.Memory
