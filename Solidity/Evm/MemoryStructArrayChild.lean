import Solidity.Evm.MemoryStructDefaultSource

/-!
# Primitive array constructor arguments stored into memory members

Legacy struct literal lowering allocates the parent before its field arguments.
A direct new-array member assignment therefore allocates its child first, then
resolves the receiver in the grown source state. This composes existing array
allocation with reference redirect; reference-element arrays remain excluded.
-/
namespace Solidity.Evm.Memory
open Semantics

private theorem adopt_arrayField_alloc {C : Contract} {Γ : Ctx} {s f : Name} (σ : State C Γ)
    (p : PrimTy) (size : Fin W) (src : MPath C Γ (.ref (.struct s)))
    (hf : C.fieldType s f = some (.ref (.array (.prim p))))
    (g : Grown σ.H (MVal · (.ref (.array (.prim p)))))
    (hg : g = Grown.alloc ⟨List.prefix_refl _, σ.heap, defaultArray p size⟩)
    (e : σ.H <+: (σ.adopt g).1.H)
    (q : HRef (σ.alloc (defaultArray p size)).1.H (.struct s))
    (hq : src.mvalT (σ.alloc (defaultArray p size)).1 = .ok q) :
    (do
      let a ← (MLoc.field src f hf).addrT (σ.adopt g).1
      let hp ← TRes.ofOpt ((σ.adopt g).1.heap.writeAddr a g.val)
      pure ⟨(σ.adopt g).1.withHeap hp, e⟩ : TRes (Solidity.Out C σ.H Γ)) =
      .ok ⟨(σ.alloc (defaultArray p size)).1.withHeap
        ((σ.alloc (defaultArray p size)).1.heap.setField q hf (σ.alloc (defaultArray p size)).2),
        List.prefix_append _ _⟩ := by
  subst hg
  have hq' : src.mvalT
      (σ.adopt (Grown.alloc ⟨List.prefix_refl _, σ.heap, defaultArray p size⟩)).1 = .ok q := hq
  simp only [MLoc.addrT, hq', bind, Except.bind, pure, Except.pure]
  rfl

/-- The source operation adopts the same primitive child before resolving its parent. -/
theorem newArray_field {C : Contract} {Γ : Ctx} {s f : Name} (σ : State C Γ)
    (p : PrimTy) (n : Simple C Γ .uint) (size : Fin W) (hn : n.evalT σ = indexValue size)
    (src : MPath C Γ (.ref (.struct s)))
    (hf : C.fieldType s f = some (.ref (.array (.prim p))))
    (q : HRef (σ.alloc (defaultArray p size)).1.H (.struct s))
    (hq : src.mvalT (σ.alloc (defaultArray p size)).1 = .ok q) :
    TRun.assignNew (.mem (.field src f hf)) n rfl σ =
      .ok ⟨(σ.alloc (defaultArray p size)).1.withHeap
        ((σ.alloc (defaultArray p size)).1.heap.setField q hf (σ.alloc (defaultArray p size)).2),
        List.prefix_append _ _⟩ := by
  have he : (newArrT (.array (.prim p)) (n.evalT σ) rfl).copyStToM σ.heap rfl =
      Grown.alloc ⟨List.prefix_refl _, σ.heap, defaultArray p size⟩ :=
    hn.symm ▸ newArray_copy σ.heap p size
  simp only [TRun.assignNew, State.copyStToMG, State.grow]
  with_unfolding_all exact adopt_arrayField_alloc σ p size src hf _ he _ q hq

def newArrayFieldCode {C : Contract} {Γ : Ctx} (b : Nat) (n : Simple C Γ .uint)
    (pointer : List Instr) (offset : Nat) : List Instr :=
  compileSimple b n ++ (allocateArrayCode ++ (pointer ++ writeFieldCode offset))

/-- A literal's primitive array child retains every older object and exact capacity cost. -/
theorem newArrayField_correct {C : Contract} {L b frame : Nat} {Γ : Ctx} {F : Frag Γ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : StateRepr L b frame F σ base m) (hb : 0 < b)
    {s f : Name} {p : PrimTy} {src : MPath C Γ (.ref (.struct s))} {pointer : List Instr}
    (hp : PtrFrag b src pointer) (hf : C.fieldType s f = some (.ref (.array (.prim p))))
    (n : Simple C Γ .uint) (hn : simpleIn n = true)
    (ha : AllocationInput b frame ((n.evalT σ).word.val + 1) σ base m) :
    GrowingResult L b frame ((n.evalT σ).word.val + 1) F σ base m
      (TRun.assignNew (.mem (.field src f hf)) n rfl σ)
      (run (newArrayFieldCode b n pointer (fieldOffset (structDef s) f)) m) := by
  rcases ha with hz | ⟨_, cursor, hal, hspace⟩
  · omega
  · let size := (n.evalT σ).word
    have hs : n.evalT σ = indexValue size := Subtype.ext (word_val (n.evalT σ)).symm
    have hspace' : cursor.val + size.val + 1 < W := by dsimp only [size]; omega
    let a := σ.alloc (defaultArray p size)
    let base' := upd base σ.H.length cursor
    let allocated := allocateMachine m cursor size
    have hnew : StateRepr L b frame F a.1 base' allocated := h.allocate hal hb p size hspace'
    have hanew := hal.allocateArray p size hspace'
    obtain ⟨q, hq, _⟩ := hp.correct hnew
    let final := writeMachine allocated ((base' q.id).val + fieldOffset (structDef s) f)
      (.val (base' a.2.id))
    have hid : base' a.2.id = cursor := upd_same _ _ _
    refine .inl ⟨⟨a.1.withHeap (a.1.heap.setField q hf a.2), List.prefix_append _ _⟩,
      final, base', newArray_field σ p n size hs src hf q hq, ?_,
      hnew.setReference q hf a.2, rfl, (fun r => allocationBase_old base cursor r), ?_⟩
    · obtain ⟨w, hw, hr⟩ := simple_sim h.core n hn
      rw [hs] at hw
      obtain ⟨v, rfl, he⟩ := hw
      have hev : v = size := Fin.ext (Int.ofNat_inj.mp he.symm)
      subst v
      rw [newArrayFieldCode, run_append_ok hr,
        run_append_ok (allocateArray_run m cursor size hal.arrays.free.cell),
        run_append_ok (hp.run_of_eval (hnew.push (.val cursor)) hq)]
      have hbnd : (base' q.id).val + fieldOffset (structDef s) f < W := by
        have ho := fieldOffset_bound hf
        have he := (hnew.structs.objects q).space
        omega
      change run (writeFieldCode (fieldOffset (structDef s) f))
        ((allocated.push (.val cursor)).push (.val (base' q.id))) = .ok final 0
      rw [← hid]
      exact writeFieldWord_run allocated (base' q.id) _ _ hbnd
    · intro c _ hc hcspace
      have he : c = cursor := Word.val.inj (hc.arrays.free.cell.symm.trans hal.arrays.free.cell)
      subst c
      simpa only [Nat.add_assoc] using hanew.setReference q hf a.2

end Solidity.Evm.Memory
