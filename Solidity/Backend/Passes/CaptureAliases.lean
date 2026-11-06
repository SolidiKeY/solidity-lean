import Solidity.Evm.MemoryCompile

/-! Captured bumps change primitive values, not memory-reference locals.
These facts follow from the independent intrinsic source run; no target
execution or desired alias equality is assumed. -/
namespace Solidity.Backend.Passes
open Solidity.Evm Solidity.Evm.Memory
variable {C : Contract} {Γ : Ctx}

private theorem value_mem_ne {p : PrimTy} {R : RefTy}
    (i : Idx Γ (.val p)) (j : Idx Γ (.mem R)) : i.toNat ≠ j.toNat :=
  fun h => by cases Idx.ty_eq i j h

private theorem bump_memory_shape {p : PrimTy} {σ : State C Γ}
    {a : MAddr σ.H (.prim p)} {op : IncDec}
    {out : Solidity.Out C σ.H Γ} {v : p.Denote}
    (h : bumpMemT σ op a = .ok (out, v)) :
    ∃ heap : Heap σ.H, out = ⟨σ.withHeap heap, List.prefix_refl _⟩ := by
  simp only [bumpMemT] at h
  obtain ⟨old, _, h⟩ := tbind_ok_inv h
  obtain ⟨new, _, h⟩ := tbind_ok_inv h
  obtain ⟨heap, _, h⟩ := tbind_ok_inv h
  cases h
  exact ⟨heap, rfl⟩

/-- Includes identical source and capture destination value locals. -/
theorem capture_local_alias {p : PrimTy} {σ : State C Γ}
    (dst src : Idx Γ (.val p)) (op : IncDec)
    {out : Solidity.Out C σ.H Γ}
    (h : TRun.assignIncDec dst op (.local src) σ = .ok out)
    {R : RefTy} (j : Idx Γ (.mem R)) :
    HEq (TEnv.get j out.st.env) (TEnv.get j σ.env) := by
  simp only [TRun.assignIncDec] at h
  obtain ⟨⟨mid, value⟩, hb, h⟩ := tbind_ok_inv h
  cases h
  simp only [OpLoc.bumpT] at hb
  obtain ⟨new, _, hb⟩ := tbind_ok_inv hb
  cases hb
  exact heq_of_eq ((TEnv.get_set_ne dst j _ _ (value_mem_ne dst j)).trans
    (TEnv.get_set_ne src j _ _ (value_mem_ne src j)))

theorem capture_memory_alias {p : PrimTy} {Q : RefTy} {σ : State C Γ}
    (dst : Idx Γ (.val p)) (op : IncDec)
    (a : ArrTy Q (.prim p)) (src : MPath C Γ (.ref Q)) (i : Simple C Γ .uint)
    {out : Solidity.Out C σ.H Γ}
    (h : TRun.assignIncDec dst op (.mindex a src i) σ = .ok out)
    {R : RefTy} (j : Idx Γ (.mem R)) :
    HEq (TEnv.get j out.st.env) (TEnv.get j σ.env) := by
  simp only [TRun.assignIncDec] at h
  obtain ⟨⟨mid, value⟩, hb, h⟩ := tbind_ok_inv h
  cases h
  simp only [OpLoc.bumpT] at hb
  obtain ⟨addr, _, hb⟩ := tbind_ok_inv hb
  obtain ⟨heap, he⟩ := bump_memory_shape hb
  cases he
  exact heq_of_eq (TEnv.get_set_ne dst j _ _ (value_mem_ne dst j))

theorem capture_field_alias {p : PrimTy} {s f : Name} {σ : State C Γ}
    (dst : Idx Γ (.val p)) (op : IncDec) (src : MPath C Γ (.struct s))
    (hf : C.fieldType s f = some (.prim p))
    {out : Solidity.Out C σ.H Γ}
    (h : TRun.assignIncDec dst op (.mfield src f hf) σ = .ok out)
    {R : RefTy} (j : Idx Γ (.mem R)) :
    HEq (TEnv.get j out.st.env) (TEnv.get j σ.env) := by
  simp only [TRun.assignIncDec] at h
  obtain ⟨⟨mid, value⟩, hb, h⟩ := tbind_ok_inv h
  cases h
  simp only [OpLoc.bumpT] at hb
  obtain ⟨addr, _, hb⟩ := tbind_ok_inv hb
  obtain ⟨heap, he⟩ := bump_memory_shape hb
  cases he
  exact heq_of_eq (TEnv.get_set_ne dst j _ _ (value_mem_ne dst j))

end Solidity.Backend.Passes
