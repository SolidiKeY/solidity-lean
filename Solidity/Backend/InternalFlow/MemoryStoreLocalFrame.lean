import Solidity.Calculus.RunFrameMem
/-! A successful actual heap store frames locals without claiming old heap contents.
The existing withinM guard and all compiler profiles remain unchanged. -/
namespace Solidity.Backend.InternalFlow.CallerView
variable {C : Contract}
/-- A real successful heap write changes no local; this is not Heap.Keeps. -/
theorem memory_store_environment {Γ : Ctx} {T : Ty} (location : MLoc C Γ T)
    (value : MSrc C Γ T) {σ : State C Γ} {out : Out C σ.H Γ}
    (executed : (Stmt.assignMem location value).run σ = .ok out) :
    out.st.env = TEnv.wk out.ext Γ σ.env := by
  change TRun.assignMem location value σ = .ok out at executed
  simp only [TRun.assignMem] at executed
  obtain ⟨v,hv,executed⟩ := tbind_ok_inv executed
  obtain ⟨address,ha,executed⟩ := tbind_ok_inv executed
  obtain ⟨heap,hh,executed⟩ := tbind_ok_inv executed
  cases executed
  apply TEnv.ext
  intro t i
  rw [TEnv.get_wk]
  exact (LTy.TDenote.wk_refl _ t (TEnv.get i σ.env)).symm
end Solidity.Backend.InternalFlow.CallerView
