import Solidity.Backend.InternalFlow.MemoryStoreLocalFrame
/-! Actual mixed storage/scalar/heap stores preserve storage-alias locals.
No old heap-content frame, liveness assumption or withinM relaxation follows. -/
namespace Solidity.Backend.InternalFlow.CallerView
variable {C : Contract}
theorem alias_get_set_value {H : HTy} {p : PrimTy} {R : RefTy} :
    {Γ : Ctx} → (i : Idx Γ (.val p)) → (j : Idx Γ (.alias R)) →
    (v : p.Denote) → (env : TEnv C H Γ) →
    TEnv.get j (TEnv.set i v env) = TEnv.get j env
  | _, .here, .there j, v, env => rfl
  | _, .there i, .here, v, env => rfl
  | _, .there i, .there j, v, env => alias_get_set_value i j v env.2

theorem storage_assign_environment {Γ : Ctx} {T : Ty} (location : Loc C Γ T)
    (value : Src C Γ T) {σ : State C Γ} {out : Out C σ.H Γ}
    (executed : (Stmt.assign location value).run σ = .ok out) :
    out.st.env = TEnv.wk out.ext Γ σ.env := by
  change TRun.assign location value σ = .ok out at executed
  simp only [TRun.assign] at executed
  obtain ⟨v,hv,executed⟩ := tbind_ok_inv executed
  obtain ⟨address,ha,executed⟩ := tbind_ok_inv executed
  obtain ⟨storage,hs,executed⟩ := tbind_ok_inv executed
  cases executed
  apply TEnv.ext
  intro t i
  rw [TEnv.get_wk]
  exact (LTy.TDenote.wk_refl _ t (TEnv.get i σ.env)).symm

theorem scalar_assign_storage_alias {Γ : Ctx} {p : PrimTy} {R : RefTy}
    (i : Idx Γ (.val p)) (j : Idx Γ (.alias R)) (value : Val C Γ p)
    {σ : State C Γ} {out : Out C σ.H Γ}
    (executed : (Stmt.assignLocal i value).run σ = .ok out) :
    TEnv.get j out.st.env = TEnv.get j σ.env := by
  change TRun.assignLocal i value σ = .ok out at executed
  simp only [TRun.assignLocal] at executed
  obtain ⟨v,hv,executed⟩ := tbind_ok_inv executed
  cases executed
  exact alias_get_set_value i j v σ.env

theorem mixed_store_alias {Γ : Ctx} {T U : Ty} {p : PrimTy} {R : RefTy}
    (location : Loc C Γ T) (value : Src C Γ T)
    (destination : Idx Γ (.val p)) (scalar : Val C Γ p)
    (memory : MLoc C Γ U) (source : MSrc C Γ U)
    (alias : Idx Γ (.alias R))
    {σ : State C Γ} {out : Out C σ.H Γ}
    (executed : (Prog.cons (.assign location value)
      (.cons (.assignLocal destination scalar) (.cons (.assignMem memory source) .nil))).run σ = .ok out) :
    TEnv.get alias out.st.env = TEnv.get alias σ.env := by
  change TRun.seq _ _ σ = .ok out at executed
  unfold TRun.seq at executed
  split at executed
  · rename_i first hfirst
    obtain ⟨rest,hrest,rfl⟩ := tmap_ok_inv executed
    change TRun.seq _ _ first.st = .ok rest at hrest
    unfold TRun.seq at hrest
    split at hrest
    · rename_i middle hmiddle
      obtain ⟨last,hlast,rfl⟩ := tmap_ok_inv hrest
      change TRun.seq _ _ middle.st = .ok last at hlast
      unfold TRun.seq at hlast
      split at hlast
      · rename_i written hwritten
        obtain ⟨done,hdone,rfl⟩ := tmap_ok_inv hlast
        cases hdone
        have hm := memory_store_environment memory source hwritten
        have hs := scalar_assign_storage_alias destination alias scalar hmiddle
        have hf := storage_assign_environment location value hfirst
        change TEnv.get alias written.st.env = TEnv.get alias σ.env
        rw [hm,TEnv.get_wk]
        change TEnv.get alias middle.st.env = TEnv.get alias σ.env
        rw [hs,hf,TEnv.get_wk]
        rfl
      · cases hlast
    · cases hrest
  · cases executed
end Solidity.Backend.InternalFlow.CallerView
