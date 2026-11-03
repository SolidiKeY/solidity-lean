import Solidity.Evm.MemoryRecursiveLift

namespace Solidity.Evm.Memory.RecursiveLift
variable {C : Contract} {Γ Δ : Ctx}

/-- Concrete existing producer instance; generic soundness is discharged by
its ACTUAL implementation, not accepted as an axiom or external oracle. -/
def BodyProfile.ofScope {b F G body code}
    (cert : LoopScopes.ProgCert (C:=C) (Γ:=Γ) (Δ:=Δ) b F G body code) : BodyProfile b F body code :=
  ⟨G,cert.need,fun σ out amount=>LoopScopes.Cost cert σ out amount,
    fun σ amount=>LoopScopes.Demand cert σ amount⟩

theorem BodyProfile.ofScope_sound {b F G body code}
    (cert : LoopScopes.ProgCert (C:=C) (Γ:=Γ) (Δ:=Δ) b F G body code) : (ofScope cert).Sound := by
  intro L frame σ base m repr cap room
  exact cert.correct σ base m repr cap room

/-- Full actual loop execution, not finite-horizon success or a loop annotation
assumption. Body divergence and infinite outer iteration both remain divergence. -/
theorem Certificate.correct {b L frame F c body cond code}
    (cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code) (sound : cert.profile.Sound) (a : LoopAnn C Γ)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (cap : b+cert.profile.need≤frame)
    (room : Room cert frame σ base m) :
    LoopScopes.Result L b frame F σ base m (fun o cost=>Prefix cert σ o cost)
      ((Stmt.loop a c body).run σ) (run [.loop cond code] m) := by
  have codeRun : run [.loop cond code] m=
      loopRun (fun m=>exec cond 0 m) (fun m=>exec code 0 m) m := by
    show (Instr.step (.loop cond code) m).bind (fun m' k'=>exec [] k' m')=_
    simp only [Instr.step]
    cases loopRun _ _ m <;> rfl
  rw [codeRun,Stmt.run_loop]
  change LoopScopes.Result L b frame F σ base m (fun o cost=>Prefix cert σ o cost)
    (TLoop.run (horizonBody body) (fun o=>c.evalT o.st) ⟨σ,List.prefix_refl _⟩) _
  by_cases finishes : ∃ res n,TLoop.iterN (horizonBody body) (fun o=>c.evalT o.st) n
      ⟨σ,List.prefix_refl _⟩=.inr res
  · obtain ⟨res,n,sourceRun⟩ := finishes
    have related := cert.correct_horizon sound repr cap room n
    rw [sourceRun] at related
    rw [TLoop.run_of_iterN sourceRun]
    generalize targetRun : loopIterN _ _ n m=target at related
    cases related with
    | done hp hr hs he hg => exact .inl ⟨_,_,_,_,rfl,loopRun_of_iterN targetRun,hp,hr,hs,he,hg⟩
    | revert => exact .inr (.inl ⟨rfl,loopRun_of_iterN targetRun⟩)
    | diverge => exact .inr (.inr ⟨rfl,loopRun_of_iterN targetRun⟩)
  · have diverges : TLoop.run (horizonBody body) (fun o=>c.evalT o.st)
        ⟨σ,List.prefix_refl _⟩=.error .diverge := by
      simp only [TLoop.run,finishes,dif_neg,not_false_eq_true]
    rw [diverges]
    refine .inr (.inr ⟨rfl,loopRun_of_forall fun n=>?_⟩)
    have related := cert.correct_horizon sound repr cap room n
    generalize sourceRun : TLoop.iterN _ _ n _=source at related
    generalize targetRun : loopIterN _ _ n m=target at related
    cases related with
    | more => exact ⟨_,rfl⟩
    | done => exact (finishes ⟨_,n,sourceRun⟩).elim
    | revert => exact (finishes ⟨_,n,sourceRun⟩).elim
    | diverge => exact (finishes ⟨_,n,sourceRun⟩).elim

end Solidity.Evm.Memory.RecursiveLift
