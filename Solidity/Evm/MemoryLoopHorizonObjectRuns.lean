import Solidity.Evm.MemoryLoopHorizonObjectFinite

/-! Whole-run observation correspondence for complete-object construction.
Capacity is required explicitly at every requested finite horizon; no such
witness is supplied. Successful runs retain a genuine stopped prefix, exact
construction cost and strong allocator history. Revert and divergence reuse
the existing loop semantics, where a perpetually pending target run is fault.
No compiler-selection, rollback or Source adequacy claim is added. -/
namespace Solidity.Evm.Memory.Construction
variable {C : Contract} {Γ Δ : Ctx}

def LoopRunResult (L b frame : Nat) (F : Frag Γ) (c : Val C Γ .bool) (body : Prog C Γ Δ)
    (state : State C Γ) (base : Nat → Fin W) (initial : Machine)
    (source : TRes (Solidity.Out C state.H Γ)) (target : Out) : Prop :=
  (∃ o reached nextBase cost count, source=.ok o ∧ target=.ok reached 0 ∧
    CountedLoopPrefix c body state o cost count ∧ c.evalT o.st=.ok false ∧
    Objects.StateRepr L b frame F o.st nextBase reached ∧ reached.stack=initial.stack ∧
    BaseExtends state.H base nextBase ∧
    Objects.GrowsAllocator b frame cost state base initial o.st nextBase reached) ∨
  (source=.error .revert ∧ target=.revert) ∨
  (source=.error .diverge ∧ target=.fault)

theorem LoopCert.correct_runs {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {state : State C Γ}
    {base : Nat → Fin W} {initial : Machine}
    (repr : Objects.StateRepr L b frame F state base initial)
    (capacity : b + frameNeedProg body ≤ frame)
    (room : ∀ horizon, FiniteLoopRoom b frame c body state base initial horizon) :
    LoopRunResult L b frame F c body state base initial
      (TLoop.run (horizonBody body) (fun o => c.evalT o.st) ⟨state,List.prefix_refl _⟩)
      (loopRun (fun m => exec cond 0 m) (fun m => exec code 0 m) initial) := by
  by_cases terminal : ∃ result n, TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n
      ⟨state,List.prefix_refl _⟩ = .inr result
  · obtain ⟨result,n,observed⟩ := terminal
    have relation := cert.correct_finite_horizon n repr capacity (room n)
    rw [observed] at relation
    rw [TLoop.run_of_iterN observed]
    generalize targetObserved : loopIterN _ _ n initial = target at relation
    cases relation with
    | done hp earlier stopped current stack bases grows =>
      exact .inl ⟨_,_,_,_,_,rfl,loopRun_of_iterN targetObserved,hp,stopped,current,stack,bases,grows⟩
    | revert => exact .inr (.inl ⟨rfl,loopRun_of_iterN targetObserved⟩)
  · have diverges : TLoop.run (horizonBody body) (fun o => c.evalT o.st)
        ⟨state,List.prefix_refl _⟩ = .error .diverge := by
      simp only [TLoop.run, terminal, dif_neg, not_false_eq_true]
    rw [diverges]
    refine .inr (.inr ⟨rfl,loopRun_of_forall fun n => ?_⟩)
    have relation := cert.correct_finite_horizon n repr capacity (room n)
    generalize sourceObserved : TLoop.iterN _ _ n _ = source at relation
    generalize targetObserved : loopIterN _ _ n initial = target at relation
    cases relation with
    | more => exact ⟨_,rfl⟩
    | done => exact (terminal ⟨_,n,sourceObserved⟩).elim
    | revert => exact (terminal ⟨_,n,sourceObserved⟩).elim

end Solidity.Evm.Memory.Construction
