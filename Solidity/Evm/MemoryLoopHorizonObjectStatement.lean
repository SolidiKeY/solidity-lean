import Solidity.Evm.MemoryLoopHorizonObjectRuns
import Solidity.Evm.MemoryLoopHorizonObjectStability

/-! Strong correspondence for the actual source loop statement and target
loop instruction. All-horizon room remains explicit in the general theorem.
An actual terminal source observation instead lets one finite-room witness
supply every horizon via proved stability. This supplies no capacity witness,
compiler-selection closure, rollback policy or whole-Source adequacy. -/
namespace Solidity.Evm.Memory.Construction
variable {C : Contract} {Γ Δ : Ctx}

theorem LoopCert.correct {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) (annotation : LoopAnn C Γ)
    {state : State C Γ} {base : Nat → Fin W} {initial : Machine}
    (repr : Objects.StateRepr L b frame F state base initial)
    (capacity : b + frameNeedProg body ≤ frame)
    (room : ∀ horizon, FiniteLoopRoom b frame c body state base initial horizon) :
    LoopRunResult L b frame F c body state base initial
      ((Stmt.loop annotation c body).run state) (run [.loop cond code] initial) := by
  have codeRun : run [.loop cond code] initial =
      loopRun (fun m => exec cond 0 m) (fun m => exec code 0 m) initial := by
    show (Instr.step (.loop cond code) initial).bind (fun m k => exec [] k m) = _
    simp only [Instr.step]
    cases loopRun _ _ initial <;> rfl
  rw [codeRun, Stmt.run_loop]
  exact cert.correct_runs repr capacity room

theorem LoopCert.correct_of_terminal {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) (annotation : LoopAnn C Γ)
    {state : State C Γ} {base : Nat → Fin W} {initial : Machine}
    (repr : Objects.StateRepr L b frame F state base initial)
    (capacity : b + frameNeedProg body ≤ frame)
    (n : Nat) (room : FiniteLoopRoom b frame c body state base initial n)
    {result : TRes (Solidity.Out C state.H Γ)}
    (finished : TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n
      ⟨state,List.prefix_refl _⟩ = .inr result) :
    LoopRunResult L b frame F c body state base initial
      ((Stmt.loop annotation c body).run state) (run [.loop cond code] initial) := by
  exact cert.correct annotation repr capacity (fun horizon => room.after_completion finished horizon)

end Solidity.Evm.Memory.Construction
