import Solidity.Evm.MemoryLoopHorizonObjectStatement
import Solidity.Evm.MemoryLoopHorizonObjectFiniteControls

/-! Inhabited actual source/target loop-statement correspondence on the existing
populated fixed-parent heap. Genuine core/nil certificates supply both constant
conditions and every annotation. All-horizon room is proved from zero body
allocation cost; no allocating capacity or compiler-selection witness is supplied. -/
namespace Solidity.Evm.Memory.HorizonObjectStatementControls

theorem represented {C : Contract} {Γ : Ctx} {L b frame : Nat}
    {state : State C Γ} {base : Nat → Fin W} {machine : Machine}
    (repr : Objects.StateRepr L b frame (Frag.init Γ) state base machine)
    (capacity : b + Γ.length ≤ frame) (truth : Bool) (annotation : LoopAnn C Γ) :
    Construction.LoopRunResult L b frame (Frag.init Γ) (.simple (.bool truth)) .nil state base machine
      ((Stmt.loop annotation (.simple (.bool truth)) (.nil : Prog C Γ Γ)).run state)
      (run [.loop (Evm.compileVal b (.simple (.bool truth) : Val C Γ .bool)) []] machine) := by
  apply (HorizonObjectFiniteControls.cert b truth).correct annotation repr capacity
  intro horizon reached cost turns hp within condition
  exact .inl (by rw [hp.cost_zero (by rfl)]; rfl)

theorem populated_runs (truth : Bool) :
    ∃ (C : Contract) (Γ : Ctx) (state : State C Γ) (base : Nat → Fin W) (machine : Machine),
      (∀ annotation : LoopAnn C Γ,
        Construction.LoopRunResult 1 1 8 (Frag.init Γ) (.simple (.bool truth)) .nil state base machine
          ((Stmt.loop annotation (.simple (.bool truth)) (.nil : Prog C Γ Γ)).run state)
          (run [.loop (Evm.compileVal 1 (.simple (.bool truth) : Val C Γ .bool)) []] machine)) ∧
      state.H.length=3 ∧ machine.stack=[w[77]] := by
  have inhabited := represented ObjectArrayExamples.initial_repr (by decide +kernel) truth
  exact ⟨_,_,_,_,_,inhabited,rfl,rfl⟩

end Solidity.Evm.Memory.HorizonObjectStatementControls
