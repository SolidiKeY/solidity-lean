import Solidity.Evm.MemoryLoopHorizonRevert
import Solidity.Evm.MemoryLoopHorizonControls

/-! An actual out-of-bounds condition is compiled by the checked memory
compiler on populated aliased memory. Its finite target revert follows from
source evaluation and the proved condition certificate, then determines both
existing run results. No revert observation is assumed as fixture input. -/
namespace Solidity.Evm.Memory.HorizonRevertControls
open CompileExamples

def condition : Val C Γ .bool :=
  .binop .eqB rfl rfl
    (.readMem (.index .dyn (.var (.there .here) rfl) (.simple (.lit 2 rfl))))
    (.simple (.lit 0 rfl))
def compiled : CompiledVal 0 (Frag.init Γ) condition :=
  (Memory.compileVal 0 (Frag.init Γ) condition).get (by decide +kernel)
def cert : LoopCert 0 (Frag.init Γ) condition HorizonControls.body compiled.code [] :=
  ⟨compiled.cert,Frag.init Γ,.nil _,rfl⟩

theorem source_condition : condition.evalT σ=.error .revert := by
  have sound {α : Type} {out : TRes α}
      (observed : (match out with | .error .revert => true | _ => false)=true) : out=.error .revert := by
    cases out with
    | ok value => cases observed
    | error error => cases error <;> cases observed <;> rfl
  exact sound (by decide +kernel)

theorem target_one : loopIterN (fun m => exec compiled.code 0 m) (fun m => exec [] 0 m) 1 machine=.inr .revert := by
  rcases compiled.cert.correct fixture_repr with ⟨v,w,source,word,code⟩ | ⟨source,code⟩
  · rw [source_condition] at source
    cases source
  · have executed : exec compiled.code 0 machine=.revert := code
    simp only [loopIterN,loopTurn,executed]

theorem reverted_runs :
    TLoop.run (horizonBody HorizonControls.body) (fun o => condition.evalT o.st)
      ⟨σ,List.prefix_refl _⟩=.error .revert ∧
    loopRun (fun m => exec compiled.code 0 m) (fun m => exec [] 0 m) machine=.revert := by
  exact cert.reverted_runs 1 fixture_repr (by decide +kernel)
    ((loopRoom_nonallocating condition HorizonControls.body rfl σ base machine).finite 1) target_one

end Solidity.Evm.Memory.HorizonRevertControls
