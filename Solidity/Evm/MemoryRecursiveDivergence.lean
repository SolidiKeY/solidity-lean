import Solidity.Evm.MemoryRecursiveHorizon
import Solidity.Evm.MemoryExprExamples
namespace Solidity.Evm.Memory.Recursive.DivergenceControls
open CompileExamples ExprExamples
private abbrev D := StorageCase.D
private def yes : Val D Γ .bool := .simple (.bool true)
private def inner : Stmt D Γ Γ := .loop .auto yes (.nil : Prog D Γ Γ)
private def body : Prog D Γ Γ := .cons inner .nil
private def compiled : CompiledProg 0 (Frag.init Γ) body :=
  (compileProg 0 body (Frag.init Γ)).get (by decide +kernel)
attribute [irreducible] compiled
/-- Divergence is proved from every actual inner iterator prefix; no native
or partial infinite evaluator is run to establish it. -/
theorem inner_diverges (σ : State D Γ) : inner.run σ=.error .diverge := by
  let initial : Solidity.Out D σ.H Γ := ⟨σ,List.prefix_refl _⟩
  have turn : TLoop.step (horizonBody (Prog.nil : Prog D Γ Γ))
      (fun o=>yes.evalT o.st) initial=.inl initial := rfl
  have iter : ∀ n,TLoop.iterN (horizonBody (Prog.nil : Prog D Γ Γ))
      (fun o=>yes.evalT o.st) n initial=.inl initial := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [TLoop.iterN,turn];exact ih
  have never : ¬ ∃ res n,TLoop.iterN (horizonBody (Prog.nil : Prog D Γ Γ))
      (fun o=>yes.evalT o.st) n initial=.inr res := by
    rintro ⟨res,n,finish⟩
    rw [iter n] at finish
    cases finish
  rw [show inner=Stmt.loop .auto yes (.nil : Prog D Γ Γ) from rfl,Stmt.run_loop]
  change TLoop.run (horizonBody (Prog.nil : Prog D Γ Γ)) (fun o=>yes.evalT o.st) initial=.error .diverge
  simp only [TLoop.run,never,dif_neg,not_false_eq_true]

theorem body_diverges (σ : State D Γ) : body.run σ=.error .diverge := by
  show TRun.seq inner.runR Prog.nil.runR σ=_
  have run := inner_diverges σ
  simp only [TRun.seq,Stmt.run] at run ⊢
  rw [run]


/-- Derive target divergence from the closed source/target theorem; never
execute a partial infinite evaluator as a proof oracle. -/
theorem target_diverges : run compiled.code machine=.fault := by
  have related := compiled.correct
    ⟨StorageCase.fixture,by unfold compiled;decide +kernel,
      room_nonallocating compiled.cert (by unfold compiled;decide +kernel) 6 StorageCase.state base machine⟩
  rw [body_diverges] at related
  rcases related with ⟨out,next,newBase,amount,bad,rest⟩ | ⟨bad,rest⟩ | ⟨source,target⟩
  · cases bad
  · cases bad
  · exact target

/-- Source divergence cannot be mistaken for an unchanged successful result. -/
theorem not_success : ¬ ∃ o,body.run StorageCase.state=.ok o := by
  rw [body_diverges]
  rintro ⟨o,bad⟩
  cases bad

end Solidity.Evm.Memory.Recursive.DivergenceControls
