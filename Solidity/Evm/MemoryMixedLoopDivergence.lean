import Solidity.Evm.MemoryMixedLoopCompile
import Solidity.Evm.MemoryExprExamples

namespace Solidity.Evm.Memory.MixedLoops.DivergenceControls
open CompileExamples ExprExamples
private abbrev D := StorageCase.D
private def yes : Val D Γ .bool := .simple (.bool true)
private def no : Val D Γ .bool := .simple (.bool false)
private def inner : Stmt D Γ Γ := .loop .auto yes (.nil : Prog D Γ Γ)
private def body : Prog D Γ Γ := .cons inner .nil
private def compiled : Compiled 0 (Frag.init Γ) yes body :=
  (compile 0 (Frag.init Γ) yes body).get (by decide +kernel)
private def stopped : Compiled 0 (Frag.init Γ) no body :=
  (compile 0 (Frag.init Γ) no body).get (by decide +kernel)
attribute [irreducible] compiled stopped

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

theorem source_first_turn : TLoop.iterN (horizonBody body) (fun o=>yes.evalT o.st) 1
    ⟨StorageCase.state,List.prefix_refl _⟩=.inr (.error .diverge) := by
  simp only [TLoop.iterN,TLoop.step,yes,Val.evalT,Simple.evalT,horizonBody,body_diverges,Except.map]

theorem target_first_turn_fault :
    loopIterN (fun m=>exec compiled.cond 0 m) (fun m=>exec compiled.code 0 m) 1 machine=.inr .fault := by
  have related := compiled.cert.correct_horizon StorageCase.fixture
    (by unfold compiled;decide +kernel)
    (room_nonallocating compiled.cert (by unfold compiled;decide +kernel) StorageCase.state base machine) 1
  rw [source_first_turn] at related
  generalize target : loopIterN (fun m=>exec compiled.cond 0 m) (fun m=>exec compiled.code 0 m) 1 machine=result at related ⊢
  cases related
  rfl

/-- A completed inner divergence is NOT a pending outer horizon. -/
theorem divergence_not_pending :
    loopIterN (fun m=>exec compiled.cond 0 m) (fun m=>exec compiled.code 0 m) 1 machine≠.inl machine := by
  rw [target_first_turn_fault]
  intro same
  cases same

/-- A false outer condition does not execute the diverging inner body. -/
theorem stopped_target :
    loopIterN (fun m=>exec stopped.cond 0 m) (fun m=>exec stopped.code 0 m) 1 machine=.inr (.ok machine 0) := by
  unfold stopped
  rfl

theorem stopped_source : TLoop.iterN (horizonBody body) (fun o=>no.evalT o.st) 1
    ⟨StorageCase.state,List.prefix_refl _⟩=.inr (.ok ⟨StorageCase.state,List.prefix_refl _⟩) := rfl

end Solidity.Evm.Memory.MixedLoops.DivergenceControls
