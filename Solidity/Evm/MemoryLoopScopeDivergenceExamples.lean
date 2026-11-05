import Solidity.Evm.Compiler
import Solidity.Evm.MemoryLoopScopeBudget
import Solidity.Evm.MemoryCompileExamples
namespace Solidity.Evm.Memory.LoopScopeDivergenceExamples

/-- This theorem observes mathematical divergence; it never executes an infinite native loop. -/
def trueSpin (K : Contract) (Θ : Ctx) : Prog K Θ Θ :=
  .cons (.loop .auto (.simple (.bool true)) .nil) .nil

theorem trueSpin_diverges {K : Contract} {Θ : Ctx} (τ : State K Θ) :
    (trueSpin K Θ).run τ = .error .diverge := by
  let step := fun o : Solidity.Out K τ.H Θ =>
    ((Prog.nil : Prog K Θ Θ).run o.st).map fun o' =>
      (⟨o'.st.drop Ext.refl, o.ext.trans o'.ext⟩ : Solidity.Out K τ.H Θ)
  let guard := fun o : Solidity.Out K τ.H Θ => (.ok true : TRes Bool)
  let start : Solidity.Out K τ.H Θ := ⟨τ, List.prefix_refl _⟩
  have hstep : TLoop.step step guard start = .inl start := rfl
  have iter : ∀ n, TLoop.iterN step guard n start = .inl start := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [TLoop.iterN, hstep]; exact ih
  have hex : ¬ ∃ r n, TLoop.iterN step guard n start = .inr r := by
    rintro ⟨r, n, hn⟩
    rw [iter n] at hn
    cases hn
  have hs : (Stmt.loop .auto (.simple (.bool true)) (Prog.nil : Prog K Θ Θ)).run τ =
      .error .diverge := by
    rw [Stmt.run_loop]
    change TLoop.run step guard start = .error .diverge
    simp only [TLoop.run, hex, dif_neg, not_false_eq_true]
  show TRun.seq (Stmt.loop .auto (.simple (.bool true)) (Prog.nil : Prog K Θ Θ)).runR Prog.nil.runR τ = _
  simp only [TRun.seq, Stmt.run] at hs ⊢
  rw [hs]

open CompileExamples
private def spinCondition : Val C Γ .bool :=
  .binop .eqB rfl rfl (.mlen (.var (.there .here) rfl) rfl) (.simple (.lit 2 rfl))
private def spin : Prog C Γ Γ := .cons (.loop .auto spinCondition (.nil : Prog C Γ Γ)) .nil

/-- Mathematical divergence is established without executing an infinite loop. -/
private theorem raw_diverges : spin.run σ = .error .diverge := by
  let step := fun o : Solidity.Out C CompileExamples.H Γ =>
    ((Prog.nil : Prog C Γ Γ).run o.st).map fun o' =>
      (⟨o'.st.drop Ext.refl, o.ext.trans o'.ext⟩ : Solidity.Out C CompileExamples.H Γ)
  let start : Solidity.Out C CompileExamples.H Γ := ⟨σ, List.prefix_refl _⟩
  have hc : spinCondition.evalT σ = .ok true := by
    simp only [spinCondition, Val.evalT, MPath.mvalT, σ, TEnv.get, Heap.lenU, Solidity.lenU,
      Heap.len, hp, r0, CompileExamples.H, Heap.get, Objs.get, MObj.elems_dyn,
      BinOp.shortT, bind, Except.bind, pure, Except.pure,
      Simple.evalT, BinOp.evalT, BinOp.evalNum, TRes.ofOpt]
    rfl
  have hstep : TLoop.step step (fun o => spinCondition.evalT o.st) start = .inl start := by
    unfold TLoop.step
    dsimp only [start]
    rw [hc]
    rfl
  have iter : ∀ n, TLoop.iterN step (fun o => spinCondition.evalT o.st) n start = .inl start := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [TLoop.iterN, hstep]
      exact ih
  have hex : ¬ ∃ r n, TLoop.iterN step (fun o => spinCondition.evalT o.st) n start = .inr r := by
    rintro ⟨r, n, hn⟩
    rw [iter n] at hn
    cases hn
  have hs : (Stmt.loop .auto spinCondition (Prog.nil : Prog C Γ Γ)).run σ = .error .diverge := by
    rw [Stmt.run_loop]
    change TLoop.run step (fun o => spinCondition.evalT o.st) start = .error .diverge
    simp only [TLoop.run, hex, dif_neg, not_false_eq_true]
  show TRun.seq (Stmt.loop .auto spinCondition (Prog.nil : Prog C Γ Γ)).runR Prog.nil.runR σ = _
  simp only [TRun.seq, Stmt.run] at hs ⊢
  rw [hs]


private def selected : Prog C Γ Γ :=
  .cons (.ite (.simple (.bool true)) spin .nil) (.cons .revert .nil)
private def skipped : Prog C Γ Γ :=
  .cons (.ite (.simple (.bool false)) spin .nil) .nil
private def prefixed : Prog C Γ Γ :=
  .cons (.require (.simple (.bool true))) selected
private def selectedPublic := (Compiler.compile 0 (Frag.init Γ) selected).get (by decide +kernel)
private def skippedPublic := (Compiler.compile 0 (Frag.init Γ) skipped).get (by decide +kernel)
private def prefixPublic := (Compiler.compile 0 (Frag.init Γ) prefixed).get (by decide +kernel)
attribute [irreducible] selectedPublic skippedPublic prefixPublic

private theorem selected_diverges : selected.run σ = .error .diverge := by
  have hs : (Stmt.ite (.simple (.bool true)) spin (Prog.nil : Prog C Γ Γ)).run σ =
      .error .diverge := by
    change (spin.run σ).map _ = _
    rw [raw_diverges]
    rfl
  show TRun.seq (Stmt.ite (.simple (.bool true)) spin (Prog.nil : Prog C Γ Γ)).runR
    (Prog.cons Stmt.revert Prog.nil).runR σ = _
  simp only [TRun.seq, Stmt.run] at hs ⊢
  rw [hs]

theorem prefix_diverges : prefixed.run σ = .error .diverge := by
  have hs : (Stmt.require (.simple (.bool true)) : Stmt C Γ Γ).run σ =
      .ok ⟨σ, List.prefix_refl _⟩ := rfl
  change (Prog.cons (Stmt.require (.simple (.bool true))) selected).run σ = _
  rw [Prog.run_cons_ok hs]
  change (selected.run σ).map _ = _
  rw [selected_diverges]
  rfl

theorem selected_simulates : selectedPublic.Agrees 1 4 base σ machine := by
  apply selectedPublic.correct
  apply (selectedPublic.memoryLoopScopes_input (by decide +kernel) 1 4 base σ machine).mpr
  exact ⟨fixture_repr, by decide +kernel,
    LoopScopes.room_nonallocating (selectedPublic.memoryLoopScopesResult (by decide +kernel)).cert
      (by decide +kernel) σ base machine⟩

theorem skipped_simulates : skippedPublic.Agrees 1 4 base σ machine := by
  apply skippedPublic.correct
  apply (skippedPublic.memoryLoopScopes_input (by decide +kernel) 1 4 base σ machine).mpr
  exact ⟨fixture_repr, by decide +kernel,
    LoopScopes.room_nonallocating (skippedPublic.memoryLoopScopesResult (by decide +kernel)).cert
      (by decide +kernel) σ base machine⟩

theorem prefix_simulates : prefixPublic.Agrees 1 4 base σ machine := by
  apply prefixPublic.correct
  apply (prefixPublic.memoryLoopScopes_input (by decide +kernel) 1 4 base σ machine).mpr
  refine ⟨fixture_repr, by decide +kernel, ?_⟩
  exact LoopScopes.room_of_prefixBudget (prefixPublic.memoryLoopScopesResult (by decide +kernel)).cert
    (show LoopScopes.prefixBudget (prefixPublic.memoryLoopScopesResult (by decide +kernel)).cert σ =
      some 0 from by decide +kernel) (.inl rfl)

private theorem agreement_fault {P : Prog C Γ Γ} (result : Compiler.Compilation 0 (Frag.init Γ) P)
    (hp : Evm.Prog.pays P = false) (hs : P.run σ = .error .diverge)
    (hr : result.Agrees 1 4 base σ machine) : run result.code machine = .fault := by
  rcases hr with ⟨o, m', ho, ht, hstack, hrepr⟩ | ⟨ho, ht⟩ | ⟨hpay, ht, hrest⟩ | ⟨ho, ht⟩
  · rw [hs] at ho
    cases ho
  · rcases ho with ho | ⟨ha, ho⟩ <;> rw [hs] at ho <;> cases ho
  · rw [hp] at hpay
    cases hpay
  · rcases ht with ht | ⟨hpay, ht⟩
    · exact ht
    · rw [hp] at hpay
      cases hpay

/-- The syntactically present revert suffix cannot replace divergence. -/
theorem selected_faults : run selectedPublic.code machine = .fault :=
  agreement_fault selectedPublic rfl selected_diverges selected_simulates
theorem prefix_faults : run prefixPublic.code machine = .fault :=
  agreement_fault prefixPublic rfl prefix_diverges prefix_simulates

/-- info: (some 0, true, true) -/
#guard_msgs in
#eval (LoopScopes.prefixBudget (prefixPublic.memoryLoopScopesResult (by decide +kernel)).cert σ,
  match skipped.run σ with | .ok _ => true | _ => false,
  match run skippedPublic.code machine with | .ok _ _ => true | _ => false)

#print axioms selected_faults
#print axioms prefix_faults

/-- Preserve the existing payment halt policy when extracting a nonpaying fault. -/
theorem agrees_fault {K : Contract} {b L frame : Nat} {Θ Ξ : Ctx} {F : Frag Θ}
    {P : Prog K Θ Ξ} (result : Compiler.Compilation b F P)
    {base : Nat → Fin W} {σ : State K Θ} {m : Machine}
    (hp : Evm.Prog.pays P = false) (hs : P.run σ = .error .diverge)
    (hr : result.Agrees L frame base σ m) : run result.code m = .fault := by
  rcases hr with ⟨o, m', ho, ht, hstack, hrepr⟩ | ⟨ho, ht⟩ | ⟨hpay, ht, hrest⟩ | ⟨ho, ht⟩
  · rw [hs] at ho
    cases ho
  · rcases ho with ho | ⟨ha, ho⟩ <;> rw [hs] at ho <;> cases ho
  · rw [hp] at hpay
    cases hpay
  · rcases ht with ht | ⟨hpay, ht⟩
    · exact ht
    · rw [hp] at hpay
      cases hpay

end Solidity.Evm.Memory.LoopScopeDivergenceExamples
