import Solidity.Evm.Compiler
import Solidity.Evm.MemoryCompileExamples
namespace Solidity.Evm.Memory.LoopScopeExamples
open CompileExamples

private def cond : Val C Γ .bool :=
  .binop .lt rfl rfl (.simple (.local .here)) (.simple (.lit 3 rfl))
private def turns : Prog C Γ Γ := .cons (.loop .auto cond writeAndRead) .nil
private def blockTurns : Prog C Γ Γ := .cons (.block turns) .nil
private def yesTurns : Prog C Γ Γ :=
  .cons (.ite (.simple (.bool true)) turns .nil) .nil
private def noTurns : Prog C Γ Γ :=
  .cons (.ite (.simple (.bool false)) turns .nil) .nil
private def exhaustedBody : Prog C Γ Γ := .cons .assumeFalse .nil
private def nestedBody : Prog C Γ Γ :=
  .cons (.loop .auto (.simple (.bool false)) turns) .nil

private def compiledBlock := (Compiler.compile 0 (Frag.init Γ) blockTurns).get (by decide +kernel)
private def compiledYes := (Compiler.compile 0 (Frag.init Γ) yesTurns).get (by decide +kernel)
private def compiledNo := (Compiler.compile 0 (Frag.init Γ) noTurns).get (by decide +kernel)
attribute [irreducible] compiledBlock compiledYes compiledNo

example : Memory.compileProg 0 (Frag.init Γ) blockTurns = none := rfl
example : Loops.compileProg 0 (Frag.init Γ) blockTurns = none := rfl
example : compiledBlock.isMemoryLoopScopes = true := by decide +kernel
example : compiledYes.isMemoryLoopScopes = true := by decide +kernel
example : compiledNo.isMemoryLoopScopes = true := by decide +kernel

theorem block_simulates : compiledBlock.Agrees 1 4 base σ machine := by
  apply compiledBlock.correct
  apply (compiledBlock.memoryLoopScopes_input (by decide +kernel) 1 4 base σ machine).mpr
  exact ⟨fixture_repr, by decide +kernel,
    LoopScopes.room_nonallocating (compiledBlock.memoryLoopScopesResult (by decide +kernel)).cert
      (by decide +kernel) σ base machine⟩
theorem selected_simulates : compiledYes.Agrees 1 4 base σ machine := by
  apply compiledYes.correct
  apply (compiledYes.memoryLoopScopes_input (by decide +kernel) 1 4 base σ machine).mpr
  exact ⟨fixture_repr, by decide +kernel,
    LoopScopes.room_nonallocating (compiledYes.memoryLoopScopesResult (by decide +kernel)).cert
      (by decide +kernel) σ base machine⟩
theorem unselected_simulates : compiledNo.Agrees 1 4 base σ machine := by
  apply compiledNo.correct
  apply (compiledNo.memoryLoopScopes_input (by decide +kernel) 1 4 base σ machine).mpr
  exact ⟨fixture_repr, by decide +kernel,
    LoopScopes.room_nonallocating (compiledNo.memoryLoopScopesResult (by decide +kernel)).cert
      (by decide +kernel) σ base machine⟩

private def sourceValue (r : TRes (Solidity.Out C CompileExamples.H Γ)) : Option Int :=
  match r with
  | .ok o => some (TEnv.get (.here : Idx Γ (.val .uint)) o.st.env).1
  | .error _ => none
private def targetValue (r : Out) : Option Nat :=
  match r with
  | .ok m _ => match m.mem 3 with | .val n => some n.val | _ => none
  | _ => none
/-- info: [(some 5, some 5), (some 5, some 5), (some 0, some 0)] -/
#guard_msgs in
#eval [(sourceValue (blockTurns.run σ), targetValue (run compiledBlock.code machine)),
       (sourceValue (yesTurns.run σ), targetValue (run compiledYes.code machine)),
       (sourceValue (noTurns.run σ), targetValue (run compiledNo.code machine))]
/-- info: (false, false) -/
#guard_msgs in
#eval (sourceValue (blockTurns.run σ) == some 4, targetValue (run compiledBlock.code machine) == some 4)

/-- Both branches must compile even when the rejected branch is unselected. -/
example : (Compiler.compile 0 (Frag.init Γ)
    (.cons (.ite (.simple (.bool false)) nestedBody turns) .nil)).isNone = true := by
  decide +kernel
example : (Compiler.compile 0 (Frag.init Γ)
    (.cons (.ite (.simple (.bool false)) exhaustedBody turns) .nil)).isNone = true := by
  decide +kernel
example : (Compiler.compile 0 (Frag.init Γ)
    (.cons (.block exhaustedBody) .nil)).isNone = true := by decide +kernel


private def zeroTurns : Prog C Γ Γ :=
  .cons (.block (.cons (.loop .auto (.simple (.bool false)) outOfBounds) .nil)) .nil
private def revertingTurns : Prog C Γ Γ :=
  .cons (.ite (.simple (.bool true))
    (.cons (.loop .auto (.simple (.bool true)) outOfBounds) .nil) .nil) .nil
private def zeroPublic := (Compiler.compile 0 (Frag.init Γ) zeroTurns).get (by decide +kernel)
private def revertingPublic := (Compiler.compile 0 (Frag.init Γ) revertingTurns).get (by decide +kernel)
attribute [irreducible] zeroPublic revertingPublic

theorem zero_simulates : zeroPublic.Agrees 1 4 base σ machine := by
  apply zeroPublic.correct
  apply (zeroPublic.memoryLoopScopes_input (by decide +kernel) 1 4 base σ machine).mpr
  exact ⟨fixture_repr, by decide +kernel,
    LoopScopes.room_nonallocating (zeroPublic.memoryLoopScopesResult (by decide +kernel)).cert
      (by decide +kernel) σ base machine⟩
theorem reverting_simulates : revertingPublic.Agrees 1 4 base σ machine := by
  apply revertingPublic.correct
  apply (revertingPublic.memoryLoopScopes_input (by decide +kernel) 1 4 base σ machine).mpr
  exact ⟨fixture_repr, by decide +kernel,
    LoopScopes.room_nonallocating (revertingPublic.memoryLoopScopesResult (by decide +kernel)).cert
      (by decide +kernel) σ base machine⟩

private def sourceReverts {α : Type} : TRes α → Bool
  | .error .revert => true
  | _ => false
private def targetReverts : Out → Bool
  | .revert => true
  | _ => false

/- A supported body really reverts, but the zero-iteration scope never reaches it. -/
/-- info: (true, some 0, some 0, false, true, true) -/
#guard_msgs in
#eval (sourceReverts (outOfBounds.run σ), sourceValue (zeroTurns.run σ),
  targetValue (run zeroPublic.code machine), targetReverts (run zeroPublic.code machine),
  sourceReverts (revertingTurns.run σ), targetReverts (run revertingPublic.code machine))

/-- Source exhaustion remains exact, alongside the earlier static refusal. -/
example : (Prog.cons (Stmt.block (.cons .assumeFalse .nil)) .nil : Prog C Γ Γ).run σ =
    .error .exhausted := rfl

#print axioms zero_simulates
#print axioms reverting_simulates

end Solidity.Evm.Memory.LoopScopeExamples
