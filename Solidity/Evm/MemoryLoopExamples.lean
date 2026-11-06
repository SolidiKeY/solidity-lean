import Solidity.Evm.Compiler
import Solidity.Evm.MemoryCompileExamples
import Solidity.Evm.MemoryAllocSourceExamples

/-! Inhabited memory-loop compiler controls. Runtime observations run both actual
evaluators; the public simulation is separately checked by the kernel. -/
namespace Solidity.Evm.Memory.LoopExamples
open CompileExamples

private def condition : Val C Γ .bool :=
  .binop .lt rfl rfl (.simple (.local .here)) (.simple (.lit 3 rfl))
private def loopStmt : Stmt C Γ Γ := .loop .auto condition writeAndRead
private def program : Prog C Γ Γ := .cons loopStmt .nil
private def compiled : Loops.CompiledProg 0 (Frag.init Γ) program :=
  (Loops.compileProg 0 (Frag.init Γ) program).get (by decide +kernel)
private def publicResult : Compiler.Compilation 0 (Frag.init Γ) program :=
  (Compiler.compile 0 (Frag.init Γ) program).get (by decide +kernel)

attribute [irreducible] publicResult

/-- Reproduce the actual old refusal before registering the new compiler path. -/
example : Memory.compileProg 0 (Frag.init Γ) program = none := rfl
example : publicResult.isMemoryLoops = true := by decide +kernel
example : publicResult = .memoryLoops compiled := by unfold publicResult; rfl

/-- The populated alias/array witness satisfies the public input, with no capacity
or termination assumption hidden in the concrete case. -/
theorem public_simulates : publicResult.Agrees 1 4 base σ machine := by
  apply publicResult.correct
  apply (publicResult.memoryLoops_input (by decide +kernel) 1 4 base σ machine).mpr
  exact ⟨fixture_repr, by decide +kernel,
    Loops.room_nonallocating (publicResult.memoryLoopsResult (by decide +kernel)).cert
      (by decide +kernel) σ base machine⟩


theorem no_exhaustion : program.run σ ≠ .error .exhausted :=
  compiled.cert.not_exhausted fixture_repr (by decide +kernel)
    (Loops.room_nonallocating compiled.cert (by decide +kernel) σ base machine)

private def sourceObserve (r : TRes (Solidity.Out C CompileExamples.H Γ)) : Option Int :=
  match r with
  | .ok o => some (TEnv.get (.here : Idx Γ (.val .uint)) o.st.env).1
  | .error _ => none
private def targetObserve (r : Out) : Option (List Nat) :=
  match r with
  | .ok m _ => [m.mem 3, m.mem 17, m.mem 18, m.mem 21].mapM fun w =>
      match w with | .val n => some n.val | _ => none
  | _ => none

/-- info: (some 5, some [5, 5, 9, 4]) -/
#guard_msgs in
#eval (sourceObserve (program.run σ), targetObserve (run publicResult.code machine))

private def zeroProgram : Prog C Γ Γ := .cons (.loop .auto (.simple (.bool false)) writeAndRead) .nil
private def zeroCompiled : Compiler.Compilation 0 (Frag.init Γ) zeroProgram :=
  (Compiler.compile 0 (Frag.init Γ) zeroProgram).get (by decide +kernel)
/-- info: (some 0, some [0, 7, 9, 4]) -/
#guard_msgs in
#eval (sourceObserve (zeroProgram.run σ), targetObserve (run zeroCompiled.code machine))

private def badProgram : Prog C Γ Γ :=
  .cons (.loop .auto (.simple (.bool true)) outOfBounds) .nil
private def badCompiled : Compiler.Compilation 0 (Frag.init Γ) badProgram :=
  (Compiler.compile 0 (Frag.init Γ) badProgram).get (by decide +kernel)
private def sourceReverts {α : Type} : TRes α → Bool
  | .error .revert => true
  | _ => false
private def targetReverts : Out → Bool
  | .revert => true
  | _ => false
/-- info: (true, true) -/
#guard_msgs in
#eval (sourceReverts (badProgram.run σ), targetReverts (run badCompiled.code machine))

/-- Exhaustion-producing statements remain refused, even in unreachable bodies. -/
example : (Loops.compileProg (C := C) 0 (Frag.init Γ)
    (.cons (.loop .auto (.simple (.bool false)) (.cons .assumeFalse .nil)) .nil)).isNone = true := by
  decide +kernel

/-- Refusal boundaries are structural, including unreachable nested/scoped loops. -/
example : (Loops.compileProg (C := C) 0 (Frag.init Γ)
    (.cons (.loop .auto (.simple (.bool false)) program) .nil)).isNone = true := by
  decide +kernel
example : (Loops.compileProg (C := C) 0 (Frag.init Γ)
    (.cons (.block program) .nil)).isNone = true := by decide +kernel
example : (Loops.compileProg (C := C) 0 (Frag.init Γ)
    (.cons (.ite (.simple (.bool false)) program .nil) .nil)).isNone = true := by
  decide +kernel

/-- The refused source shape still exhausts; it is not reclassified as revert. -/
example : (Stmt.loop .auto (.simple (.bool true))
    (.cons .assumeFalse .nil : Prog C Γ Γ)).run σ = .error .exhausted := by
  rw [Stmt.run_loop]
  exact TLoop.run_of_iterN (n := 1) rfl

private def spinCondition : Val C Γ .bool :=
  .binop .eqB rfl rfl (.mlen (.var (.there .here) rfl) rfl) (.simple (.lit 2 rfl))
private def spin : Prog C Γ Γ := .cons (.loop .auto spinCondition (.nil : Prog C Γ Γ)) .nil
private def spinCompiled : Loops.CompiledProg 0 (Frag.init Γ) spin :=
  (Loops.compileProg 0 (Frag.init Γ) spin).get (by decide +kernel)

/-- Mathematical divergence is established without executing an infinite loop. -/
theorem source_diverges : spin.run σ = .error .diverge := by
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

/-- Every finite machine prefix corresponds, hence no machine outcome exists. -/
theorem target_faults : run spinCompiled.code machine = .fault := by
  have hr := spinCompiled.cert.correct fixture_repr (by decide +kernel)
    (Loops.room_nonallocating spinCompiled.cert (by decide +kernel) σ base machine)
  rcases hr with ⟨o, _, _, _, ho, _⟩ | ⟨ho, ht⟩ | ⟨ho, ht⟩
  · rw [source_diverges] at ho; cases ho
  · rw [source_diverges] at ho; cases ho
  · exact ht

#print axioms source_diverges
#print axioms target_faults
#print axioms public_simulates
#print axioms no_exhaustion
end Solidity.Evm.Memory.LoopExamples
