import Solidity.Yul.Compilation.ScopedControlCompilation
/-! Actual finite original loop-phase completion through recursively scoped
body/post compiler artifacts. Existing source and model loop executors are
unchanged; no native/divergence/capacity/G24 adequacy is inferred. -/
namespace Solidity.Yul.Compilation.ScopedLoopExecution
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fc fp fb : Nat} {test : Expr [] [] n 1}
 {step : Stmt [] [] ⟨c.function,false⟩ n} {work : Stmt [] [] ⟨c.function,true⟩ n}

theorem finite (condition : ProducerExpressions.Compiled fc test)
 (post : ScopedControlCompilation.Artifact fp step) (body : ScopedControlCompilation.Artifact fb work)
 (p : Backend.Program) (q : List Evm.Instr)
 (emitted : condition.lowered.code 0 = some p) (selected : WordMachine.selectCode p = some q)
 (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalLoop horizon .nil True.intro test condition.profile step post.compiled.profile
   work body.compiled.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.loopIterN (Evm.run q) (Evm.run (body.code++post.code)) horizon
   {m with stack := locals.toList.map coreWord++caller} =
 .inr (.ok {m with stack := out.toList.map coreWord++caller} 0) := by
 induction horizon generalizing locals result with
 | zero => cases ran
 | succ horizon ih =>
   change Option.bind (evalExpr horizon .nil True.intro test condition.profile (sourceLocals locals)) _ = some result at ran
   obtain ⟨values,tested,remaining⟩ := Option.bind_eq_some_iff.mp ran
   have same := evalExpr_completed_unique .nil True.intro test condition.profile (sourceLocals locals)
     tested (condition.source locals)
   subst values
   change (if (condition.value locals).toNat = 0 then
     some (⟨sourceLocals locals,.normal⟩ : Outcome c n) else _) = some result at remaining
   have testedTarget : Evm.run q {m with stack := locals.toList.map coreWord++caller} =
     .ok {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} 0 := by
     simpa only [Vector.toList_empty,List.nil_append] using
       WordExecution.loweredExpr_machine condition.lowered 0 p q emitted selected locals #v[] m caller
   by_cases zero : condition.value locals = 0
   · have zn : (condition.value locals).toNat = 0 := congrArg BitVec.toNat zero
     rw [if_pos zn] at remaining
     refine ⟨locals,(Option.some.inj remaining).symm,?_⟩
     rw [Evm.loopIterN,Evm.loopTurn,testedTarget,zero]
     rfl
   · have nz : (condition.value locals).toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
     rw [if_neg nz] at remaining
     change Option.bind (evalStmt horizon .nil True.intro work body.compiled.profile (sourceLocals locals)) _ = some result at remaining
     obtain ⟨afterBody,bodySource,remaining⟩ := Option.bind_eq_some_iff.mp remaining
     obtain ⟨mid,same,bodyTarget⟩ := body.source_to_model horizon locals afterBody bodySource m caller
     subst afterBody
     change Option.bind (evalStmt horizon .nil True.intro step post.compiled.profile (sourceLocals mid)) _ = some result at remaining
     obtain ⟨afterPost,postSource,remaining⟩ := Option.bind_eq_some_iff.mp remaining
     obtain ⟨next,same,postTarget⟩ := post.source_to_model horizon mid afterPost postSource m caller
     subst afterPost
     change evalLoop horizon .nil True.intro test condition.profile step post.compiled.profile
       work body.compiled.profile (sourceLocals next) = some result at remaining
     obtain ⟨out,same,completed⟩ := ih next result remaining
     have iteration : Evm.run (body.code++post.code) {m with stack := locals.toList.map coreWord++caller} =
       .ok {m with stack := next.toList.map coreWord++caller} 0 := by
       rw [Evm.run_append_ok bodyTarget]
       exact postTarget
     refine ⟨out,same,?_⟩
     rw [Evm.loopIterN,Evm.loopTurn,testedTarget]
     change (match (if (condition.value locals).toNat = 0 then
       .inr (.ok {m with stack := locals.toList.map coreWord++caller} 0)
       else match Evm.run (body.code++post.code) {m with stack := locals.toList.map coreWord++caller} with
        | .ok updated 0 => .inl updated
        | .ok _ (_+1) => .inr .fault
        | result => .inr result : Evm.Machine ⊕ Evm.Out) with
      | .inl updated => Evm.loopIterN (Evm.run q) (Evm.run (body.code++post.code)) horizon updated
      | .inr result => .inr result) = _
     rw [if_neg nz,iteration]
     exact completed

theorem model (condition : ProducerExpressions.Compiled fc test)
 (post : ScopedControlCompilation.Artifact fp step) (body : ScopedControlCompilation.Artifact fb work)
 (p : Backend.Program) (q : List Evm.Instr)
 (emitted : condition.lowered.code 0 = some p) (selected : WordMachine.selectCode p = some q)
 (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalLoop horizon .nil True.intro test condition.profile step post.compiled.profile
   work body.compiled.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run [.loop q (body.code++post.code)] {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 obtain ⟨out,same,completed⟩ := finite condition post body p q emitted selected horizon locals result ran m caller
 refine ⟨out,same,?_⟩
 have ended := Evm.loopRun_of_iterN completed
 change (Evm.loopRun (Evm.run q) (Evm.run (body.code++post.code)) _).bind
   (fun next pending => Evm.exec [] pending next) = _
 rw [ended]
 rfl

/-- Existing compiler blocks are emitted directly; body and post retain their
actual scoped compiler artifacts and exact original control indices. -/
def emit (condition : ProducerExpressions.Compiled fc test)
 (post : ScopedControlCompilation.Artifact fp step) (body : ScopedControlCompilation.Artifact fb work) :
 Option Backend.Block :=
 (condition.lowered.code 0).map (fun p => .loop p (.seq body.block post.block))

theorem selection (condition : ProducerExpressions.Compiled fc test)
 (post : ScopedControlCompilation.Artifact fp step) (body : ScopedControlCompilation.Artifact fb work)
 (p : Backend.Program) (q : List Evm.Instr)
 (emitted : condition.lowered.code 0 = some p) (selected : WordMachine.selectCode p = some q) :
 emit condition post body = some (.loop p (.seq body.block post.block)) ∧
 WordControl.blockCode (.loop p (.seq body.block post.block)) = some [.loop q (body.code++post.code)] := by
 constructor
 · rw [emit,emitted]; rfl
 · change (WordMachine.selectCode p).bind (fun q =>
     ((WordControl.blockCode body.block).bind (fun b => (WordControl.blockCode post.block).map (fun p => b++p))).map
       (fun b => [Evm.Instr.loop q b])) = _
   rw [selected,body.selected,post.selected]
   rfl

/-- info: 'Solidity.Yul.Compilation.ScopedLoopExecution.finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finite
/-- info: 'Solidity.Yul.Compilation.ScopedLoopExecution.model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model
/-- info: 'Solidity.Yul.Compilation.ScopedLoopExecution.selection' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms selection
end Solidity.Yul.Compilation.ScopedLoopExecution
