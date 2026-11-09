import Solidity.Yul.Compilation.ScopedLoopExecution
import Solidity.Yul.Compilation.ScopedControlCompletion
import Solidity.Yul.Compilation.CompletionControls
/-! Reverse finite-success correspondence for existing scoped body/post loop
artifacts. Actual successful model traces supply genuine source completions;
model noncompletion faults are not source/native divergence equivalence. -/
namespace Solidity.Yul.Compilation.ScopedLoopCompletion
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
variable {c : Control} {n fc fp fb : Nat} {test : Expr [] [] n 1}
 {step : Stmt [] [] ⟨c.function,false⟩ n} {work : Stmt [] [] ⟨c.function,true⟩ n}

theorem source_zero (condition : ProducerExpressions.Compiled fc test)
 (post : ScopedControlCompilation.Artifact fp step) (body : ScopedControlCompilation.Artifact fb work)
 (locals : Vector Scalar.Word n) (zero : condition.value locals = 0) :
 evalLoop (c := c) (fc+1) .nil True.intro test condition.profile step post.compiled.profile
   work body.compiled.profile (sourceLocals locals) = some ⟨sourceLocals locals,.normal⟩ := by
 change Option.bind (evalExpr fc .nil True.intro test condition.profile (sourceLocals locals)) _ = _
 rw [condition.source locals]
 change (if (condition.value locals).toNat = 0 then _ else _) = _
 have zn : (condition.value locals).toNat = 0 := congrArg BitVec.toNat zero
 rw [if_pos zn]
 rfl

theorem source_more (condition : ProducerExpressions.Compiled fc test)
 (post : ScopedControlCompilation.Artifact fp step) (body : ScopedControlCompilation.Artifact fb work)
 (hb hp hr : Nat) (locals mid next out : Vector Scalar.Word n)
 (nonzero : condition.value locals ≠ 0)
 (worked : evalStmt hb .nil True.intro work body.compiled.profile (sourceLocals locals) = some ⟨sourceLocals mid,.normal⟩)
 (stepped : evalStmt hp .nil True.intro step post.compiled.profile (sourceLocals mid) = some ⟨sourceLocals next,.normal⟩)
 (remaining : evalLoop hr .nil True.intro test condition.profile step post.compiled.profile
   work body.compiled.profile (sourceLocals next) = some (⟨sourceLocals out,.normal⟩ : Outcome c n)) :
 evalLoop (max fc (max hb (max hp hr))+1) .nil True.intro test condition.profile step post.compiled.profile
   work body.compiled.profile (sourceLocals locals) = some (⟨sourceLocals out,.normal⟩ : Outcome c n) := by
 let H := max fc (max hb (max hp hr))
 have tested : evalExpr H .nil True.intro test condition.profile (sourceLocals locals) =
   some (fun _ => (condition.value locals).toFin) := CompletionControls.completed_horizon
   (fun fuel => evalExpr fuel .nil True.intro test condition.profile (sourceLocals locals))
   (fun fuel extra => evalExpr_refines_add fuel extra .nil True.intro test condition.profile (sourceLocals locals))
   (show fc ≤ H by dsimp only [H]; omega) (condition.source locals)
 have worked' : evalStmt H .nil True.intro work body.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals mid,.normal⟩ := CompletionControls.completed_horizon
   (fun fuel => evalStmt fuel .nil True.intro work body.compiled.profile (sourceLocals locals))
   (fun fuel extra => evalStmt_refines_add fuel extra .nil True.intro work body.compiled.profile (sourceLocals locals))
   (show hb ≤ H by dsimp only [H]; omega) worked
 have stepped' : evalStmt H .nil True.intro step post.compiled.profile (sourceLocals mid) =
   some ⟨sourceLocals next,.normal⟩ := CompletionControls.completed_horizon
   (fun fuel => evalStmt fuel .nil True.intro step post.compiled.profile (sourceLocals mid))
   (fun fuel extra => evalStmt_refines_add fuel extra .nil True.intro step post.compiled.profile (sourceLocals mid))
   (show hp ≤ H by dsimp only [H]; omega) stepped
 have remaining' : evalLoop H .nil True.intro test condition.profile step post.compiled.profile
   work body.compiled.profile (sourceLocals next) = some (⟨sourceLocals out,.normal⟩ : Outcome c n) := by
   exact CompletionControls.completed_horizon
     (fun fuel => evalLoop fuel .nil True.intro test condition.profile step post.compiled.profile
       work body.compiled.profile (sourceLocals next))
     (fun fuel extra => evalLoop_refines_add fuel extra .nil True.intro test condition.profile
       step post.compiled.profile work body.compiled.profile (sourceLocals next))
     (show hr ≤ H by dsimp only [H]; omega) remaining
 change Option.bind (evalExpr H .nil True.intro test condition.profile (sourceLocals locals)) _ = _
 rw [tested]
 change (if (condition.value locals).toNat = 0 then _ else _) = _
 have nz : (condition.value locals).toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
 rw [if_neg nz]
 change Option.bind (evalStmt H .nil True.intro work body.compiled.profile (sourceLocals locals)) _ = _
 rw [worked']
 change Option.bind (evalStmt H .nil True.intro step post.compiled.profile (sourceLocals mid)) _ = _
 rw [stepped']
 exact remaining'

theorem iteration_completed (condition : ProducerExpressions.Compiled fc test)
 (post : ScopedControlCompilation.Artifact fp step) (body : ScopedControlCompilation.Artifact fb work)
 (p : Backend.Program) (q : List Evm.Instr)
 (emitted : condition.lowered.code 0 = some p) (selected : WordMachine.selectCode p = some q)
 (count : Nat) (locals : Vector Scalar.Word n)
 (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.loopIterN (Evm.run q) (Evm.run (body.code++post.code)) count
   {m with stack := locals.toList.map coreWord++caller} = .inr (.ok final skip)) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalLoop horizon .nil True.intro test condition.profile step post.compiled.profile
   work body.compiled.profile (sourceLocals locals) = some (⟨sourceLocals out,.normal⟩ : Outcome c n) ∧
 skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} := by
 induction count generalizing locals with
 | zero => cases ran
 | succ count ih =>
   have tested : Evm.run q {m with stack := locals.toList.map coreWord++caller} =
     .ok {m with stack := coreWord (condition.value locals)::(locals.toList.map coreWord++caller)} 0 := by
     simpa only [Vector.toList_empty,List.nil_append] using
       WordExecution.loweredExpr_machine condition.lowered 0 p q emitted selected locals #v[] m caller
   rw [Evm.loopIterN,Evm.loopTurn,tested] at ran
   change (match (if (condition.value locals).toNat = 0 then
      .inr (.ok {m with stack := locals.toList.map coreWord++caller} 0)
      else match Evm.run (body.code++post.code) {m with stack := locals.toList.map coreWord++caller} with
       | .ok next 0 => .inl next
       | .ok _ (_+1) => .inr .fault
       | result => .inr result : Evm.Machine ⊕ Evm.Out) with
     | .inl next => Evm.loopIterN (Evm.run q) (Evm.run (body.code++post.code)) count next
     | .inr result => .inr result) = .inr (.ok final skip) at ran
   by_cases zero : condition.value locals = 0
   · have zn : (condition.value locals).toNat = 0 := congrArg BitVec.toNat zero
     rw [if_pos zn] at ran
     have parts := Evm.Out.ok.inj (Sum.inr.inj ran)
     exact ⟨fc+1,locals,source_zero condition post body locals zero,parts.2.symm,parts.1.symm⟩
   · have nz : (condition.value locals).toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
     rw [if_neg nz] at ran
     cases combined : Evm.run (body.code++post.code) {m with stack := locals.toList.map coreWord++caller} with
     | revert => rw [combined] at ran; cases ran
     | fault => rw [combined] at ran; cases ran
     | ok updated pending =>
       cases pending with
       | succ pending => rw [combined] at ran; cases ran
       | zero =>
         rw [combined] at ran
         change Evm.loopIterN (Evm.run q) (Evm.run (body.code++post.code)) count updated = .inr (.ok final skip) at ran
         have whole : (Evm.run body.code {m with stack := locals.toList.map coreWord++caller}).bind
           (fun mid pending => Evm.exec post.code pending mid) = .ok updated 0 := by
           simpa only [Evm.run,Evm.exec_append] using combined
         cases bodyRun : Evm.run body.code {m with stack := locals.toList.map coreWord++caller} with
         | revert => rw [bodyRun] at whole; cases whole
         | fault => rw [bodyRun] at whole; cases whole
         | ok mid pending =>
           obtain ⟨hb,intermediate,bodySource,done,bodyFrame⟩ := ScopedControlCompletion.artifact_reflected body locals m mid caller pending bodyRun
           rw [bodyRun,done,bodyFrame] at whole
           change Evm.run post.code {m with stack := intermediate.toList.map coreWord++caller} = .ok updated 0 at whole
           obtain ⟨hp,next,postSource,_,postFrame⟩ := ScopedControlCompletion.artifact_reflected post intermediate m updated caller 0 whole
           rw [postFrame] at ran
           obtain ⟨hr,out,rest,done,frame⟩ := ih next ran
           exact ⟨_,out,source_more condition post body hb hp hr locals intermediate next out zero bodySource postSource rest,done,frame⟩

theorem model_to_source (condition : ProducerExpressions.Compiled fc test)
 (post : ScopedControlCompilation.Artifact fp step) (body : ScopedControlCompilation.Artifact fb work)
 (p : Backend.Program) (q : List Evm.Instr)
 (emitted : condition.lowered.code 0 = some p) (selected : WordMachine.selectCode p = some q)
 (locals : Vector Scalar.Word n) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run [.loop q (body.code++post.code)] {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word n),
 evalLoop horizon .nil True.intro test condition.profile step post.compiled.profile
   work body.compiled.profile (sourceLocals locals) = some (⟨sourceLocals out,.normal⟩ : Outcome c n) ∧
 skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} := by
 rw [FramedLoop.singleton_run] at ran
 by_cases ends : ∃ result count, Evm.loopIterN (Evm.run q) (Evm.run (body.code++post.code)) count
   {m with stack := locals.toList.map coreWord++caller} = .inr result
 · obtain ⟨result,count,actual⟩ := ends
   have same : result = .ok final skip := (Evm.loopRun_of_iterN actual).symm.trans ran
   exact iteration_completed condition post body p q emitted selected count locals m final caller skip
     (actual.trans (congrArg Sum.inr same))
 · simp only [Evm.loopRun,ends,↓reduceDIte] at ran
   cases ran

/-- info: 'Solidity.Yul.Compilation.ScopedLoopCompletion.source_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_zero
/-- info: 'Solidity.Yul.Compilation.ScopedLoopCompletion.source_more' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_more
/-- info: 'Solidity.Yul.Compilation.ScopedLoopCompletion.iteration_completed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms iteration_completed
/-- info: 'Solidity.Yul.Compilation.ScopedLoopCompletion.model_to_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms model_to_source
end Solidity.Yul.Compilation.ScopedLoopCompletion
