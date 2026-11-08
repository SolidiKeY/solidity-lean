import Solidity.Yul.Compilation.ScopedLoopExecution
import Solidity.Yul.Compilation.CompletionControls
/-! Original intrinsic for visitor using actual recursively scoped component
artifacts. Existing compiler blocks and source/model executors are unchanged.
This is forward normal-success transport, not logical Source/G24/native closure. -/
namespace Solidity.Yul.Compilation.ScopedForCompilation
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions

inductive Compiled {c : Control} {n : Nat} (fuel : Nat) : Stmt [] [] c n → Type where
 | loop {pre : Stmt [] [] ⟨c.function,false⟩ n} {test : Expr [] [] n 1}
     {post : Stmt [] [] ⟨c.function,false⟩ n} {body : Stmt [] [] ⟨c.function,true⟩ n}
     (initializer : ScopedControlCompilation.Artifact fuel pre)
     (condition : ProducerExpressions.Compiled fuel test)
     (step : ScopedControlCompilation.Artifact fuel post)
     (work : ScopedControlCompilation.Artifact fuel body) : Compiled fuel (.for_ pre test post body)

def Compiled.profile {c n fuel} {stmt : Stmt [] [] c n} (compiled : Compiled fuel stmt) : StmtWordP stmt :=
 Compiled.casesOn (motive := fun stmt _ => StmtWordP stmt) compiled
   (fun initializer condition step work =>
     ⟨initializer.compiled.profile,condition.profile,step.compiled.profile,work.compiled.profile⟩)

def Compiled.emit {c n fuel} {stmt : Stmt [] [] c n} (compiled : Compiled fuel stmt) : Option Backend.Block :=
 Compiled.casesOn (motive := fun _ _ => Option Backend.Block) compiled
   (fun initializer condition step work =>
     (condition.lowered.code 0).map (fun p => .seq initializer.block (.loop p (.seq work.block step.block))))

/-- Inspect the actual original for constructor and call actual component
visitors; local refusal is not an admission change. -/
def compile {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Compiled fuel stmt) := by
 apply Stmt.casesOn (motive_1 := fun F X c n stmt =>
   match F,X with
   | [],[] => Option (Compiled fuel stmt)
   | _,_ => Unit) stmt
 case for_ =>
   intro F X c n pre test post body
   cases F <;> cases X
   · exact do
       let initializer ← ScopedControlCompilation.lower fuel pre
       let condition ← PureExpressions.compile fuel test
       let step ← ScopedControlCompilation.lower fuel post
       let work ← ScopedControlCompilation.lower fuel body
       pure (.loop initializer condition step work)
   all_goals exact ()
 all_goals intro F X; cases F <;> cases X <;> intros <;> first | exact none | exact ()

structure Artifact {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) where
 compiled : Compiled fuel stmt
 block : Backend.Block
 code : List Evm.Instr
 emitted : compiled.emit = some block
 selected : WordControl.blockCode block = some code

def lower {c : Control} {n : Nat} (fuel : Nat) (stmt : Stmt [] [] c n) : Option (Artifact fuel stmt) := do
 let compiled ← compile fuel stmt
 match emitted : compiled.emit with
 | none => none
 | some block =>
   match selected : WordControl.blockCode block with
   | none => none
   | some code => some ⟨compiled,block,code,emitted,selected⟩

/-- Compose genuine original initializer and phase source completions. The
arbitrary source components prevent concrete evaluator reduction from hiding
the bind; no compiler/target run or new calling convention is assumed. -/
theorem source_for {c : Control} {n : Nat}
 {pre : Stmt [] [] ⟨c.function,false⟩ n} {test : Expr [] [] n 1}
 {post : Stmt [] [] ⟨c.function,false⟩ n} {body : Stmt [] [] ⟨c.function,true⟩ n}
 (hp : StmtWordP pre) (ht : ExprWordP test) (hs : StmtWordP post) (hb : StmtWordP body)
 (horizon : Nat) (locals mid out : Vector Scalar.Word n)
 (started : evalStmt horizon .nil True.intro pre hp (sourceLocals locals) = some ⟨sourceLocals mid,.normal⟩)
 (completed : evalLoop horizon .nil True.intro test ht post hs body hb (sourceLocals mid) =
   some (⟨sourceLocals out,.normal⟩ : Outcome c n)) :
 evalStmt (horizon+1) .nil True.intro (.for_ pre test post body) ⟨hp,ht,hs,hb⟩ (sourceLocals locals) =
 some (⟨sourceLocals out,.normal⟩ : Outcome c n) := by
 change Option.bind (evalStmt horizon .nil True.intro pre hp (sourceLocals locals)) _ = _
 rw [started]
 exact completed

theorem Artifact.source_to_model {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (horizon : Nat) (locals : Vector Scalar.Word n) (result : Outcome c n)
 (ran : evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word n, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 rcases artifact with ⟨compiled,block,code,emitted,selected⟩
 cases compiled with
 | loop initializer condition step work =>
   change (condition.lowered.code 0).map (fun p =>
     Backend.Block.seq initializer.block (.loop p (.seq work.block step.block))) = some block at emitted
   obtain ⟨p,hp,same⟩ := Option.map_eq_some_iff.mp emitted
   subst block
   change (WordControl.blockCode initializer.block).bind (fun a =>
     ((WordMachine.selectCode p).bind (fun q =>
       ((WordControl.blockCode work.block).bind (fun b =>
         (WordControl.blockCode step.block).map (fun s => b++s))).map
           (fun b => [Evm.Instr.loop q b]))).map (fun b => a++b)) = some code at selected
   rw [initializer.selected,work.selected,step.selected] at selected
   simp only [Option.bind_some,Option.map_some] at selected
   obtain ⟨loopCode,loopSelected,same⟩ := Option.map_eq_some_iff.mp selected
   obtain ⟨q,sq,loopSame⟩ := Option.bind_eq_some_iff.mp loopSelected
   cases Option.some.inj loopSame
   subst code
   cases horizon with
   | zero => cases ran
   | succ horizon =>
     change Option.bind (evalStmt horizon .nil True.intro _ initializer.compiled.profile (sourceLocals locals)) _ = some result at ran
     obtain ⟨middle,preSource,remaining⟩ := Option.bind_eq_some_iff.mp ran
     obtain ⟨mid,same,entering⟩ := initializer.source_to_model horizon locals middle preSource m caller
     subst middle
     change evalLoop horizon .nil True.intro _ condition.profile _ step.compiled.profile
       _ work.compiled.profile (sourceLocals mid) = some result at remaining
     obtain ⟨out,same,loopTarget⟩ := ScopedLoopExecution.model condition step work p q hp sq horizon mid result remaining m caller
     refine ⟨out,same,?_⟩
     rw [Evm.run_append_ok entering]
     exact loopTarget

theorem Artifact.normal_to_model {c : Control} {n fuel : Nat} {stmt : Stmt [] [] c n}
 (artifact : Artifact fuel stmt) (horizon : Nat) (locals out : Vector Scalar.Word n)
 (ran : evalStmt horizon .nil True.intro stmt artifact.compiled.profile (sourceLocals locals) =
   some ⟨sourceLocals out,.normal⟩) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 exact CompletionControls.normal_output (c := c) out
   (fun actual => Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
     .ok {m with stack := actual.toList.map coreWord++caller} 0)
   (artifact.source_to_model horizon locals ⟨sourceLocals out,.normal⟩ ran m caller)


/-- info: 'Solidity.Yul.Compilation.ScopedForCompilation.source_for' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms source_for
/-- info: 'Solidity.Yul.Compilation.ScopedForCompilation.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile
/-- info: 'Solidity.Yul.Compilation.ScopedForCompilation.lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lower
/-- info: 'Solidity.Yul.Compilation.ScopedForCompilation.Artifact.source_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.source_to_model
/-- info: 'Solidity.Yul.Compilation.ScopedForCompilation.Artifact.normal_to_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Artifact.normal_to_model
end Solidity.Yul.Compilation.ScopedForCompilation
