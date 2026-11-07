import Solidity.Yul.Compilation.ScopedLoopExecution
import Solidity.Yul.Compilation.ScopedControlCompletion
import Solidity.Yul.Compilation.SourceLoopControls
/-! A genuine conditional/scoped loop body beyond the older normal-component
visitor: clear the counter, retire dirty fresh words, preserve another local.
This checks existing original source/model executors, not native EVM validity. -/
namespace Solidity.Yul.Compilation.ScopedLoopExecution.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root dirty)

def inner : Solidity.Yul.Stmt [] [] ⟨false,true⟩ 4 := .seq
 (.assign (fun _ : Fin 1 => .local 2) (.literal 0))
 (.assign (fun _ : Fin 1 => .local 0) (.local 3))
def innerReference : ProducerStatements.Compiled 3 inner :=
 ProducerStatements.seq (ProducerStatements.assign 2 (literal 0 0))
  (ProducerStatements.assign 0 (localExpr 0 3))
def letSource : Solidity.Yul.Stmt [] [] ⟨false,true⟩ 3 := .let_ 1 (.local 2) inner
def initializer := localExpr (n := 3) 2 2
def scopeSource : Solidity.Yul.Stmt [] [] ⟨false,true⟩ 2 := .zero 1 letSource
def work : Solidity.Yul.Stmt [] [] ⟨false,true⟩ 2 := .if_ (.local 0) scopeSource
def body := (ScopedControlCompilation.lower 6 work).get (by rfl)
def postSource : Solidity.Yul.Stmt [] [] root 2 := .skip
def post := (ScopedControlCompilation.lower 1 postSource).get (by rfl)
def condition := localExpr (n := 2) 0 0
def guardCondition := localExpr (n := 2) 5 0
def scopeProfile : StmtWordP scopeSource := ⟨initializer.profile,innerReference.profile⟩
def p := (condition.lowered.code 0).get (by rfl)
def q := (WordMachine.selectCode p).get (by rfl)
def code := [Evm.Instr.loop q (body.code++post.code)]
def block := Backend.Block.loop p (.seq body.block post.block)

theorem inner_source (b c : Scalar.Word) :
 evalStmt 3 .nil True.intro inner innerReference.profile (sourceLocals #v[c,0,b,c]) =
 some ⟨sourceLocals #v[c,0,0,c],.normal⟩ := by
 have same : innerReference.update #v[c,0,b,c] = #v[c,0,0,c] := by rfl
 have ran := innerReference.source #v[c,0,b,c]
 rw [same] at ran
 exact ran

theorem body_source (b c : Scalar.Word) (nonzero : b ≠ 0) :
 evalStmt 6 .nil True.intro work body.compiled.profile (sourceLocals #v[b,c]) =
 some ⟨sourceLocals #v[0,c],.normal⟩ := by
 have projectedInner : outerLocals (fresh := 1) #v[c,(0 : Scalar.Word),0,c] = #v[0,0,c] := by
  apply Vector.toList_inj.mp
  rw [outerLocals_toList]
  rfl
 have letRan := ScopedControlCompletion.source_let initializer innerReference.profile 3 #v[0,b,c]
   #v[c,0,0,c] (inner_source b c)
 change evalStmt 4 .nil True.intro letSource _ (sourceLocals #v[0,b,c]) = _ at letRan
 rw [projectedInner] at letRan
 have projectedOuter : outerLocals (fresh := 1) #v[(0 : Scalar.Word),0,c] = #v[0,c] := by
  apply Vector.toList_inj.mp
  rw [outerLocals_toList]
  rfl
 have scopeRan := ScopedControlCompletion.source_zero (c := ⟨false,true⟩) (n := 2) (fresh := 1) (body := letSource) (⟨initializer.profile,innerReference.profile⟩ : StmtWordP letSource)
   4 #v[b,c] #v[0,0,c] letRan
 rw [projectedOuter] at scopeRan
 exact LetControlCompletion.source_true guardCondition scopeProfile 5 #v[b,c] #v[0,c] nonzero scopeRan

theorem loop_source (b c : Scalar.Word) (nonzero : b ≠ 0) :
 evalLoop (c := root) 7 .nil True.intro (.local 0) condition.profile postSource post.compiled.profile
   work body.compiled.profile (sourceLocals #v[b,c]) = some ⟨sourceLocals #v[0,c],.normal⟩ := by
 have nz : b.toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
 change (if b.toNat = 0 then some (⟨sourceLocals #v[b,c],.normal⟩ : Outcome root 2) else _) = _
 rw [if_neg nz]
 change Option.bind (evalStmt 6 .nil True.intro work body.compiled.profile (sourceLocals #v[b,c])) _ = _
 rw [body_source b c nonzero]
 have stepped : evalStmt 6 .nil True.intro postSource post.compiled.profile (sourceLocals #v[0,c]) =
   some ⟨sourceLocals #v[0,c],.normal⟩ := by rfl
 change Option.bind (evalStmt 6 .nil True.intro postSource post.compiled.profile (sourceLocals #v[0,c])) _ = _
 rw [stepped]
 change evalLoop (c := root) 6 .nil True.intro (.local 0) condition.profile postSource post.compiled.profile
   work body.compiled.profile (sourceLocals #v[0,c]) = _
 rfl

theorem emitted_selected : emit (c := root) condition post body = some block ∧ WordControl.blockCode block = some code :=
 selection (c := root) condition post body p q (by rfl) (by rfl)

theorem target_done (b c : Scalar.Word) (nonzero : b ≠ 0) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run code {m with stack := coreWord b::coreWord c::caller} =
 .ok {m with stack := coreWord 0::coreWord c::caller} 0 := by
 obtain ⟨out,same,target⟩ := model condition post body p q (by rfl) (by rfl) 7 #v[b,c]
   ⟨sourceLocals #v[0,c],.normal⟩ (loop_source b c nonzero) m caller
 have equal : #v[(0 : Scalar.Word),c] = out := SourceLoopCompletion.sourceLocals_injective (congrArg Outcome.vars same)
 cases equal
 exact target

theorem zero_source (c : Scalar.Word) :
 evalLoop (c := root) 2 .nil True.intro (.local 0) condition.profile postSource post.compiled.profile
   work body.compiled.profile (sourceLocals #v[0,c]) = some ⟨sourceLocals #v[0,c],.normal⟩ := by rfl

theorem zero_target (c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run code {m with stack := coreWord 0::coreWord c::caller} =
 .ok {m with stack := coreWord 0::coreWord c::caller} 0 := by
 obtain ⟨out,same,target⟩ := model condition post body p q (by rfl) (by rfl) 2 #v[0,c]
   ⟨sourceLocals #v[0,c],.normal⟩ (zero_source c) m caller
 have equal : #v[(0 : Scalar.Word),c] = out := SourceLoopCompletion.sourceLocals_injective (congrArg Outcome.vars same)
 cases equal
 exact target

theorem target_all (b c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run code {m with stack := coreWord b::coreWord c::caller} =
 .ok {m with stack := coreWord 0::coreWord c::caller} 0 := by
 by_cases zero : b = 0
 · subst b
   exact zero_target c m caller
 · exact target_done b c zero m caller

def wholeSource : Solidity.Yul.Stmt [] [] root 2 := .for_ .skip (.local 0) .skip work
#guard (ForCompilation.lower 6 wholeSource 0).isNone
#guard (evalLoop (c := root) 0 .nil True.intro (.local 0) condition.profile postSource post.compiled.profile
 work body.compiled.profile (sourceLocals #v[dirty,dirty])).isNone
#guard Scalar.stackBound [Backend.Instr.op (.DUP 0)] (1024 : Int) = false
#guard Scalar.run [Backend.Instr.op (.DUP 0)] [] = none
#guard dirty ≠ 0

/-- info: 'Solidity.Yul.Compilation.ScopedLoopExecution.Controls.inner_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms inner_source
/-- info: 'Solidity.Yul.Compilation.ScopedLoopExecution.Controls.body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms body_source
/-- info: 'Solidity.Yul.Compilation.ScopedLoopExecution.Controls.loop_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loop_source
/-- info: 'Solidity.Yul.Compilation.ScopedLoopExecution.Controls.emitted_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms emitted_selected
/-- info: 'Solidity.Yul.Compilation.ScopedLoopExecution.Controls.target_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_done
/-- info: 'Solidity.Yul.Compilation.ScopedLoopExecution.Controls.zero_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_source
/-- info: 'Solidity.Yul.Compilation.ScopedLoopExecution.Controls.zero_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_target
/-- info: 'Solidity.Yul.Compilation.ScopedLoopExecution.Controls.target_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_all
end Solidity.Yul.Compilation.ScopedLoopExecution.Controls
