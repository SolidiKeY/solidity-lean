import Solidity.Yul.Compilation.StructuredLoopExecution
import Solidity.Yul.Compilation.ScopedLoopExecutionControls
import Solidity.Yul.Compilation.MultiSwitchCompilationControls
/-! A real switch body clears the counter through nested zero/let scopes;
the post updates the dirty-capable outer word exactly once before the next
zero guard stops. Zero-entry loops skip both body and post. Kernel model only. -/
namespace Solidity.Yul.Compilation.StructuredLoopExecution.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root)

def work : Solidity.Yul.Stmt [] [] ⟨false,true⟩ 2 :=
 .switch (.local 0) (.cons 1 ScopedLoopExecution.Controls.scopeSource .nil) .skip
def body := (StructuredSequenceCompilation.lower 10 work).get (by rfl)
def postSource := SourceLoop.Controls.step
def post := (StructuredSequenceCompilation.lower 4 postSource).get (by rfl)
def condition := localExpr (n := 2) 0 0
def p := (condition.lowered.code 0).get (by rfl)
def q := (WordMachine.selectCode p).get (by rfl)
def code := [Evm.Instr.loop q (body.code++post.code)]
def block := Backend.Block.loop p (.seq body.block post.block)

theorem scope_source (c : Scalar.Word) :
 evalStmt 5 .nil True.intro ScopedLoopExecution.Controls.scopeSource ScopedLoopExecution.Controls.scopeProfile
   (sourceLocals #v[1,c]) = some ⟨sourceLocals #v[0,c],.normal⟩ := by
 have ran := ScopedLoopExecution.Controls.body_source 1 c (by decide)
 change evalStmt 5 .nil True.intro ScopedLoopExecution.Controls.scopeSource ScopedLoopExecution.Controls.scopeProfile
   (sourceLocals #v[1,c]) = some ⟨sourceLocals #v[0,c],.normal⟩ at ran
 exact ran

theorem body_source (c : Scalar.Word) :
 evalStmt 7 .nil True.intro work body.compiled.profile (sourceLocals #v[1,c]) =
 some ⟨sourceLocals #v[0,c],.normal⟩ := by
 have chosen := CaseCompilation.source_hit (body := ScopedLoopExecution.Controls.scopeSource) (rest := .nil)
   1 1 ScopedLoopExecution.Controls.scopeProfile True.intro 5 #v[1,c] #v[0,c] rfl (scope_source c)
 exact MultiSwitchCompilation.source_chosen (c := ⟨false,true⟩)
   (arms := .cons 1 ScopedLoopExecution.Controls.scopeSource .nil) (fallback := .skip)
   condition ⟨ScopedLoopExecution.Controls.scopeProfile,True.intro⟩ True.intro 6 #v[1,c]
   (some ⟨sourceLocals #v[0,c],.normal⟩) ⟨sourceLocals #v[0,c],.normal⟩ (by omega) chosen rfl

theorem post_source (c : Scalar.Word) :
 evalStmt 7 .nil True.intro postSource post.compiled.profile (sourceLocals #v[0,c]) =
 some ⟨sourceLocals #v[0,c+3],.normal⟩ :=
 evalStmt_stable (by omega : 3 ≤ 7) .nil True.intro postSource post.compiled.profile
   (sourceLocals #v[0,c]) (MultiSwitchCompilation.Controls.head_run c)

theorem loop_source (c : Scalar.Word) :
 evalLoop (c := root) 8 .nil True.intro (.local 0) condition.profile postSource post.compiled.profile
   work body.compiled.profile (sourceLocals #v[1,c]) = some ⟨sourceLocals #v[0,c+3],.normal⟩ := by
 generalize firstEq : (1 : Scalar.Word) = first
 have nonzero : first.toNat ≠ 0 := by
   rw [←firstEq]
   decide
 change (if first.toNat = 0 then some (⟨sourceLocals #v[first,c],.normal⟩ : Outcome root 2) else _) = _
 rw [if_neg nonzero]
 change Option.bind (evalStmt 7 .nil True.intro work body.compiled.profile (sourceLocals #v[first,c])) _ = _
 rw [←firstEq]
 rw [body_source c]
 change Option.bind (evalStmt 7 .nil True.intro postSource post.compiled.profile (sourceLocals #v[0,c])) _ = _
 rw [post_source c]
 change evalLoop (c := root) 7 .nil True.intro (.local 0) condition.profile postSource post.compiled.profile
   work body.compiled.profile (sourceLocals #v[0,c+3]) = _
 rfl

theorem emitted_selected : emit (c := root) condition post body = some block ∧
 WordControl.blockCode block = some code := selection (c := root) condition post body p q (by rfl) (by rfl)

theorem finite_done (c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.loopIterN (Evm.run q) (Evm.run (body.code++post.code)) 8
   {m with stack := coreWord 1::coreWord c::caller} =
 .inr (.ok {m with stack := coreWord 0::coreWord (c+3)::caller} 0) := by
 obtain ⟨out,same,done⟩ := finite (c := root) condition post body p q (by rfl) (by rfl)
   8 #v[1,c] ⟨sourceLocals #v[0,c+3],.normal⟩ (loop_source c) m caller
 have equal : #v[0,c+3] = out := SourceLoopCompletion.sourceLocals_injective (congrArg Outcome.vars same)
 cases equal
 exact done

theorem target_done (c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run code {m with stack := coreWord 1::coreWord c::caller} =
 .ok {m with stack := coreWord 0::coreWord (c+3)::caller} 0 := by
 obtain ⟨out,same,done⟩ := model (c := root) condition post body p q (by rfl) (by rfl)
   8 #v[1,c] ⟨sourceLocals #v[0,c+3],.normal⟩ (loop_source c) m caller
 have equal : #v[0,c+3] = out := SourceLoopCompletion.sourceLocals_injective (congrArg Outcome.vars same)
 cases equal
 exact done

theorem zero_source (c : Scalar.Word) :
 evalLoop (c := root) 2 .nil True.intro (.local 0) condition.profile postSource post.compiled.profile
   work body.compiled.profile (sourceLocals #v[0,c]) = some ⟨sourceLocals #v[0,c],.normal⟩ := by rfl

theorem zero_target (c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run code {m with stack := coreWord 0::coreWord c::caller} =
 .ok {m with stack := coreWord 0::coreWord c::caller} 0 := by
 obtain ⟨out,same,done⟩ := model (c := root) condition post body p q (by rfl) (by rfl)
   2 #v[0,c] ⟨sourceLocals #v[0,c],.normal⟩ (zero_source c) m caller
 have equal : #v[0,c] = out := SourceLoopCompletion.sourceLocals_injective (congrArg Outcome.vars same)
 cases equal
 exact done

theorem old_body_refused : ScopedControlCompilation.lower 10 work = none := by rfl
example : evalLoop (c := root) 7 .nil True.intro (.local 0) condition.profile postSource post.compiled.profile
 work body.compiled.profile (sourceLocals #v[1,0]) = none := by rfl
example : evalStmt 1 .nil True.intro postSource post.compiled.profile (sourceLocals #v[0,0]) = none := by rfl

/-- info: 'Solidity.Yul.Compilation.StructuredLoopExecution.Controls.scope_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms scope_source
/-- info: 'Solidity.Yul.Compilation.StructuredLoopExecution.Controls.body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms body_source
/-- info: 'Solidity.Yul.Compilation.StructuredLoopExecution.Controls.post_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms post_source
/-- info: 'Solidity.Yul.Compilation.StructuredLoopExecution.Controls.loop_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loop_source
/-- info: 'Solidity.Yul.Compilation.StructuredLoopExecution.Controls.emitted_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms emitted_selected
/-- info: 'Solidity.Yul.Compilation.StructuredLoopExecution.Controls.finite_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms finite_done
/-- info: 'Solidity.Yul.Compilation.StructuredLoopExecution.Controls.target_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_done
/-- info: 'Solidity.Yul.Compilation.StructuredLoopExecution.Controls.zero_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_source
/-- info: 'Solidity.Yul.Compilation.StructuredLoopExecution.Controls.zero_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_target
/-- info: 'Solidity.Yul.Compilation.StructuredLoopExecution.Controls.old_body_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms old_body_refused
end Solidity.Yul.Compilation.StructuredLoopExecution.Controls
