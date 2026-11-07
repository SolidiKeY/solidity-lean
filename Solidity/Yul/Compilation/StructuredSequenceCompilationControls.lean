import Solidity.Yul.Compilation.StructuredSequenceCompilation
import Solidity.Yul.Compilation.ZeroSequenceCompilationControls
/-! Original zero/let/if/seq/switch composition accepted by one real visitor.
The nested fresh words become dirty and9, then both are retired in order;
interior target controls distinguish the true update from the false identity. -/
namespace Solidity.Yul.Compilation.StructuredSequenceCompilation.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root dirty)

def branch : Solidity.Yul.Stmt [] [] root 2 := .if_ (.literal dirty.toFin) ZeroSequenceCompilation.Controls.body
def inner : Solidity.Yul.Stmt [] [] root 1 := .let_ 1 (.literal 0) branch
def source : Solidity.Yul.Stmt [] [] root 0 := .zero 1 inner
def artifact := (lower 20 source).get (by rfl)
def innerArtifact := (lower 19 inner).get (by rfl)
def condition := (PureExpressions.compile (n := 2) 17 (.literal dirty.toFin)).get (by rfl)
def initializer := (PureExpressions.compile (n := 1) 18 (.literal 0)).get (by rfl)

theorem branch_source :
 evalStmt 18 .nil True.intro branch ⟨condition.profile,ZeroSequenceCompilation.Controls.bodyArtifact.compiled.profile⟩
   (sourceLocals #v[0,0]) = some ⟨sourceLocals #v[dirty,9],.normal⟩ :=
 LetControlCompletion.source_true condition ZeroSequenceCompilation.Controls.bodyArtifact.compiled.profile 8
   #v[0,0] #v[dirty,9] (by decide) ZeroSequenceCompilation.Controls.body_source

theorem inner_source :
 evalStmt 19 .nil True.intro inner innerArtifact.compiled.profile (sourceLocals #v[0]) =
 some ⟨sourceLocals #v[9],.normal⟩ :=
 ScopedControlCompletion.source_let (c := root) (n := 1) (fuel := 18) (rhs := .literal 0) (body := branch) initializer (⟨condition.profile,ZeroSequenceCompilation.Controls.bodyArtifact.compiled.profile⟩ : StmtWordP branch)
   18 #v[0] #v[dirty,9] branch_source

theorem source_done :
 evalStmt 20 .nil True.intro source artifact.compiled.profile (sourceLocals #v[]) =
 some ⟨sourceLocals #v[],.normal⟩ :=
 ScopedControlCompletion.source_zero innerArtifact.compiled.profile 19 #v[] #v[9] inner_source

theorem inner_target (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run innerArtifact.code {m with stack := coreWord 0::caller} = .ok {m with stack := coreWord 9::caller} 0 :=
 innerArtifact.normal_to_model 19 #v[0] #v[9] inner_source m caller

theorem target_done (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := caller} = .ok {m with stack := caller} 0 :=
 artifact.normal_to_model 20 #v[] #v[] source_done m caller

def falseBranch : Solidity.Yul.Stmt [] [] root 2 := .if_ (.literal 0) ZeroSequenceCompilation.Controls.body
def falseInner : Solidity.Yul.Stmt [] [] root 1 := .let_ 1 (.literal 0) falseBranch
def falseArtifact := (lower 19 falseInner).get (by rfl)
def falseCondition := (PureExpressions.compile (n := 2) 17 (.literal 0)).get (by rfl)

theorem false_branch_source :
 evalStmt 18 .nil True.intro falseBranch ⟨falseCondition.profile,ZeroSequenceCompilation.Controls.bodyArtifact.compiled.profile⟩
   (sourceLocals #v[0,0]) = some ⟨sourceLocals #v[0,0],.normal⟩ :=
 LetControlCompletion.source_false falseCondition ZeroSequenceCompilation.Controls.bodyArtifact.compiled.profile #v[0,0] rfl

theorem false_inner_source :
 evalStmt 19 .nil True.intro falseInner falseArtifact.compiled.profile (sourceLocals #v[0]) =
 some ⟨sourceLocals #v[0],.normal⟩ :=
 ScopedControlCompletion.source_let (c := root) (n := 1) (fuel := 18) (rhs := .literal 0) (body := falseBranch) initializer (⟨falseCondition.profile,ZeroSequenceCompilation.Controls.bodyArtifact.compiled.profile⟩ : StmtWordP falseBranch)
   18 #v[0] #v[0,0] false_branch_source

theorem false_target (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run falseArtifact.code {m with stack := coreWord 0::caller} = .ok {m with stack := coreWord 0::caller} 0 :=
 falseArtifact.normal_to_model 19 #v[0] #v[0] false_inner_source m caller

theorem lowered : lower 20 source = some artifact := by rfl
theorem budget_refusal : lower 2 source = none := by rfl
theorem old_scoped_refusal : ScopedControlCompilation.lower 20 source = none := by rfl
theorem old_sequence_refusal : SequenceCompilation.lower 20 source = none := by rfl
example : evalStmt 0 .nil True.intro source artifact.compiled.profile (sourceLocals #v[]) = none := by rfl
example : coreWord (9 : Scalar.Word) ≠ coreWord 0 := by decide

/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompilation.Controls.branch_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms branch_source
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompilation.Controls.inner_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms inner_source
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompilation.Controls.source_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_done
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompilation.Controls.inner_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms inner_target
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompilation.Controls.target_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_done
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompilation.Controls.false_branch_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms false_branch_source
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompilation.Controls.false_inner_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms false_inner_source
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompilation.Controls.false_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms false_target
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompilation.Controls.lowered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lowered
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompilation.Controls.budget_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms budget_refusal
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompilation.Controls.old_scoped_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms old_scoped_refusal
/-- info: 'Solidity.Yul.Compilation.StructuredSequenceCompilation.Controls.old_sequence_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms old_sequence_refusal
end Solidity.Yul.Compilation.StructuredSequenceCompilation.Controls
