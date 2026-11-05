import Solidity.Yul.Compilation.ZeroSequenceCompilation
import Solidity.Yul.Compilation.SequenceCompilationControls
/-! Actual switch sequences inside initialized scopes. The body updates an
outer local, writes a full dirty word into a fresh local, then scope exit drops
exactly the fresh prefix. Entry-capacity controls are separate scalar traces. -/
namespace Solidity.Yul.Compilation.ZeroSequenceCompilation.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root dirty)

def setFresh : Solidity.Yul.Stmt [] [] root 2 := .assign (fun _ : Fin 1 => .local 0) (.literal dirty.toFin)
def setReference : ProducerStatements.Compiled 2 setFresh := ProducerStatements.assign 0 (literal 0 dirty.toFin)
def body : Solidity.Yul.Stmt [] [] root 2 := .seq SequenceCompilation.Controls.source setFresh
def bodyArtifact := (SequenceCompilation.lower 15 body).get (by rfl)
def one := (lower (n := 1) 1 15 body).get (by rfl)
def two := (lower (n := 0) 2 15 body).get (by rfl)

theorem dirty_write :
 evalStmt 2 .nil True.intro setFresh setReference.profile (sourceLocals #v[0,9]) =
 some ⟨sourceLocals #v[dirty,9],.normal⟩ := by
 have written := setReference.source #v[0,9]
 exact written

theorem body_source :
 evalStmt 8 .nil True.intro body bodyArtifact.compiled.profile (sourceLocals #v[0,0]) =
 some ⟨sourceLocals #v[dirty,9],.normal⟩ := by
 have written := evalStmt_stable (by omega : 2 ≤ 7) .nil True.intro setFresh setReference.profile
   (sourceLocals #v[0,9]) dirty_write
 exact LoopControlCompilation.sequence_source _ _ _ _ 7 (sourceLocals #v[0,0]) (sourceLocals #v[0,9])
   (sourceLocals #v[dirty,9]) SequenceCompilation.Controls.source_done written

theorem one_source :
 evalStmt 9 .nil True.intro (.zero 1 body) one.profile (sourceLocals #v[0]) =
 some ⟨sourceLocals #v[9],.normal⟩ :=
 ScopedControlCompletion.source_zero bodyArtifact.compiled.profile 8 #v[0] #v[dirty,9] body_source

theorem one_target (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run one.code {m with stack := coreWord 0::caller} = .ok {m with stack := coreWord 9::caller} 0 :=
 one.normal_to_model 9 #v[0] #v[9] one_source m caller

/-- Both updated body locals are fresh here; neither survives the real two-word
prefix exit, and the entire arbitrary caller is restored unchanged. -/
theorem two_source :
 evalStmt 9 .nil True.intro (.zero 2 body) two.profile (sourceLocals #v[]) =
 some ⟨sourceLocals #v[],.normal⟩ :=
 ScopedControlCompletion.source_zero bodyArtifact.compiled.profile 8 #v[] #v[dirty,9] body_source

theorem two_target (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run two.code {m with stack := caller} = .ok {m with stack := caller} 0 :=
 two.normal_to_model 9 #v[] #v[] two_source m caller

theorem source_recovered (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro (.zero 1 body) one.profile (sourceLocals #v[0]) =
 some ⟨sourceLocals #v[9],.normal⟩ :=
 (one.completion_iff #v[0] #v[9] m caller).mpr (one_target m caller)

theorem final_height (locals : Vector Scalar.Word 1) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run one.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 skip = 0 ∧ final.stack.length = 1+caller.length := by
 obtain ⟨_,out,_,done,frame⟩ := one.model_to_source locals m final caller skip ran
 refine ⟨done,?_⟩
 rw [frame]
 simp only [List.length_append,List.length_map,Vector.length_toList]

theorem lowered : lower (n := 1) 1 15 body = some one := by rfl
theorem body_fuel_refusal : lower (n := 1) 1 1 body = none := by rfl
theorem old_scope_refusal : ScopedControlCompilation.lower 15 (.zero (n := 1) 1 body) = none := by rfl

/-- Actual entry traces permit exactly two spare words here. This is only the
entry trace; it supplies no bound for the body/native/charged whole program. -/
example : Scalar.stackBound (ZeroLoopScope.entry 2) 1022 = true := by decide
example : Scalar.stackBound (ZeroLoopScope.entry 2) 1023 = false := by decide
example : dirty.toNat = 2^200+257 := by decide

/-- info: 'Solidity.Yul.Compilation.ZeroSequenceCompilation.Controls.dirty_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dirty_write
/-- info: 'Solidity.Yul.Compilation.ZeroSequenceCompilation.Controls.body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms body_source
/-- info: 'Solidity.Yul.Compilation.ZeroSequenceCompilation.Controls.one_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms one_source
/-- info: 'Solidity.Yul.Compilation.ZeroSequenceCompilation.Controls.one_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms one_target
/-- info: 'Solidity.Yul.Compilation.ZeroSequenceCompilation.Controls.two_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms two_source
/-- info: 'Solidity.Yul.Compilation.ZeroSequenceCompilation.Controls.two_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms two_target
/-- info: 'Solidity.Yul.Compilation.ZeroSequenceCompilation.Controls.source_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_recovered
/-- info: 'Solidity.Yul.Compilation.ZeroSequenceCompilation.Controls.final_height' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms final_height
/-- info: 'Solidity.Yul.Compilation.ZeroSequenceCompilation.Controls.lowered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lowered
/-- info: 'Solidity.Yul.Compilation.ZeroSequenceCompilation.Controls.body_fuel_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms body_fuel_refusal
/-- info: 'Solidity.Yul.Compilation.ZeroSequenceCompilation.Controls.old_scope_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms old_scope_refusal
end Solidity.Yul.Compilation.ZeroSequenceCompilation.Controls
