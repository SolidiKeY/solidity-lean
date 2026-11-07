import Solidity.Yul.Compilation.MultiSwitchCompilation
import Solidity.Yul.Compilation.SwitchCompilationControls
/-! Actual first/later/default dispatch over distinct original labels. Case
and fallback runtime horizons differ, and only the chosen arm must complete.
This is kernel model evidence, not static admission or native validation. -/
namespace Solidity.Yul.Compilation.MultiSwitchCompilation.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root dirty)
open ScopedControlCompilation.Controls (update)

def head : Solidity.Yul.Stmt [] [] root 2 := .assign (fun _ : Fin 1 => .local 1)
 (.builtin (.pure .add) (Fin.cases (.local 1) (fun _ => .literal 3)))
def headReference : ProducerStatements.Compiled 3 head :=
 ProducerStatements.assign 1 (binary addBridge (localExpr 0 1) (literal 0 3))
def nested := ScopedControlCompilation.Controls.source
def nestedArtifact := ScopedControlCompilation.Controls.artifact
def tail : Cases [] [] root 2 := .cons dirty.toFin nested .nil
def arms : Cases [] [] root 2 := .cons 0 head tail
def tailProfile : CasesWordP tail := ⟨nestedArtifact.compiled.profile,True.intro⟩
def profile : CasesWordP arms := ⟨headReference.profile,tailProfile⟩
def source : Solidity.Yul.Stmt [] [] root 2 := .switch (.local 0) arms .skip
def artifact := (lower 12 source).get (by rfl)
def condition := localExpr (n := 2) 0 0

theorem head_run (c : Scalar.Word) :
 evalStmt 3 .nil True.intro head headReference.profile (sourceLocals #v[0,c]) =
 some ⟨sourceLocals #v[0,c+3],.normal⟩ := by
 have same : headReference.update #v[0,c] = #v[0,c+3] := by rfl
 have ran := headReference.source #v[0,c]
 rw [same] at ran
 exact ran

theorem first_source (c : Scalar.Word) :
 evalStmt 5 .nil True.intro source artifact.compiled.profile (sourceLocals #v[0,c]) =
 some ⟨sourceLocals #v[0,c+3],.normal⟩ := by
 have selected := CaseCompilation.source_hit (body := head) (rest := tail)
   0 0 headReference.profile tailProfile 3 #v[0,c] #v[0,c+3] rfl (head_run c)
 exact source_chosen (c := root) (arms := arms) (fallback := .skip) condition profile True.intro
   4 #v[0,c] (some ⟨sourceLocals #v[0,c+3],.normal⟩) ⟨sourceLocals #v[0,c+3],.normal⟩ (by omega) selected rfl

theorem first_target (c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord 0::coreWord c::caller} =
 .ok {m with stack := coreWord 0::coreWord (c+3)::caller} 0 :=
 artifact.normal_to_model 5 #v[0,c] #v[0,c+3] (first_source c) m caller

theorem later_source (c : Scalar.Word) :
 evalStmt 13 .nil True.intro source artifact.compiled.profile (sourceLocals #v[dirty,c]) =
 some ⟨sourceLocals #v[update dirty,c],.normal⟩ := by
 have nestedSource := ScopedControlCompilation.Controls.source_done dirty c
 have hit := CaseCompilation.source_hit (body := nested) (rest := .nil) dirty.toFin dirty.toFin
   nestedArtifact.compiled.profile True.intro 10 #v[dirty,c] #v[update dirty,c] rfl nestedSource
 have selected := CaseCompilation.source_miss (body := head) (rest := tail) 0 dirty.toFin
   headReference.profile tailProfile 11 #v[dirty,c] (some ⟨sourceLocals #v[update dirty,c],.normal⟩) (by decide) hit
 exact source_chosen (c := root) (arms := arms) (fallback := .skip) condition profile True.intro
   12 #v[dirty,c] (some ⟨sourceLocals #v[update dirty,c],.normal⟩) ⟨sourceLocals #v[update dirty,c],.normal⟩ (by omega) selected rfl

theorem later_target (c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord dirty::coreWord c::caller} =
 .ok {m with stack := coreWord (update dirty)::coreWord c::caller} 0 :=
 artifact.normal_to_model 13 #v[dirty,c] #v[update dirty,c] (later_source c) m caller

theorem default_source (b c : Scalar.Word) (nonzero : b.toFin ≠ 0) (different : b.toFin ≠ dirty.toFin) :
 evalStmt 4 .nil True.intro source artifact.compiled.profile (sourceLocals #v[b,c]) =
 some ⟨sourceLocals #v[b,c],.normal⟩ := by
 have ended : evalCases 1 .nil True.intro (.nil : Cases [] [] root 2) True.intro b.toFin (sourceLocals #v[b,c]) = some none := by rfl
 have missedTail := CaseCompilation.source_miss (body := nested) (rest := .nil) dirty.toFin b.toFin
   nestedArtifact.compiled.profile True.intro 1 #v[b,c] none different ended
 have selected := CaseCompilation.source_miss (body := head) (rest := tail) 0 b.toFin
   headReference.profile tailProfile 2 #v[b,c] none nonzero missedTail
 exact source_chosen (c := root) (arms := arms) (fallback := .skip) condition profile True.intro
   3 #v[b,c] none ⟨sourceLocals #v[b,c],.normal⟩ (by omega) selected rfl

theorem default_target (b c : Scalar.Word) (nonzero : b.toFin ≠ 0) (different : b.toFin ≠ dirty.toFin)
 (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord b::coreWord c::caller} =
 .ok {m with stack := coreWord b::coreWord c::caller} 0 :=
 artifact.normal_to_model 4 #v[b,c] #v[b,c] (default_source b c nonzero different) m caller

theorem alias_target (c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord SwitchCompilation.Controls.lowOnly::coreWord c::caller} =
 .ok {m with stack := coreWord SwitchCompilation.Controls.lowOnly::coreWord c::caller} 0 :=
 default_target SwitchCompilation.Controls.lowOnly c (by decide) (by decide) m caller

def emptySource : Solidity.Yul.Stmt [] [] root 2 := .switch (.local 0) .nil .skip
def emptyArtifact := (lower 1 emptySource).get (by rfl)

theorem empty_source (b c : Scalar.Word) :
 evalStmt 2 .nil True.intro emptySource emptyArtifact.compiled.profile (sourceLocals #v[b,c]) =
 some ⟨sourceLocals #v[b,c],.normal⟩ :=
 source_chosen (c := root) (arms := .nil) (fallback := .skip) condition True.intro True.intro
   1 #v[b,c] none ⟨sourceLocals #v[b,c],.normal⟩ (by omega) rfl rfl

theorem empty_target (b c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run emptyArtifact.code {m with stack := coreWord b::coreWord c::caller} =
 .ok {m with stack := coreWord b::coreWord c::caller} 0 :=
 emptyArtifact.normal_to_model 2 #v[b,c] #v[b,c] (empty_source b c) m caller

#guard ([0,dirty.toFin] : List Solidity.Yul.Word).Nodup
#guard (SwitchCompilation.lower 12 source).isNone
#guard (lower 0 source).isNone
#guard (CaseCompilation.compile 1 arms).isNone
#guard (evalStmt 0 .nil True.intro source artifact.compiled.profile (sourceLocals #v[dirty,dirty])).isNone
#guard (evalStmt 1 .nil True.intro nested nestedArtifact.compiled.profile (sourceLocals #v[SwitchCompilation.Controls.lowOnly,dirty])).isNone
#guard (dirty &&& 255) = (SwitchCompilation.Controls.lowOnly &&& 255)
-- Comparison-only capacity does not imply capacity of the whole dispatch/arms.
#guard Scalar.stackBound SwitchCompilation.Controls.comparisonProgram (1022 : Int) = true
#guard Scalar.stackBound SwitchCompilation.Controls.comparisonProgram (1023 : Int) = false
#guard (Scalar.run SwitchCompilation.Controls.comparisonProgram []).isNone

/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompilation.Controls.head_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms head_run
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompilation.Controls.first_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms first_source
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompilation.Controls.first_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms first_target
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompilation.Controls.later_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms later_source
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompilation.Controls.later_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms later_target
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompilation.Controls.default_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms default_source
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompilation.Controls.default_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms default_target
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompilation.Controls.alias_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms alias_target
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompilation.Controls.empty_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms empty_source
/-- info: 'Solidity.Yul.Compilation.MultiSwitchCompilation.Controls.empty_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms empty_target
end Solidity.Yul.Compilation.MultiSwitchCompilation.Controls
