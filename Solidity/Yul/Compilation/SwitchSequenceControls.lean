import Solidity.Yul.Compilation.SwitchSequence
import Solidity.Yul.Compilation.MultiSwitchCompilationControls
/-! Two genuine original switches: the first changes local 1 from 0 to 3;
the second dispatches on that changed local and changes it to 6. Selecting on
the stale initial frame would take the default and leave 3. Kernel model only. -/
namespace Solidity.Yul.Compilation.SwitchSequence.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root)

def second : Solidity.Yul.Stmt [] [] root 2 :=
 .switch (.local 1) (.cons 3 MultiSwitchCompilation.Controls.head .nil) .skip
def secondArtifact := (MultiSwitchCompilation.lower 12 second).get (by rfl)
def artifact := (lower 12 12 MultiSwitchCompilation.Controls.source second).get (by rfl)

theorem second_source :
 evalStmt 5 .nil True.intro second secondArtifact.compiled.profile (sourceLocals #v[0,3]) =
 some ⟨sourceLocals #v[0,6],.normal⟩ := by
 have selected := CaseCompilation.source_hit (body := MultiSwitchCompilation.Controls.head) (rest := .nil)
   3 3 MultiSwitchCompilation.Controls.headReference.profile True.intro 3 #v[0,3] #v[0,6] rfl (MultiSwitchCompilation.Controls.head_run 3)
 exact MultiSwitchCompilation.source_chosen (c := root) (arms := .cons 3 MultiSwitchCompilation.Controls.head .nil) (fallback := .skip)
   (localExpr (n := 2) 0 1) ⟨MultiSwitchCompilation.Controls.headReference.profile,True.intro⟩ True.intro 4 #v[0,3]
   (some ⟨sourceLocals #v[0,6],.normal⟩) ⟨sourceLocals #v[0,6],.normal⟩ (by omega) selected rfl

theorem source_done :
 evalStmt 6 .nil True.intro (.seq MultiSwitchCompilation.Controls.source second) artifact.profile (sourceLocals #v[0,0]) =
 some ⟨sourceLocals #v[0,6],.normal⟩ :=
 artifact.join_source 5 5 #v[0,0] #v[0,3] #v[0,6] (MultiSwitchCompilation.Controls.first_source 0) second_source

theorem target_done (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord 0::coreWord 0::caller} =
 .ok {m with stack := coreWord 0::coreWord 6::caller} 0 :=
 artifact.normal_to_model 6 #v[0,0] #v[0,6] source_done m caller

theorem lowered : lower 12 12 MultiSwitchCompilation.Controls.source second = some artifact := by rfl
theorem first_fuel_refusal : lower 0 12 MultiSwitchCompilation.Controls.source second = none := by rfl
theorem second_fuel_refusal : lower 12 0 MultiSwitchCompilation.Controls.source second = none := by rfl
example : evalStmt 0 .nil True.intro (.seq MultiSwitchCompilation.Controls.source second) artifact.profile (sourceLocals #v[0,0]) = none := by rfl
example : coreWord (6 : Scalar.Word) ≠ coreWord 3 := by decide

/-- info: 'Solidity.Yul.Compilation.SwitchSequence.Controls.second_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms second_source
/-- info: 'Solidity.Yul.Compilation.SwitchSequence.Controls.source_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_done
/-- info: 'Solidity.Yul.Compilation.SwitchSequence.Controls.target_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_done
/-- info: 'Solidity.Yul.Compilation.SwitchSequence.Controls.lowered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowered
/-- info: 'Solidity.Yul.Compilation.SwitchSequence.Controls.first_fuel_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms first_fuel_refusal
/-- info: 'Solidity.Yul.Compilation.SwitchSequence.Controls.second_fuel_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms second_fuel_refusal
end Solidity.Yul.Compilation.SwitchSequence.Controls
