import Solidity.Yul.Compilation.InitializedSequenceCompilation
import Solidity.Yul.Compilation.ZeroSequenceCompilationControls
/-! Actual pre-scope local initialization and full dirty-word transport into
outer locals through a real let/switch sequence. Fresh contents are retired
using original POP order. Scalar initializer capacity is separately checked. -/
namespace Solidity.Yul.Compilation.InitializedSequenceCompilation.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root dirty)

def borrowed := (lower (n := 1) 2 15 (.local 0) ZeroSequenceCompilation.Controls.body).get (by rfl)

theorem borrowed_source :
 evalStmt 9 .nil True.intro (.let_ 1 (.local 0) ZeroSequenceCompilation.Controls.body) borrowed.profile (sourceLocals #v[0]) =
 some ⟨sourceLocals #v[9],.normal⟩ :=
 ScopedControlCompletion.source_let borrowed.initializer borrowed.compiledBody.compiled.profile 8 #v[0] #v[dirty,9]
   ZeroSequenceCompilation.Controls.body_source

theorem borrowed_target (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run borrowed.code {m with stack := coreWord 0::caller} = .ok {m with stack := coreWord 9::caller} 0 :=
 borrowed.normal_to_model 9 #v[0] #v[9] borrowed_source m caller

def copyFresh : Solidity.Yul.Stmt [] [] root 2 := .assign (fun _ : Fin 1 => .local 1) (.local 0)
def copyReference : ProducerStatements.Compiled 2 copyFresh := ProducerStatements.assign 1 (localExpr 0 0)
def emptySwitch : Solidity.Yul.Stmt [] [] root 2 := .switch (.local 0) .nil .skip
def emptyArtifact := (MultiSwitchCompilation.lower 3 emptySwitch).get (by rfl)
def copiedBody : Solidity.Yul.Stmt [] [] root 2 := .seq copyFresh emptySwitch
def copiedBodyArtifact := (SequenceCompilation.lower 6 copiedBody).get (by rfl)
def copied := (lower (n := 1) 2 6 (.literal dirty.toFin) copiedBody).get (by rfl)

theorem copy_source (old : Scalar.Word) :
 evalStmt 2 .nil True.intro copyFresh copyReference.profile (sourceLocals #v[dirty,old]) =
 some ⟨sourceLocals #v[dirty,dirty],.normal⟩ := copyReference.source #v[dirty,old]

theorem empty_source :
 evalStmt 2 .nil True.intro emptySwitch emptyArtifact.compiled.profile (sourceLocals #v[dirty,dirty]) =
 some ⟨sourceLocals #v[dirty,dirty],.normal⟩ := by rfl

theorem copied_body_source (old : Scalar.Word) :
 evalStmt 3 .nil True.intro copiedBody copiedBodyArtifact.compiled.profile (sourceLocals #v[dirty,old]) =
 some ⟨sourceLocals #v[dirty,dirty],.normal⟩ :=
 LoopControlCompilation.sequence_source _ _ _ _ 2 (sourceLocals #v[dirty,old]) (sourceLocals #v[dirty,dirty])
   (sourceLocals #v[dirty,dirty]) (copy_source old) empty_source

theorem copied_source (old : Scalar.Word) :
 evalStmt 4 .nil True.intro (.let_ 1 (.literal dirty.toFin) copiedBody) copied.profile (sourceLocals #v[old]) =
 some ⟨sourceLocals #v[dirty],.normal⟩ :=
 ScopedControlCompletion.source_let copied.initializer copied.compiledBody.compiled.profile 3 #v[old] #v[dirty,dirty]
   (copied_body_source old)

theorem copied_target (old : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run copied.code {m with stack := coreWord old::caller} = .ok {m with stack := coreWord dirty::caller} 0 :=
 copied.normal_to_model 4 #v[old] #v[dirty] (copied_source old) m caller

theorem source_recovered (old : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro (.let_ 1 (.literal dirty.toFin) copiedBody) copied.profile (sourceLocals #v[old]) =
 some ⟨sourceLocals #v[dirty],.normal⟩ :=
 (copied.completion_iff #v[old] #v[dirty] m caller).mpr (copied_target old m caller)

theorem final_height (locals : Vector Scalar.Word 1) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run copied.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 skip = 0 ∧ final.stack.length = 1+caller.length := by
 obtain ⟨_,out,_,done,frame⟩ := copied.model_to_source locals m final caller skip ran
 refine ⟨done,?_⟩
 rw [frame]
 simp only [List.length_append,List.length_map,Vector.length_toList]

theorem lowered : lower (n := 1) 2 15 (.local 0) ZeroSequenceCompilation.Controls.body = some borrowed := by rfl
theorem initializer_fuel_refusal : lower (n := 1) 0 15 (.local 0) ZeroSequenceCompilation.Controls.body = none := by rfl
theorem body_fuel_refusal : lower (n := 1) 2 1 (.local 0) ZeroSequenceCompilation.Controls.body = none := by rfl

/-- Exact actual initializer code and its capacity/operand controls. These are
entry-only checks, not whole-body/native/charged capacity certificates. -/
example : borrowed.program = [readSlot 0] := by rfl
example : Scalar.stackBound borrowed.program 1023 = true := by decide
example : Scalar.stackBound borrowed.program 1024 = false := by decide
example : Scalar.run borrowed.program [] = none := by decide
example : dirty.toNat = 2^200+257 := by decide

/-- info: 'Solidity.Yul.Compilation.InitializedSequenceCompilation.Controls.borrowed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms borrowed_source
/-- info: 'Solidity.Yul.Compilation.InitializedSequenceCompilation.Controls.borrowed_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms borrowed_target
/-- info: 'Solidity.Yul.Compilation.InitializedSequenceCompilation.Controls.copy_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms copy_source
/-- info: 'Solidity.Yul.Compilation.InitializedSequenceCompilation.Controls.empty_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms empty_source
/-- info: 'Solidity.Yul.Compilation.InitializedSequenceCompilation.Controls.copied_body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms copied_body_source
/-- info: 'Solidity.Yul.Compilation.InitializedSequenceCompilation.Controls.copied_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms copied_source
/-- info: 'Solidity.Yul.Compilation.InitializedSequenceCompilation.Controls.copied_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms copied_target
/-- info: 'Solidity.Yul.Compilation.InitializedSequenceCompilation.Controls.source_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_recovered
/-- info: 'Solidity.Yul.Compilation.InitializedSequenceCompilation.Controls.final_height' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms final_height
/-- info: 'Solidity.Yul.Compilation.InitializedSequenceCompilation.Controls.lowered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lowered
/-- info: 'Solidity.Yul.Compilation.InitializedSequenceCompilation.Controls.initializer_fuel_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms initializer_fuel_refusal
/-- info: 'Solidity.Yul.Compilation.InitializedSequenceCompilation.Controls.body_fuel_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms body_fuel_refusal
end Solidity.Yul.Compilation.InitializedSequenceCompilation.Controls
