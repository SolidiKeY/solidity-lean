import Solidity.Yul.Compilation.ConditionalCompilation
import Solidity.Yul.Compilation.SequenceCompilationControls
/-! Actual conditionals around three recursively compiled switches. The dirty
nonzero guard executes ordered updates; zero retires the guard and preserves
all locals without requiring the untaken body to complete. Kernel model only. -/
namespace Solidity.Yul.Compilation.ConditionalCompilation.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root dirty)
open SequenceCompilation.Controls (source)

def taken := (lower 2 14 (.literal dirty.toFin) source).get (by rfl)
def skipped := (lower 2 14 (.literal 0) source).get (by rfl)

theorem taken_source :
 evalStmt 8 .nil True.intro (.if_ (.literal dirty.toFin) source) taken.profile (sourceLocals #v[0,0]) =
 some ⟨sourceLocals #v[0,9],.normal⟩ :=
 LetControlCompletion.source_true taken.condition taken.arm.compiled.profile 7 #v[0,0] #v[0,9]
   (by decide) SequenceCompilation.Controls.source_done

theorem taken_target (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run taken.code {m with stack := coreWord 0::coreWord 0::caller} =
 .ok {m with stack := coreWord 0::coreWord 9::caller} 0 :=
 taken.normal_to_model 8 #v[0,0] #v[0,9] taken_source m caller

theorem skipped_source (locals : Vector Scalar.Word 2) :
 evalStmt 3 .nil True.intro (.if_ (.literal 0) source) skipped.profile (sourceLocals locals) =
 some ⟨sourceLocals locals,.normal⟩ :=
 LetControlCompletion.source_false skipped.condition skipped.arm.compiled.profile locals rfl

theorem skipped_target (locals : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run skipped.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := locals.toList.map coreWord++caller} 0 :=
 skipped.normal_to_model 3 locals locals (skipped_source locals) m caller

/-- The false conditional succeeds at source3 although the untaken body at
its available source2 horizon cannot complete. No favourable body run assumed. -/
theorem untaken_incomplete :
 evalStmt 2 .nil True.intro source skipped.arm.compiled.profile (sourceLocals #v[0,0]) = none := by rfl

theorem source_recovered (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro (.if_ (.literal dirty.toFin) source) taken.profile (sourceLocals #v[0,0]) =
 some ⟨sourceLocals #v[0,9],.normal⟩ :=
 (taken.completion_iff #v[0,0] #v[0,9] m caller).mpr (taken_target m caller)

theorem final_height (locals : Vector Scalar.Word 2) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run taken.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 skip = 0 ∧ final.stack.length = 2+caller.length := by
 obtain ⟨_,out,_,done,frame⟩ := taken.model_to_source locals m final caller skip ran
 refine ⟨done,?_⟩
 rw [frame]
 simp only [List.length_append,List.length_map,Vector.length_toList]

theorem lowered : lower 2 14 (.literal dirty.toFin) source = some taken := by rfl
theorem body_fuel_refusal : lower 2 1 (.literal dirty.toFin) source = none := by rfl
example : evalStmt 3 .nil True.intro (.if_ (.literal dirty.toFin) source) taken.profile (sourceLocals #v[0,0]) = none := by rfl
example : dirty.toNat = 2^200+257 := by decide

/-- Target-only missing-frame controls: neither empty stack represents the
original two-local source input. The selected body faults; zero skips it. -/
theorem taken_underflow (m : Evm.Machine) :
 Evm.run taken.code {m with stack := []} = .fault := by rfl

theorem skipped_empty (m : Evm.Machine) :
 Evm.run skipped.code {m with stack := []} = .ok {m with stack := []} 0 := by rfl

/-- info: 'Solidity.Yul.Compilation.ConditionalCompilation.Controls.taken_underflow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms taken_underflow
/-- info: 'Solidity.Yul.Compilation.ConditionalCompilation.Controls.skipped_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms skipped_empty

/-- info: 'Solidity.Yul.Compilation.ConditionalCompilation.Controls.taken_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms taken_source
/-- info: 'Solidity.Yul.Compilation.ConditionalCompilation.Controls.taken_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms taken_target
/-- info: 'Solidity.Yul.Compilation.ConditionalCompilation.Controls.skipped_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms skipped_source
/-- info: 'Solidity.Yul.Compilation.ConditionalCompilation.Controls.skipped_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms skipped_target
/-- info: 'Solidity.Yul.Compilation.ConditionalCompilation.Controls.untaken_incomplete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms untaken_incomplete
/-- info: 'Solidity.Yul.Compilation.ConditionalCompilation.Controls.source_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_recovered
/-- info: 'Solidity.Yul.Compilation.ConditionalCompilation.Controls.final_height' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms final_height
/-- info: 'Solidity.Yul.Compilation.ConditionalCompilation.Controls.lowered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lowered
/-- info: 'Solidity.Yul.Compilation.ConditionalCompilation.Controls.body_fuel_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms body_fuel_refusal
end Solidity.Yul.Compilation.ConditionalCompilation.Controls
