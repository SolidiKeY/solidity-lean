import Solidity.Yul.Compilation.ScopedForCompletion
import Solidity.Yul.Compilation.ScopedForCompilationControls
/-! Exact success equivalence for genuine initialized scoped FOR outputs.
Recovery uses actual prior kernel target witnesses, not an independent native
oracle; resource/refusal controls remain separate from normal equivalence. -/
namespace Solidity.Yul.Compilation.ScopedForCompletion.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open ScopedForCompilation.Controls (source artifact finish)
open SourceLoop.Controls (dirty)

theorem success_iff (locals out : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := completion_iff artifact locals out m caller

theorem reflected (locals : Vector Scalar.Word 2) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word 2),
 evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} :=
 model_to_source artifact locals m final caller skip ran

theorem recovered (b c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals #v[b,c]) =
 some ⟨sourceLocals #v[0,finish b c],.normal⟩ :=
 (success_iff #v[b,c] #v[0,finish b c] m caller).mpr (ScopedForCompilation.Controls.target_done b c m caller)

theorem zero_recovered (c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals #v[0,c]) =
 some ⟨sourceLocals #v[0,c+3],.normal⟩ :=
 (success_iff #v[0,c] #v[0,c+3] m caller).mpr (ScopedForCompilation.Controls.zero_target c m caller)

theorem nonzero_recovered (b c : Scalar.Word) (nonzero : b ≠ 0) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals #v[b,c]) =
 some ⟨sourceLocals #v[0,(c+3)+7],.normal⟩ :=
 (success_iff #v[b,c] #v[0,(c+3)+7] m caller).mpr (ScopedForCompilation.Controls.nonzero_target b c nonzero m caller)

theorem phase_reflected (locals : Vector Scalar.Word 2) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run ScopedLoopExecution.Controls.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word 2),
 evalLoop (c := SourceLoop.Controls.root) horizon .nil True.intro (.local 0) ScopedLoopExecution.Controls.condition.profile
   ScopedLoopExecution.Controls.postSource ScopedLoopExecution.Controls.post.compiled.profile
   ScopedLoopExecution.Controls.work ScopedLoopExecution.Controls.body.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} :=
 ScopedLoopCompletion.model_to_source (c := SourceLoop.Controls.root)
   ScopedLoopExecution.Controls.condition ScopedLoopExecution.Controls.post ScopedLoopExecution.Controls.body
   ScopedLoopExecution.Controls.p ScopedLoopExecution.Controls.q (by rfl) (by rfl) locals m final caller skip ran

#guard finish dirty dirty = BitVec.ofNat 256 (2^200+267)
#guard finish 0 dirty = BitVec.ofNat 256 (2^200+260)
#guard finish 0 dirty ≠ finish dirty dirty
#guard (ScopedForCompilation.lower 0 source).isNone
#guard (evalStmt 0 .nil True.intro source artifact.compiled.profile (sourceLocals #v[dirty,dirty])).isNone
-- Neither success iff nor recovery establishes charged/native capacity.
#guard Scalar.stackBound [Backend.Instr.op (.DUP 0)] (1024 : Int) = false
#guard Scalar.run [Backend.Instr.op (.DUP 0)] [] = none

/-- info: 'Solidity.Yul.Compilation.ScopedForCompletion.Controls.success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success_iff
/-- info: 'Solidity.Yul.Compilation.ScopedForCompletion.Controls.reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reflected
/-- info: 'Solidity.Yul.Compilation.ScopedForCompletion.Controls.recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms recovered
/-- info: 'Solidity.Yul.Compilation.ScopedForCompletion.Controls.zero_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_recovered
/-- info: 'Solidity.Yul.Compilation.ScopedForCompletion.Controls.nonzero_recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nonzero_recovered
/-- info: 'Solidity.Yul.Compilation.ScopedForCompletion.Controls.phase_reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms phase_reflected
end Solidity.Yul.Compilation.ScopedForCompletion.Controls
