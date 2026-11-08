import Solidity.Yul.Compilation.LoopControlCompletion
import Solidity.Yul.Compilation.LoopControlCompilationControls
/-! Actual combined visitor artifact: source recovery, unknown frame/pending
reflection and refusal of nonzero pending control. No external oracle claim. -/
namespace Solidity.Yul.Compilation.LoopControlCompletion.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open LoopControlCompilation.Controls
open SourceLoop.Controls (dirty)

theorem success_iff (locals out : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 :=
 artifact_iff artifact locals out #v[] m caller

/-- Recovered original source completion from the actual combined target
witness. That witness is kernel composition, not an independent EVM oracle. -/
theorem recovered (a b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals #v[a,b]) =
 some ⟨sourceLocals #v[0,~~~(~~~b+3)+3],.normal⟩ :=
 (success_iff #v[a,b] #v[0,~~~(~~~b+3)+3] m caller).mpr (target_done a b m caller)

theorem reflected (locals : Vector Scalar.Word 2) (m final : Evm.Machine)
 (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word 2),
 evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧
 final = {m with stack := out.toList.map coreWord++caller} :=
 artifact_reflected artifact locals #v[] m final caller skip ran

theorem pending_refused (locals : Vector Scalar.Word 2) (m final : Evm.Machine)
 (caller : List Evm.Word) (skip : Nat) :
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} ≠ .ok final (skip+1) := by
 exact CompletionControls.pending_refused (code := artifact.code)
   (initial := {m with stack := locals.toList.map coreWord++caller})
   (fun actual pending ran => by
     obtain ⟨_,_,_,done,_⟩ := reflected locals m actual caller pending ran
     exact done) final skip

#guard (evalStmt 0 .nil True.intro source artifact.compiled.profile (sourceLocals #v[99,dirty])).isNone
#guard (LoopControlCompilation.lower 0 source 0).isNone
#guard (LoopControlCompilation.lower 8 source 15).isNone
#guard (LoopControlCompilation.lower 8 nestedBody 0).isNone
/-- info: 'Solidity.Yul.Compilation.LoopControlCompletion.Controls.success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success_iff
/-- info: 'Solidity.Yul.Compilation.LoopControlCompletion.Controls.recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms recovered
/-- info: 'Solidity.Yul.Compilation.LoopControlCompletion.Controls.reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reflected
/-- info: 'Solidity.Yul.Compilation.LoopControlCompletion.Controls.pending_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pending_refused
end Solidity.Yul.Compilation.LoopControlCompletion.Controls
