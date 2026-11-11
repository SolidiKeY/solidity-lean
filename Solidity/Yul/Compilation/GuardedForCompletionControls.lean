import Solidity.Yul.Compilation.Artifact
import Solidity.Yul.Compilation.GuardedForCompletion
import Solidity.Yul.Compilation.GuardedForControls
/-! Source recovery from actual guard/loop model witnesses. Inactive-body
completion is unnecessary. Raw high-word data and explicit exhaustion controls. -/
namespace Solidity.Yul.Compilation.GuardedForCompletion.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open GuardedFor.Controls
open SourceLoop.Controls (dirty)

theorem recovered_skipped (locals : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ fuel, evalStmt fuel .nil True.intro (.if_ zeroExpr ForCompilation.Controls.constantGuard)
   ⟨zeroGuard.profile,endless.compiled.profile⟩ (sourceLocals locals) =
 some ⟨sourceLocals locals,.normal⟩ := by
 let represented : Solidity.Yul.Compilation.Artifact 0
     (.if_ zeroExpr ForCompilation.Controls.constantGuard) :=
   { profile := ⟨zeroGuard.profile,endless.compiled.profile⟩
     code := skippedCode
     source_to_model :=
       GuardedFor.source_to_model zeroGuard endless skippedCode (Option.some_get (by rfl)).symm
     model_to_source :=
       GuardedForCompletion.model_to_source zeroGuard endless skippedCode (Option.some_get (by rfl)).symm }
 exact (represented.completion_iff locals locals #v[] m caller).mpr (skipped locals m caller)

theorem recovered_taken (a b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ fuel, evalStmt fuel .nil True.intro (.if_ oneExpr SourceLoopInitializer.Controls.source)
   ⟨oneGuard.profile,ForCompilation.Controls.artifact.compiled.profile⟩ (sourceLocals #v[a,b]) =
 some ⟨sourceLocals #v[0,~~~(~~~b+3)+3],.normal⟩ :=
 (completion_iff oneGuard ForCompilation.Controls.artifact takenCode (Option.some_get (by rfl)).symm
   #v[a,b] #v[0,~~~(~~~b+3)+3] #v[] m caller).mpr (target_taken a b m caller)

/-- Unknown successful final/pending state is reflected; no chosen output or
source completion is a caller premise, and the inactive loop is not executed. -/
theorem reflected_skipped (locals : Vector Scalar.Word 2) (m final : Evm.Machine)
 (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run skippedCode {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (fuel : Nat) (out : Vector Scalar.Word 2),
 evalStmt fuel .nil True.intro (.if_ zeroExpr ForCompilation.Controls.constantGuard)
   ⟨zeroGuard.profile,endless.compiled.profile⟩ (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧
 final = {m with stack := out.toList.map coreWord++caller} :=
 model_to_source zeroGuard endless skippedCode (Option.some_get (by rfl)).symm
   locals #v[] m final caller skip ran

def dirtyExpr : Solidity.Yul.Expr [] [] 2 1 := .literal dirty.toFin
def dirtyGuard := (PureExpressions.compile 1 dirtyExpr).get (by rfl)
#guard dirtyGuard.value #v[0,0] = dirty
#guard dirtyGuard.value #v[0,0] ≠ 0
#guard (PureExpressions.compile 0 dirtyExpr).isNone
#guard (evalStmt 0 .nil True.intro (.if_ zeroExpr ForCompilation.Controls.constantGuard)
 ⟨zeroGuard.profile,endless.compiled.profile⟩ (sourceLocals #v[99,dirty])).isNone
/-- info: 'Solidity.Yul.Compilation.GuardedForCompletion.Controls.recovered_skipped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms recovered_skipped
/-- info: 'Solidity.Yul.Compilation.GuardedForCompletion.Controls.recovered_taken' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms recovered_taken
/-- info: 'Solidity.Yul.Compilation.GuardedForCompletion.Controls.reflected_skipped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reflected_skipped
end Solidity.Yul.Compilation.GuardedForCompletion.Controls
