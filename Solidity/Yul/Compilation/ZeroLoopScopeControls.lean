import Solidity.Yul.Compilation.ZeroLoopScope
import Solidity.Yul.Compilation.LoopControlCompilationControls
/-! A fresh loop counter around the real structured body updates an outer raw
word, then retires the counter. Capacity remains distinct from execution. -/
namespace Solidity.Yul.Compilation.ZeroLoopScope.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root dirty)

def bodyArtifact := LoopControlCompilation.Controls.artifact
def source : Solidity.Yul.Stmt [] [] root 1 := .zero 1 LoopControlCompilation.Controls.source
def code := (lower 1 (n := 1) bodyArtifact).get (by rfl)

theorem source_done (b : Scalar.Word) :
 evalStmt 13 .nil True.intro source bodyArtifact.compiled.profile (sourceLocals #v[b]) =
 some ⟨sourceLocals #v[~~~(~~~b+3)+3],.normal⟩ :=
 source_scope bodyArtifact 12 #v[b] #v[0,~~~(~~~b+3)+3] (LoopControlCompilation.Controls.source_done 0 b)

/-- Whole PUSH/body/POP code mutates the real outer word and preserves every
arbitrary caller word and non-stack field. Fresh counter contents do not leak. -/
theorem target_done (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run code {m with stack := coreWord b::caller} =
 .ok {m with stack := coreWord (~~~(~~~b+3)+3)::caller} 0 := by
 obtain ⟨out,same,ran⟩ := source_to_model (n := 1) (fresh := 1) bodyArtifact code (Option.some_get (by rfl)).symm
   13 #v[b] _ (source_done b) m caller
 have equal : #v[~~~(~~~b+3)+3] = out :=
   SourceLoopCompletion.sourceLocals_injective (congrArg Outcome.vars same)
 subst out
 exact ran

/-- Fresh arity zero is supported by the SAME original binder laws, without
an invented scope entry convention or different source evaluator. -/
theorem no_fresh_source (a b : Scalar.Word) :
 evalStmt 13 .nil True.intro (.zero (n := 2) 0 LoopControlCompilation.Controls.source)
   bodyArtifact.compiled.profile (sourceLocals #v[a,b]) =
 some ⟨sourceLocals #v[0,~~~(~~~b+3)+3],.normal⟩ :=
 source_scope bodyArtifact 12 #v[a,b] #v[0,~~~(~~~b+3)+3] (LoopControlCompilation.Controls.source_done a b)

/-- An intrinsically sized full stack still admits scalar PUSH success;
the actual height check below refuses that overflow separately. -/
theorem scalar_large_prefix (tail : Vector Scalar.Word 1024) :
 Scalar.run (entry 1) tail.toList = some (0::tail.toList) := pushPrefix_run [0] tail.toList

#guard Scalar.stackBound (entry 1) (1024 : Int) = false
#guard Scalar.run (popPrefix 1) [] = none
#guard (lower 0 (n := 2) bodyArtifact).isSome
#guard (LoopControlCompilation.lower 8 LoopControlCompilation.Controls.source 15).isNone
#guard (evalStmt 0 .nil True.intro source bodyArtifact.compiled.profile (sourceLocals #v[dirty])).isNone
/-- info: 'Solidity.Yul.Compilation.ZeroLoopScope.Controls.source_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_done
/-- info: 'Solidity.Yul.Compilation.ZeroLoopScope.Controls.target_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target_done
/-- info: 'Solidity.Yul.Compilation.ZeroLoopScope.Controls.no_fresh_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms no_fresh_source
/-- info: 'Solidity.Yul.Compilation.ZeroLoopScope.Controls.scalar_large_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms scalar_large_prefix
end Solidity.Yul.Compilation.ZeroLoopScope.Controls
