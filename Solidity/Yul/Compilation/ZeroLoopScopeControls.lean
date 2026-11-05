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
/-- Extra observable outer update after the structured loop body. Existing
scope fixtures remain unchanged; this source has its own artifact and laws. -/
def mutatingBody : Solidity.Yul.Stmt [] [] root 2 :=
 .seq LoopControlCompilation.Controls.source SourceLoop.Controls.step
def mutatingArtifact : LoopControlCompilation.Artifact 9 mutatingBody 0 :=
 (LoopControlCompilation.lower 9 mutatingBody 0).get (by rfl)
def mutatingSource : Solidity.Yul.Stmt [] [] root 1 := .zero 1 mutatingBody
def mutatingCode := (lower 1 (n := 1) mutatingArtifact).get (by rfl)

theorem mutating_body_source (a b : Scalar.Word) :
 evalStmt 13 .nil True.intro mutatingBody mutatingArtifact.compiled.profile (sourceLocals #v[a,b]) =
 some ⟨sourceLocals #v[0,(~~~(~~~b+3)+3)+3],.normal⟩ := by
 have last := evalStmt_stable (show 4 ≤ 12 by omega) .nil True.intro SourceLoop.Controls.step
   SourceLoop.Controls.post.profile (sourceLocals #v[0,~~~(~~~b+3)+3])
   (SourceLoop.Controls.post.source #v[0,~~~(~~~b+3)+3])
 exact LoopControlCompilation.sequence_source LoopControlCompilation.Controls.source SourceLoop.Controls.step
   LoopControlCompilation.Controls.profile SourceLoop.Controls.post.profile 12
   (sourceLocals #v[a,b]) (sourceLocals #v[0,~~~(~~~b+3)+3])
   (sourceLocals #v[0,(~~~(~~~b+3)+3)+3]) (LoopControlCompilation.Controls.source_done a b) last

theorem mutating_source (b : Scalar.Word) :
 evalStmt 14 .nil True.intro mutatingSource mutatingArtifact.compiled.profile (sourceLocals #v[b]) =
 some ⟨sourceLocals #v[(~~~(~~~b+3)+3)+3],.normal⟩ :=
 source_scope mutatingArtifact 13 #v[b] #v[0,(~~~(~~~b+3)+3)+3] (mutating_body_source 0 b)

theorem mutating_target (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run mutatingCode {m with stack := coreWord b::caller} =
 .ok {m with stack := coreWord ((~~~(~~~b+3)+3)+3)::caller} 0 := by
 obtain ⟨out,same,ran⟩ := ZeroLoopScope.source_to_model (n := 1) (fresh := 1) mutatingArtifact mutatingCode
   (Option.some_get (by rfl)).symm 14 #v[b] _ (mutating_source b) m caller
 have equal : #v[(~~~(~~~b+3)+3)+3] = out :=
   SourceLoopCompletion.sourceLocals_injective (congrArg Outcome.vars same)
 subst out
 exact ran

#guard ((~~~(~~~dirty+3)+3)+3) ≠ dirty

/-- info: 'Solidity.Yul.Compilation.ZeroLoopScope.Controls.mutating_body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mutating_body_source
/-- info: 'Solidity.Yul.Compilation.ZeroLoopScope.Controls.mutating_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mutating_source
/-- info: 'Solidity.Yul.Compilation.ZeroLoopScope.Controls.mutating_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mutating_target
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
