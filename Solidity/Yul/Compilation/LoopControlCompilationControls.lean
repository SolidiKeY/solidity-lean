import Solidity.Yul.Compilation.LoopControlCompilation
import Solidity.Yul.Compilation.GuardedForControls
/-! A real selected combination: skip, then a false branch with an untaken
constant guard loop, then a true branch with the initialized two-turn loop. -/
namespace Solidity.Yul.Compilation.LoopControlCompilation.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root dirty)

def left : Solidity.Yul.Stmt [] [] root 2 :=
 .if_ GuardedFor.Controls.zeroExpr ForCompilation.Controls.constantGuard
def right : Solidity.Yul.Stmt [] [] root 2 :=
 .if_ GuardedFor.Controls.oneExpr SourceLoopInitializer.Controls.source
def leftProfile : StmtWordP left := ⟨GuardedFor.Controls.zeroGuard.profile,GuardedFor.Controls.endless.compiled.profile⟩
def rightProfile : StmtWordP right := ⟨GuardedFor.Controls.oneGuard.profile,ForCompilation.Controls.artifact.compiled.profile⟩
def inner : Solidity.Yul.Stmt [] [] root 2 := .seq left right
def source : Solidity.Yul.Stmt [] [] root 2 := .seq .skip inner
def profile : StmtWordP source := ⟨True.intro,leftProfile,rightProfile⟩
def artifact : Artifact 8 source 0 := (lower 8 source 0).get (by rfl)

theorem source_done (a b : Scalar.Word) :
 evalStmt 12 .nil True.intro source profile (sourceLocals #v[a,b]) =
 some ⟨sourceLocals #v[0,~~~(~~~b+3)+3],.normal⟩ := by
 have first := evalStmt_stable (show 2 ≤ 10 by omega) .nil True.intro left leftProfile
   (sourceLocals #v[a,b]) (GuardedFor.Controls.source_skipped #v[a,b])
 have last := GuardedFor.Controls.source_taken a b
 have innerDone := sequence_source left right leftProfile rightProfile 10
   (sourceLocals #v[a,b]) (sourceLocals #v[a,b]) (sourceLocals #v[0,~~~(~~~b+3)+3]) first last
 exact sequence_source .skip inner True.intro ⟨leftProfile,rightProfile⟩ 11
   (sourceLocals #v[a,b]) (sourceLocals #v[a,b]) (sourceLocals #v[0,~~~(~~~b+3)+3]) rfl innerDone

/-- Actual whole visitor output executes with arbitrary raw locals, caller
and machine fields. Every component run is discharged from real source proof. -/
theorem target_done (a b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := [coreWord a,coreWord b]++caller} =
 .ok {m with stack := [coreWord 0,coreWord (~~~(~~~b+3)+3)]++caller} 0 := by
 obtain ⟨out,same,ran⟩ := artifact.source_to_model 12 #v[a,b] _ (source_done a b) #v[] m caller
 have equal : #v[0,~~~(~~~b+3)+3] = out :=
   SourceLoopCompletion.sourceLocals_injective (congrArg Outcome.vars same)
 subst out
 exact ran

/-- For leaves still delegate the unchanged normal-component visitor;
this semantically untaken nested-for body remains an explicit refusal. -/
def nestedBody : Solidity.Yul.Stmt [] [] root 2 :=
 .for_ .skip (.literal 0) .skip (.for_ .skip (.literal 0) .skip .skip)
#guard (lower 8 source 0).isSome
#guard (lower 0 source 0).isNone
#guard (lower 8 source 15).isNone
#guard (lower 8 nestedBody 0).isNone
#guard (evalStmt 0 .nil True.intro source profile (sourceLocals #v[99,dirty])).isNone
/-- info: 'Solidity.Yul.Compilation.LoopControlCompilation.Controls.artifact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms artifact
/-- info: 'Solidity.Yul.Compilation.LoopControlCompilation.Controls.source_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_done
/-- info: 'Solidity.Yul.Compilation.LoopControlCompilation.Controls.target_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_done
end Solidity.Yul.Compilation.LoopControlCompilation.Controls
