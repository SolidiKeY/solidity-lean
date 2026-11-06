import Solidity.Yul.Compilation.ZeroControlCompilation
import Solidity.Yul.Compilation.LetControlCompilationControls
/-! Actual zero scope around recursive if/seq/let work. The fresh local is
written dirty before retirement while the outer word is updated. Existing
source and target semantics are reused; kernel source/model evidence only. -/
namespace Solidity.Yul.Compilation.ZeroControlCompilation.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root dirty)

def conditional : Solidity.Yul.Stmt [] [] root 2 := .let_ 1 (.local 1)
 (.assign (fun _ : Fin 1 => .local 2) (.builtin (.pure .add) (Fin.cases (.local 0) (fun _ => .literal 3))))
def conditionalCompiled := (ScopedStatements.compile 7 conditional).get (by rfl)
def tail : Solidity.Yul.Stmt [] [] root 2 := .let_ 1 (.literal dirty.toFin)
 (.seq (.assign (fun _ : Fin 1 => .local 2) (.builtin (.pure .add) (Fin.cases (.local 2) (fun _ => .local 0))))
   (.assign (fun _ : Fin 1 => .local 1) (.literal dirty.toFin)))
def tailCompiled := (ScopedStatements.compile 7 tail).get (by rfl)
def branch : Solidity.Yul.Stmt [] [] root 2 := .if_ (.local 1) conditional
def body : Solidity.Yul.Stmt [] [] root 2 := .seq branch tail
def bodyArtifact := (LetControlCompilation.lower 9 body).get (by rfl)
def source : Solidity.Yul.Stmt [] [] root 1 := .zero 1 body
def artifact := (lower 9 source).get (by rfl)
def intermediate (b : Scalar.Word) := if b = 0 then b else b+3
def update (b : Scalar.Word) := intermediate b+dirty

theorem conditional_source (b : Scalar.Word) :
 evalStmt 7 .nil True.intro conditional conditionalCompiled.profile (sourceLocals #v[0,b]) =
 some ⟨sourceLocals #v[0,b+3],.normal⟩ := conditionalCompiled.source #v[0,b]

theorem tail_source (b : Scalar.Word) :
 evalStmt 7 .nil True.intro tail tailCompiled.profile (sourceLocals #v[0,b]) =
 some ⟨sourceLocals #v[dirty,b+dirty],.normal⟩ := tailCompiled.source #v[0,b]

theorem branch_source (b : Scalar.Word) :
 evalStmt 8 .nil True.intro branch
   (⟨True.intro,conditionalCompiled.profile⟩ : StmtWordP branch) (sourceLocals #v[0,b]) =
 some ⟨sourceLocals #v[0,intermediate b],.normal⟩ := by
 change (if b.toNat = 0 then some (⟨sourceLocals #v[0,b],.normal⟩ : Outcome root 2)
   else evalStmt 7 .nil True.intro conditional conditionalCompiled.profile (sourceLocals #v[0,b])) = _
 by_cases zero : b = 0
 · have zn : b.toNat = 0 := congrArg BitVec.toNat zero
   rw [if_pos zn,intermediate,if_pos zero]
 · have nz : b.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
   rw [if_neg nz,intermediate,if_neg zero]
   exact conditional_source b

theorem body_source (b : Scalar.Word) :
 evalStmt 9 .nil True.intro body bodyArtifact.compiled.profile (sourceLocals #v[0,b]) =
 some ⟨sourceLocals #v[dirty,update b],.normal⟩ := by
 have last := evalStmt_stable (show 7 ≤ 8 by omega) .nil True.intro tail tailCompiled.profile
   (sourceLocals #v[0,intermediate b]) (tail_source (intermediate b))
 exact LoopControlCompilation.sequence_source branch tail ⟨True.intro,conditionalCompiled.profile⟩ tailCompiled.profile
   8 (sourceLocals #v[0,b]) (sourceLocals #v[0,intermediate b])
   (sourceLocals #v[dirty,update b]) (branch_source b) last

theorem source_done (b : Scalar.Word) :
 evalStmt 10 .nil True.intro source artifact.compiled.profile (sourceLocals #v[b]) =
 some ⟨sourceLocals #v[update b],.normal⟩ :=
 source_scope bodyArtifact 9 #v[b] #v[dirty,update b] (body_source b)

theorem target_done (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord b::caller} =
 .ok {m with stack := coreWord (update b)::caller} 0 :=
 artifact.normal_to_model 10 #v[b] #v[update b] (source_done b) m caller

def emptySource : Solidity.Yul.Stmt [] [] root 1 := .zero 0 LetControlCompilation.Controls.source
def emptyArtifact := (lower 15 emptySource).get (by rfl)
theorem empty_source (b : Scalar.Word) :
 evalStmt 21 .nil True.intro emptySource emptyArtifact.compiled.profile (sourceLocals #v[b]) =
 some ⟨sourceLocals #v[LetControlCompilation.Controls.update b],.normal⟩ :=
 source_scope (fresh := 0) LetControlCompilation.Controls.artifact 20 #v[b]
   #v[LetControlCompilation.Controls.update b] (LetControlCompilation.Controls.source_done b)

#guard dirty ≠ 0
#guard update 0 = dirty
#guard update (BitVec.ofNat 256 (2^200)) = BitVec.ofNat 256 (2*2^200+260)
#guard (lower 0 source).isNone
#guard (ZeroScopeCompilation.lower 9 source).isNone
#guard (evalStmt 0 .nil True.intro source artifact.compiled.profile (sourceLocals #v[dirty])).isNone
def lastSource : Solidity.Yul.Stmt [] [] root 1 :=
 .zero 15 (.if_ (.local 15) (.let_ 1 (.literal 0) .skip))
def beyondSource : Solidity.Yul.Stmt [] [] root 1 :=
 .zero 16 (.if_ (.local 16) (.let_ 1 (.literal 0) .skip))
#guard (lower 4 lastSource).isSome
#guard (lower 4 beyondSource).isNone
-- These actual operation bounds remain separate from whole model success.
#guard Scalar.stackBound (ZeroLoopScope.entry 1) (1024 : Int) = false
#guard Scalar.run (popPrefix 1) [] = none

/-- info: 'Solidity.Yul.Compilation.ZeroControlCompilation.Controls.conditional_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms conditional_source
/-- info: 'Solidity.Yul.Compilation.ZeroControlCompilation.Controls.tail_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms tail_source
/-- info: 'Solidity.Yul.Compilation.ZeroControlCompilation.Controls.branch_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms branch_source
/-- info: 'Solidity.Yul.Compilation.ZeroControlCompilation.Controls.body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms body_source
/-- info: 'Solidity.Yul.Compilation.ZeroControlCompilation.Controls.source_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_done
/-- info: 'Solidity.Yul.Compilation.ZeroControlCompilation.Controls.target_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms target_done
/-- info: 'Solidity.Yul.Compilation.ZeroControlCompilation.Controls.empty_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms empty_source
end Solidity.Yul.Compilation.ZeroControlCompilation.Controls
