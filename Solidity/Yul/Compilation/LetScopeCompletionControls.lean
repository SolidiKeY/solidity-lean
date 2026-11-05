import Solidity.Yul.Compilation.LetScopeCompletion
import Solidity.Yul.Compilation.LetScopeCompilationControls
/-! Exact reflection over actual let visitor outputs, including a computed
dirty initializer consumed by a structured loop and the last accessible DUP.
Kernel source/model witnesses only; no external compiler/native oracle. -/
namespace Solidity.Yul.Compilation.LetScopeCompletion.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open LetScopeCompilation.Controls (artifact source lastSource)
open SourceLoop.Controls (root dirty)

theorem success_iff (locals out : Vector Scalar.Word 1) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := completion_iff artifact locals out m caller

theorem recovered (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals #v[b]) =
 some ⟨sourceLocals #v[(~~~(~~~(b+dirty)+3)+3)+3],.normal⟩ :=
 (success_iff #v[b] #v[(~~~(~~~(b+dirty)+3)+3)+3] m caller).mpr
   (LetScopeCompilation.Controls.target_done b m caller)

theorem reflected (locals : Vector Scalar.Word 1) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word 1),
 evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} :=
 model_to_source artifact locals m final caller skip ran

def boundaryArtifact := (LetScopeCompilation.lower 2 lastSource).get (by rfl)
def boundaryInitializer := (PureExpressions.compile 2 (Solidity.Yul.Expr.local (F := []) (X := []) (n := 16) 15)).get (by rfl)
def boundaryBody := (LoopControlCompilation.lower 2 (Solidity.Yul.Stmt.skip (F := []) (X := []) (c := root) (n := 17)) 0).get (by rfl)

theorem boundary_source (locals : Vector Scalar.Word 16) :
 evalStmt 3 .nil True.intro lastSource boundaryArtifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals locals,.normal⟩ := by
 have frame : outerLocals (#v[boundaryInitializer.value locals] ++ locals) = locals := by
   apply Vector.toList_inj.mp
   rw [outerLocals_toList,Vector.toList_append]
   change (boundaryInitializer.value locals :: locals.toList).drop 1 = locals.toList
   rfl
 have sourceRun := LetScopeCompilation.scope_source boundaryInitializer boundaryBody 1 locals
   (#v[boundaryInitializer.value locals] ++ locals) (by rfl)
 rw [frame] at sourceRun
 exact sourceRun

theorem boundary_target (locals : Vector Scalar.Word 16) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run boundaryArtifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := locals.toList.map coreWord++caller} 0 :=
 boundaryArtifact.normal_to_model 3 locals locals (boundary_source locals) m caller

theorem boundary_iff (locals out : Vector Scalar.Word 16) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro lastSource boundaryArtifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run boundaryArtifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := completion_iff boundaryArtifact locals out m caller

theorem oversized_model (m : Evm.Machine) :
 Evm.run boundaryArtifact.code
   {m with stack := (Vector.replicate 16 dirty).toList.map coreWord ++ List.replicate 1024 (coreWord 257)} =
 .ok {m with stack := (Vector.replicate 16 dirty).toList.map coreWord ++ List.replicate 1024 (coreWord 257)} 0 :=
 boundary_target (Vector.replicate 16 dirty) m (List.replicate 1024 (coreWord 257))

#guard boundaryInitializer.value #v[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,dirty] = dirty

-- boundary_target also applies to an oversized arbitrary caller; capacity
-- remains a separate actual trace obligation rather than an inferred pass.
#guard Scalar.stackBound [Backend.Instr.op (.DUP 15)] (1040 : Int) = false
#guard (LetScopeCompilation.lower 2 LetScopeCompilation.Controls.beyondSource).isNone
#guard Scalar.run (popPrefix 1) [] = none
#guard (evalStmt 0 .nil True.intro source artifact.compiled.profile (sourceLocals #v[dirty])).isNone

/-- info: 'Solidity.Yul.Compilation.LetScopeCompletion.Controls.success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success_iff
/-- info: 'Solidity.Yul.Compilation.LetScopeCompletion.Controls.recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms recovered
/-- info: 'Solidity.Yul.Compilation.LetScopeCompletion.Controls.reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reflected
/-- info: 'Solidity.Yul.Compilation.LetScopeCompletion.Controls.boundary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms boundary_source
/-- info: 'Solidity.Yul.Compilation.LetScopeCompletion.Controls.boundary_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms boundary_target
/-- info: 'Solidity.Yul.Compilation.LetScopeCompletion.Controls.boundary_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms boundary_iff
/-- info: 'Solidity.Yul.Compilation.LetScopeCompletion.Controls.oversized_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms oversized_model
end Solidity.Yul.Compilation.LetScopeCompletion.Controls
