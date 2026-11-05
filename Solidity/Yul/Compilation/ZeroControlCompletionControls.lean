import Solidity.Yul.Compilation.ZeroControlCompletion
import Solidity.Yul.Compilation.ZeroControlCompilationControls
/-! Exact reflection over actual zero/control compiler outputs. Controls
cover dirty prefix retirement, zero arity and an actual last-slot execution.
Kernel source/model evidence only, not external/native validity evidence. -/
namespace Solidity.Yul.Compilation.ZeroControlCompletion.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open ZeroControlCompilation.Controls (artifact source update emptyArtifact emptySource lastSource)
open SourceLoop.Controls (root dirty)

theorem success_iff (locals out : Vector Scalar.Word 1) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := completion_iff artifact locals out m caller

theorem recovered (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ horizon, evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals #v[b]) =
 some ⟨sourceLocals #v[update b],.normal⟩ :=
 (success_iff #v[b] #v[update b] m caller).mpr (ZeroControlCompilation.Controls.target_done b m caller)

theorem reflected (locals : Vector Scalar.Word 1) (m final : Evm.Machine) (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run artifact.code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (horizon : Nat) (out : Vector Scalar.Word 1),
 evalStmt horizon .nil True.intro source artifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩ ∧ skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} :=
 model_to_source artifact locals m final caller skip ran

theorem empty_iff (locals out : Vector Scalar.Word 1) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro emptySource emptyArtifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run emptyArtifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := completion_iff emptyArtifact locals out m caller

theorem empty_target (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run emptyArtifact.code {m with stack := coreWord b::caller} =
 .ok {m with stack := coreWord (LetControlCompilation.Controls.update b)::caller} 0 :=
 emptyArtifact.normal_to_model 21 #v[b] #v[LetControlCompilation.Controls.update b]
   (ZeroControlCompilation.Controls.empty_source b) m caller

def boundaryArtifact := (ZeroControlCompilation.lower 4 lastSource).get (by rfl)

def boundaryLeaf : Solidity.Yul.Stmt [] [] root 16 := .let_ 1 (.literal 0) .skip
def boundaryLeafCompiled := (ScopedStatements.compile 3 boundaryLeaf).get (by rfl)
def boundaryBody : Solidity.Yul.Stmt [] [] root 16 := .if_ (.local 15) boundaryLeaf
def boundaryBodyArtifact := (LetControlCompilation.lower 4 boundaryBody).get (by rfl)
def boundaryCondition := (PureExpressions.compile 3 (Solidity.Yul.Expr.local (F := []) (X := []) (n := 16) 15)).get (by rfl)
def boundaryInitial := Vector.replicate 15 (0 : Scalar.Word) ++ #v[dirty]

theorem boundary_source :
 evalStmt 5 .nil True.intro lastSource boundaryArtifact.compiled.profile (sourceLocals #v[dirty]) =
 some ⟨sourceLocals #v[dirty],.normal⟩ := by
 have innerFrame : outerLocals (fresh := 1) (#v[(0 : Scalar.Word)] ++ boundaryInitial) = boundaryInitial := by
   apply Vector.toList_inj.mp
   rw [outerLocals_toList,Vector.toList_append]
   change (0 :: boundaryInitial.toList).drop 1 = boundaryInitial.toList
   rfl
 have leaf := boundaryLeafCompiled.source boundaryInitial
 change evalStmt 3 .nil True.intro boundaryLeaf boundaryLeafCompiled.profile (sourceLocals boundaryInitial) =
   some ⟨sourceLocals (outerLocals (fresh := 1) (#v[(0 : Scalar.Word)] ++ boundaryInitial)),.normal⟩ at leaf
 rw [innerFrame] at leaf
 have bodyRun : evalStmt 4 .nil True.intro boundaryBody boundaryBodyArtifact.compiled.profile (sourceLocals boundaryInitial) =
   some ⟨sourceLocals boundaryInitial,.normal⟩ :=
   LetControlCompletion.source_true boundaryCondition boundaryLeafCompiled.profile 3 boundaryInitial boundaryInitial (by decide) leaf
 have outerFrame : outerLocals (fresh := 15) (n := 1) boundaryInitial = #v[dirty] := by
   apply Vector.toList_inj.mp
   rw [outerLocals_toList]
   rfl
 have scopeSource := ZeroControlCompilation.source_scope (fresh := 15) boundaryBodyArtifact 4 #v[dirty] boundaryInitial bodyRun
 rw [outerFrame] at scopeSource
 exact scopeSource

theorem boundary_target (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run boundaryArtifact.code {m with stack := coreWord dirty::caller} =
 .ok {m with stack := coreWord dirty::caller} 0 :=
 boundaryArtifact.normal_to_model 5 #v[dirty] #v[dirty] boundary_source m caller

theorem boundary_iff (locals out : Vector Scalar.Word 1) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ horizon, evalStmt horizon .nil True.intro lastSource boundaryArtifact.compiled.profile (sourceLocals locals) =
 some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run boundaryArtifact.code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := completion_iff boundaryArtifact locals out m caller

#guard dirty ≠ 0
#guard (ZeroControlCompilation.lower 4 ZeroControlCompilation.Controls.beyondSource).isNone
#guard (evalStmt 0 .nil True.intro source artifact.compiled.profile (sourceLocals #v[dirty])).isNone
-- Even a selected/executed last-slot model witness does not imply capacity.
#guard Scalar.stackBound (ZeroLoopScope.entry 15) (1024 : Int) = false
#guard Scalar.run (popPrefix 1) [] = none

/-- info: 'Solidity.Yul.Compilation.ZeroControlCompletion.Controls.success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success_iff
/-- info: 'Solidity.Yul.Compilation.ZeroControlCompletion.Controls.recovered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms recovered
/-- info: 'Solidity.Yul.Compilation.ZeroControlCompletion.Controls.reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reflected
/-- info: 'Solidity.Yul.Compilation.ZeroControlCompletion.Controls.empty_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms empty_iff
/-- info: 'Solidity.Yul.Compilation.ZeroControlCompletion.Controls.empty_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms empty_target
/-- info: 'Solidity.Yul.Compilation.ZeroControlCompletion.Controls.boundary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms boundary_source
/-- info: 'Solidity.Yul.Compilation.ZeroControlCompletion.Controls.boundary_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms boundary_target
/-- info: 'Solidity.Yul.Compilation.ZeroControlCompletion.Controls.boundary_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms boundary_iff
end Solidity.Yul.Compilation.ZeroControlCompletion.Controls
