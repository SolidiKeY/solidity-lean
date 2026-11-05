import Solidity.Yul.Compilation.SwitchCompilation
import Solidity.Yul.Compilation.ScopedControlCompilationControls
/-! Inhabited one-case/default switch with a dirty fullword label and nested
scoped matching arm. A low-bit alias must take default; the untaken arm may
lack source horizon. Kernel model evidence only, not native EVM validation. -/
namespace Solidity.Yul.Compilation.SwitchCompilation.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls (root dirty)
open ScopedControlCompilation.Controls (source update)

def switchSource : Solidity.Yul.Stmt [] [] root 2 := .switch (.local 0) (.cons dirty.toFin source .nil) .skip
def artifact := (lower 10 switchSource).get (by rfl)
def condition := localExpr (n := 2) 0 0
def armArtifact := ScopedControlCompilation.Controls.artifact
def lowOnly : Scalar.Word := 257

theorem matching_source (c : Scalar.Word) :
 evalStmt 12 .nil True.intro switchSource artifact.compiled.profile (sourceLocals #v[dirty,c]) =
 some ⟨sourceLocals #v[update dirty,c],.normal⟩ :=
 source_match (arm := source) (fallback := .skip) condition dirty.toFin armArtifact.compiled.profile True.intro
   10 #v[dirty,c] #v[update dirty,c] (by omega) (by rfl) (ScopedControlCompilation.Controls.source_done dirty c)

theorem matching_target (c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord dirty::coreWord c::caller} =
 .ok {m with stack := coreWord (update dirty)::coreWord c::caller} 0 :=
 artifact.normal_to_model 12 #v[dirty,c] #v[update dirty,c] (matching_source c) m caller

theorem default_source (b c : Scalar.Word) (different : b.toFin ≠ dirty.toFin) :
 evalStmt 3 .nil True.intro switchSource artifact.compiled.profile (sourceLocals #v[b,c]) =
 some ⟨sourceLocals #v[b,c],.normal⟩ :=
 source_default (arm := source) (fallback := .skip) condition dirty.toFin armArtifact.compiled.profile True.intro
   0 #v[b,c] #v[b,c] (by omega) different (by rfl)

theorem default_target (b c : Scalar.Word) (different : b.toFin ≠ dirty.toFin)
 (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord b::coreWord c::caller} =
 .ok {m with stack := coreWord b::coreWord c::caller} 0 :=
 artifact.normal_to_model 3 #v[b,c] #v[b,c] (default_source b c different) m caller

theorem low_alias_target (c : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run artifact.code {m with stack := coreWord lowOnly::coreWord c::caller} =
 .ok {m with stack := coreWord lowOnly::coreWord c::caller} 0 :=
 default_target lowOnly c (by decide) m caller

def multipleSource : Solidity.Yul.Stmt [] [] root 2 :=
 .switch (.local 0) (.cons dirty.toFin source (.cons 0 .skip .nil)) .skip
def emptySource : Solidity.Yul.Stmt [] [] root 2 := .switch (.local 0) .nil .skip
def comparisonProgram := ((comparison dirty.toFin).code 0).get (by rfl)
#guard (lower 10 multipleSource).isNone
#guard (lower 10 emptySource).isNone
#guard (lower 0 switchSource).isNone
#guard (ScopedControlCompilation.lower 10 switchSource).isNone
#guard (evalStmt 0 .nil True.intro switchSource artifact.compiled.profile (sourceLocals #v[dirty,dirty])).isNone
-- Default completes at source3 even though this untaken arm cannot at source1.
#guard (evalStmt 1 .nil True.intro source armArtifact.compiled.profile (sourceLocals #v[lowOnly,dirty])).isNone
#guard (dirty &&& 255) = (lowOnly &&& 255)
#guard dirty ≠ lowOnly
#guard update dirty = BitVec.ofNat 256 (2*2^200+514)
-- These actual scalar capacity/underflow checks are separate from model success.
#guard Scalar.stackBound comparisonProgram (1022 : Int) = true
#guard Scalar.stackBound comparisonProgram (1023 : Int) = false
#guard (Scalar.run comparisonProgram []).isNone

/-- info: 'Solidity.Yul.Compilation.SwitchCompilation.Controls.matching_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms matching_source
/-- info: 'Solidity.Yul.Compilation.SwitchCompilation.Controls.matching_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms matching_target
/-- info: 'Solidity.Yul.Compilation.SwitchCompilation.Controls.default_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms default_source
/-- info: 'Solidity.Yul.Compilation.SwitchCompilation.Controls.default_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms default_target
/-- info: 'Solidity.Yul.Compilation.SwitchCompilation.Controls.low_alias_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms low_alias_target
end Solidity.Yul.Compilation.SwitchCompilation.Controls
