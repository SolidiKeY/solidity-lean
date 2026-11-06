import Solidity.Yul.Compilation.SignedInstructionCertificates
import Solidity.Yul.Compilation.SignedExecutionControls
/-! Actual original four-signed-op expression consumed through a real existing
leaf lowering certificate. Signed zero/wrap/remainder, refusal and caller rescue
remain separate from native gas/capacity and logical Source/G24 adequacy. -/
namespace Solidity.Yul.Compilation.SignedInstructionCertificates.Controls
open Backend Scalar Selection MachineAdapter
open Solidity.Yul Solidity.Yul.Closed ProducerExpressions

abbrev expr := SignedExecution.Controls.expr
abbrev compiled := SignedExecution.Controls.compiled
abbrev program := SignedExecution.Controls.code
abbrev model := SignedExecution.Controls.model
abbrev minimum := SignedExecution.Controls.minimum
abbrev negativeOne := SignedExecution.Controls.negativeOne
abbrev negativeTwo := SignedExecution.Controls.negativeTwo
abbrev negativeThree := SignedExecution.Controls.negativeThree
abbrev negativeSeven := SignedExecution.Controls.negativeSeven
abbrev dirty := SignedExecution.Controls.dirty

def leafCertificate : LoweringCertificate model (.code program) :=
 lowering program model SignedExecution.Controls.actual_selection

def divisionCertificate : InstructionCertificate .sdiv := instruction (.op .SDIV) .sdiv (by rfl)
def remainderCertificate : InstructionCertificate .smod := instruction (.op .SMOD) .smod (by rfl)

theorem division_origin : divisionCertificate.code = [.op .SDIV] := rfl
theorem remainder_origin : remainderCertificate.code = [.op .SMOD] := rfl

theorem scalar_source (locals : Vector Scalar.Word 2) :
 Scalar.run program locals.toList = some (compiled.value locals::locals.toList) := by
 have actual := compiled.lowered.correct 0 program SignedExecution.Controls.actual_emission locals #v[] []
 simpa only [Vector.toList_empty,List.nil_append,List.append_nil] using actual

/-- The actual source and actual leaf certificate, not a desired run premise. -/
theorem source_certificate (locals : Vector Scalar.Word 2) (m : Evm.Machine) :
 (evalExpr 6 .nil True.intro expr compiled.profile (sourceLocals locals) =
   some (fun _ => (compiled.value locals).toFin)) ∧
 Evm.run model {m with stack := irStack locals.toList} =
 .ok {m with stack := irStack (compiled.value locals::locals.toList)} 0 := by
 constructor
 · exact compiled.source locals
 · exact (leafCertificate.success locals.toList (compiled.value locals::locals.toList)
     {m with stack := irStack locals.toList} rfl).mpr (.code (scalar_source locals))

theorem zero_divisor_run (m : Evm.Machine) :
 Evm.run model {m with stack := irStack [negativeSeven,0]} =
 .ok {m with stack := irStack [1,negativeSeven,0]} 0 := by
 have actual := (source_certificate #v[negativeSeven,0] m).2
 simpa only [SignedExecution.Controls.zero_divisor_value] using actual

theorem overflow_run (m : Evm.Machine) :
 Evm.run model {m with stack := irStack [minimum,negativeOne]} =
 .ok {m with stack := irStack [minimum+1,minimum,negativeOne]} 0 := by
 have actual := (source_certificate #v[minimum,negativeOne] m).2
 simpa only [SignedExecution.Controls.overflow_value] using actual

theorem negative_remainder_run (m : Evm.Machine) :
 Evm.run model {m with stack := irStack [negativeSeven,negativeThree]} =
 .ok {m with stack := irStack [2,negativeSeven,negativeThree]} 0 := by
 have actual := (source_certificate #v[negativeSeven,negativeThree] m).2
 simpa only [SignedExecution.Controls.negative_divisor_value] using actual

theorem dirty_run (m : Evm.Machine) :
 Evm.run model {m with stack := irStack [dirty,3]} =
 .ok {m with stack := irStack [compiled.value #v[dirty,3],dirty,3]} 0 :=
 (source_certificate #v[dirty,3] m).2

/-- First PUSH succeeds; subsequent SDIV lacks its divisor. -/
def failingProgram : Backend.Program := [pushWord dirty,.op .SDIV]
def failingModel : List Evm.Instr := [.push (coreWord dirty),.sdiv]

theorem failing_selection : SignedMachine.selectCode failingProgram = some failingModel := by rfl

theorem prefix_failure (m : Evm.Machine) : Evm.run failingModel {m with stack := []} = .fault := by
 exact SignedClosedExecution.run failingProgram failingModel failing_selection [] m

/-- A numeric caller can supply the missing ZERO divisor: actual source-word
semantics yields0, so arbitrary suffixes cannot be added to refusal laws. -/
theorem caller_rescue (m : Evm.Machine) : Scalar.run failingProgram [] = none ∧
 Evm.run failingModel {m with stack := [coreWord 0]} = .ok {m with stack := [coreWord 0]} 0 := by
 constructor
 · rfl
 · have actual := SignedClosedExecution.run failingProgram failingModel failing_selection [0] m
   exact actual

theorem division_underflow (m : Evm.Machine) :
 Evm.Instr.step .sdiv {m with stack := [coreWord dirty]} = .fault :=
 SignedClosedExecution.step_failure (.op .SDIV) .sdiv (by rfl) [dirty] (by rfl) m

theorem remainder_underflow (m : Evm.Machine) :
 Evm.Instr.step .smod {m with stack := []} = .fault :=
 SignedClosedExecution.step_failure (.op .SMOD) .smod (by rfl) [] (by rfl) m

def observed := match Evm.run model {Evm.Machine.init with stack := irStack [minimum,negativeOne]} with
 | .ok m skip => some (m.stack,skip)
 | _ => none
#guard observed = some (irStack [minimum+1,minimum,negativeOne],0)
#guard Scalar.run [.op .SDIV] [dirty,0] = some [0]
#guard Scalar.run [.op .SMOD] [dirty,0] = some [0]
#guard (WordMachine.selectInstr (.op .SDIV)).isNone
#guard (WordMachine.selectInstr (.op .SMOD)).isNone
#guard (SignedMachine.selectInstr (.op .SAR)).isNone
#guard (SignedMachine.selectInstr (.op .SIGNEXTEND)).isNone
#guard (SignedMachine.selectInstr (.op .SSTORE)).isNone
#guard (SignedMachine.selectInstr (.op .GAS)).isNone
#guard match Evm.run failingModel Evm.Machine.init with | .fault => true | _ => false
#guard match Evm.run model {Evm.Machine.init with stack := irStack [dirty,3]} with
 | .ok m 0 => m.stack == irStack [compiled.value #v[dirty,3],dirty,3]
 | _ => false
#guard (SignedMachine.selectCode [.op (.DUP 15)]).isSome
#guard Scalar.run [.op (.DUP 15)] (List.replicate 15 dirty) = none
#guard Scalar.run [.op (.DUP 15)] (List.replicate 16 dirty) = some (List.replicate 17 dirty)
/-- info: 'Solidity.Yul.Compilation.SignedInstructionCertificates.Controls.division_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms division_origin
/-- info: 'Solidity.Yul.Compilation.SignedInstructionCertificates.Controls.remainder_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms remainder_origin
/-- info: 'Solidity.Yul.Compilation.SignedInstructionCertificates.Controls.scalar_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms scalar_source
/-- info: 'Solidity.Yul.Compilation.SignedInstructionCertificates.Controls.source_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_certificate
/-- info: 'Solidity.Yul.Compilation.SignedInstructionCertificates.Controls.zero_divisor_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_divisor_run
/-- info: 'Solidity.Yul.Compilation.SignedInstructionCertificates.Controls.overflow_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms overflow_run
/-- info: 'Solidity.Yul.Compilation.SignedInstructionCertificates.Controls.negative_remainder_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms negative_remainder_run
/-- info: 'Solidity.Yul.Compilation.SignedInstructionCertificates.Controls.dirty_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dirty_run
/-- info: 'Solidity.Yul.Compilation.SignedInstructionCertificates.Controls.failing_selection' depends on axioms: [propext] -/
#guard_msgs in
#print axioms failing_selection
/-- info: 'Solidity.Yul.Compilation.SignedInstructionCertificates.Controls.prefix_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms prefix_failure
/-- info: 'Solidity.Yul.Compilation.SignedInstructionCertificates.Controls.caller_rescue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms caller_rescue
/-- info: 'Solidity.Yul.Compilation.SignedInstructionCertificates.Controls.division_underflow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms division_underflow
/-- info: 'Solidity.Yul.Compilation.SignedInstructionCertificates.Controls.remainder_underflow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms remainder_underflow
/-- info: 'Solidity.Yul.Compilation.SignedInstructionCertificates.Controls.leafCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms leafCertificate
/-- info: 'Solidity.Yul.Compilation.SignedInstructionCertificates.Controls.divisionCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms divisionCertificate
/-- info: 'Solidity.Yul.Compilation.SignedInstructionCertificates.Controls.remainderCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms remainderCertificate
end Solidity.Yul.Compilation.SignedInstructionCertificates.Controls
