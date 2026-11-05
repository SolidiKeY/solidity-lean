import Solidity.Yul.Compilation.FramedWordLowering
import Solidity.Yul.Compilation.SignedClosedExecutionControls
/-! Inhabited original signed-expression framed-lowering witness. Full dirty
words, division-by-zero, wraparound and failure remain the existing semantics.
The reflected caller is numeric; this adds no symbolic/native capacity claim. -/
namespace Solidity.Yul.Compilation.FramedWordLowering.Controls
open Backend Scalar Selection MachineAdapter
open SignedInstructionCertificates.Controls

def certificate : FramedLoweringCertificate model (.code program) :=
 lowering program model SignedExecution.Controls.actual_selection

/-- Forward field is genuinely inhabited for every local vector and complete
nonstack machine frame, rather than relying on hypothetical successful runs. -/
theorem success (locals : Vector Scalar.Word 2) (m : Evm.Machine) :
 Evm.run model {m with stack := irStack locals.toList} =
 .ok {m with stack := irStack (compiled.value locals::locals.toList)} 0 :=
 (source_certificate locals m).2

theorem exact_result (locals : Vector Scalar.Word 2) (m final : Evm.Machine) (skip : Nat)
 (ran : Evm.run model {m with stack := irStack locals.toList} = .ok final skip) :
 skip = 0 ∧ final = {m with stack := irStack (compiled.value locals::locals.toList)} := by
 have actual := expression_reflect compiled program model SignedExecution.Controls.actual_emission SignedExecution.Controls.actual_selection
   locals #v[] [] {m with stack := irStack locals.toList} final skip (by simp only [Vector.toList_empty,List.nil_append,List.append_nil]) ran
 simpa only [Vector.toList_empty,List.nil_append,List.append_nil] using actual

/-- No actual selected successful run can hide a pending skip. -/
theorem pending_refused (locals : Vector Scalar.Word 2) (m final : Evm.Machine) (skip : Nat) :
 Evm.run model {m with stack := irStack locals.toList} ≠ .ok final (skip+1) := by
 intro ran
 have zero := (exact_result locals m final (skip+1) ran).1
 omega

theorem dirty_frame (m final : Evm.Machine) (skip : Nat)
 (ran : Evm.run model {m with stack := irStack [dirty,3]} = .ok final skip) :
 skip = 0 ∧ final = {m with stack := irStack [compiled.value #v[dirty,3],dirty,3]} :=
 exact_result #v[dirty,3] m final skip ran

theorem failure_after_push (m : Evm.Machine) :
 Evm.run failingModel {m with stack := []} = .fault := prefix_failure m

/-- A caller word changes operand availability; no failure theorem is lifted
from the empty input to arbitrary suffixes. -/
theorem caller_operand_rescue (m : Evm.Machine) : Scalar.run failingProgram [] = none ∧
 Evm.run failingModel {m with stack := [coreWord 0]} =
 .ok {m with stack := [coreWord 0]} 0 := by
 exact caller_rescue m

#guard (SignedMachine.selectCode [.op .GAS]).isNone
#guard (SignedMachine.selectCode [.op (.DUP 15)]).isSome
#guard Scalar.run [.op (.DUP 15)] [] = none
#guard compiled.value #v[dirty,3] ≠ compiled.value #v[257,3]
#guard compiled.value #v[minimum,negativeOne] = minimum+1
#guard compiled.value #v[negativeSeven,0] = 1
/-- info: 'Solidity.Yul.Compilation.FramedWordLowering.Controls.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms certificate
/-- info: 'Solidity.Yul.Compilation.FramedWordLowering.Controls.success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success
/-- info: 'Solidity.Yul.Compilation.FramedWordLowering.Controls.exact_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exact_result
/-- info: 'Solidity.Yul.Compilation.FramedWordLowering.Controls.pending_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pending_refused
/-- info: 'Solidity.Yul.Compilation.FramedWordLowering.Controls.dirty_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dirty_frame
/-- info: 'Solidity.Yul.Compilation.FramedWordLowering.Controls.failure_after_push' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms failure_after_push
/-- info: 'Solidity.Yul.Compilation.FramedWordLowering.Controls.caller_operand_rescue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms caller_operand_rescue

/-- Actual multiwrite statement witness, not a generic desired-run premise. -/
def statementCertificate : FramedLoweringCertificate SignedExecution.Controls.statementModel
 (.code SignedExecution.Controls.statementCode) :=
 lowering _ _ (Option.some_get (by rfl)).symm

theorem statement_success (locals : Vector Scalar.Word 2) (m : Evm.Machine) :
 Evm.run SignedExecution.Controls.statementModel {m with stack := irStack locals.toList} =
 .ok {m with stack := irStack (SignedExecution.Controls.statementCompiled.update locals).toList} 0 := by
 apply (statementCertificate.success locals.toList _ {m with stack := irStack locals.toList} rfl).mpr
 apply StructuredExec.code
 simpa only [Vector.toList_empty,List.nil_append,List.append_nil] using
  SignedExecution.Controls.statementCompiled.lowered.correct 0 _ (Option.some_get (by rfl)).symm locals #v[] []

theorem statement_exact (m final : Evm.Machine) (skip : Nat)
 (ran : Evm.run SignedExecution.Controls.statementModel
   {m with stack := irStack [negativeSeven,3]} = .ok final skip) :
 skip = 0 ∧ final = {m with stack := irStack [negativeTwo,1]} := by
 have actual := statement_reflect SignedExecution.Controls.statementCompiled _ _
  (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm
  #v[negativeSeven,3] #v[] [] {m with stack := irStack [negativeSeven,3]} final skip
  (by simp only [Vector.toList_empty,List.nil_append,List.append_nil]; rfl) ran
 simpa only [Vector.toList_empty,List.nil_append,List.append_nil,SignedExecution.Controls.statement_update] using actual

/-- info: 'Solidity.Yul.Compilation.FramedWordLowering.Controls.statementCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms statementCertificate
/-- info: 'Solidity.Yul.Compilation.FramedWordLowering.Controls.statement_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms statement_success
/-- info: 'Solidity.Yul.Compilation.FramedWordLowering.Controls.statement_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms statement_exact
end Solidity.Yul.Compilation.FramedWordLowering.Controls
