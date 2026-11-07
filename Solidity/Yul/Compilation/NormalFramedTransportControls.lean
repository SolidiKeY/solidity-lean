import Solidity.Yul.Compilation.NormalFramedTransport
import Solidity.Yul.Compilation.NormalWordTransportControls
/-! Actual recursive sequence/conditional original compiler witnesses and
shifted locals consume the strong certificate. Existing source/model forward
proofs are reused; reflection is stronger and no native/G24 claim follows. -/
namespace Solidity.Yul.Compilation.NormalFramedTransport.Controls
open Backend Scalar Selection MachineAdapter
open NormalWordTransport.Controls

def rootCertificate : FramedLoweringCertificate code block :=
 certificate compiled 0 block code actual_emission actual_selection

def shiftedCertificate : FramedLoweringCertificate shiftedCode shiftedBlock :=
 certificate compiled 13 shiftedBlock shiftedCode
  (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm

/-- Real same-horizon original evaluator success and the matching exact model
update jointly inhabit the new strong certificate for all locals/numeric tails.
No new source semantics, embedding premise or desired execution is introduced. -/
theorem source_and_run (locals : Vector Scalar.Word 2) (tail : Stack) (m : Evm.Machine) :
 (Closed.evalStmt 11 .nil True.intro statement compiled.profile
   (ProducerExpressions.sourceLocals locals) =
     some ⟨ProducerExpressions.sourceLocals (compiled.update locals),.normal⟩) ∧
 Evm.run code {m with stack := irStack (locals.toList++tail)} =
 .ok {m with stack := irStack ((compiled.update locals).toList++tail)} 0 := by
 simpa only [irStack_words,List.map_append] using source_model locals m (tail.map coreWord)

theorem whole_reflected (input : Stack) (m final : Evm.Machine) (skip : Nat)
 (ran : Evm.run code {m with stack := irStack input} = .ok final skip) :
 ∃ output : Stack, skip = 0 ∧ final = {m with stack := irStack output} ∧ StructuredExec block input output := by
 simpa only [] using rootCertificate.reflect input {m with stack := irStack input} final skip rfl ran

/-- Newer locals and caller contents are actually supplied by the old generic
compiler execution, while every successful result is covered by the new cert. -/
theorem shifted_success (locals : Vector Scalar.Word 2) (newer : Vector Scalar.Word 13)
 (tail : Stack) (m : Evm.Machine) :
 Evm.run shiftedCode {m with stack := irStack (newer.toList++locals.toList++tail)} =
 .ok {m with stack := irStack (newer.toList++(compiled.update locals).toList++tail)} 0 := by
 simpa only [irStack_words,List.map_append] using shifted_run locals newer m (tail.map coreWord)

theorem high_only_success (m : Evm.Machine) :
 Evm.run code {m with stack := irStack [highOnly,0]} =
 .ok {m with stack := irStack [7,~~~highOnly]} 0 := by
 simpa only [irStack_words,List.map_cons,List.map_nil,List.append_nil] using high_run m []

#guard (NormalControl.compile 0 statement).isNone
#guard (compiled.emit 16).isNone
#guard (WordMachine.selectCode [.op .GAS]).isNone
#guard (SignedMachine.selectCode [.op .GAS]).isNone
#guard compiled.update #v[highOnly,0] = #v[7,~~~highOnly]
#guard compiled.update #v[0,0] = #v[0,~~~(0 : Scalar.Word)]
/-- info: 'Solidity.Yul.Compilation.NormalFramedTransport.Controls.rootCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rootCertificate
/-- info: 'Solidity.Yul.Compilation.NormalFramedTransport.Controls.shiftedCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shiftedCertificate
/-- info: 'Solidity.Yul.Compilation.NormalFramedTransport.Controls.source_and_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_and_run
/-- info: 'Solidity.Yul.Compilation.NormalFramedTransport.Controls.whole_reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms whole_reflected
/-- info: 'Solidity.Yul.Compilation.NormalFramedTransport.Controls.shifted_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shifted_success
/-- info: 'Solidity.Yul.Compilation.NormalFramedTransport.Controls.high_only_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms high_only_success
end Solidity.Yul.Compilation.NormalFramedTransport.Controls
