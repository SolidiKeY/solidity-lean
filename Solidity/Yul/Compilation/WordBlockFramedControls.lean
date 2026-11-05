import Solidity.Yul.Compilation.WordBlockFramed
import Solidity.Yul.Compilation.WhileWordExecutionControls
/-! Actual compiled test/body counter loop, zero exit, shifted frames and
nested branch/loop/sequence witnesses. Existing source test/body proofs and
forward executions are reused. Model noncompletion fault is not source/native
divergence, and model success is not 1024-word capacity or gas admission. -/
namespace Solidity.Yul.Compilation.WordBlockFramed.Controls
open Backend Scalar Selection MachineAdapter
open WhileWordExecution.Controls

def rootCertificate : FramedLoweringCertificate code block :=
 certificate block code actual_selection

def shiftedCertificate : FramedLoweringCertificate shiftedCode shiftedBlock :=
 certificate shiftedBlock shiftedCode (Option.some_get (by rfl)).symm

def boundaryCertificate : FramedLoweringCertificate boundaryCode boundaryBlock :=
 certificate boundaryBlock boundaryCode (Option.some_get (by rfl)).symm

theorem two_success (value : Scalar.Word) (tail : Stack) (m : Evm.Machine) :
 Evm.run code {m with stack := irStack ([2,value]++tail)} =
 .ok {m with stack := irStack ([0,value]++tail)} 0 := by
 simp only [NormalFramedTransport.irStack_words]
 simpa only [List.map_append,List.map_cons,List.map_nil,List.nil_append] using
  two_run value m (tail.map coreWord)

theorem zero_success (value : Scalar.Word) (tail : Stack) (m : Evm.Machine) :
 Evm.run code {m with stack := irStack ([0,value]++tail)} =
 .ok {m with stack := irStack ([0,value]++tail)} 0 := by
 simp only [NormalFramedTransport.irStack_words]
 simpa only [List.map_append,List.map_cons,List.map_nil,List.nil_append] using
  zero_run value m (tail.map coreWord)

/-- Every actual successful loop run, not only the two-turn witness, yields a
finite structured trace, zero pending skip and the entire restored frame. -/
theorem loop_reflected (input : Stack) (m final : Evm.Machine) (skip : Nat)
 (ran : Evm.run code {m with stack := irStack input} = .ok final skip) :
 ∃ output : Stack, skip = 0 ∧ final = {m with stack := irStack output} ∧ StructuredExec block input output := by
 simpa only [] using rootCertificate.reflect input {m with stack := irStack input} final skip rfl ran

private theorem fault_turn (rc rb : Evm.Machine → Evm.Out) (initial : Evm.Machine)
 (word : Scalar.Word) (nonzero : word ≠ 0)
 (conditionRun : rc initial = .ok {initial with stack := coreWord word::initial.stack} 0)
 (bodyRun : rb initial = .fault) : Evm.loopIterN rc rb 1 initial = .inr .fault := by
 have nz : word.toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
 simp only [Evm.loopIterN,Evm.loopTurn,conditionRun,coreWord,nz,ite_false,bodyRun]

/-- A real invalid local/operand input faults after a finite actual iteration;
this is not relabelled as nontermination or as a successful empty loop. -/
theorem body_underflow (m : Evm.Machine) : Evm.run code {m with stack := irStack [1]} = .fault := by
 have ccSelected : WordMachine.selectCode cc = some qc := (Option.some_get (by rfl)).symm
 have bbSelected : WordMachine.selectCode bb = some qb := (Option.some_get (by rfl)).symm
 have cScalar : Scalar.run cc [1] = some [1,1] := by rfl
 have bScalar : Scalar.run bb [1] = none := by rfl
 have cRun := WordClosedExecution.run cc qc ccSelected [1] m
 rw [cScalar] at cRun
 simp only [] at cRun
 have bRun := (WordClosedExecution.failure_iff bb qb bbSelected [1] m).mpr bScalar
 simp only [List.map_cons,List.map_nil] at cRun bRun
 have actual := fault_turn (Evm.run qc) (Evm.run qb) {m with stack := [coreWord 1]}
   1 (by decide) cRun bRun
 have shape : code = [.loop qc qb] := rfl
 have stackShape : irStack [1] = [coreWord 1] := by
  rewrite [FramedConditional.irStack_cons]
  rfl
 rewrite [shape,stackShape,FramedLoop.singleton_run]
 exact Evm.loopRun_of_iterN actual

def nestedBlock : Backend.Block := .seq
 (.ite [pushWord 1] block (.code [.op .POP,.op .POP,.op .POP])) (.code [pushWord dirty])
def nestedCode := (WordControl.blockCode nestedBlock).get (by rfl)
def nestedCertificate : FramedLoweringCertificate nestedCode nestedBlock :=
 certificate nestedBlock nestedCode (Option.some_get (by rfl)).symm

/-- A genuine loop inside a branch followed by a suffix. The loop trace is
recovered from real compiler execution; no favourable intermediate is assumed. -/
theorem nested_success (value : Scalar.Word) (tail : Stack) (m : Evm.Machine) :
 Evm.run nestedCode {m with stack := irStack ([2,value]++tail)} =
 .ok {m with stack := irStack (dirty::([0,value]++tail))} 0 := by
 have loopTrace : StructuredExec block ([2,value]++tail) ([0,value]++tail) :=
  (rootCertificate.success _ _ {m with stack := irStack ([2,value]++tail)} rfl).mp (two_success value tail m)
 apply (nestedCertificate.success _ _ {m with stack := irStack ([2,value]++tail)} rfl).mpr
 exact StructuredExec.seq (StructuredExec.iteTrue (by rfl) (by decide) loopTrace) (.code (by rfl))

/-- Existing model default for all-running prefixes is kept separate from
any claim that source/native divergence has been proved. Never host-evaluated. -/
theorem endless_fault (locals : Vector Scalar.Word 2) (tail : Stack) (m : Evm.Machine) :
 Evm.run [.loop aq qb] {m with stack := irStack (locals.toList++tail)} = .fault := by
 simpa only [NormalFramedTransport.irStack_words,List.map_append] using endless_model_fault locals m (tail.map coreWord)

#guard (WordControl.blockCode (.loop [.op .GAS] (.code []))).isNone
#guard (lowerWhile test.lowered body.lowered 15).isNone
#guard (lowerWhile test.lowered body.lowered 14).isSome
#guard body.update #v[2,dirty] = #v[1,~~~dirty]
/-- info: 'Solidity.Yul.Compilation.WordBlockFramed.Controls.rootCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms rootCertificate
/-- info: 'Solidity.Yul.Compilation.WordBlockFramed.Controls.shiftedCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shiftedCertificate
/-- info: 'Solidity.Yul.Compilation.WordBlockFramed.Controls.boundaryCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms boundaryCertificate
/-- info: 'Solidity.Yul.Compilation.WordBlockFramed.Controls.two_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms two_success
/-- info: 'Solidity.Yul.Compilation.WordBlockFramed.Controls.zero_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_success
/-- info: 'Solidity.Yul.Compilation.WordBlockFramed.Controls.loop_reflected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms loop_reflected
/-- info: 'Solidity.Yul.Compilation.WordBlockFramed.Controls.body_underflow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms body_underflow
/-- info: 'Solidity.Yul.Compilation.WordBlockFramed.Controls.nestedCertificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nestedCertificate
/-- info: 'Solidity.Yul.Compilation.WordBlockFramed.Controls.nested_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nested_success
/-- info: 'Solidity.Yul.Compilation.WordBlockFramed.Controls.endless_fault' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms endless_fault
end Solidity.Yul.Compilation.WordBlockFramed.Controls
