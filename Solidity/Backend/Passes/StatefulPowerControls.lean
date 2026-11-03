import Solidity.Backend.Passes.StatefulPower
import Solidity.Backend.Passes.StatefulCaptureControls

namespace Solidity.Backend.Passes.StatefulPowerControls
open Evm Evm.Memory Backend.Scalar
open Backend.Passes.Controls.Fixture ValueSequenceControls StatefulValueControls

def power : Val C Γ .int := Val.checkedSignedPower negated first
def compiled : CompiledVal 0 (Frag.init Γ) power := (compileVal 0 _ power).get (by decide +kernel)
def answer : PrimTy.int.Denote := ⟨-823543,by decide⟩
def invocation : SignedPowerInvocation minusSeven seven [99] where
  prepareCapacity := by decide +kernel
  powerTestCapacity := by decide +kernel
  powerBodyCapacity := by decide +kernel
  resultTestCapacity := by decide +kernel
  resultBodyCapacity := by decide +kernel

theorem source_result : powerSourceResult minusSeven seven = some answer := by decide +kernel

theorem successful (tail : List Evm.Word) :
    power.evalT σ = .ok answer ∧ ∃ w : Fin W, ReprV .int answer (.val w) ∧
      encodeValue .int answer = BitVec.ofNat 256 w.val ∧
      Evm.run compiled.code {machine with stack := tail} =
        .ok ({machine with stack := tail}.push (.val w)) 0 :=
  StatefulPower.success compiled fixture_repr negated_source first_source source_result tail

theorem component : signedPowerExecute (encodeValue .int minusSeven :: encodeValue .uint seven :: [99]) =
    some (.ok (encodeValue .int answer :: [99])) := by
  rw [invocation.correct,source_result]
  rfl

theorem original_capacities :
    stackBound powerPrepare 3 = true ∧ stackBound checkedUintPow.test 4 = true ∧
    stackBound checkedUintPow.body 4 = true ∧ stackBound powerPostTest 3 = true ∧
    stackBound powerSignBody 3 = true := by
  have applied := StatefulPower.application compiled fixture_repr negated_source first_source
    [] [99] invocation
  exact applied.2.2.2

theorem operand_words (tail : List Evm.Word) :
    ∃ wa wn : Fin W, ReprV .int minusSeven (.val wa) ∧ ReprV .uint seven (.val wn) ∧
      encodeValue .int minusSeven = BitVec.ofNat 256 wa.val ∧
      encodeValue .uint seven = BitVec.ofNat 256 wn.val ∧
      Evm.run (a.code ++ negatedCode.code) {machine with stack := tail} =
        .ok (({machine with stack := tail}.push (.val wn)).push (.val wa)) 0 :=
  StatefulPower.operands negatedCode a fixture_repr negated_source first_source tail

/-- Complete unchanged machine observation before the pure power application. -/
theorem ordered_memory : [3,2,1,0,16,17,18,20,21].mapM
    (fun n => match machine.mem n with | .val w => some w.val | _ => none) =
      some [0,16,16,20,2,7,9,1,4] := by decide +kernel

/-- Full post-run vector follows the actual typed success, without computing
an expanded helper or selecting only a convenient cell. -/
theorem ordered_after_power (tail : List Evm.Word) :
    [3,2,1,0,16,17,18,20,21].mapM (fun n =>
      match Evm.run compiled.code {machine with stack := tail} with
      | .ok out _ => match out.mem n with | .val w => some w.val | _ => none
      | _ => none) = some [0,16,16,20,2,7,9,1,4] := by
  obtain ⟨_,w,_,_,ht⟩ := successful tail
  rw [ht]
  exact ordered_memory

def afterAnswer : PrimTy.int.Denote := ⟨16777216,by decide⟩

theorem after_source : power.evalT CaptureControls.afterCapture = .ok afterAnswer :=
  StatefulPower.source_success (a := ⟨-8,by decide⟩) (n := ⟨8,rfl⟩)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by decide +kernel)

/-- ACTUAL preceding capture supplies the selected full represented input.
No post-capture map is replaced or inferred from a desired power result. -/
theorem reached_capture : ∃ (mb : Nat → Fin W) (mid : Machine) (w : Fin W),
    Evm.run StatefulCaptureControls.captureCompiled.code machine = .ok mid 0 ∧
    MappedOutput (.memory StatefulCaptureControls.captureCompiled) 1 6 base σ machine
      CaptureControls.afterCapture mid mb ∧
    ReprV .int afterAnswer (.val w) ∧ encodeValue .int afterAnswer = BitVec.ofNat 256 w.val ∧
    ∀ tail : List Evm.Word, Evm.run compiled.code {mid with stack := tail} =
      .ok ({mid with stack := tail}.push (.val w)) 0 := by
  obtain ⟨mb,ob,mid,final,oldword,ha,_,_,ma,_,_,_,_,_,_⟩ := StatefulCaptureControls.reached_application
  obtain ⟨word,hw,ht⟩ := value_success_tail compiled ma.1 after_source []
  obtain ⟨w,ew,he⟩ := ClosedValues.represented_word hw
  subst word
  refine ⟨mb,mid,w,ha,ma,hw,he,?_⟩
  intro tail
  obtain ⟨other,ho,hr⟩ := value_success_tail compiled ma.1 after_source tail
  obtain ⟨ow,eo,heo⟩ := ClosedValues.represented_word ho
  have bits : BitVec.ofNat 256 ow.val = BitVec.ofNat 256 w.val := heo.symm.trans he
  have vals := congrArg BitVec.toNat bits
  simp only [BitVec.toNat_ofNat] at vals
  rw [Nat.mod_eq_of_lt (show ow.val < 2^256 from ow.isLt),
    Nat.mod_eq_of_lt (show w.val < 2^256 from w.isLt)] at vals
  have same : other = .val w := eo.trans (congrArg Word.val (Fin.ext vals))
  simpa only [same] using hr

theorem skipped_capture_wrong : answer ≠ afterAnswer := by decide +kernel

def overflow : Val C Γ .int := Val.checkedSignedPower StatefulValueNegatives.minimumOperand first
def overflowCompiled : CompiledVal 0 (Frag.init Γ) overflow := (compileVal 0 _ overflow).get (by decide +kernel)
def overflowInvocation : SignedPowerInvocation minimumInt seven [99] where
  prepareCapacity := invocation.prepareCapacity
  powerTestCapacity := invocation.powerTestCapacity
  powerBodyCapacity := invocation.powerBodyCapacity
  resultTestCapacity := invocation.resultTestCapacity
  resultBodyCapacity := invocation.resultBodyCapacity

theorem overflow_result : powerSourceResult minimumInt seven = none := by decide +kernel

theorem overflow_failure (tail : List Evm.Word) :
    overflow.evalT StatefulValueNegatives.minimumSource = .error .revert ∧
      Evm.run overflowCompiled.code {StatefulValueNegatives.minimumMachine with stack := tail} = .revert :=
  StatefulPower.failure overflowCompiled StatefulValueNegatives.minimum_input
    StatefulValueNegatives.minimum_operand_source (by with_unfolding_all rfl) overflow_result tail

theorem overflow_component : signedPowerExecute
    (encodeValue .int minimumInt :: encodeValue .uint seven :: [99]) = some (.error overflowFailure) := by
  rw [overflowInvocation.correct,overflow_result]
  rfl

/-- Actual earlier assignment, then typed helper failure; saved tails arbitrary. -/
theorem reached_overflow (tail : List Evm.Word) :
    Evm.run (StatefulValueNegatives.minimumProgramCode.code ++ overflowCompiled.code)
      {machine with stack := tail} = .revert := by
  rw [Evm.run_append_ok (StatefulValueNegatives.minimum_reached tail).2]
  exact (overflow_failure tail).2

theorem ignored_sign : Backend.Scalar.run checkedUintPow.body [7,7,99] = some [823543,99] ∧
    (823543 : Backend.Scalar.Word) ≠ encodeValue .int answer := by decide +kernel

theorem capacity_refused : stackBound powerPrepare 1025 = false := by decide +kernel

theorem actual_bytes : Backend.encode checkedUintPow.body = [0x0a] ∧
    Backend.encode powerSignBody = [0x81,0x7f] ++ List.replicate 31 0 ++
      [2,0x02,0x7f] ++ List.replicate 31 0 ++ [1,0x03,0x02,0x90,0x50] := by decide +kernel

end Solidity.Backend.Passes.StatefulPowerControls
