import Solidity.Backend.WorldCalls.SelfCalls
import Solidity.Backend.WorldCalls.PaymentControl

/-! Actual source self-call identity/code controls and existing EVM self-CALL
control. Source cb writes are retained; this is not a joint compiler simulation
nor a replacement of an unknown receiver by self. -/
namespace Solidity.Backend.WorldCalls.SelfControls
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Lowering.Readonly

def dCb : Decl := ⟨.function, "cb", some "C", false, fn "cb" .nil .nil⟩
theorem declared : EB.declOf .function ⟨some "C", "cb"⟩ = some dCb := by rfl
theorem signature : dCb.fnSig EB = some ([], []) := by rfl

def origin : InvocationFrame.Invocation EB [] ⟨none, "C"⟩ [] [] where
  global := GB answerOnly
  frame := FC
  horizon := 30
  declaration := dCb
  declared := declared
  signature := signature
  target := .this "C"
  value := lit 0
  arguments := .nil
  before := (L0 EB, sB)
  after := (L0 EB, sB)
  captured := ⟨thisC, word 0, .nil, selOf "cb()"⟩
  execution := by rfl

theorem receiver_self : origin.captured.receiver = origin.frame.this := rfl
theorem actual_code : (instanceAt origin.global origin.captured.receiver : EM EB [] _).run
    (L0 EB, origin.after.2) = (.ok (some origin.frame.contract), (L0 EB, origin.after.2)) := by rfl

def observed : Option (Solidity.Roadmap.Bytes × Option Int) :=
  match (callAddr origin.global origin.frame origin.horizon origin.captured.receiver origin.captured.value
    origin.captured.input origin.requested).run (L0 EB, origin.after.2) with
  | (.ok (.success data), (_, final)) => some (data, readX final)
  | _ => none

theorem ordinary_self_mutation : observed = some ([], some 4) := by decide +kernel

theorem unknown_receiver_not_self :
    PaymentControl.origin.captured.receiver ≠ PaymentControl.origin.frame.this := by decide +kernel

theorem actual_machine_self_payment :
    Evm.Instr.step .call {PaymentControl.initial with stack := (.val ⟨0, Evm.W_pos⟩ :: .val PaymentControl.initial.self :: PaymentControl.initial.stack)} =
      .ok {PaymentControl.initial with stack := .val ⟨1, by decide⟩ :: PaymentControl.initial.stack} 0 :=
  SelfCalls.payment_self_zero _ rfl

def staticObserved : Option (Solidity.Roadmap.Bytes × Option Int) :=
  match (callAddr origin.global {origin.frame with static := true} origin.horizon origin.captured.receiver
    origin.captured.value origin.captured.input origin.requested).run (L0 EB, origin.after.2) with
  | (.ok (.revert data), (_, final)) => some (data, readX final)
  | _ => none

theorem inherited_static_write_refused : staticObserved = some ([], some 3) := by decide +kernel

end Solidity.Backend.WorldCalls.SelfControls
