import Solidity.Backend.WorldCalls.Callbacks
import Solidity.Backend.Passes.SourceCallControls

/-! Inhabited interface test using actual current Evm.Machine payment CALL.
The marker protocol is control-only, not the future G37 frame encoding.
Its raw observation is status1/empty payment payload, not general RETURNDATA.
No payment opcode is promoted to execution of recipient callback code. -/
namespace Solidity.Backend.WorldCalls.PaymentControl
open Solidity.Source Solidity.Source.SemanticsExamples
open Solidity.Lowering.Readonly
open Solidity.Backend.Passes.SourceCallControls

def origin : InvocationFrame.Invocation EB [.address false] ⟨none, "I"⟩ [] [] where
  global := GB answerOnly
  frame := FC
  horizon := 6
  declaration := dPing
  declared := by rfl
  signature := dPing_sig
  target := target
  value := lit 0
  arguments := .nil
  before := before
  after := before
  captured := captured
  execution := capture_nonself

def sourceFinal : St EB := {sB with events :=
  [.call ext (word 0) (selOf "ping()") false, .answer (.success []) none]}
theorem source_raw : origin.RawAt (.ok (.success [])) sourceFinal := by rfl

def marker : Evm.Word := .val ⟨7, by decide⟩
def one : Evm.Word := .val ⟨1, by decide⟩
def address : Fin Evm.W := ⟨9, by decide⟩
def code : Code := ⟨[.push marker], [.push (.val address), .push (.val ⟨0, by decide⟩), .call], [.pop, .pop]⟩
def initial : Evm.Machine := Evm.Machine.init (fun _ => 0) ⟨thisC.val, Nat.lt_trans thisC.isLt (by decide)⟩
def pushed : Evm.Machine := {initial with stack := [marker]}
def returned : Evm.Machine := {pushed with stack := [one, marker], bal := Evm.pay initial.bal initial.self address 0}
def final : Evm.Machine := {returned with stack := []}

def view (machine : Evm.Machine) : List Identity :=
  if machine.stack.any (fun item => match item with | .val value => value.val == 7 | _ => false)
  then [identity origin] else []

def frame : ReturnedFrame code view (identity origin) initial final where
  pushed := pushed
  returned := returned
  pushRun := by rfl
  bodyRun := by rfl
  popRun := by rfl
  pushView := by rfl
  bodyView := by rfl
  popView := by rfl

theorem executed : Evm.run code.full initial = .ok final 0 := by
  unfold Code.full
  rw [Evm.run_append_ok frame.pushRun, Evm.run_append_ok frame.bodyRun]
  exact frame.popRun

/-- Explicit restricted payment status observation, with actual emitted runs. -/
def Observed (key : Identity) (machine : Evm.Machine) (out : Evm.Out)
    (raw : Except Halt Solidity.Roadmap.Outcome) : Prop :=
  key = identity origin ∧ ∃ entered returned exited,
    Evm.run code.push machine = .ok entered 0 ∧
    Evm.run code.body entered = .ok returned 0 ∧ returned.stack = one :: entered.stack ∧
    Evm.run code.pop returned = .ok exited 0 ∧ out = .ok exited 0 ∧ raw = .ok (.success [])

def Step (key : Identity) (machine : Evm.Machine) (raw : Except Halt Solidity.Roadmap.Outcome)
    (state : St EB) (out : Evm.Out) : Prop :=
  key = identity origin ∧ machine = initial ∧ raw = .ok (.success []) ∧
    state = sourceFinal ∧ out = .ok final 0 ∧ Evm.run code.full machine = out

def premises : Premises origin where
  code := code
  Observed := Observed
  Step := Step
  bound _ _ _ _ _ h := h.1
  execution _ _ _ _ _ h := h.2.2.2.2.2
  observed key machine raw state out h := by
    rw [h.1, h.2.1, h.2.2.1, h.2.2.2.2.1]
    exact ⟨rfl, pushed, returned, final, frame.pushRun, frame.bodyRun, rfl, frame.popRun, rfl, rfl⟩
  sourceRaw key machine raw state out h := by
    rw [h.2.2.1, h.2.2.2.1]
    exact source_raw
  p2History key machine raw state out h := by
    rw [h.2.2.2.1]
    exact .start _ _

theorem inhabited : premises.Step (identity origin) initial (.ok (.success [])) sourceFinal (.ok final 0) :=
  ⟨rfl, rfl, rfl, rfl, rfl, executed⟩

theorem restored : view final = view initial := Callbacks.restore frame

theorem spoofed_mode_refused :
    ¬ premises.Step {identity origin with static := true} initial (.ok (.success [])) sourceFinal (.ok final 0) := by
  intro h
  have eq := congrArg Identity.static (premises.bound _ _ _ _ _ h)
  change true = false at eq
  cases eq

theorem unrelated_raw_refused :
    ¬ premises.Step (identity origin) initial (.ok (.success [1])) sourceFinal (.ok final 0) := by
  intro h
  have eq := h.2.2.1
  cases eq

/-- Real fetched CALL evidence is available; general RETURNDATA is not. -/
def fetched_call : FetchedCall code.full initial where
  pc := 3
  reached := {pushed with stack := [.val ⟨0, by decide⟩, .val address, marker]}
  result := .ok returned 0
  instruction := by rfl
  prefixRun := by rfl
  execute := by rfl

theorem caller_address_bound : initial.self.val = (identity origin).sender.val := rfl
theorem receiver_address_bound : address.val = (identity origin).receiver.val := rfl

end Solidity.Backend.WorldCalls.PaymentControl
