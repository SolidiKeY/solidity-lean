import Solidity.Yul.World.PhysicalCallOutput

/-! Typed consumer port carrying the actual physical state, never an operation
replay. A port body/answer is not by itself raw-callee reachability. -/
namespace Solidity.Yul.World.PhysicalCompletion
open Solidity.Source
open Solidity.Roadmap (Address Word Bytes Outcome)
open Solidity.Yul.Views

/-- Actual boundary inputs include code target separately from storage frame.
None is producer/admission refusal before a completed invocation exists. Halts
retain the full returned carrier and ordered suffix. -/
abbrev Invoke (E : Env) (Γ : RCtx) :=
  ObservedEffects E.layout E.lay E.lay → ResidualFrame → CallKind → Address → Word → Bytes → Carrier E Γ →
    Option ((Except Halt Outcome × Carrier E Γ) × List Observation)

def completeReturned {E Γ} (s : EMState E Γ) (b : BoolEncodingJournal)
    (o : ObservedEffects E.layout E.lay E.lay) (frame : ResidualFrame)
    (answer : (Except Halt Outcome × Carrier E Γ) × List Observation) : Except Halt Outcome × Result E Γ :=
  finishStep s b o frame
    (((answer.1.1.map (fun _=>()),answer.1.2.1.1),answer.1.2.1.2),answer.1.2.2) answer.2
    (match answer.1.1 with | .ok out=>out | .error _=>.success [])

/-- Input loading/preflight precede invocation. No failure after invocation can
erase its carrier. Output writeback is separately bounded by copyOutput. -/
def call {E Γ} (invoke : Invoke E Γ) (s : EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects E.layout E.lay E.lay) (_shared : o.effects.execution=s.2.ex) (m : ByteView) (parent : CallFrame) (kind : CallKind)
    (callee : Address) (gas value inputOffset inputSize : Word) : Option (Except Halt Outcome × Result E Γ) :=
  if callPreflight parent kind value then do
    let input ← PhysicalHeapPort.port.load m inputOffset inputSize
    let frame := enter s r parent kind callee value input
    let answer ← invoke o frame kind callee gas input ⟨⟨s,r⟩,b⟩
    pure (completeReturned s b o frame answer)
  else none

theorem call_exact {E Γ} (invoke : Invoke E Γ) (s : EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects E.layout E.lay E.lay) (shared : o.effects.execution=s.2.ex) (m : ByteView) (parent : CallFrame) (kind : CallKind)
    (callee : Address) (gas value inputOffset inputSize : Word) (input : Bytes) (answer)
    (allowed : callPreflight parent kind value=true)
    (loaded : PhysicalHeapPort.port.load m inputOffset inputSize=some input)
    (ran : invoke o (enter s r parent kind callee value input) kind callee gas input ⟨⟨s,r⟩,b⟩=some answer) :
    call invoke s r b o shared m parent kind callee gas value inputOffset inputSize =
      some (completeReturned s b o (enter s r parent kind callee value input) answer) := by
  simp only [call,allowed,if_true,loaded,ran,bind,Option.bind_some,pure]

theorem call_static_value_refusal {E Γ} (invoke : Invoke E Γ) (s : EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects E.layout E.lay E.lay) (shared : o.effects.execution=s.2.ex) (m : ByteView) (parent : CallFrame)
    (callee : Address) (gas value inputOffset inputSize : Word)
    (static : parent.static=true) (nonzero : value.val≠0) :
    call invoke s r b o shared m parent .call callee gas value inputOffset inputSize=none := by
  simp only [call,callPreflight,static,if_true,nonzero,decide_false,Bool.false_eq_true,if_false]

/-- Concrete checked physical slot body for the port. The configured return
bytes are explicit boundary data; no source RETURN/code/gas theorem is assumed.
The current account comes from the actual childContext, never the code target. -/
def slotInvoke {E Γ}
    (ps ts : (a : Address) → List (ScalarPath E.layout (E.lay a)))
    (bank : Bool) (slot raw : Word) (data : Bytes) (contract : String) (depth : Nat) : Invoke E Γ :=
  fun _ frame _ _ _ _ carrier =>
    (representedFrameWrite? ps ts (PhysicalSlotPort.sourceFrame frame.source contract true depth)
      bank slot raw carrier.2 carrier.1.1 carrier.1.2).map (fun result =>
      ((result.1.1.1.map (fun _=>Outcome.success data),⟨⟨result.1.1.2,result.1.2⟩,result.2⟩),[]))

/-- Normal local rule over the actual full-carrier call adapter. Its explicit
ran premise is a producer equality, not a reachability/adequacy theorem. -/
theorem call_normal_rule {E Γ} (invoke : Invoke E Γ) (s : EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects E.layout E.lay E.lay) (shared : o.effects.execution=s.2.ex) (m : ByteView) (parent : CallFrame) (kind : CallKind)
    (callee : Address) (gas value inputOffset inputSize : Word) (input : Bytes) (c : Carrier E Γ)
    (xs : List Observation) (out : Outcome)
    (allowed : callPreflight parent kind value=true)
    (loaded : PhysicalHeapPort.port.load m inputOffset inputSize=some input)
    (ran : invoke o (enter s r parent kind callee value input) kind callee gas input ⟨⟨s,r⟩,b⟩=some ((.ok out,c),xs)) :
    call invoke s r b o shared m parent kind callee gas value inputOffset inputSize =
      some (.ok out,finish s b o (enter s r parent kind callee value input) c xs out) :=
  call_exact invoke s r b o shared m parent kind callee gas value inputOffset inputSize input _ allowed loaded ran

theorem completeReturned_shared {E Γ} (s : EMState E Γ) b o f
    (answer : (Except Halt Outcome × Carrier E Γ) × List Observation) :
    (completeReturned s b o f answer).2.2.effects.execution =
      (completeReturned s b o f answer).2.1.1.1.2.ex := by
  rcases answer with ⟨⟨status,c⟩,xs⟩
  cases status with
  | ok out => rfl
  | error h => cases h <;> rfl

/-- Non-revert source halt rule retains the exact dirty physical carrier and
ordered pending observations. It is not a successful or reverted EVM call. -/
theorem call_stuck_rule {E Γ} (invoke : Invoke E Γ) (s : EMState E Γ)
    (r : ResidualJournal complementCarrierOwnership) (b : BoolEncodingJournal)
    (o : ObservedEffects E.layout E.lay E.lay) (shared : o.effects.execution=s.2.ex) (m : ByteView) (parent : CallFrame) (kind : CallKind)
    (callee : Address) (gas value inputOffset inputSize : Word) (input : Bytes) (c : Carrier E Γ)
    (xs : List Observation) (why : String)
    (allowed : callPreflight parent kind value=true)
    (loaded : PhysicalHeapPort.port.load m inputOffset inputSize=some input)
    (ran : invoke o (enter s r parent kind callee value input) kind callee gas input ⟨⟨s,r⟩,b⟩=some ((.error (.stuck why),c),xs)) :
    call invoke s r b o shared m parent kind callee gas value inputOffset inputSize =
      some (.error (.stuck why),pending o c xs) :=
  call_exact invoke s r b o shared m parent kind callee gas value inputOffset inputSize input _ allowed loaded ran

end Solidity.Yul.World.PhysicalCompletion
