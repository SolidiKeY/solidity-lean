import Solidity.Backend.WorldCalls.Callbacks
import Solidity.Backend.Passes.SourceCallFrame
import Solidity.Lowering.V08.SourceCallable

/-! G42.01 self-call consumers. Equality with self and actual source code
lookup are explicit producer obligations, never substituted for unknown calls.
Source callee-body facts below do not bypass ABI dispatch or frame producers. -/
namespace Solidity.Backend.WorldCalls.SelfCalls
open Solidity.Source Solidity.Roadmap
open Solidity.Lowering.Readonly
variable {E : Env} {Γ : RCtx} {dn : DeclName} {ps rs : List STy}
variable {i : InvocationFrame.Invocation E Γ dn ps rs}

structure SelfPremises (i : InvocationFrame.Invocation E Γ dn ps rs) extends Premises i where
  receiver : i.captured.receiver = i.frame.this
  codeAtSelf : (instanceAt i.global i.captured.receiver : EM E [] _).run (L0 E, i.after.2) =
    (.ok (some i.frame.contract), (L0 E, i.after.2))

def calleeFrame (i : InvocationFrame.Invocation E Γ dn ps rs) : Fr :=
  Solidity.Backend.Passes.SourceCallFrame.childFrame i.captured.receiver i.frame.this i.captured.value
    i.captured.input i.mode i.frame.contract (i.frame.depth + 1)

theorem self_identity (p : SelfPremises i) :
    (identity i).receiver = (identity i).sender := p.receiver

theorem sender_and_mode (p : SelfPremises i) :
    (calleeFrame i).sender = i.frame.this ∧ (calleeFrame i).this = i.frame.this ∧
      (calleeFrame i).static = i.mode := ⟨rfl, p.receiver, rfl⟩

theorem returned_execution (p : SelfPremises i) (key : Identity) (initial machine : Evm.Machine)
    (raw : Except Halt Outcome) (final : St E)
    (step : p.Step key initial raw final (.ok machine 0)) :
    Evm.run p.code.full initial = .ok machine 0 :=
  p.execution _ _ _ _ _ step

/-- Published V08 `Source.callInternal` execution of the callee body (an external
self-call itself goes through `callAddr`/`enterInstance`/`dispatch`, not this).
Selection, initialization, body execution and return extraction remain explicit.
This uses captured typed arguments: agreement with actual ABI-decoded child
arguments is still a P3 obligation, not a dispatch/target adequacy shortcut. -/
theorem callee_body (_p : SelfPremises i) (body : RBody E)
    (selected : i.global.prog.body (i.global.dispatchFn (calleeFrame i).contract i.declaration) = some body)
    (zero : Source.Vals E.layout rs) (fits : rs.reverseAux (ps.reverseAux []) = body.locals)
    (returned : Source.Locals E.layout body.locals) (outputs : Source.RVals E.layout rs)
    (state initialized final : St E)
    (initialization : (zeroVals i.horizon rs : EM E [] _).run (L0 E, state) =
      (.ok zero, (L0 E, initialized)))
    (execution : (runMods i.global {calleeFrame i with checked := true} i.horizon body body.mods
      (fits ▸ zero.onto (i.captured.arguments.onto (L0 E)))).run (L0 E, initialized) =
        (.ok returned, (L0 E, final)))
    (extraction : retVals returned 0 rs = .ok outputs) :
    (callInternal i.global (calleeFrame i) (i.horizon + 1) i.declaration i.captured.arguments rs).run
      (L0 E, state) = (.ok (mkRet rs outputs), (L0 E, final)) :=
  Solidity.Lowering.V08.SourceCallable.complete _ _ _ _ _ _ selected zero fits returned outputs
    state initialized final initialization execution extraction

/-- Current master allows a real zero-value payment CALL to self. It is a
control for that opcode only, not recipient-code or ABI self-call execution. -/
theorem payment_self_zero (machine : Evm.Machine)
    (accepts : machine.accepts machine.self ⟨0, by exact Evm.W_pos⟩ = true) :
    Evm.Instr.step .call {machine with stack := .val ⟨0, Evm.W_pos⟩ :: .val machine.self :: machine.stack} =
      .ok {machine with stack := .val ⟨1, by decide⟩ :: machine.stack} 0 := by
  simp only [Evm.Instr.step, Nat.not_lt_zero, accepts, Bool.true_eq_false, or_self, ↓reduceIte]
  rfl

/-- A real caller source horizon0 still exhausts; no self-body fast path is introduced. -/
theorem callee_exhaustion (_p : SelfPremises i) (state : St E) :
    (callInternal i.global (calleeFrame i) 0 i.declaration i.captured.arguments rs).run (L0 E, state) =
      (.error .timeout, (L0 E, state)) := rfl

end Solidity.Backend.WorldCalls.SelfCalls
