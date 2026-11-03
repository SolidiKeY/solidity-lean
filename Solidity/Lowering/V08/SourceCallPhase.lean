import Solidity.Source.Eval

/-!
# Same-invocation source raw-return phase

This adapter executes the published callAddr once through its actual sub frame.
It preserves the complete Outcome until the declared-return decoder runs. It is
not a Source-to-Core StateRepr or frame relation.
The caller must first execute target/value/arguments, encoding and the extCall
code-presence guard; this interface starts at that reached point.
-/
namespace Solidity.Lowering.V08.SourceCallPhase
open Solidity Source

/-- The actual reached source caller, not an invented Core frame. -/
structure Point (E : Source.Env) (Γ : RCtx) where
  frame : Source.Fr
  locals : Source.Locals E.layout Γ
  state : Source.St E

/-- Exact raw request metadata at that point, before declared-return decoding. -/
structure Request where
  receiver : Roadmap.Address
  value : Roadmap.Word
  input : Roadmap.Bytes
  requestedStatic : Bool

def effectiveStatic (frame : Source.Fr) (request : Request) : Bool :=
  request.requestedStatic || frame.static

/-- The actual source call subcomputation. In particular errors/timeouts have
not been converted into completed revert Outcomes. -/
def raw {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (horizon : Nat) (request : Request) : EM E Γ Roadmap.Outcome := do
  let (out, _) ← EM.sub (Source.L0 E) (Source.callAddr global frame horizon
    request.receiver request.value request.input request.requestedStatic)
  pure out

/-- A snapshot of that same raw result and its actual reached state, before
extReturn, any caller continuation, catch selection or binder discard. -/
def capture {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (horizon : Nat) (request : Request) : EM E Γ (Roadmap.Outcome × Source.St E) := do
  let out ← raw global frame horizon request
  return (out, ← EM.st)

/-- This equation exposes the actual call, not an assumed invocation oracle. -/
theorem raw_run {E : Source.Env} {Γ : RCtx} (global : Glob E)
    (point : Point E Γ) (horizon : Nat) (request : Request) :
    (raw global point.frame horizon request).run (point.locals, point.state) =
      match (Source.callAddr global point.frame horizon request.receiver request.value
        request.input request.requestedStatic).run (Source.L0 E, point.state) with
      | (.ok out, (_, final)) => (.ok out, (point.locals, final))
      | (.error halt, (_, final)) => (.error halt, (point.locals, final)) := by
  simp only [raw, EM.sub, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind]
  cases h : (Source.callAddr global point.frame horizon request.receiver request.value
    request.input request.requestedStatic).run (Source.L0 E, point.state) with
  | mk result final =>
      simp only [ExceptT.run] at h
      rw [h]
      cases final
      cases result <;> rfl

/-- Every actual raw outcome or halt retains the caller's typed locals. No
heap/world immutability is claimed: final state comes from the real operation. -/
theorem caller_locals {E : Source.Env} {Γ : RCtx} (global : Glob E)
    (point : Point E Γ) (horizon : Nat) (request : Request) :
    ((raw global point.frame horizon request).run (point.locals, point.state)).2.1 =
      point.locals := by
  rw [raw_run]
  cases h : (Source.callAddr global point.frame horizon request.receiver request.value
    request.input request.requestedStatic).run (Source.L0 E, point.state) with
  | mk result final => cases result <;> rfl

/-- Raw bytes are captured only on a completed outcome. A halt remains a halt. -/
theorem capture_run {E : Source.Env} {Γ : RCtx} (global : Glob E)
    (point : Point E Γ) (horizon : Nat) (request : Request) :
    (capture global point.frame horizon request).run (point.locals, point.state) =
      match (raw global point.frame horizon request).run (point.locals, point.state) with
      | (.ok out, (locals, final)) => (.ok (out, final), (locals, final))
      | (.error halt, final) => (.error halt, final) := by
  simp only [capture, EM.st, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, ExceptT.lift]
  cases h : (raw global point.frame horizon request).run (point.locals, point.state) with
  | mk result final =>
      simp only [ExceptT.run] at h
      rw [h]
      cases final
      cases result <;> rfl

/-- The declared types are supplied BEFORE projection/discard of caller binders.
This is the existing extReturn, not a replacement return decoder. -/
def consume {E : Source.Env} {Γ : RCtx} (declared : List STy)
    (out : Roadmap.Outcome) : EM E Γ (RVal E.layout (STy.ret declared)) :=
  Source.extReturn declared out

/-- Exact composition with the existing caller decoder, with no catch around it. -/
theorem consume_run {E : Source.Env} {Γ : RCtx} (global : Glob E) (frame : Fr)
    (horizon : Nat) (request : Request) (declared : List STy)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    ((do let out ← raw global frame horizon request; consume declared out) : EM E Γ _).run
      (locals, state) =
      match (raw global frame horizon request).run (locals,state) with
      | (.ok out, final) => (consume declared out : EM E Γ _).run final
      | (.error halt, final) => (.error halt, final) := by
  simp only [bind, ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind]
  cases h : raw global frame horizon request (locals,state) with
  | mk result final => cases result <;> rfl

/-- A successful callee with a short declared result fails in the caller phase;
it is never rewritten into a callee revert for a try/catch to intercept. -/
theorem short_success {E : Source.Env} {Γ : RCtx} (declared : List STy)
    (bytes : Roadmap.Bytes) (short : bytes.length < 32 * declared.length)
    (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (consume declared (.success bytes) : EM E Γ _).run (locals, state) =
      (.error (.revert []), (locals, state)) := by
  simp only [consume, Source.extReturn, Source.reraise, EM.halt, bind, pure, ExceptT.bind, ExceptT.pure, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure]
  rw [if_pos short]
  rfl

/-- A completed callee revert keeps the full ordered payload at this boundary. -/
theorem callee_revert {E : Source.Env} {Γ : RCtx} (declared : List STy)
    (bytes : Roadmap.Bytes) (locals : Source.Locals E.layout Γ) (state : Source.St E) :
    (consume declared (.revert bytes) : EM E Γ _).run (locals, state) =
      (.error (.revert bytes), (locals, state)) := rfl

/-- Link to the actual resolved external-call constructor: receiver, value,
arguments, encoding and code-presence guard precede raw capture, while declared
return validation follows it. This is an equation of the existing evaluator. -/
theorem external_phase {E : Source.Env} {Γ : RCtx} {dn : DeclName}
    {ps rs : List STy} (global : Glob E) (frame : Fr) (horizon : Nat)
    (target : RExpr E Γ (.contract dn)) (declaration : Decl)
    (signature : declaration.fnSig E = some (ps, rs))
    (value : RExpr E Γ (.int IntTy.u256)) (arguments : RConvArgs E Γ ps) :
    Source.evalE global frame (horizon + 1)
      (.extCall target declaration signature value arguments) = (do
        let a ← match ← Source.getV (← Source.evalE global frame horizon target) with
          | .contract x => pure x
        let v ← match ← Source.getV (← Source.evalE global frame horizon value) with
          | .int x _ => pure x
        let vs ← Source.evalConvArgs global frame horizon arguments
        let params := match declaration.fnSig E with | some (params, _) => params | none => []
        let input := global.selector (Source.sigOf E.layout declaration.name params) ++
          (← Source.encodeVals frame horizon false vs.toR)
        if (← Source.instanceAt global a).isNone && !global.hasCode (← EM.st).events a then
          EM.halt (.revert [])
        let out ← raw global frame horizon
          ⟨a, ⟨v.toNat % 2 ^ 256, Nat.mod_lt _ (by decide +kernel)⟩, input,
            declaration.fnMut == some .view || declaration.fnMut == some .pure⟩
        consume rs out) := by
  simp only [raw, consume, bind_assoc, pure_bind]
  rfl

theorem inherited_static (frame : Fr) (request : Request) (active : frame.static = true) :
    effectiveStatic frame request = true := by
  simp only [effectiveStatic, active, Bool.or_true]

theorem requested_static (frame : Fr) (request : Request)
    (active : request.requestedStatic = true) : effectiveStatic frame request = true := by
  simp only [effectiveStatic, active, Bool.true_or]

end Solidity.Lowering.V08.SourceCallPhase
