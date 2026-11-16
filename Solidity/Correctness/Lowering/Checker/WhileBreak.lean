import Solidity.Correctness.Lowering.Checker.IntrinsicProbe
import Solidity.Semantics.RunFuel
import Solidity.Correctness.Lowering.Checker.SourceAssociation

/-! Semantic experiment on the actual intrinsic output. A successful bounded
replay is lifted to the unbounded model using the existing approximation
lemma. The numeric replay bound is neither a source horizon equation nor a
general loop termination theorem. -/
namespace Solidity.Correctness.Lowering.Checker.WhileBreak

open IntrinsicProbe
open Solidity.Lowering.V07

/-- Generic model bridge: a successful finite replay is the actual model
result. This uses an existing proved approximation, not a new adequacy premise. -/
theorem replay_sound {C : Contract} {Γ Δ : Ctx} (P : Prog C Γ Δ) (n : Nat)
    (target : State C Γ) (out : Out C target.H Δ)
    (replay : P.runF n target = .ok out) : P.run target = .ok out := by
  have approximation : TRes.Approx (P.runF n target) (P.run target) :=
    Prog.runF_approx n P target
  rw [replay] at approximation
  exact (approximation.eq (by intro impossible; cases impossible)).symm

/-- A concrete initial model state for the true/false probe paths. -/
def start (choice : Bool) : State C Γ :=
  ((State.init C).push (t := .val .bool) choice).push (t := .val .bool) false

/-- Does the concrete replay finish on both Boolean RHS paths? -/
theorem actual_replay_normal (choice : Bool) :
    (Prog.runFC 2 actual.program.2 (start choice)).isOk = true := by
  cases choice <;> decide +kernel

/-- Read only caller locals from the actual extended target context. -/
def observe (out : Out C [] actual.program.1) : Bool × Bool :=
  (TEnv.get (.there .here) out.st.env, TEnv.get (.there (.there .here)) out.st.env)

/-- Observe only successful results. Failure remains `none`; no error is
identified with a successful value. -/
def successValue {α β : Type} (observer : α → β) : TRes α → Option β
  | .ok out => some (observer out)
  | .error _ => none

/-- Both paths preserve the RHS and perform the assignment to the caller. -/
theorem actual_replay_observation (choice : Bool) :
    successValue observe (Prog.runFC 2 actual.program.2 (start choice)) = some (choice, choice) := by
  cases choice <;> decide +kernel

/-- A generic observation bridge, using the existing proved approximation.
A successful replay is computational evidence, not a gas/horizon premise. -/
theorem replay_observation_sound {C : Contract} {Γ Δ : Ctx} {α : Type}
    (P : Prog C Γ Δ) (n : Nat) (target : State C Γ)
    (observer : Out C target.H Δ → α) (value : α)
    (replay : successValue observer (Prog.runFC n P target) = some value) :
    successValue observer (P.run target) = some value := by
  have approximation : TRes.Approx (Prog.runFC n P target) (P.run target) := by
    rw [← Prog.runF_eq]
    exact Prog.runF_approx n P target
  rcases approximation with divergence | equal
  · rw [divergence] at replay
    cases replay
  · rw [equal] at replay
    exact replay

/-- The observation concerns the actual unbounded model execution. -/
theorem actual_observation (choice : Bool) :
    successValue observe (actual.program.2.run (start choice)) = some (choice, choice) := by
  exact replay_observation_sound actual.program.2 2 (start choice) observe
    (choice, choice) (actual_replay_observation choice)

/-- Canonical map for this concrete pair of Boolean caller locals. -/
def mapping : ContextMap [.bool, .bool] Γ :=
  (ContextMap.empty.cons .bool (.val .bool)).cons .bool (.val .bool)

/-- Initial value relation from the existing G19 interface. -/
def BoolRel {E : Source.Env} {H : HTy} :
    (τ : Source.STy) → (u : LTy) → Source.Val E.layout τ → u.TDenote C H → Prop
  | .bool, .val .bool, v, b => v = .bool b
  | _, _, _, _ => False

/-- Caller values paired with the concrete model start; no new source carrier. -/
def sourceLocals {E : Source.Env} (choice : Bool) : Source.Locals E.layout [.bool, .bool] :=
  .cons (.bool false) (.cons (.bool choice) .nil)

/-- Initial alignment for the concrete probe. -/
theorem initial {E : Source.Env} (choice : Bool) :
    mapping.Related (BoolRel (E := E)) (sourceLocals choice) (start choice).env := by
  intro τ i
  cases i with
  | here => rfl
  | there i => cases i with
    | here => rfl
    | there i => nomatch i

/-- Bare-G19-source semantic observation, reusing G19.correct rather
than copying its source proof. `G` ranges over both pipelines; the target is
exactly the actual quoted intrinsic output. This is a first-leaf experiment,
not the soundness theorem for arbitrary accepted triples, state association,
full journal/storage agreement, physical gas or general termination. -/
theorem prototype_sound {E : Source.Env} (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (ph : Option (Source.Ph E)) (st : Source.St E) (choice : Bool) :
    (Source.execS G F (fuel + 3) nps ph (R := []) (M := false)
      (.whileLoop (l := false) (u := false)
        (.assign (.local (.here : Source.Idx [.bool, .bool] .bool)) (.local (.there .here)))
        .brk) (sourceLocals choice)).run (.nil, st) =
      (.ok (Source.Out.normal ((sourceLocals choice).set .here (.bool choice))), (.nil, st)) ∧
    successValue observe (actual.program.2.run (start choice)) = some (choice, choice) := by
  have result := Solidity.Lowering.G19.AssignmentWhileBreak.correct G F fuel nps ph
    (returns := []) (M := false) (l := false) (u := false)
    (sourceLocals choice, st) (start choice) mapping (BoolRel (E := E)) (initial choice)
    (fun _ _ h => h) .here (.there .here) rfl rfl rfl rfl
  exact ⟨result.1, actual_observation choice⟩

/-- Bare-source gate: kernel raw acceptance and the actual intrinsic
semantic observation are required together. This is not universal soundness
for the larger syntactic family recognized by `checkRaw`. -/
theorem prototype_gate {E : Source.Env} (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (ph : Option (Source.Ph E)) (st : Source.St E) (choice : Bool) :
    RawProbe.checkRaw RawProbe.input RawProbe.actual.raw 1 = true ∧
    (Source.execS G F (fuel + 3) nps ph (R := []) (M := false)
      (.whileLoop (l := false) (u := false)
        (.assign (.local (.here : Source.Idx [.bool, .bool] .bool)) (.local (.there .here)))
        .brk) (sourceLocals choice)).run (.nil, st) =
      (.ok (Source.Out.normal ((sourceLocals choice).set .here (.bool choice))), (.nil, st)) ∧
    successValue observe (actual.program.2.run (start choice)) = some (choice, choice) := by
  exact ⟨RawProbe.accepts_actual, prototype_sound G F fuel nps ph st choice⟩

/-- The resolved input paired with RawProbe.input by the concrete leaf
association below. The pairing is a syntactic obligation, not an assumed
execution or preservation fact. -/
def resolvedInput (E : Source.Env) :
    Source.RStmt E [] false .body [.bool, .bool] [.bool, .bool] := SourceAssociation.resolved E

/-- Exact unfrozen association specification for the one concrete leaf.
All equalities are obligations on an accepted triple, not certificate fields
or semantic premises. The program is the actual captured intrinsic output;
placement of the supplied scoped statements is checked separately. No claim
is made that a checker implementing this relation is supplied here. -/
def ConcreteAssociation {E : Source.Env} (m : ContextMap [.bool, .bool] Γ)
    (input : Input E [] false .body [.bool, .bool]) (output : Output C Γ)
    (cert : Certificate) : Prop :=
  m = mapping ∧
  input.raw = RawProbe.input ∧ input.resolved = resolvedInput E ∧
  input.returnSlots = none ∧ input.scope = RawProbe.scope ∧
  input.before.locals = (RawProbe.inputLocals, 1) ∧ input.before.memo = ({} : CallMemo) ∧
  output.raw = RawProbe.actual.raw ∧
  output.afterLower.locals = (RawProbe.actual.locals, RawProbe.actual.counter) ∧
  output.afterLower.memo = RawProbe.actual.memo ∧
  output.elabScope = RawProbe.scope ∧ output.beforeElab = output.afterLower ∧
  output.afterElab.locals = (IntrinsicProbe.actual.locals, IntrinsicProbe.actual.counter) ∧
  output.afterElab.memo = IntrinsicProbe.actual.memo ∧
  output.names = (ECtx.toNCtx RawProbe.inputLocals).names ∧
  output.program = IntrinsicProbe.actual.program ∧
  SProg.chain output.names Γ output.elaborated = .ok output.program ∧
  cert.destination = "i" ∧ cert.rhs = "a" ∧ cert.breakFlag = "brk1" ∧
  cert.counter = 1 ∧ cert.sourceOffset = 4 ∧ cert.destinationPosition = 0 ∧ cert.rhsPosition = 1

/-- Full desired association/semantic/state contract for the concrete first
leaf. This is a proposition to prove of a total syntax-directed checker,
not a proof, implemented checker, interface freeze or whole-language claim.
Unlike the generic semantic component alone, this also ties both states,
raw input, resolved input, certificate and actual intrinsic output together.
The supplied intermediate statements must place into that actual program;
identity with the unquoted actual intermediate SProg is not claimed.
Unsupported triples remain coverage gaps. Producer execution itself stays outside the kernel trust
boundary: the quoted outputs are what the checker must validate. -/
def ConcreteSoundnessStatement {E : Source.Env}
    (check : Solidity.Correctness.Lowering.Checker.Checker E [] false .body
      [.bool, .bool] C Γ) : Prop :=
  (∀ (m : ContextMap [.bool, .bool] Γ) (input : Input E [] false .body [.bool, .bool])
    (output : Output C Γ) (cert : Certificate),
    check m input output cert = true → ConcreteAssociation m input output cert) ∧
  Solidity.Correctness.Lowering.Checker.SoundnessStatement check

/-- A view frame preserves the complete model global part. This is a
model-state fact, not an identification with the independent Source journal. -/
theorem view_frame_globals {C : Contract} {Γ Δ : Ctx} (source : State C Γ)
    (target : State C Δ) (frame : TGFrame .view source target) :
    target.glob = source.glob := by
  rcases source with ⟨ss, sh, sp, se, sn, sb, st⟩
  rcases target with ⟨ts, th, tp, te, tn, tb, tt⟩
  rcases frame with ⟨hh, hp, hb, ht, hk⟩
  cases hh
  have heapEq : tp = sp := eq_of_heq hp
  have balanceEq : tb = sb := hb (by decide)
  have stateEq : ts = ss ∧ tn = sn := hk (by decide)
  rcases stateEq with ⟨storageEq, netEq⟩
  cases heapEq
  cases balanceEq
  cases storageEq
  cases netEq
  cases ht
  rfl

/-- The actual quoted program satisfies the existing view-frame checker. -/
theorem actual_within : Prog.within .view actual.program.2 = true := by
  decide +kernel

/-- Existing generic framing supplies unchanged target globals. -/
theorem actual_globals (target : State C Γ) (out : Out C target.H actual.program.1)
    (run : actual.program.2.run target = .ok out) : out.st.glob = target.glob := by
  have frame : TGFrame .view target out.st :=
    (Prog.run_frame actual.program.2 actual_within 0 run).1
  exact view_frame_globals target out.st frame

/-- Caller bindings are embedded past the retained break flag. -/
def embedding : Thin Γ actual.program.1 := .drop .refl

/-- The actual execution yields the existing G19 mapped post-local relation. -/
theorem actual_related {E : Source.Env} (choice : Bool) :
    ∃ out : Out C [] actual.program.1,
      actual.program.2.run (start choice) = .ok out ∧
      (mapping.wk embedding).Related (BoolRel (E := E) (H := out.st.H))
        ((sourceLocals choice).set .here (.bool choice)) out.st.env := by
  have observation := actual_observation choice
  cases run : actual.program.2.run (start choice) with
  | error err =>
    rw [run] at observation
    cases observation
  | ok out =>
    refine ⟨out, rfl, ?_⟩
    rw [run] at observation
    have pair : observe out = (choice, choice) := Option.some.inj observation
    have left : TEnv.get (.there .here) out.st.env = choice := congrArg Prod.fst pair
    have right : TEnv.get (.there (.there .here)) out.st.env = choice := congrArg Prod.snd pair
    intro τ i
    cases i with
    | here =>
      change (Source.Val.bool choice : Source.Val E.layout .bool) = .bool (TEnv.get (.there .here) out.st.env)
      rw [left]
    | there i => cases i with
      | here =>
        change (Source.Val.bool choice : Source.Val E.layout .bool) = .bool (TEnv.get (.there (.there .here)) out.st.env)
        rw [right]
      | there i => nomatch i

/-- G19-style mapped endpoint for the concrete actual-output prototype.
The Source half is reused; all actual target caller bindings and target
globals are accounted for. Initial target states remain the two `start`
samples; this is not generic checker soundness or a whole-world relation. -/
def MappedEndpoint {E : Source.Env} (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (ph : Option (Source.Ph E)) (st : Source.St E) (choice : Bool) : Prop :=
    ∃ out : Out C [] actual.program.1,
      (Source.execS G F (fuel + 4) nps ph (resolvedInput E) (sourceLocals choice)).run
        (.nil, st) =
        (.ok (Source.Out.normal ((sourceLocals choice).set .here (.bool choice))), (.nil, st)) ∧
      actual.program.2.run (start choice) = .ok out ∧
      (mapping.wk embedding).Related (BoolRel (E := E) (H := out.st.H))
        ((sourceLocals choice).set .here (.bool choice)) out.st.env ∧
      out.st.glob = (start choice).glob

/-- Actual resolved Source and actual intrinsic target reach the mapped
endpoint; no G19 source correctness proof is copied. -/
theorem prototype_mapped_sound {E : Source.Env} (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (ph : Option (Source.Ph E)) (st : Source.St E) (choice : Bool) : MappedEndpoint G F fuel nps ph st choice := by
  obtain ⟨out, run, related⟩ := actual_related (E := E) choice
  have sourceRun : (Source.execS G F (fuel + 4) nps ph (resolvedInput E)
      (sourceLocals choice)).run (.nil, st) =
      (.ok (Source.Out.normal ((sourceLocals choice).set .here (.bool choice))), (.nil, st)) := by
    change (Source.execS G F (fuel + 4) nps ph (SourceAssociation.resolved E)
      (sourceLocals choice)).run (.nil, st) = _
    rw [SourceAssociation.resolved_run_eq_bare]
    exact (prototype_sound G F fuel nps ph st choice).1
  exact ⟨out, sourceRun, run, related, actual_globals (start choice) out run⟩

/-- Measurable actual-resolved-source gate. Raw acceptance, actual Source
typing/elaboration, explicit horizon transport, mapped caller locals and
unchanged target globals are checked together for the concrete sample. -/
theorem actual_gate {E : Source.Env} (G : Source.Glob E) (F : Source.Fr)
    (fuel nps : Nat) (ph : Option (Source.Ph E)) (st : Source.St E) (choice : Bool) :
    RawProbe.checkRaw RawProbe.input RawProbe.actual.raw 1 = true ∧
      MappedEndpoint G F fuel nps ph st choice := by
  exact ⟨RawProbe.accepts_actual, prototype_mapped_sound G F fuel nps ph st choice⟩

#print axioms actual_gate
#print axioms view_frame_globals
#print axioms actual_within
#print axioms actual_globals
#print axioms actual_related
#print axioms prototype_mapped_sound

#print axioms prototype_gate
#print axioms replay_sound
#print axioms actual_replay_normal
#print axioms actual_replay_observation
#print axioms replay_observation_sound
#print axioms actual_observation
#print axioms initial
#print axioms prototype_sound

end Solidity.Correctness.Lowering.Checker.WhileBreak
