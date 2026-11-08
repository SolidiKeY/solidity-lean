import Solidity.Correctness.Lowering.Checker.IntrinsicProbe
import Solidity.Semantics.RunFuel

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

/-- Concrete end-to-end semantic observation, reusing G19.correct rather
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

/-- Measurable concrete gate: kernel raw acceptance and the actual intrinsic
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

#print axioms prototype_gate
#print axioms replay_sound
#print axioms actual_replay_normal
#print axioms actual_replay_observation
#print axioms replay_observation_sound
#print axioms actual_observation
#print axioms initial
#print axioms prototype_sound

end Solidity.Correctness.Lowering.Checker.WhileBreak
