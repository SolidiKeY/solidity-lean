import Solidity.Backend.Failure.Correct
import Solidity.Semantics.Run

/-!
# Existing intrinsic outcomes and exact payload observations

This is an observation relation on the committed intrinsic run, not a new
source semantics. It has no exhaustion/divergence constructor: resource and
whole-session completion remain the source/world owners' obligations. Returns
here have already been encoded by the existing ABI boundary.
-/
namespace Solidity.Backend.Failure

/-- The primitive panic tag is assert's Panic(1); other panic codes already
arrive in revertWith bytes from the existing checked-expression lowering. -/
inductive HaltObserves : THalt → Roadmap.Outcome → Prop
  | empty : HaltObserves .revert (.revert [])
  | panic : HaltObserves .panic (.revert (Semantics.encodePanic 1))
  | data (d : Semantics.RevertData) : HaltObserves (.revertWith d) (.revert d)

inductive ResultObserves {α : Type} (encodeReturn : α → List UInt8) :
    TRes α → Roadmap.Outcome → Prop
  | success (a : α) : ResultObserves encodeReturn (.ok a) (.success (encodeReturn a))
  | failure {e : THalt} {o : Roadmap.Outcome} (h : HaltObserves e o) :
      ResultObserves encodeReturn (.error e) o

theorem HaltObserves.functional {e : THalt} {o₁ o₂ : Roadmap.Outcome}
    (h₁ : HaltObserves e o₁) (h₂ : HaltObserves e o₂) : o₁ = o₂ := by
  cases h₁ <;> cases h₂ <;> rfl

theorem ResultObserves.functional {α : Type} {enc : α → List UInt8}
    {t : TRes α} {o₁ o₂ : Roadmap.Outcome}
    (h₁ : ResultObserves enc t o₁) (h₂ : ResultObserves enc t o₂) : o₁ = o₂ := by
  cases h₁ with
  | success a => cases h₂; rfl
  | failure h₁ => cases h₂ with
    | failure h₂ => exact h₁.functional h₂

theorem wrong_observation {α : Type} {enc : α → List UInt8} {t : TRes α}
    {correct wrong : Roadmap.Outcome} (hc : ResultObserves enc t correct)
    (h : correct ≠ wrong) : ¬ ResultObserves enc t wrong :=
  fun hw => h (hc.functional hw)

theorem ofData_observes (d : Semantics.RevertData) :
    HaltObserves (THalt.ofData d) (.revert d) := by
  cases d with
  | nil => exact .empty
  | cons b bs => exact .data (b :: bs)

/-- This adapter accepts only existing finite intrinsic byte results.
It does not supply a new interpretation of exhausted or diverging runs. -/
def inputOfResult : TRes (List UInt8) → Option Input
  | .ok bs => some (.returned bs)
  | .error .revert => some .empty
  | .error .panic => some (.panic ⟨1, by decide⟩)
  | .error (.revertWith bs) => some (.custom bs)
  | .error .diverge | .error .exhausted => none

theorem inputOfResult_sound (t : TRes (List UInt8)) (i : Input)
    (h : inputOfResult t = some i) : ResultObserves id t i.observation := by
  cases t with
  | ok bs => cases h; exact .success bs
  | error e =>
    cases e with
    | revert => cases h; exact .failure .empty
    | panic => cases h; exact .failure .panic
    | diverge => cases h
    | exhausted => cases h
    | revertWith bs => cases h; exact .failure (.data bs)

/-- The observed result is the one of the original intrinsic result, and the
exact initial payload is retained even when it aliases no machine memory. -/
theorem intrinsic_emission (t : TRes (List UInt8)) (i : Input)
    (hi : inputOfResult t = some i) (a : Nat) (s : Slice.Machine)
    (hf : Fits a i.bytes) (hs : s.stack.length + 2 ≤ 1024) :
    Slice.checkedRun (emit a i) s =
      some ({ s with memory := Slice.putBytes s.memory a i.bytes }, some i.observation) ∧
      ResultObserves id t i.observation := by
  constructor
  · simpa only [List.append_nil] using checkedRun_emit_suffix a i [] s hf hs
  · exact inputOfResult_sound t i hi

theorem assert_false_intrinsic {C : Contract} {Γ : Ctx} (c : Val C Γ .bool)
    (σ : State C Γ) (h : c.evalT σ = .ok false) : TRun.assert c σ = .error .panic := by
  unfold TRun.assert
  rw [h]
  rfl

theorem require_false_intrinsic {C : Contract} {Γ : Ctx} (c : Val C Γ .bool)
    (σ : State C Γ) (h : c.evalT σ = .ok false) : TRun.require c σ = .error .revert := by
  unfold TRun.require
  rw [h]
  rfl

theorem revert_bytes_intrinsic {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (d : Semantics.RevertData) :
    TRun.revertData [.bytes d] σ = .error (THalt.ofData d) := by
  change Except.error (THalt.ofData (d ++ [])) = _
  rw [List.append_nil]

theorem custom_parts_intrinsic {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (signature : String) (args : List UInt8) :
    TRun.revertData [.sel signature, .bytes args] σ =
      .error (THalt.ofData (Semantics.selectorBytes (Semantics.customSelector signature) ++ args)) := by
  change Except.error (THalt.ofData
    (Semantics.selectorBytes (Semantics.customSelector signature) ++ (args ++ []))) = _
  rw [List.append_nil]

theorem assert_false_observed {C : Contract} {Γ : Ctx} (c : Val C Γ .bool)
    (σ : State C Γ) (h : c.evalT σ = .ok false)
    (encodeReturn : Out C σ.H Γ → List UInt8) :
    ResultObserves encodeReturn (TRun.assert c σ) (.revert (Semantics.encodePanic 1)) := by
  rw [assert_false_intrinsic c σ h]
  exact .failure .panic

theorem require_false_observed {C : Contract} {Γ : Ctx} (c : Val C Γ .bool)
    (σ : State C Γ) (h : c.evalT σ = .ok false)
    (encodeReturn : Out C σ.H Γ → List UInt8) :
    ResultObserves encodeReturn (TRun.require c σ) (.revert []) := by
  rw [require_false_intrinsic c σ h]
  exact .failure .empty

theorem custom_parts_observed {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (signature : String) (args : List UInt8) (encodeReturn : Out C σ.H Γ → List UInt8) :
    ResultObserves encodeReturn (TRun.revertData [.sel signature, .bytes args] σ)
      (.revert (Semantics.selectorBytes (Semantics.customSelector signature) ++ args)) := by
  rw [custom_parts_intrinsic]
  exact .failure (ofData_observes _)

theorem return_revert_distinct (bs : List UInt8) :
    (Input.returned bs).observation ≠ (Input.custom bs).observation := by
  intro h
  cases h

theorem distinct_payloads (xs ys : List UInt8) (h : xs ≠ ys) :
    (Input.custom xs).observation ≠ (Input.custom ys).observation := by
  intro he
  cases he
  exact h rfl

end Solidity.Backend.Failure
