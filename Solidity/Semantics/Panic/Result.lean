import Solidity.Semantics.Run
import Solidity.Source.Observe

/-!
# Panic-carrying typed results

A parallel result interface; the existing `THalt`, `TRes` and run are unchanged.
Origins are parameters, independent of the later typed-origin implementation.
Successes retain their entire type (including `Out` or `Grew` and their proofs).
The projection below forgets information in one result. It is not a theorem
relating the old and new interpreters: a self-call's catch can observe a changed
panic code and hence choose a different continuation.
-/

namespace Solidity.Semantics.Panic

/-- An intrinsic failure has a solc code and a caller-supplied typed origin.
External revert bytes remain external even when they encode `Panic(uint256)`.
`revertWith` retains explicit local revert data without labeling it external.
Exhaustion and divergence are separate from all reverting outcomes. -/
inductive Halt (Origin : Type) where
  | intrinsic (code : Source.PanicCode) (origin : Origin)
  | externalRevert (data : List UInt8)
  | revert
  | revertWith (data : List UInt8)
  | exhausted
  | diverge
  deriving Repr, DecidableEq

/-- Full success values, with panic provenance retained on failure. -/
abbrev Result (Origin α : Type) := Except (Halt Origin) α

namespace Halt

/-- Local information loss to the existing halt type. In particular an external
payload projects as data, never as the old intrinsic `panic` constructor. -/
def toV1 {Origin : Type} : Halt Origin → THalt
  | .intrinsic _ _ => .panic
  | .externalRevert data => THalt.ofData data
  | .revert => .revert
  | .revertWith data => .revertWith data
  | .exhausted => .exhausted
  | .diverge => .diverge

/-- Replacing the origin cannot change the local V1 observation. -/
def mapOrigin {Origin Other : Type} (f : Origin → Other) : Halt Origin → Halt Other
  | .intrinsic code origin => .intrinsic code (f origin)
  | .externalRevert data => .externalRevert data
  | .revert => .revert
  | .revertWith data => .revertWith data
  | .exhausted => .exhausted
  | .diverge => .diverge

theorem toV1_mapOrigin {Origin Other : Type} (f : Origin → Other) (h : Halt Origin) :
    (h.mapOrigin f).toV1 = h.toV1 := by
  cases h <;> rfl

/-- Constructor injectivity retains both the exact code and its origin. -/
theorem intrinsic_eq_iff {Origin : Type} (c d : Source.PanicCode) (o p : Origin) :
    (Halt.intrinsic c o = .intrinsic d p) ↔ c = d ∧ o = p := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Even a byte-for-byte panic payload cannot become an intrinsic panic. -/
theorem intrinsic_ne_external {Origin : Type} (c : Source.PanicCode) (o : Origin)
    (data : List UInt8) : Halt.intrinsic c o ≠ .externalRevert data := by
  intro h
  cases h

end Halt

namespace Result

/-- Forget failure provenance locally and preserve the complete success value. -/
def toV1 {Origin α : Type} : Result Origin α → TRes α
  | .ok value => .ok value
  | .error halt => .error halt.toV1

theorem toV1_ok {Origin α : Type} (value : α) :
    toV1 (.ok value : Result Origin α) = .ok value := rfl

theorem toV1_intrinsic {Origin α : Type} (code : Source.PanicCode) (origin : Origin) :
    toV1 (.error (.intrinsic code origin) : Result Origin α) = .error .panic := rfl

theorem toV1_external {Origin α : Type} (data : List UInt8) :
    toV1 (.error (.externalRevert data) : Result Origin α) =
      .error (THalt.ofData data) := rfl

/-- Projection cannot invent, discard or alter a successful value. -/
theorem toV1_eq_ok_iff {Origin α : Type} (result : Result Origin α) (value : α) :
    result.toV1 = .ok value ↔ result = .ok value := by
  cases result <;> simp only [toV1, Except.ok.injEq, reduceCtorEq]

/-- A local map changes only the success value. -/
theorem toV1_map {Origin α β : Type} (f : α → β) (result : Result Origin α) :
    toV1 (result.map f) = result.toV1.map f := by
  cases result <;> rfl

/-- Bind commutes with projection when the *same* continuation is projected.
This does not identify V1 and V2 catch handlers or interpreter executions. -/
theorem toV1_bind {Origin α β : Type} (result : Result Origin α)
    (next : α → Result Origin β) :
    toV1 (result >>= next) = (result.toV1 >>= fun value => (next value).toV1) := by
  cases result <;> rfl

/-- Pure embedding is available only for successes; it reconstructs no origin. -/
def success {Origin α : Type} (value : α) : Result Origin α := .ok value

theorem success_project {Origin α : Type} (value : α) :
    (success (Origin := Origin) value).toV1 = .ok value := rfl

end Result
end Solidity.Semantics.Panic
