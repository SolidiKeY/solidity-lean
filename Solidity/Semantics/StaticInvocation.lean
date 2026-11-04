import Solidity.Semantics.Callback

/-! Intrinsic operational storage frames ported to H22 CallMode.
The call's mode is explicit; no indexed ExtCall or side invocation registry
is introduced. These effects do not themselves establish Source/native
execution adequacy or authenticate a compiler AST id. -/
namespace Solidity.StaticInvocation
variable {C : Contract} {Γ : Ctx}

def inheritMode : CallMode → CallMode → CallMode
  | .call, requested => requested
  | .static, _ => .static

def inheritCall (active : CallMode) (call : ExtCall C Γ) : ExtCall C Γ :=
  { call with mode := inheritMode active call.mode }

theorem inheritCall_mode (active : CallMode) (call : ExtCall C Γ) :
    (inheritCall active call).mode = inheritMode active call.mode := rfl
theorem inheritCall_invocation (active : CallMode) (call : ExtCall C Γ) :
    (inheritCall active call).invocation = call.invocation := rfl

/-- H22's current oracle key ignores these fields. Inheritance does not
reevaluate arguments at a different state or split deterministic lookups. -/
theorem inheritCall_key (active : CallMode) (call : ExtCall C Γ) (σ : State C Γ) :
    (inheritCall active call).keyT σ = call.keyT σ := rfl
theorem inheritCall_lookup (active : CallMode) (call : ExtCall C Γ) (σ : State C Γ) :
    Semantics.lookupBy ((inheritCall active call).keyT σ) σ.tx.ext =
      Semantics.lookupBy (call.keyT σ) σ.tx.ext := rfl

inductive Outcome where
  | returned (bytes : List UInt8)
  | halted (reason : THalt)

/-- Only actual call failures enter a catch. Exhaustion and divergence escape. -/
def catchable : THalt → Bool
  | .revert | .revertWith _ | .panic => true
  | .exhausted | .diverge => false

/-- Successful children commit. Failed children restore their own checkpoint. -/
def checkpoint (result : Outcome) (entry dirty : State C Γ) : State C Γ :=
  match result with
  | .returned _ => dirty
  | .halted _ => entry

/-- An operational effect relation over intrinsic states, not an untyped IR.
`credit` deliberately demonstrates that storage restrictions alone do not
supply a ledger/balance preservation theorem. It is not a modeled SSTORE.
-/
inductive Exec : CallMode → State C Γ → Outcome → State C Γ → Prop where
  | returned (mode : CallMode) (σ : State C Γ) (bytes : List UInt8) :
      Exec mode σ (.returned bytes) σ
  | halted (mode : CallMode) (σ : State C Γ) (reason : THalt) :
      Exec mode σ (.halted reason) σ
  | read {mode : CallMode} {σ τ : State C Γ} {result : Outcome}
      (label : Name) (rest : Exec mode σ result τ) : Exec mode σ result τ
  | credit {mode : CallMode} {σ τ : State C Γ} {result : Outcome}
      (net : Ledger) (balance : PrimTy.uint.Denote)
      (rest : Exec mode (σ.havoc σ.storage net balance) result τ) :
      Exec mode σ result τ
  | write {σ τ : State C Γ} {result : Outcome} (storage : Storage C)
      (net : Ledger) (balance : PrimTy.uint.Denote)
      (rest : Exec .call (σ.havoc storage net balance) result τ) :
      Exec .call σ result τ
  | refused (σ : State C Γ) (attempted : Storage C) :
      Exec .static σ (.halted .revert) σ
  | reentryReturn {mode requested : CallMode} {σ child final : State C Γ}
      {bytes : List UInt8} {result : Outcome} (callee : Name)
      (nested : Exec (inheritMode mode requested) σ (.returned bytes) child)
      (rest : Exec mode child result final) : Exec mode σ result final
  | reentryCatch {mode requested : CallMode} {σ dirty final : State C Γ}
      {reason : THalt} {result : Outcome} (callee : Name)
      (nested : Exec (inheritMode mode requested) σ (.halted reason) dirty)
      (caught : catchable reason = true)
      (rest : Exec mode σ result final) : Exec mode σ result final
  | reentryEscape {mode requested : CallMode} {σ dirty : State C Γ}
      {reason : THalt} (callee : Name)
      (nested : Exec (inheritMode mode requested) σ (.halted reason) dirty)
      (escape : catchable reason = false) :
      Exec mode σ (.halted reason) σ

/-- Storage preservation includes arbitrary unknown-code read-only reentry. -/
theorem Exec.storage (h : Exec mode σ result τ) (static : mode = .static) :
    τ.storage = σ.storage := by
  induction h with
  | returned => rfl
  | halted => rfl
  | read _ _ ih => exact ih static
  | credit _ _ _ ih => exact ih static
  | write => cases static
  | refused => rfl
  | @reentryReturn mode requested _ _ _ _ _ _ _ _ childIH restIH =>
    have nestedStatic : inheritMode mode requested = .static := by
      rw [static]
      rfl
    exact (restIH static).trans (childIH nestedStatic)
  | reentryCatch _ _ _ _ _ restIH => exact restIH static
  | reentryEscape => rfl

/-- The externally visible state of one call frame. -/
def Frame (mode : CallMode) (entry : State C Γ) (result : Outcome)
    (visible : State C Γ) : Prop :=
  ∃ dirty, Exec mode entry result dirty ∧ visible = checkpoint result entry dirty

theorem Frame.storage (h : Frame .static σ result τ) : τ.storage = σ.storage := by
  obtain ⟨dirty, run, visible⟩ := h
  cases result with
  | returned bytes => exact visible ▸ run.storage rfl
  | halted reason => exact visible ▸ rfl

/-- Rollback uses the child entry, not the state before caller argument effects. -/
theorem Frame.rollback (h : Frame mode active (.halted reason) visible) :
    visible = active := by
  obtain ⟨dirty, _, visible⟩ := h
  exact visible

/-- Ordinary success retains arbitrary caller-storage replacement. -/
theorem ordinary_havoc (σ : State C Γ) (storage : Storage C)
    (net : Ledger) (balance : PrimTy.uint.Denote) (bytes : List UInt8) :
    Frame .call σ (.returned bytes) (σ.havoc storage net balance) :=
  ⟨_, .write storage net balance (.returned _ _ bytes), rfl⟩

/-- A write attempt is refused even when its requested value is unchanged. -/
theorem static_noop_write_refused (σ : State C Γ) :
    Frame .static σ (.halted .revert) σ := ⟨σ, .refused σ σ.storage, rfl⟩

/-- Inherited restrictions apply to an unknown callback requesting ordinary CALL. -/
theorem static_reentry_write_refused (σ : State C Γ) (attempt : Storage C)
    (bytes : List UInt8) : Frame .static σ (.returned bytes) σ :=
  ⟨σ, .reentryCatch (requested := .call) "unknown-callback"
    (.refused σ attempt) rfl (.returned _ _ bytes), rfl⟩

/-- A caller's post-argument checkpoint survives a failed child. -/
theorem child_rollback_after_captures (active : State C Γ) (attempt : Storage C)
    (bytes : List UInt8) : Frame .call active (.returned bytes) active :=
  ⟨active, .reentryCatch (requested := .static) "unknown-callee"
    (.refused active attempt) rfl (.returned _ _ bytes), rfl⟩

/-- Credits illustrate the deliberately narrower, storage-only guarantee. -/
theorem static_credit (σ : State C Γ) (net : Ledger)
    (balance : PrimTy.uint.Denote) (bytes : List UInt8) :
    Frame .static σ (.returned bytes) (σ.havoc σ.storage net balance) :=
  ⟨_, .credit net balance (.returned _ _ bytes), rfl⟩

/-- The effect relation retains the caller's local/heap/transaction skeleton.
Only the explicitly modeled persistent projections may vary. -/
theorem Exec.havoc_form (h : Exec mode σ result τ) :
    τ = σ.havoc τ.storage τ.net τ.selfBalance := by
  induction h with
  | returned => rfl
  | halted => rfl
  | read _ _ ih => exact ih
  | credit _ _ _ ih => exact ih
  | write _ _ _ _ ih => exact ih
  | refused => rfl
  | reentryReturn _ _ _ childIH restIH =>
    rw [childIH] at restIH
    exact restIH
  | reentryCatch _ _ _ _ _ restIH => exact restIH
  | reentryEscape => rfl

theorem Frame.havoc_form (h : Frame mode σ result τ) :
    τ = σ.havoc τ.storage τ.net τ.selfBalance := by
  obtain ⟨dirty, run, visible⟩ := h
  cases result with
  | returned bytes => exact visible ▸ run.havoc_form
  | halted reason => exact visible ▸ rfl

/-- Full typed-state equality additionally needs independent ledger and balance
agreement. Neither follows from storage-only mode. -/
theorem Frame.full_static_resume (h : Frame .static σ result τ)
    (net : τ.net = σ.net) (balance : τ.selfBalance = σ.selfBalance) :
    τ = σ := by
  have shape := h.havoc_form
  rw [h.storage, net, balance] at shape
  exact shape

/-- Direct H22 field use; static mode is an operational restriction, not
source/compiler/native provenance. -/
theorem Frame.call_storage {call : ExtCall C Γ}
    (mode : call.mode = .static) (h : Frame call.mode σ result τ) :
    τ.storage = σ.storage := by
  rw [mode] at h
  exact h.storage

end Solidity.StaticInvocation
