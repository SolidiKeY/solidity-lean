import Solidity.Semantics.Panic.Eval

namespace Solidity.Semantics.Panic

namespace Loop

variable {α : Type}

def step (body : α → EvalResult α) (c : α → EvalResult Bool) (σ : α) : α ⊕ EvalResult α :=
  match c σ with
  | .error h => .inr (.error h)
  | .ok false => .inr (.ok σ)
  | .ok true =>
    match body σ with
    | .error h => .inr (.error h)
    | .ok τ => .inl τ

def iterN (body : α → EvalResult α) (c : α → EvalResult Bool) : Nat → α → α ⊕ EvalResult α
  | 0, σ => .inl σ
  | n + 1, σ =>
    match step body c σ with
    | .inl τ => iterN body c n τ
    | .inr r => .inr r

/-- The existing trusted loop engine carries the richer terminal result as data.
No intrinsic failure is projected to a V1 halt. -/
def advance (body : α → EvalResult α) (c : α → EvalResult Bool) :
    α ⊕ EvalResult α → TRes (α ⊕ EvalResult α)
  | .inl σ => .ok (step body c σ)
  | .inr r => .ok (.inr r)

def active : α ⊕ EvalResult α → TRes Bool
  | .inl _ => .ok true
  | .inr _ => .ok false

def finish : TRes (α ⊕ EvalResult α) → EvalResult α
  | .ok (.inr r) => r
  | _ => .error .diverge

/-- Reuse TLoop's inventoried implementation, preserving all panic payloads. -/
def run (body : α → EvalResult α) (c : α → EvalResult Bool) (σ : α) : EvalResult α :=
  finish (TLoop.run (advance body c) active (.inl σ))

theorem iterN_done_le {body : α → EvalResult α} {c : α → EvalResult Bool} {n m : Nat} {σ : α} {r : EvalResult α}
    (hnm : n ≤ m) (h : iterN body c n σ = .inr r) : iterN body c m σ = .inr r := by
  induction n generalizing σ m with
  | zero => simp only [iterN, reduceCtorEq] at h
  | succ n ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [iterN] at h ⊢
    cases hs : step body c σ with
    | inl τ => rw [hs] at h; exact ih (by omega) h
    | inr r' => rw [hs] at h; exact h

theorem iterN_done_unique {body : α → EvalResult α} {c : α → EvalResult Bool} {n m : Nat} {σ : α}
    {r r' : EvalResult α} (h : iterN body c n σ = .inr r) (h' : iterN body c m σ = .inr r') :
    r = r' := by
  rcases Nat.le_total n m with hnm | hmn
  · rw [iterN_done_le hnm h] at h'
    exact Sum.inr.inj h'
  · rw [iterN_done_le hmn h'] at h
    exact (Sum.inr.inj h).symm

/-- A terminal panic iteration becomes terminal data in the existing loop engine. -/
theorem lifted_done {body : α → EvalResult α} {c : α → EvalResult Bool}
    {n : Nat} {σ : α} {r : EvalResult α} (h : iterN body c n σ = .inr r) :
    TLoop.iterN (advance body c) active (n + 1) (.inl σ) = .inr (.ok (.inr r)) := by
  induction n generalizing σ with
  | zero => cases h
  | succ n ih =>
    cases hs : step body c σ with
    | inl τ =>
      simp only [iterN, hs] at h
      change TLoop.iterN (advance body c) active (n + 1) (step body c σ) = _
      rw [hs]
      exact ih h
    | inr result =>
      simp only [iterN, hs, Sum.inr.injEq] at h
      subst result
      simp only [TLoop.iterN, TLoop.step, active, advance, hs]

/-- A loop done at n returns exactly that outcome, with its complete origin. -/
theorem run_of_iterN {body : α → EvalResult α} {c : α → EvalResult Bool}
    {n : Nat} {σ : α} {r : EvalResult α}
    (h : iterN body c n σ = .inr r) : run body c σ = r := by
  unfold run
  rw [TLoop.run_of_iterN (lifted_done h)]
  rfl

/-- Induction preserves arbitrary properties of the complete panic result. -/
theorem run_induct {body : α → EvalResult α} {c : α → EvalResult Bool}
    {P : α → Prop} {Q : EvalResult α → Prop} {σ : α} (h0 : P σ)
    (hstep : ∀ τ, P τ →
      match step body c τ with
      | .inl τ' => P τ'
      | .inr r => Q r)
    (hdiv : Q (.error .diverge)) : Q (run body c σ) := by
  let invariant : α ⊕ EvalResult α → Prop
    | .inl τ => P τ
    | .inr r => Q r
  apply TLoop.run_induct (P := invariant) (Q := fun r => Q (finish r)) h0
  · intro state h
    cases state with
    | inl τ => exact hstep τ h
    | inr r => exact h
  · exact hdiv

/-- Absence of a terminal iteration is exactly the diverging execution case. -/
theorem run_diverge {body : α → EvalResult α} {c : α → EvalResult Bool} {σ : α}
    (h : ¬ ∃ r n, iterN body c n σ = .inr r) : run body c σ = .error .diverge := by
  apply run_induct (P := fun τ => ¬ ∃ r n, iterN body c n τ = .inr r)
    (Q := fun result => result = .error .diverge) h ?_ rfl
  intro τ hn
  cases hs : step body c τ with
  | inl next =>
    intro ⟨r, n, hr⟩
    exact hn ⟨r, n + 1, by simp only [iterN, hs, hr]⟩
  | inr r =>
    exact False.elim (hn ⟨r, 1, by simp only [iterN, hs]⟩)

/-- A condition failure propagates unchanged, including resource failures. -/
theorem run_condition_error (body : α → EvalResult α) (c : α → EvalResult Bool)
    (σ : α) (halt : Halt Raised) (h : c σ = .error halt) :
    run body c σ = .error halt :=
  run_of_iterN (n := 1) (by simp only [iterN, step, h])

/-- A body failure propagates unchanged after a true condition. -/
theorem run_body_error (body : α → EvalResult α) (c : α → EvalResult Bool)
    (σ : α) (halt : Halt Raised) (hc : c σ = .ok true)
    (hb : body σ = .error halt) : run body c σ = .error halt :=
  run_of_iterN (n := 1) (by simp only [iterN, step, hc, hb])

end Loop

end Solidity.Semantics.Panic
