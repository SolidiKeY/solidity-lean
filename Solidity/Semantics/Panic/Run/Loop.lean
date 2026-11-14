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

partial def runImpl [Inhabited α] (body : α → EvalResult α) (c : α → EvalResult Bool) (σ : α) : EvalResult α :=
  match step body c σ with
  | .inl τ => runImpl body c τ
  | .inr r => r

/-- The compiled loop, for a state type with no `Inhabited` instance. -/
def runImpl' (body : α → EvalResult α) (c : α → EvalResult Bool) (σ : α) : EvalResult α :=
  @runImpl α ⟨σ⟩ body c σ

open Classical in
/-- The loop's outcome, or `diverge` when no iteration is done. -/
@[implemented_by runImpl']
noncomputable def run (body : α → EvalResult α) (c : α → EvalResult Bool) (σ : α) : EvalResult α :=
  if h : ∃ r n, iterN body c n σ = .inr r then Classical.choose h else .error .diverge

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

/-- A loop done at `n` ends as it is done there. -/
theorem run_of_iterN {body : α → EvalResult α} {c : α → EvalResult Bool} {n : Nat} {σ : α} {r : EvalResult α}
    (h : iterN body c n σ = .inr r) : run body c σ = r := by
  have hex : ∃ r n, iterN body c n σ = .inr r := ⟨r, n, h⟩
  simp only [run, hex, dite_true]
  obtain ⟨n', h'⟩ := Classical.choose_spec hex
  exact iterN_done_unique h' h

/-- **Induction over a loop's run**: `P` holds of the first state and of
every state an iteration from a state in `P` goes on in, and `Q` of every
outcome an iteration from a state in `P` is done with, and of a divergence:
then `Q` holds of the loop's run. -/
theorem run_induct {body : α → EvalResult α} {c : α → EvalResult Bool} {P : α → Prop} {Q : EvalResult α → Prop}
    {σ : α} (h0 : P σ)
    (hstep : ∀ τ, P τ →
      match step body c τ with
      | .inl τ' => P τ'
      | .inr r => Q r)
    (hdiv : Q (.error .diverge)) : Q (run body c σ) := by
  have key : ∀ (n : Nat) (τ : α) (r : EvalResult α), P τ → iterN body c n τ = .inr r → Q r := by
    intro n
    induction n with
    | zero => intro τ r _ h; exact nomatch h
    | succ n ih =>
      intro τ r hp h
      have hs := hstep τ hp
      simp only [iterN] at h
      revert hs h
      cases step body c τ with
      | inl τ' => exact fun he hp => ih τ' r hp he
      | inr r' =>
        intro he hp
        cases (show Sum.inr r' = (Sum.inr r : α ⊕ EvalResult α) from he)
        exact hp
  unfold run
  split
  · rename_i hex
    obtain ⟨n, hn⟩ := Classical.choose_spec hex
    exact key n σ _ h0 hn
  · exact hdiv

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
