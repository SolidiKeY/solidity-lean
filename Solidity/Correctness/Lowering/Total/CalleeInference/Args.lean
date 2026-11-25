import Solidity.Source.Infer

/-!
# Argument-list inference at the fuel `TypedArgs.inferN` uses

Equations of the actual `Source.TypedArgs.inferN` over an ordered positional
list (`argExprs`): no fuel fails (`argsN_zero`), the empty list succeeds at any
positive fuel (`argsN_nil`), and a cons infers its head with `Typed.inferN` at
one less fuel, then its tail at that same fuel (`argsN_cons`, `argsN_cons_some`).
So position `i` is inferred at `n - 1 - i` when the list is inferred at `n`.

Failure propagates: a failing head or tail (`argsN_head_none`, `argsN_tail_none`),
a failing position at its fuel (`argsN_fail_at`) or too little fuel for the list
(`argsN_short`) leaves no result; conversely a failing list with enough fuel
has a position failing at its fuel (`fail_at_of_argsN`). Success is derived from the individual
argument results at their actual fuels (`argsN_of_each`), and conversely each
position of a successful result was inferred there (`each_of_argsN`). Nothing
here relates `Typed.inferN` to a `Typed` derivation found otherwise.
-/
namespace Solidity.Correctness.Lowering.Total.CalleeInference

open Source (STy Syn Ctx Typed TypedArgs)

/-- The ordered positional arguments of an argument list. -/
def argExprs : Syn (.list .expr) → List (Syn .expr)
  | .nil => []
  | .cons e es => e :: argExprs es

variable {Γ : Ctx} {n : Nat} {e : Syn .expr} {es : Syn (.list .expr)}

/-! ## Equations -/

theorem argsN_zero : TypedArgs.inferN 0 Γ es = none := by
  simp only [TypedArgs.inferN]

theorem argsN_nil : TypedArgs.inferN (n + 1) Γ .nil = some ⟨[], .nil⟩ := by
  simp only [TypedArgs.inferN]

/-- The cons step: the head at one less fuel, then the tail at that fuel. -/
theorem argsN_cons :
    TypedArgs.inferN (n + 1) Γ (.cons e es) =
      (Typed.inferN n Γ e).bind fun r =>
        (TypedArgs.inferN n Γ es).bind fun rs => some ⟨r.1 :: rs.1, .cons r.2 rs.2⟩ := by
  simp only [TypedArgs.inferN]
  rfl

/-- The derivation of a cons is built from the head's and the tail's results. -/
theorem argsN_cons_some {τ : STy} {τs : List STy} {d : Typed Γ e τ} {ds : TypedArgs Γ es τs}
    (hd : Typed.inferN n Γ e = some ⟨τ, d⟩) (hds : TypedArgs.inferN n Γ es = some ⟨τs, ds⟩) :
    TypedArgs.inferN (n + 1) Γ (.cons e es) = some ⟨τ :: τs, .cons d ds⟩ := by
  rw [argsN_cons, hd]; simp only [Option.bind_some, hds]

theorem argsN_head_none (h : Typed.inferN n Γ e = none) :
    TypedArgs.inferN (n + 1) Γ (.cons e es) = none := by
  rw [argsN_cons, h]; rfl

theorem argsN_tail_none (h : TypedArgs.inferN n Γ es = none) :
    TypedArgs.inferN (n + 1) Γ (.cons e es) = none := by
  rw [argsN_cons]
  cases Typed.inferN n Γ e <;> simp [h]

/-! ## Positions -/

/-- Too little fuel for the list: one unit per position and one for the end. -/
theorem argsN_short : ∀ {n : Nat} {es : Syn (.list .expr)}, n ≤ (argExprs es).length →
    TypedArgs.inferN n Γ es = none
  | 0, _, _ => argsN_zero
  | _ + 1, .nil, h => by simp [argExprs] at h
  | _ + 1, .cons _ es, h => argsN_tail_none (argsN_short (es := es) (by simp [argExprs] at h; omega))

/-- A position failing at its actual fuel `n - 1 - i` fails the list. -/
theorem argsN_fail_at : ∀ {n i : Nat} {es : Syn (.list .expr)} {e : Syn .expr},
    (argExprs es)[i]? = some e → Typed.inferN (n - 1 - i) Γ e = none →
    TypedArgs.inferN n Γ es = none
  | 0, _, _, _, _, _ => argsN_zero
  | _ + 1, _, .nil, _, hi, _ => by simp [argExprs] at hi
  | n + 1, 0, .cons _ _, _, hi, h => by
      simp only [argExprs, List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact argsN_head_none (by simpa using h)
  | n + 1, i + 1, .cons _ es, _, hi, h =>
      argsN_tail_none (argsN_fail_at (n := n) (i := i) (es := es)
        (by simpa [argExprs] using hi) (by simpa [Nat.sub_sub, Nat.add_comm] using h))

/-- A failing list with enough fuel has a position failing at its actual fuel. -/
theorem fail_at_of_argsN : ∀ {n : Nat} {es : Syn (.list .expr)},
    TypedArgs.inferN n Γ es = none → (argExprs es).length < n →
    ∃ i e, (argExprs es)[i]? = some e ∧ Typed.inferN (n - 1 - i) Γ e = none
  | 0, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | _ + 1, .nil, h, _ => by simp [argsN_nil] at h
  | n + 1, .cons e es, h, hn => by
      cases hd : Typed.inferN n Γ e with
      | none => exact ⟨0, e, by simp [argExprs], by simpa using hd⟩
      | some r =>
          cases hds : TypedArgs.inferN n Γ es with
          | some rs => rw [argsN_cons, hd, hds] at h; cases h
          | none =>
              obtain ⟨i, a, hi, ha⟩ := fail_at_of_argsN hds (by simp [argExprs] at hn; omega)
              exact ⟨i + 1, a, by simpa [argExprs] using hi,
                by simpa [Nat.sub_sub, Nat.add_comm] using ha⟩

/-- **Success from individual results**: each position `i` inferred with type
`σs[i]` at the fuel `n - 1 - i` the implementation uses, with enough fuel for
the list, makes the list infer to `σs`. -/
theorem argsN_of_each : ∀ {n : Nat} {es : Syn (.list .expr)} {σs : List STy},
    (argExprs es).length < n → σs.length = (argExprs es).length →
    (∀ i e σ, (argExprs es)[i]? = some e → σs[i]? = some σ →
      ∃ d, Typed.inferN (n - 1 - i) Γ e = some ⟨σ, d⟩) →
    ∃ da, TypedArgs.inferN n Γ es = some ⟨σs, da⟩
  | 0, _, _, hn, _, _ => absurd hn (Nat.not_lt_zero _)
  | _ + 1, .nil, [], _, _, _ => ⟨.nil, argsN_nil⟩
  | _ + 1, .nil, _ :: _, _, hl, _ => by simp [argExprs] at hl
  | _ + 1, .cons _ _, [], _, hl, _ => by simp [argExprs] at hl
  | n + 1, .cons e es, σ :: σs, hn, hl, h => by
      obtain ⟨d, hd⟩ := h 0 e σ (by simp [argExprs]) rfl
      obtain ⟨ds, hds⟩ := argsN_of_each (n := n) (es := es) (σs := σs)
        (by simp [argExprs] at hn; omega) (by simpa [argExprs] using hl)
        fun i a τ hi hτ => by
          obtain ⟨d', hd'⟩ := h (i + 1) a τ (by simpa [argExprs] using hi) (by simpa using hτ)
          exact ⟨d', by simpa [Nat.sub_sub, Nat.add_comm] using hd'⟩
      exact ⟨.cons d ds, argsN_cons_some (by simpa using hd) hds⟩

/-- Each position of a successful list was inferred at its actual fuel, in order. -/
theorem each_of_argsN : ∀ {n : Nat} {es : Syn (.list .expr)} {σs : List STy}
    {da : TypedArgs Γ es σs}, TypedArgs.inferN n Γ es = some ⟨σs, da⟩ →
    (argExprs es).length < n ∧ σs.length = (argExprs es).length ∧
    ∀ i e σ, (argExprs es)[i]? = some e → σs[i]? = some σ →
      ∃ d, Typed.inferN (n - 1 - i) Γ e = some ⟨σ, d⟩
  | 0, _, _, _, h => by simp [argsN_zero] at h
  | _ + 1, .nil, _, _, h => by
      simp only [argsN_nil, Option.some.injEq] at h
      cases h
      exact ⟨by simp [argExprs], by simp [argExprs], fun _ _ _ hi => by simp [argExprs] at hi⟩
  | n + 1, .cons e es, _, _, h => by
      rw [argsN_cons] at h
      cases hd : Typed.inferN n Γ e with
      | none => simp [hd] at h
      | some r =>
          cases hds : TypedArgs.inferN n Γ es with
          | none => simp [hd, hds] at h
          | some rs =>
              simp only [hd, hds, Option.bind_some, Option.some.injEq] at h
              cases h
              obtain ⟨hn, hl, ht⟩ := each_of_argsN hds
              refine ⟨by simp [argExprs]; omega, by simp [argExprs, hl], fun i a σ hi hσ => ?_⟩
              cases i with
              | zero =>
                  simp only [argExprs, List.getElem?_cons_zero, Option.some.injEq] at hi hσ
                  subst hi hσ
                  exact ⟨r.2, by simpa using hd⟩
              | succ i =>
                  obtain ⟨d', hd'⟩ := ht i a σ (by simpa [argExprs] using hi) (by simpa using hσ)
                  exact ⟨d', by simpa [Nat.sub_sub, Nat.add_comm] using hd'⟩

end Solidity.Correctness.Lowering.Total.CalleeInference
