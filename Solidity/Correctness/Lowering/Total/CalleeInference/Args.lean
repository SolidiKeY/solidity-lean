import Solidity.Source.Infer

/-!
# Argument-list inference at the fuel `TypedArgs.inferN` uses

Equations of the actual `Source.TypedArgs.inferN` over an ordered positional
list (`argExprs`): a cons infers its head at one less fuel, then its tail at that
fuel, so position `i` gets `n - 1 - i`. Failure propagates from any position or
from too little fuel; success follows from the individual results
(`argsN_of_each`).
-/
namespace Solidity.Correctness.Lowering.Total.CalleeInference

open Source (STy Syn Ctx Typed TypedArgs)

/-- The ordered positional arguments of an argument list. -/
def argExprs : Syn (.list .expr) → List (Syn .expr)
  | .nil => []
  | .cons e es => e :: argExprs es

variable {Γ : Ctx} {n : Nat} {e : Syn .expr} {es : Syn (.list .expr)}

theorem argsN_zero : TypedArgs.inferN 0 Γ es = none := by simp only [TypedArgs.inferN]

theorem argsN_nil : TypedArgs.inferN (n + 1) Γ .nil = some ⟨[], .nil⟩ := by simp [TypedArgs.inferN]

/-- The cons step: the head at one less fuel, then the tail at that fuel. -/
theorem argsN_cons :
    TypedArgs.inferN (n + 1) Γ (.cons e es) =
      (Typed.inferN n Γ e).bind fun r =>
        (TypedArgs.inferN n Γ es).bind fun rs => some ⟨r.1 :: rs.1, .cons r.2 rs.2⟩ := by
  simp only [TypedArgs.inferN]; rfl

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
  rw [argsN_cons]; cases Typed.inferN n Γ e <;> simp [h]

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
      subst hi; exact argsN_head_none (by simpa using h)
  | n + 1, i + 1, .cons _ es, _, hi, h =>
      argsN_tail_none (argsN_fail_at (n := n) (i := i) (es := es)
        (by simpa [argExprs] using hi) (by simpa [Nat.sub_sub, Nat.add_comm] using h))

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

end Solidity.Correctness.Lowering.Total.CalleeInference
