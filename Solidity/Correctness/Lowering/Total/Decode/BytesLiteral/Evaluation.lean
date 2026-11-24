import Solidity.Correctness.Lowering.Total.Decode.BytesLiteral.Checked
import Solidity.Source.Eval

namespace Solidity.Correctness.Lowering.Total.Decode.BytesLiteral

/-- Model alignment success supplies the Source implicit-conversion length
check. No additional restriction on individual raw components is needed. -/
theorem conversion (E : Source.Env) {n v : Nat} {bs : List Nat}
    (width : 1 ≤ n ∧ n ≤ 32) (aligned : bytesAlign n bs = .ok v) :
    Source.Conv E.isBase E.mapFree (.stringLit (bytes bs)) (.fixedBytes n width) := by
  have len : bs.length ≤ n := by
    unfold bytesAlign at aligned
    split at aligned
    · cases aligned
    · omega
  apply Or.inl
  change decide ((bytes bs).length ≤ n) = true
  rw [length]
  exact decide_eq_true len

/-- The normalized spelling has the literal type used by Source resolution. -/
def typed (Γ : Source.Ctx) (bs : List Nat) :
    Source.Typed Γ (spelling bs) (.stringLit (bytes bs)) := .hexStr _

/-- The actual resolved literal, implicitly converted to its contextual fixed
width using the conversion check derived from model alignment. -/
def resolved (Γ : Source.Ctx) {n v : Nat} (bs : List Nat)
    (width : 1 ≤ n ∧ n ≤ 32) (aligned : bytesAlign n bs = .ok v) :
    Source.RExpr Γ.env Γ.tys (.fixedBytes n width) :=
  .conv (typed Γ bs).toR (conversion Γ.env width aligned)

/-- At every sufficient horizon the resolved fixed-bytes literal evaluates to
its padded bytes. Equality of the computations includes preservation of all
Source locals and state; it does not assert whole-program simulation. -/
theorem eval_resolved (Γ : Source.Ctx) (G : Source.Glob Γ.env) (F : Source.Fr)
    (k : Nat) {n v : Nat} (bs : List Nat) (width : 1 ≤ n ∧ n ≤ 32)
    (aligned : bytesAlign n bs = .ok v) :
    Source.evalE G F (k + 2) (resolved Γ bs width aligned) =
      pure (.val (Source.mkBytes (n := n) (h := width) (bytes bs))) := by
  simp only [resolved, typed, Source.Typed.toR, Source.evalE,
    pure_bind]
  rfl

/-- The Source runtime value obtained above has exactly the checked model
value. This joins evaluation to the local elaborator checks, not to
Request.success or the still-open shared semantic-boundary binding. -/
theorem evaluated_value [FreshNames] (C : Contract) (Γ : ECtx) (Δ : NCtx)
    {n v : Nat} {o e : RawExpr} {bs : List Nat} (width : 1 ≤ n ∧ n ≤ 32)
    (literal : o.bytesLit? = some bs)
    (converted : toBytesAt C Γ n o e = .ok (.num v))
    (fitted : fitCheck C Γ .uint (8 * n) (.num v) = .ok ())
    (checked : (check C Δ .uint (.num v)).isOk = true) (D : Source.Layout) :
    (Source.mkBytes (D := D) (n := n) (h := width) (bytes bs)).key = some (v : Int) := by
  change some (Source.bytesNat (Source.fitBytes n (bytes bs)) : Int) = some (v : Int)
  rw [faithful_checked C Γ Δ width.2 literal converted fitted checked]

end Solidity.Correctness.Lowering.Total.Decode.BytesLiteral
