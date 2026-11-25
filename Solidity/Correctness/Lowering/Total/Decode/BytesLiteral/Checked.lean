import Solidity.Correctness.Lowering.Total.Decode.BytesLiteral

namespace Solidity.Correctness.Lowering.Total.Decode.BytesLiteral

variable [FreshNames]

/-- The literal branch of the actual contextual bytes conversion retains the
alignment result. The rewritten operand is irrelevant on this branch. -/
theorem aligned_of_conversion (C : Contract) (Γ : ECtx) {n v : Nat}
    {o e : RawExpr} {bs : List Nat} (literal : o.bytesLit? = some bs)
    (converted : toBytesAt C Γ n o e = .ok (.num v)) : bytesAlign n bs = .ok v := by
  unfold toBytesAt at converted
  rw [literal] at converted
  cases aligned : bytesAlign n bs with
  | error err =>
    simp only [aligned] at converted
    cases converted
  | ok x =>
    simp [aligned] at converted
    cases converted
    rfl

omit [FreshNames] in
private theorem literal_range (C : Contract) (Δ : NCtx) (p : PrimTy) (v : Int)
    (checked : (litAt C Δ p v).isOk = true) : p.inRange v = true := by
  unfold litAt at checked
  split at checked
  · rename_i hr
    exact hr
  · split at checked <;>
      simp [Except.isOk, Except.toBool] at checked

private theorem check_num_range (C : Contract) (Δ : NCtx) (p : PrimTy) (v : Nat)
    (checked : (check C Δ p (.num v)).isOk = true) : p.inRange (v : Int) = true := by
  apply literal_range C Δ
  simp only [check] at checked
  cases h : litAt C Δ p (v : Int) <;>
    simp [h, Except.isOk, Except.toBool, bind, Bind.bind, Except.bind, pure, Pure.pure] at checked ⊢

private theorem checked_uint_bound (C : Contract) (Δ : NCtx) {v : Nat}
    (checked : (check C Δ .uint (.num v)).isOk = true) : v < 2 ^ 256 := by
  have full := check_num_range C Δ .uint v checked
  simp only [PrimTy.inRange, decide_eq_true_eq] at full
  exact Int.ofNat_lt.mp full.2

/-- The existing narrow-width and full-word checks jointly bound a converted
literal. The full-word check matters at bytes32, where fitCheck returns early. -/
theorem range_of_checks (C : Contract) (Γ : ECtx) (Δ : NCtx) {n v : Nat}
    (width : n ≤ 32) (fitted : fitCheck C Γ .uint (8 * n) (.num v) = .ok ())
    (checked : (check C Δ .uint (.num v)).isOk = true) : v < 256 ^ n := by
  have power : 256 ^ n = 2 ^ (8 * n) := by rw [Nat.pow_mul]
  by_cases small : 8 * n < 256
  · have bound : (v : Int) ≤ ((2 ^ (8 * n) - 1 : Nat) : Int) := by
      by_cases h : (v : Int) ≤ ((2 ^ (8 * n) - 1 : Nat) : Int)
      · exact h
      · simp [fitCheck, show ¬256 ≤ 8 * n by omega, RawExpr.litVal?, intRange, h] at fitted
    have positive : 0 < 2 ^ (8 * n) := Nat.pow_pos (by decide)
    rw [power]
    exact Nat.lt_of_le_pred (by omega) (Int.ofNat_le.mp bound)
  · have hn : n = 32 := by omega
    subst n
    rw [power]
    exact checked_uint_bound C Δ checked


/-- Value faithfulness from the actual contextual conversion and its existing
checks, without a separately assumed mathematical range bound. This is a local
elaboration result; deriving these successful calls from Request.success and
proving Source evaluation correspondence remain integration obligations. -/
theorem faithful_checked (C : Contract) (Γ : ECtx) (Δ : NCtx) {n v : Nat}
    {o e : RawExpr} {bs : List Nat} (width : n ≤ 32)
    (literal : o.bytesLit? = some bs)
    (converted : toBytesAt C Γ n o e = .ok (.num v))
    (fitted : fitCheck C Γ .uint (8 * n) (.num v) = .ok ())
    (checked : (check C Δ .uint (.num v)).isOk = true) :
    Source.bytesNat (Source.fitBytes n (bytes bs)) = v :=
  faithful (aligned_of_conversion C Γ literal converted)
    (range_of_checks C Γ Δ width fitted checked)

end Solidity.Correctness.Lowering.Total.Decode.BytesLiteral
