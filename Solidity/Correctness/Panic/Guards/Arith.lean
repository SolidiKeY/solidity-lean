import Solidity.Syntax.Elab.Panic
import Solidity.Syntax.Elab.Arms

/-!
# Origins of the arithmetic and assertion panic guards

Local association for the guards the elaborator generates beside the
unsigned `/` divisor of `Syntax/Elab/Panic.lean`: the remaining divisors of
`Checked.divPG`, the modulus of `addmod`/`mulmod`, the `assert` arm of
`elabStmt1With`, and the `0x11` range guards of `Checked.range`,
`Checked.negRange` and `Checked.bumpRange`. Each family gives the guard
list's equation, the origin of its `Panic/Origins` producer at the evaluated
operands, the unguarded V1 failure, and the emitted panic bytes. Operand
reads are explicit hypotheses; no whole-program instrumentation equivalence
is claimed.
-/

namespace Solidity.Correctness.Panic

open Solidity Semantics Checked

variable {C : Contract} {Γ : Ctx}

/-! ## Divisors (`0x12`) -/

/-- The signed divisor guard after its operand is read. -/
theorem int_divisor_guard_eval (σ : State C Γ) (b : Val C Γ .int)
    (y : PrimTy.int.Denote) (read : b.evalT σ = .ok y) :
    (cmpI .neB rfl rfl b (litI 0 (by decide))).evalT σ = .ok (!decide (y.val = 0)) := by
  simp [cmpI, litI, Val.evalT, read, BinOp.shortT,
    Simple.evalT, PrimTy.ofLit, BinOp.evalT, BinOp.evalNum, TRes.ofOpt, bind, Except.bind]

/-- Unsigned `%`: guard list, origin, V1 bare revert and panic bytes. -/
theorem uint_mod_source (σ : State C Γ) (a b : Val C Γ .uint)
    (x y : PrimTy.uint.Denote) (left : a.evalT σ = .ok x) (right : b.evalT σ = .ok y)
    (failed : (cmpU .neB rfl rfl b (litU 0 (by decide))).evalT σ = .ok false) :
    divPG .mod .uint b = [(Panic.Site.zeroDivisor.code,
      cmpU .neB rfl rfl b (litU 0 (by decide)))] ∧
    Panic.Origin (.binary .mod .uint rfl x y) .zeroDivisor ∧
    (Val.binop .mod rfl rfl a b).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.zeroDivisor.code
      (cmpU .neB rfl rfl b (litU 0 (by decide)))).runR σ =
        .error (THalt.ofData (encodePanic Panic.Site.zeroDivisor.code)) := by
  rw [uint_divisor_guard_eval σ b y right] at failed
  have zero : y.val = 0 := by
    by_cases h : y.val = 0
    · exact h
    · simp [h] at failed
  refine ⟨rfl, ?_, ?_, panic_guard_source_failure σ _ ?_ _⟩
  · apply Panic.binary_origin
    · simp [Panic.Checked.op, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, zero]
    · simp [Panic.Checked.failure, PrimTy.key, zero]
  · simp [Val.evalT, left, right, BinOp.shortT, BinOp.evalT,
      BinOp.evalNum, BinOp.arithInt, zero, TRes.ofOpt, bind, Except.bind]
  · rw [uint_divisor_guard_eval σ b y right, zero]; rfl

/-- Signed `/` and `%` share their divisor guard, origin and V1 revert. -/
private theorem int_divisor (op : Panic.Checked) (hop : op = .div ∨ op = .mod)
    (σ : State C Γ) (a b : Val C Γ .int) (ha : op.op.accepts .int = true)
    (x y : PrimTy.int.Denote) (left : a.evalT σ = .ok x) (right : b.evalT σ = .ok y)
    (failed : (cmpI .neB rfl rfl b (litI 0 (by decide))).evalT σ = .ok false) :
    Panic.Origin (.binary op .int ha x y) .zeroDivisor ∧
    (Val.binop op.op ha rfl a b).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.zeroDivisor.code
      (cmpI .neB rfl rfl b (litI 0 (by decide)))).runR σ =
        .error (THalt.ofData (encodePanic Panic.Site.zeroDivisor.code)) := by
  rw [int_divisor_guard_eval σ b y right] at failed
  have zero : y.val = 0 := by
    by_cases h : y.val = 0
    · exact h
    · simp [h] at failed
  refine ⟨?_, ?_, panic_guard_source_failure σ _ ?_ _⟩
  · apply Panic.binary_origin <;> rcases hop with rfl | rfl <;>
      simp [Panic.Checked.op, Panic.Checked.failure, PrimTy.key, BinOp.evalT,
        BinOp.evalNum, BinOp.arithInt, zero]
  · rcases hop with rfl | rfl <;>
      simp [Panic.Checked.op, Val.evalT, left, right, BinOp.shortT, BinOp.evalT,
        BinOp.evalNum, BinOp.arithInt, zero, TRes.ofOpt, bind, Except.bind]
  · rw [int_divisor_guard_eval σ b y right, zero]; rfl

/-- Signed `/` by zero: guard list, origin, V1 bare revert and panic bytes. -/
theorem int_div_zero_source (σ : State C Γ) (a b : Val C Γ .int)
    (x y : PrimTy.int.Denote) (left : a.evalT σ = .ok x) (right : b.evalT σ = .ok y)
    (failed : (cmpI .neB rfl rfl b (litI 0 (by decide))).evalT σ = .ok false) :
    divPG .div .int b = [(Panic.Site.zeroDivisor.code,
      cmpI .neB rfl rfl b (litI 0 (by decide)))] ∧
    Panic.Origin (.binary .div .int rfl x y) .zeroDivisor ∧
    (Val.binop .div rfl rfl a b).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.zeroDivisor.code
      (cmpI .neB rfl rfl b (litI 0 (by decide)))).runR σ =
        .error (THalt.ofData (encodePanic Panic.Site.zeroDivisor.code)) :=
  ⟨rfl, int_divisor .div (.inl rfl) σ a b rfl x y left right failed⟩

/-- Signed `%` by zero: guard list, origin, V1 bare revert and panic bytes. -/
theorem int_mod_source (σ : State C Γ) (a b : Val C Γ .int)
    (x y : PrimTy.int.Denote) (left : a.evalT σ = .ok x) (right : b.evalT σ = .ok y)
    (failed : (cmpI .neB rfl rfl b (litI 0 (by decide))).evalT σ = .ok false) :
    divPG .mod .int b = [(Panic.Site.zeroDivisor.code,
      cmpI .neB rfl rfl b (litI 0 (by decide)))] ∧
    Panic.Origin (.binary .mod .int rfl x y) .zeroDivisor ∧
    (Val.binop .mod rfl rfl a b).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.zeroDivisor.code
      (cmpI .neB rfl rfl b (litI 0 (by decide)))).runR σ =
        .error (THalt.ofData (encodePanic Panic.Site.zeroDivisor.code)) :=
  ⟨rfl, int_divisor .mod (.inr rfl) σ a b rfl x y left right failed⟩

/-! ## `addmod` and `mulmod` (`0x12`) -/

/-- The modulus guard is the last of the modular value's guard list; a
failed guard is the zero modulus of the `.modular` producer. -/
theorem modular_source (σ : State C Γ) (op : ModOp) (a b k : Val C Γ .uint)
    (x y m : PrimTy.uint.Denote) (ra : a.evalT σ = .ok x) (rb : b.evalT σ = .ok y)
    (rk : k.evalT σ = .ok m)
    (failed : (cmpU .neB rfl rfl k (litU 0 (by decide))).evalT σ = .ok false) :
    (Val.modular op a b k).panics = a.panics ++ b.panics ++ k.panics ++
      [(Panic.Site.zeroDivisor.code, cmpU .neB rfl rfl k (litU 0 (by decide)))] ∧
    Panic.Origin (.modular op x y m) .zeroDivisor ∧
    (Val.modular op a b k).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.zeroDivisor.code
      (cmpU .neB rfl rfl k (litU 0 (by decide)))).runR σ =
        .error (THalt.ofData (encodePanic Panic.Site.zeroDivisor.code)) := by
  rw [uint_divisor_guard_eval σ k m rk] at failed
  have zero : m.val = 0 := by
    by_cases h : m.val = 0
    · exact h
    · simp [h] at failed
  refine ⟨by simp [Val.panics]; rfl, Panic.modular_zero_origin op x y m zero, ?_,
    panic_guard_source_failure σ _ ?_ _⟩
  · simp [Val.evalT, ra, rb, rk, ModOp.evalT, zero, TRes.ofOpt, bind, Except.bind]
  · rw [uint_divisor_guard_eval σ k m rk, zero]; rfl

/-! ## `assert` (`0x01`) -/

section
variable [FreshNames]

/-- The `assert` arm of `elabStmt1With`: panic data where a failure's bytes
are observed (a self-call's callee or a retaining entry), V1's `assert`
otherwise. -/
theorem assert_elab_source (rc : ElabRec C) (c : RawExpr) :
    elabStmt1With C rc (.assert c) = (do
      let Γ ← nctx
      if (← read).selfFrame || (← read).retainFailureData then
        return [.of Γ (.ite (← checkIn C Γ .bool c) .nil
          (.cons (.revertData [.bytes (Semantics.encodePanic 1)]) .nil))]
      pure [.of Γ (.assert (← checkIn C Γ .bool c))]) := rfl

end

/-- A false assertion condition: the assertion producer's origin, V1's
panic for the legacy statement, and the data-retaining statement's bytes. -/
theorem assert_source (σ : State C Γ) (c : Val C Γ .bool)
    (failed : c.evalT σ = .ok false) :
    Panic.Origin (.assertion false) .assertion ∧
    (Stmt.assert c).runR σ = .error .panic ∧
    (Stmt.ite c .nil (.cons (.revertData [.bytes (Semantics.encodePanic 1)]) .nil)).runR σ =
      .error (THalt.ofData (encodePanic Panic.Site.assertion.code)) :=
  ⟨Panic.assertion_origin, Panic.assertion_v1 σ c failed,
    panic_guard_source_failure σ c failed _⟩

end Solidity.Correctness.Panic
