import Solidity.Correctness.Panic.Guards.Arith

/-!
# Arithmetic and assertion guard origins on concrete failures

Each family of `Correctness/Panic/Guards/Arith.lean` at a literal failing
operand: a signed division by zero, `x % 0`, `mulmod` by zero, a false
`assert` in both elaboration modes, and the `0x11` range guards (an
overflowing `x++`, signed `MIN / -1`, `-MIN`). Each emitted payload is the
solc code derived from the site.
-/

namespace Solidity.Examples.Panic.GuardsArith

open Solidity Solidity.Correctness.Panic Checked Semantics

variable {C : Contract} {Γ : Ctx} (σ : State C Γ)

/-- `5 / 0` at `int`: zero divisor, V1 bare revert, `Panic(0x12)` bytes. -/
example : Panic.Origin (.binary .div .int rfl ⟨5, by decide⟩ ⟨0, by decide⟩) .zeroDivisor ∧
    (Val.binop .div rfl rfl (litI (C := C) (Γ := Γ) 5 (by decide)) (litI 0 (by decide))).evalT σ =
      .error .revert ∧
    (panicStmt Panic.Site.zeroDivisor.code
      (cmpI .neB rfl rfl (litI (C := C) (Γ := Γ) 0 (by decide)) (litI 0 (by decide)))).runR σ =
        .error (THalt.ofData (encodePanic 0x12)) :=
  (int_div_zero_source σ (litI 5 (by decide)) (litI 0 (by decide)) _ _ rfl rfl rfl).2

/-- `7 % 0` at `uint`. -/
example : Panic.Origin (.binary .mod .uint rfl ⟨7, by decide⟩ ⟨0, by decide⟩) .zeroDivisor ∧
    (Val.binop .mod rfl rfl (litU (C := C) (Γ := Γ) 7 (by decide)) (litU 0 (by decide))).evalT σ =
      .error .revert :=
  let h := uint_mod_source σ (litU 7 (by decide)) (litU 0 (by decide)) _ _ rfl rfl rfl
  ⟨h.2.1, h.2.2.1⟩

/-- `mulmod(3, 4, 0)`: the modulus guard emits `Panic(0x12)`. -/
example : Panic.Origin (.modular .mulmod ⟨3, by decide⟩ ⟨4, by decide⟩ ⟨0, by decide⟩)
      .zeroDivisor ∧
    (panicStmt Panic.Site.zeroDivisor.code
      (cmpU .neB rfl rfl (litU (C := C) (Γ := Γ) 0 (by decide)) (litU 0 (by decide)))).runR σ =
        .error (THalt.ofData (encodePanic 0x12)) :=
  let h := modular_source σ .mulmod (litU 3 (by decide)) (litU 4 (by decide))
    (litU 0 (by decide)) _ _ _ rfl rfl rfl rfl
  ⟨h.2.1, h.2.2.2⟩

/-- `assert(false)`: V1's legacy panic, and `Panic(0x01)` bytes where the
data is retained. -/
example : (Stmt.assert (C := C) (Γ := Γ) (.simple (.bool false))).runR σ = .error .panic ∧
    (Stmt.ite (.simple (.bool false)) .nil
      (.cons (.revertData [.bytes (encodePanic 1)]) .nil)).runR σ =
      .error (THalt.ofData (encodePanic 0x01)) :=
  (assert_source σ (.simple (.bool false)) rfl).2

section
variable [FreshNames] (rc : ElabRec C) (c : RawExpr)

/-- A self-call's callee elaborates `assert` to the data-retaining branch. -/
example : elabStmt1With C rc (.assert c) { funs := [], selfFrame := true } = (do
      let Γ ← nctx
      pure [.of Γ (.ite (← checkIn C Γ .bool c) .nil
        (.cons (.revertData [.bytes (encodePanic Panic.Site.assertion.code)]) .nil))] :
      ElabM _) { funs := [], selfFrame := true } :=
  assert_elab_data rc c _ rfl

/-- The default scope keeps V1's `assert`. -/
example : elabStmt1With C rc (.assert c) { funs := [] } = (do
      let Γ ← nctx
      pure [.of Γ (.assert (← checkIn C Γ .bool c))] : ElabM _) { funs := [] } :=
  assert_elab_legacy rc c _ rfl

end

private def umax : Int := ((2 ^ 256 - 1 : Nat) : Int)

/-- `x++` at `type(uint256).max`: `bumpRange` is the `+ 1` range guard. -/
example : pg Panic.Site.arithmetic.code
      (bumpRange .postInc .uint (litU (C := C) (Γ := Γ) umax (by decide))) =
      [(0x11, cmpU .le rfl rfl (litU umax (by decide))
        (arU .addW rfl rfl (litU umax (by decide)) (litU 1 (by decide))))] ∧
    Panic.Origin (.binary .add .uint rfl ⟨umax, by decide⟩ ⟨1, by decide⟩) .arithmetic :=
  let h := uint_add_source σ (litU umax (by decide)) (litU 1 (by decide)) _ _ rfl rfl rfl
  ⟨h.1, h.2.1⟩

/-- `MIN / -1` at `int` overflows (`0x11`), unlike its zero divisor. -/
example : Panic.Origin (.binary .div .int rfl ⟨minI, by decide⟩ ⟨-1, by decide⟩) .arithmetic :=
  (int_div_overflow_source σ (litI minI (by decide)) (litI (-1) (by decide)) _ _
    rfl rfl rfl).2.1

/-- `-MIN` at `int`: the negation guard emits `Panic(0x11)`. -/
example : Panic.Origin (.neg ⟨minI, by decide⟩) .arithmetic ∧
    (panicStmt Panic.Site.arithmetic.code
      (cmpI .neB rfl rfl (litI (C := C) (Γ := Γ) minI (by decide))
        (litI minI (by decide)))).runR σ =
        .error (THalt.ofData (encodePanic 0x11)) :=
  let h := int_neg_source σ (litI minI (by decide)) _ rfl rfl
  ⟨h.2.1, h.2.2.2⟩

end Solidity.Examples.Panic.GuardsArith
