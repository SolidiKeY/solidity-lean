import Solidity.Syntax.Elab.Panic
import Solidity.Syntax.Elab.Arms

/-!
# Origins of the arithmetic and assertion panic guards

Local association for the guards the elaborator generates beside the
unsigned `/` divisor of `Syntax/Elab/Panic.lean`: the remaining divisors of
`Checked.divPG`, the modulus of `addmod`/`mulmod`, the `assert` arm of
`elabStmt1With`, and the `0x11` range guards of `Checked.range`,
`Checked.negRange` and `Checked.bumpRange`, except signed `*` (`rangeI .mul`,
not covered here). Each family gives the guard
list's equation, the origin of its `Panic/Origins` producer at the evaluated
operands, the unguarded V1 failure, and the emitted panic bytes. Operand
reads are explicit hypotheses; no whole-program instrumentation claim.
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

/-- The data-retaining mode emits `panicStmt` at the assertion site's code. -/
theorem assert_elab_data (rc : ElabRec C) (c : RawExpr) (scope : ElabScope)
    (data : (scope.selfFrame || scope.retainFailureData) = true) :
    elabStmt1With C rc (.assert c) scope = (do
      let Γ ← nctx
      pure [.of Γ (.ite (← checkIn C Γ .bool c) .nil
        (.cons (.revertData [.bytes (Semantics.encodePanic 1)]) .nil))] : ElabM _) scope := by
  rcases scope with ⟨_, _, _, _, _, _, self, retain, _, _⟩
  cases self <;> cases retain <;> first | rfl | simp at data

/-- Otherwise the arm keeps V1's `assert`. -/
theorem assert_elab_legacy (rc : ElabRec C) (c : RawExpr) (scope : ElabScope)
    (legacy : (scope.selfFrame || scope.retainFailureData) = false) :
    elabStmt1With C rc (.assert c) scope = (do
      let Γ ← nctx
      pure [.of Γ (.assert (← checkIn C Γ .bool c))] : ElabM _) scope := by
  rcases scope with ⟨_, _, _, _, _, _, self, retain, _, _⟩
  cases self <;> cases retain <;> first | rfl | simp at legacy

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

/-! ## Range guards (`0x11`)

`Checked.range` at `+`, `-` (both types), unsigned `*` and signed `/`, and
`Checked.negRange`; not signed `*` (`rangeI .mul`), which has no theorem here. `bumpRange` (`x++`, `x--`) is `rangeU`/`rangeI` at the
literal `1`, and the compound and push forms apply `range` to the target's
value or the default `0`: they are instances of these theorems. -/

/-- Unsigned `+`: the wrapping-sum guard failed exactly on overflow. -/
theorem uint_add_source (σ : State C Γ) (a b : Val C Γ .uint)
    (x y : PrimTy.uint.Denote) (left : a.evalT σ = .ok x) (right : b.evalT σ = .ok y)
    (failed : (cmpU .le rfl rfl a (arU .addW rfl rfl a b)).evalT σ = .ok false) :
    pg Panic.Site.arithmetic.code (range .add .uint a b) =
      [(Panic.Site.arithmetic.code, cmpU .le rfl rfl a (arU .addW rfl rfl a b))] ∧
    Panic.Origin (.binary .add .uint rfl x y) .arithmetic ∧
    (Val.binop .add rfl rfl a b).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.arithmetic.code
      (cmpU .le rfl rfl a (arU .addW rfl rfl a b))).runR σ =
        .error (THalt.ofData (encodePanic Panic.Site.arithmetic.code)) := by
  have guard := failed
  have hx := x.2; have hy := y.2
  simp [PrimTy.inRange] at hx hy
  simp [cmpU, arU, Val.evalT, left, right, BinOp.shortT, BinOp.evalT, BinOp.evalNum,
    BinOp.arithInt, PrimTy.ofInt?, PrimTy.inRange, Semantics.uintBound, TRes.ofOpt,
    bind, Except.bind] at guard
  rw [dif_pos (by omega)] at guard
  simp at guard
  have over := of_decide_eq_false guard
  refine ⟨rfl, ?_, ?_, panic_guard_source_failure σ _ failed _⟩
  · apply Panic.binary_origin
    · simp [Panic.Checked.op, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, PrimTy.ofInt?,
        PrimTy.inRange]
      omega
    · rfl
  · simp [Val.evalT, left, right, BinOp.shortT, BinOp.evalT, BinOp.evalNum,
      BinOp.arithInt, PrimTy.ofInt?, PrimTy.inRange, TRes.ofOpt, bind, Except.bind]
    rw [dif_neg (by omega)]

/-- Unsigned `-`: the guard `b <= a` failed exactly on underflow. -/
theorem uint_sub_source (σ : State C Γ) (a b : Val C Γ .uint)
    (x y : PrimTy.uint.Denote) (left : a.evalT σ = .ok x) (right : b.evalT σ = .ok y)
    (failed : (cmpU .le rfl rfl b a).evalT σ = .ok false) :
    pg Panic.Site.arithmetic.code (range .sub .uint a b) =
      [(Panic.Site.arithmetic.code, cmpU .le rfl rfl b a)] ∧
    Panic.Origin (.binary .sub .uint rfl x y) .arithmetic ∧
    (Val.binop .sub rfl rfl a b).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.arithmetic.code (cmpU .le rfl rfl b a)).runR σ =
        .error (THalt.ofData (encodePanic Panic.Site.arithmetic.code)) := by
  have guard := failed
  simp [cmpU, Val.evalT, left, right, BinOp.shortT, BinOp.evalT, BinOp.evalNum,
    TRes.ofOpt, bind, Except.bind] at guard
  have under := of_decide_eq_false guard
  refine ⟨rfl, ?_, ?_, panic_guard_source_failure σ _ failed _⟩
  · apply Panic.binary_origin
    · simp [Panic.Checked.op, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, PrimTy.ofInt?, PrimTy.inRange]
      omega
    · rfl
  · simp [Val.evalT, left, right, BinOp.shortT, BinOp.evalT, BinOp.evalNum,
      BinOp.arithInt, PrimTy.ofInt?, PrimTy.inRange, TRes.ofOpt, bind, Except.bind]
    rw [dif_neg (by omega)]

/-- Unsigned `*`: the guard `a == 0 || (a *% b) / a == b` failed exactly on
overflow. -/
theorem uint_mul_source (σ : State C Γ) (a b : Val C Γ .uint)
    (x y : PrimTy.uint.Denote) (left : a.evalT σ = .ok x) (right : b.evalT σ = .ok y)
    (failed : (orB (cmpU .eqB rfl rfl a (litU 0 (by decide)))
      (cmpU .eqB rfl rfl (arU .div rfl rfl (arU .mulW rfl rfl a b) a) b)).evalT σ =
        .ok false) :
    pg Panic.Site.arithmetic.code (range .mul .uint a b) =
      [(Panic.Site.arithmetic.code, orB (cmpU .eqB rfl rfl a (litU 0 (by decide)))
        (cmpU .eqB rfl rfl (arU .div rfl rfl (arU .mulW rfl rfl a b) a) b))] ∧
    Panic.Origin (.binary .mul .uint rfl x y) .arithmetic ∧
    (Val.binop .mul rfl rfl a b).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.arithmetic.code (orB (cmpU .eqB rfl rfl a (litU 0 (by decide)))
      (cmpU .eqB rfl rfl (arU .div rfl rfl (arU .mulW rfl rfl a b) a) b))).runR σ =
        .error (THalt.ofData (encodePanic Panic.Site.arithmetic.code)) := by
  have guard := failed
  have hx := x.2; have hy := y.2
  simp [PrimTy.inRange] at hx hy
  by_cases zero : x.val = 0
  · simp [orB, cmpU, litU, Val.evalT, left, BinOp.shortT, Simple.evalT, PrimTy.ofLit,
      BinOp.evalT, BinOp.evalNum, TRes.ofOpt, bind, Except.bind, pure, Except.pure, zero] at guard
  simp [orB, cmpU, arU, litU, Val.evalT, left, right, BinOp.shortT, Simple.evalT,
    PrimTy.ofLit, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, PrimTy.ofInt?, PrimTy.inRange,
    Semantics.uintBound, TRes.ofOpt, bind, Except.bind, zero, BinOp.evalBool] at guard
  have m0 : 0 ≤ x.val * y.val % 115792089237316195423570985008687907853269984665640564039457584007913129639936 :=
    Int.emod_nonneg _ (by decide)
  have q0 := Int.tdiv_nonneg m0 hx.1
  have q1 := Int.tdiv_le_self x.val m0
  rw [dif_pos (by omega)] at guard
  simp at guard
  rw [dif_pos (by omega)] at guard
  simp at guard
  have over : ¬ x.val * y.val < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    intro h
    have ne := of_decide_eq_false guard
    rw [Int.emod_eq_of_lt (Int.mul_nonneg hx.1 hy.1) h, Int.mul_tdiv_cancel_left _ zero] at ne
    exact ne rfl
  refine ⟨rfl, ?_, ?_, panic_guard_source_failure σ _ failed _⟩
  · apply Panic.binary_origin
    · simp [Panic.Checked.op, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, PrimTy.ofInt?, PrimTy.inRange]
      omega
    · rfl
  · simp [Val.evalT, left, right, BinOp.shortT, BinOp.evalT, BinOp.evalNum,
      BinOp.arithInt, PrimTy.ofInt?, PrimTy.inRange, TRes.ofOpt, bind, Except.bind]
    rw [dif_neg (by omega)]

/-- Signed `/`: the guard `!(a == MIN && b == -1)` failed exactly at the one
overflowing quotient (the zero divisor is `int_div_zero_source`'s). -/
theorem int_div_overflow_source (σ : State C Γ) (a b : Val C Γ .int)
    (x y : PrimTy.int.Denote) (left : a.evalT σ = .ok x) (right : b.evalT σ = .ok y)
    (failed : (notB (andB (cmpI .eqB rfl rfl a (litI minI (by decide)))
      (cmpI .eqB rfl rfl b (litI (-1) (by decide))))).evalT σ = .ok false) :
    pg Panic.Site.arithmetic.code (range .div .int a b) =
      [(Panic.Site.arithmetic.code, notB (andB (cmpI .eqB rfl rfl a (litI minI (by decide)))
        (cmpI .eqB rfl rfl b (litI (-1) (by decide)))))] ∧
    Panic.Origin (.binary .div .int rfl x y) .arithmetic ∧
    (Val.binop .div rfl rfl a b).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.arithmetic.code (notB (andB (cmpI .eqB rfl rfl a (litI minI (by decide)))
      (cmpI .eqB rfl rfl b (litI (-1) (by decide)))))).runR σ =
        .error (THalt.ofData (encodePanic Panic.Site.arithmetic.code)) := by
  have guard := failed
  have hx : x.val = minI ∧ y.val = -1 := by
    by_cases hx : x.val = minI <;> by_cases hy : y.val = -1 <;>
      simp_all [notB, andB, cmpI, litI, Val.evalT, BinOp.shortT, Simple.evalT, PrimTy.ofLit,
        BinOp.evalT, BinOp.evalNum, BinOp.evalBool, UnOp.evalT, TRes.ofOpt, bind, Except.bind,
        pure, Except.pure]
  refine ⟨rfl, ?_, ?_, panic_guard_source_failure σ _ failed _⟩
  · apply Panic.binary_origin
    · simp [Panic.Checked.op, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, PrimTy.ofInt?, PrimTy.inRange,
        hx.1, hx.2, minI]
    · simp [Panic.Checked.failure, PrimTy.key, hx.2]
  · simp [Val.evalT, left, right, BinOp.shortT, BinOp.evalT, BinOp.evalNum,
      BinOp.arithInt, PrimTy.ofInt?, PrimTy.inRange, TRes.ofOpt, bind, Except.bind, hx.1, hx.2, minI]

/-- Signed `-a`: the guard `a != MIN` failed exactly at the one overflowing
negation. -/
theorem int_neg_source (σ : State C Γ) (a : Val C Γ .int) (x : PrimTy.int.Denote)
    (read : a.evalT σ = .ok x)
    (failed : (cmpI .neB rfl rfl a (litI minI (by decide))).evalT σ = .ok false) :
    pg Panic.Site.arithmetic.code (negRange .int a) =
      [(Panic.Site.arithmetic.code, cmpI .neB rfl rfl a (litI minI (by decide)))] ∧
    Panic.Origin (.neg x) .arithmetic ∧
    (Val.unop .neg rfl rfl a).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.arithmetic.code (cmpI .neB rfl rfl a (litI minI (by decide)))).runR σ =
        .error (THalt.ofData (encodePanic Panic.Site.arithmetic.code)) := by
  have guard := failed
  simp [cmpI, litI, Val.evalT, read, BinOp.shortT, Simple.evalT, PrimTy.ofLit,
    BinOp.evalT, BinOp.evalNum, TRes.ofOpt, bind, Except.bind] at guard
  replace guard : x.val = minI := by
    by_cases h : x.val = minI
    · exact h
    · simp [h] at guard
  refine ⟨rfl, Panic.neg_origin x ?_, ?_, panic_guard_source_failure σ _ failed _⟩
  · simp [UnOp.evalT, PrimTy.ofInt?, PrimTy.inRange, guard, minI]
  · simp [Val.evalT, read, UnOp.evalT, PrimTy.ofInt?, PrimTy.inRange, guard, minI, TRes.ofOpt, bind,
      Except.bind]

/-- Signed `+`: the generated guard (`b >= 0 ? … : …`, `Checked.rangeI`)
failed exactly on overflow. -/
theorem int_add_source (σ : State C Γ) (a b : Val C Γ .int)
    (x y : PrimTy.int.Denote) (left : a.evalT σ = .ok x) (right : b.evalT σ = .ok y)
    (g : Val C Γ .bool) (gen : range .add .int a b = some g)
    (failed : g.evalT σ = .ok false) :
    pg Panic.Site.arithmetic.code (range .add .int a b) = [(Panic.Site.arithmetic.code, g)] ∧
    Panic.Origin (.binary .add .int rfl x y) .arithmetic ∧
    (Val.binop .add rfl rfl a b).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.arithmetic.code g).runR σ =
        .error (THalt.ofData (encodePanic Panic.Site.arithmetic.code)) := by
  refine ⟨by rw [gen]; rfl, ?_, ?_, panic_guard_source_failure σ g failed _⟩ <;>
  · have hx := x.2; have hy := y.2
    simp [PrimTy.inRange] at hx hy
    have over : ¬(-57896044618658097711785492504343953926634992332820282019728792003956564819968 ≤
        x.val + y.val ∧
        x.val + y.val < 57896044618658097711785492504343953926634992332820282019728792003956564819968) := by
      simp only [range, rangeI, Option.some.injEq] at gen
      subst gen
      by_cases hy0 : 0 ≤ y.val <;>
        simp [cmpI, arI, litI, Val.evalT, left, right, BinOp.shortT, Simple.evalT, PrimTy.ofLit,
          BinOp.evalT, BinOp.evalNum, BinOp.arithInt, PrimTy.ofInt?, PrimTy.inRange, maxI, minI,
          TRes.ofOpt, bind, Except.bind, hy0] at failed <;>
        rw [dif_pos (by omega)] at failed <;>
        simp at failed <;>
        (have := of_decide_eq_false failed; omega)
    simp [Panic.Origin, Panic.Producer.run, Panic.checked, Panic.Checked.op, Val.evalT, left,
      right, BinOp.shortT, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, PrimTy.ofInt?,
      PrimTy.inRange, TRes.ofOpt, bind, Except.bind]
    rw [dif_neg over]
    try rfl

/-- Signed `-`: the generated guard (`b >= 0 ? … : …`, `Checked.rangeI`)
failed exactly on overflow. -/
theorem int_sub_source (σ : State C Γ) (a b : Val C Γ .int)
    (x y : PrimTy.int.Denote) (left : a.evalT σ = .ok x) (right : b.evalT σ = .ok y)
    (g : Val C Γ .bool) (gen : range .sub .int a b = some g)
    (failed : g.evalT σ = .ok false) :
    pg Panic.Site.arithmetic.code (range .sub .int a b) = [(Panic.Site.arithmetic.code, g)] ∧
    Panic.Origin (.binary .sub .int rfl x y) .arithmetic ∧
    (Val.binop .sub rfl rfl a b).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.arithmetic.code g).runR σ =
        .error (THalt.ofData (encodePanic Panic.Site.arithmetic.code)) := by
  refine ⟨by rw [gen]; rfl, ?_, ?_, panic_guard_source_failure σ g failed _⟩ <;>
  · have hx := x.2; have hy := y.2
    simp [PrimTy.inRange] at hx hy
    have over : ¬(-57896044618658097711785492504343953926634992332820282019728792003956564819968 ≤
        x.val - y.val ∧
        x.val - y.val < 57896044618658097711785492504343953926634992332820282019728792003956564819968) := by
      simp only [range, rangeI, Option.some.injEq] at gen
      subst gen
      by_cases hy0 : 0 ≤ y.val <;>
        simp [cmpI, arI, litI, Val.evalT, left, right, BinOp.shortT, Simple.evalT, PrimTy.ofLit,
          BinOp.evalT, BinOp.evalNum, BinOp.arithInt, PrimTy.ofInt?, PrimTy.inRange, maxI, minI,
          TRes.ofOpt, bind, Except.bind, hy0] at failed <;>
        rw [dif_pos (by omega)] at failed <;>
        simp at failed <;>
        (have := of_decide_eq_false failed; omega)
    simp [Panic.Origin, Panic.Producer.run, Panic.checked, Panic.Checked.op, Val.evalT, left,
      right, BinOp.shortT, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, PrimTy.ofInt?,
      PrimTy.inRange, TRes.ofOpt, bind, Except.bind]
    rw [dif_neg over]
    try rfl

end Solidity.Correctness.Panic
