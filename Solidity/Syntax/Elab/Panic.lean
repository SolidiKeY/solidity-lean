import Solidity.Syntax.Elab.Values
import Solidity.Semantics.Panic.Source

/-!
# Equations at transparent source panic producers

These equations retain the actual producer calls, scopes, captures and order.
They expose their intrinsic site constants without reclassifying arbitrary
revert data. They do not assert a theorem about the opaque recursive dispatch
or self-call elaborators. In particular an ignoring-overflow guard and an
ordinary require are not claimed to raise a panic.
-/

namespace Solidity

variable {C : Contract}

/-- The data-retaining checked guard uses the arithmetic site's code. -/
theorem checking_guard_source {Γ : Ctx} (condition : Val C Γ .bool) :
    OFMode.checking.guardStmt condition true =
      panicStmt Panic.Site.arithmetic.code condition := rfl

/-- Instrumentation preserves the generated guard list's order and leaves
its statement and tail after those guards. This is not result erasure. -/
theorem withPanics_source_cons {Γ Γ₁ Γ₂ : Ctx}
    (statement : Stmt C Γ Γ₁) (tail : Prog C Γ₁ Γ₂) :
    (Prog.cons statement tail).withPanics =
      statement.panics.foldr (fun (code, condition) rest =>
        .cons (panicStmt code condition) rest)
        (.cons statement.withPanics tail.withPanics) := rfl

variable [FreshNames]

/-- Exact equation for the existing narrowing producer. Its three modes
remain distinct; the data-retaining ordinary and checking branches emit
arithmetic panic bytes directly or through the checking-mode guard. No evaluation is moved ahead of the width bypass. -/
theorem narrowCheck_source (p : PrimTy) (width : Nat) (expression : RawExpr) :
    narrowCheck C p width expression = (do
      if 256 ≤ width then return []
      let Γ ← nctx
      let condition ← checkIn C Γ .bool (inTyCond p width expression)
      let scope ← read
      let data := scope.selfFrame || scope.retainFailureData
      pure [.of Γ (match (← read).overflow with
        | some mode => mode.guardStmt condition data
        | none => if data then panicStmt Panic.Site.arithmetic.code condition
                  else .require condition)]) := rfl

/-- The actual enum producer captures the operand once, then checks the
captured local. The legacy assertion is preserved beside the data branch. -/
theorem enumCapture_source (members : Nat) (expression : RawExpr) :
    enumCapture C members expression = (do
      let Γ ← nctx
      let value ← checkIn C Γ .uint expression
      let name ← captureAs C "se" (.val .uint)
      let captured : RawExpr := .name (toString name)
      let Γ' ← nctx
      let condition ← checkIn C Γ' .bool (.binop .lt captured (.num members))
      let scope ← read
      let check := if scope.selfFrame || scope.retainFailureData then
        panicStmt Panic.Site.enumConversion.code condition else .assert condition
      pure ([.of Γ (.declLocal .uint name (some value)), .of Γ' check], captured)) := rfl

omit [FreshNames] in
/-- Local enum origin after a supplied membership failure. No relation between
this value and the evaluated local of `enumCapture` is proved here. -/
theorem enum_value_source (members : Nat) (value : PrimTy.uint.Denote)
    (failed : ¬value.val.toNat < members) :
    Panic.Source.OriginV2 (.original (.enumConversion members value)) .enumConversion :=
  Panic.enum_origin members value failed

end Solidity

namespace Solidity
open Semantics
variable {C : Contract} {Γ : Ctx}

/-- Evaluate the actual unsigned divisor guard after its operand is read. -/
theorem uint_divisor_guard_eval (σ : State C Γ) (b : Val C Γ .uint)
    (y : PrimTy.uint.Denote) (read : b.evalT σ = .ok y) :
    (Checked.cmpU .neB rfl rfl b (Checked.litU 0 (by decide))).evalT σ =
      .ok (!decide (y.val = 0)) := by
  simp [Checked.cmpU, Checked.litU, Val.evalT, read, BinOp.shortT,
    Simple.evalT, PrimTy.ofLit, BinOp.evalT, BinOp.evalNum, TRes.ofOpt, bind, Except.bind]

/-- A failed divisor guard classifies the evaluated operation, retaining its V1 revert. -/
theorem uint_divisor_guard_origin (σ : State C Γ) (a b : Val C Γ .uint)
    (x y : PrimTy.uint.Denote) (left : a.evalT σ = .ok x)
    (right : b.evalT σ = .ok y)
    (failed : (Checked.cmpU .neB rfl rfl b (Checked.litU 0 (by decide))).evalT σ =
      .ok false) :
    Panic.Origin (.binary .div .uint rfl x y) .zeroDivisor ∧
      (Val.binop .div rfl rfl a b).evalT σ = .error .revert := by
  rw [uint_divisor_guard_eval σ b y right] at failed
  have zero : y.val = 0 := by
    by_cases h : y.val = 0
    · exact h
    · simp [h] at failed
  constructor
  · apply Panic.binary_origin
    · simp [Panic.Checked.op, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, zero]
    · simp [Panic.Checked.failure, PrimTy.key, zero]
  · simp [Val.evalT, left, right, BinOp.shortT, BinOp.evalT,
      BinOp.evalNum, BinOp.arithInt, zero, TRes.ofOpt, bind, Except.bind]

/-- A false generated guard emits precisely its own constructed panic data. -/
theorem panic_guard_source_failure (σ : State C Γ) (condition : Val C Γ .bool)
    (failed : condition.evalT σ = .ok false) (code : Nat) :
    (panicStmt code condition).runR σ =
      .error (THalt.ofData (encodePanic code)) := by
  simp [panicStmt, Stmt.runR, TRun.ite, failed, boolT,
    TRun.seq, TRun.revertData, RevPart.evalT, bind, Except.bind, Except.map, pure, Except.pure]

/-- A failed operand read is propagated, even if it carries arbitrary bytes;
it is not evidence that the guard's own site failed. -/
theorem panic_guard_source_halt (σ : State C Γ) (condition : Val C Γ .bool)
    (halt : THalt) (failed : condition.evalT σ = .error halt) (code : Nat) :
    (panicStmt code condition).runR σ = .error halt := by
  simp [panicStmt, Stmt.runR, TRun.ite, failed, bind, Except.bind]

/-- Association at the actual unsigned divisor-guard producer. Operand reads
are explicit; V1 bare revert and emitted panic bytes remain separate. This
local theorem does not claim whole-program instrumentation equivalence. -/
theorem uint_divisor_source (σ : State C Γ) (a b : Val C Γ .uint)
    (x y : PrimTy.uint.Denote) (left : a.evalT σ = .ok x)
    (right : b.evalT σ = .ok y)
    (failed : (Checked.cmpU .neB rfl rfl b (Checked.litU 0 (by decide))).evalT σ =
      .ok false) :
    Checked.divPG .div .uint b = [(Panic.Site.zeroDivisor.code,
      Checked.cmpU .neB rfl rfl b (Checked.litU 0 (by decide)))] ∧
    Panic.Origin (.binary .div .uint rfl x y) .zeroDivisor ∧
    (Val.binop .div rfl rfl a b).evalT σ = .error .revert ∧
    (panicStmt Panic.Site.zeroDivisor.code
      (Checked.cmpU .neB rfl rfl b (Checked.litU 0 (by decide)))).runR σ =
        .error (THalt.ofData (encodePanic Panic.Site.zeroDivisor.code)) :=
  ⟨rfl, (uint_divisor_guard_origin σ a b x y left right failed).1,
    (uint_divisor_guard_origin σ a b x y left right failed).2,
    panic_guard_source_failure σ _ failed _⟩

/-- Once the captured local is evaluated, the enum guard's numeric failure
is exactly the membership failure of the existing enum producer. The literal
range proof is the intrinsic type required to construct this typed guard. -/
theorem enum_guard_origin (σ : State C Γ) (captured : Val C Γ .uint)
    (value : PrimTy.uint.Denote) (members : Nat)
    (range : PrimTy.uint.inRange (members : Int) = true)
    (read : captured.evalT σ = .ok value)
    (failed : (Checked.cmpU .lt rfl rfl captured
      (Checked.litU members range)).evalT σ = .ok false) :
    Panic.Source.OriginV2 (.original (.enumConversion members value)) .enumConversion := by
  have evaluated : (Checked.cmpU .lt rfl rfl captured
      (Checked.litU members range)).evalT σ = .ok (decide (value.val < (members : Int))) := by
    simp [Checked.cmpU, Checked.litU, Val.evalT, read, BinOp.shortT,
      Simple.evalT, PrimTy.ofLit, BinOp.evalT, BinOp.evalNum,
      TRes.ofOpt, bind, Except.bind]
  rw [evaluated] at failed
  have bound : ¬value.val < (members : Int) := of_decide_eq_false (Except.ok.inj failed)
  apply enum_value_source
  have nonneg := PrimTy.uint_nonneg value
  omega

end Solidity
