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
