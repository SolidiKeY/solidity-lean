import Solidity.Correctness.Lowering.Total.Decode.SuccessfulExpr
import Solidity.Source.Value

/-! Concrete Source inference checks for effects and arrays. These are model
checks, not producer completeness or external EVM validation. -/
namespace Solidity.Examples.Lowering.Total.SuccessfulExpr
open Source

private def Γ : Ctx :=
  { env := (Syn.unit .nil).env, scope := none, locals := [("x", .int IntTy.u256), ("b", .bool)] }
private def ty (e : Syn .expr) : Option STy := (Typed.infer Γ e).map (·.1)
private def one : Syn .expr := .lit (.num (.dec 1 0 0))

-- Numeric locals accept prefix and suffix forms; booleans and rvalues are refused.
#guard ty (.unaryPrefix .inc (.ident "x")) = some (.int IntTy.u256)
#guard ty (.unarySuffix .dec (.ident "x")) = some (.int IntTy.u256)
#guard ty (.unarySuffix .inc (.ident "b")) = none
#guard ty (.unaryPrefix .inc one) = none
#guard ty (.unaryPrefix .delete (.ident "x")) = some (.tuple [])
-- Allocation accepts an integer size and refuses a boolean size.
#guard ty (.call (.new (.array (.elem (.int false 256 (by decide))) .none))
  (.positional (.cons one .nil))) = some (.array .memory (.int IntTy.u256) none)
#guard ty (.call (.new (.array (.elem (.int false 256 (by decide))) .none))
  (.positional (.cons (.lit (.bool true)) .nil))) = none

-- Inline arrays require a common one-word element type.
#guard ty (.inlineArray (.ident "x") (.cons one .nil)) =
  some (.array .memory (.int IntTy.u256) (some 2))
#guard ty (.inlineArray (.ident "x") (.cons (.lit (.bool true)) .nil)) = none

end Solidity.Examples.Lowering.Total.SuccessfulExpr
