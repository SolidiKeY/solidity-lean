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

open Solidity.Correctness.Lowering.Total.Decode.SuccessfulExpr

-- Apply each exported family to a concrete Source inference problem.
example : ∃ d, Typed.inferN 3 Γ (.unaryPrefix .inc (.ident "x")) =
    some ⟨.int IntTy.u256, d⟩ := ⟨_, inferN_preInc rfl rfl⟩
example : ∃ d, Typed.inferN 3 Γ (.unaryPrefix .dec (.ident "x")) =
    some ⟨.int IntTy.u256, d⟩ := ⟨_, inferN_preDec rfl rfl⟩
example : ∃ d, Typed.inferN 3 Γ (.unarySuffix .inc (.ident "x")) =
    some ⟨.int IntTy.u256, d⟩ := ⟨_, inferN_suffix .inc rfl rfl⟩
example : Typed.inferN 3 Γ (.unarySuffix .inc (.ident "b")) = none :=
  inferN_suffix_refused .inc rfl rfl
example : ∃ d, Typed.inferN 3 Γ (.unaryPrefix .delete (.ident "x")) =
    some ⟨.tuple [], d⟩ := ⟨_, inferN_delete rfl rfl rfl⟩
example : ∃ d, Typed.inferN 3 Γ (.inlineArray (.ident "x") (.cons one .nil)) =
    some ⟨.array .memory (.int IntTy.u256) (some 2), d⟩ :=
  ⟨_, inferN_inlineArray (τs := [.rational (NumLit.dec 1 0 0).value]) rfl rfl rfl rfl rfl⟩
example : ∃ d, Typed.inferN 3 Γ
    (.call (.new (.array (.elem (.int false 256 (by decide))) .none))
      (.positional (.cons one .nil))) =
    some ⟨.array .memory (.int IntTy.u256) none, d⟩ :=
  ⟨_, inferN_newArray rfl rfl rfl rfl⟩

end Solidity.Examples.Lowering.Total.SuccessfulExpr
