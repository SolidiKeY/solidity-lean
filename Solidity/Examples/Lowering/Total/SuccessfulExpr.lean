import Solidity.Correctness.Lowering.Total.Decode.SuccessfulExpr
import Solidity.Source.Value

/-! Concrete Source inference checks for effects and arrays. These are model
checks, not producer completeness or external EVM validation. -/
namespace Solidity.Examples.Lowering.Total.SuccessfulExpr
open Source

private def Γ : Source.Ctx :=
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

-- Tuple mobility, environment admission, shadowing, and refusal boundaries.
example : ∃ d, Typed.inferN 3 Γ (.tuple (.some (.ident "x"))
    (.cons (.some (.ident "b")) .nil)) =
    some ⟨.tuple [.int IntTy.u256, .bool], d⟩ :=
  ⟨_, inferN_tuple (τ := .int IntTy.u256) (σ := .bool) (σs := []) rfl rfl⟩
example : ∃ d, Typed.inferN 3 Γ (.member (.ident "msg") "sender") =
    some ⟨.address false, d⟩ := ⟨_, inferN_magic rfl rfl rfl rfl⟩
#guard ty (.member (.ident "msg") "value") = some (.int IntTy.u256)
#guard ty (.member (.ident "block") "timestamp") = some (.int IntTy.u256)
#guard (Typed.infer {Γ with msgValue := false} (.member (.ident "msg") "value")).isNone
#guard (Typed.infer {Γ with locals := [("msg", .bool)]}
  (.member (.ident "msg") "sender")).isNone
#guard ty (.tuple (.some (.ident "x")) (.cons .none .nil)) = none

open Solidity.Correctness.Lowering.Total.Decode
open Solidity.Correctness.Lowering.Total.CallSpellExt

example (T : Tables) (bs : List Nat) :
    Calls.expr T registry1 (.bytesLit bs) = some (BytesLiteral.spelling bs) := bytes_call rfl bs
example (bs : List Nat) : ∃ d, Typed.inferN 1 Γ (BytesLiteral.spelling bs) =
    some ⟨.stringLit (BytesLiteral.bytes bs), d⟩ := ⟨_, inferN_bytes bs⟩
#guard (Calls.expr tables1 registry1 (.call bytesLitName [.bool true])).isNone

private def Γself : Source.Ctx :=
  {Γ with scope := some "C", env := (Syn.unit (.cons (.contract false "C" .none .nil .nil) .nil)).env}
example : ∃ d, Typed.inferN 2 Γself thisAddress = some ⟨.address false, d⟩ :=
  ⟨_, inferN_thisAddress rfl rfl⟩
example : ∃ d, Typed.inferN 3 Γself thisBalance = some ⟨.int IntTy.u256, d⟩ :=
  ⟨_, inferN_thisBalance rfl rfl⟩
#guard (Typed.infer {Γself with scope := none} thisAddress).isNone
#guard ty (.member (.ident "msg") "data") = none

-- Real producer helpers, with arbitrary contracts and concrete callback results.
-- The named-input callback example tests interface generality, not named lowering.
example (C : Contract) [FreshNames] (T : Tables) (R : Registry) :
    ElabControlProof.Obs (captureExpr C (.num 7))
      (fun out => ∃ t, ExprX T R out.2 t) := capture_spells C (.num 7)
example (C : Contract) [FreshNames] (T : Tables) (R : Registry) :
    ElabControlProof.Obs (captureBefore C (.name "x") [.incDec .preInc (.name "x")])
      (fun out => ∃ t, ExprX T R out.2 t) := captureBefore_spells C _ (.name "x")
example (C : Contract) [FreshNames] (T : Tables) (R : Registry) :
    ElabControlProof.Obs (hoistArgsWith C (fun _ => pure ([], .bool true))
      [.named "S" ["x"] [.num 1]])
      (fun out => ∃ ts, ExprsX T R out.2 ts ∧ Calls.exprs T R out.2 = some ts) :=
  hoistArgs_spells C _ _ (fun _ _ => ElabControlProof.obs_pure ⟨_, .bool true⟩)
example (C : Contract) [FreshNames] (T : Tables) (R : Registry) :
    ElabControlProof.Obs (hoistCallArgsWith C (fun _ => pure ([], .num 2))
      (fun _ => pure []) "f" [.bool true])
      (fun out => ∃ ts, ExprsX T R out.2 ts ∧ Calls.exprs T R out.2 = some ts) := by
  apply hoistCallArgs_spells
  · intro a ha; simp only [List.mem_singleton] at ha; subst a
    exact ⟨_, .bool true⟩
  · exact fun _ _ => ElabControlProof.obs_pure ⟨_, .num 2⟩

end Solidity.Examples.Lowering.Total.SuccessfulExpr
