import Solidity.Correctness.Lowering.Total.Versions
import Solidity.Correctness.Lowering.Total.Decode.Self
import Solidity.Source.Eval

/-!
# The self-aware decoder version: `address(this)` and its balance

`Decode.tablesT` spells the model's own address and own balance. Here:

* `soundT`, `boundaryT`: the version is sound, so total initial matching holds
  for it (`Version.initialMatchingAt`), and it has its boundary.
* `Self.typedAddress`, `Self.typedBalance`: inside a contract, where `this` is
  the builtin, the spellings have Source types `address` and `uint256`.
* `Self.eval_address`, `Self.eval_balance`: their resolved forms evaluate to
  the frame's own address and to the balance Source observes for it
  (`Relation.ownBalance`), leaving the Source state unchanged.
* `selfAddress_faithful`, `selfBalance_faithful`: under related globals the
  model's `address(this)` and `address(this).balance` are value-related to
  those Source results.

Not shown here: that the model keeps the two globals related along a run (the
simulation obligation), and the remaining gaps of every version listed in
`Total.Versions`. No goal is stated.
-/
namespace Solidity.Correctness.Lowering.Total

namespace Version

/-- The self-aware tables are sound: they type locals and cells as the
bytes-aware ones do. -/
theorem soundT : Sound Decode.tablesT := ⟨soundB.localTy, soundB.cell⟩

/-- The self-aware version's boundary. -/
def boundaryT : SemanticBoundary := boundaryAt Decode.tablesT rel

namespace Self

/-- `address(this)` is an `address` inside a contract. -/
def typedAddress (Γ : Source.Ctx) {c : String}
    (builtin : Γ.resolve "this" = some (.builtin .this)) (scope : Γ.scope = some c) :
    Source.Typed Γ Decode.thisAddress (.address false) :=
  .convElem (.this builtin scope) rfl rfl

/-- `address(this).balance` is a `uint256` inside a contract. -/
def typedBalance (Γ : Source.Ctx) {c : String}
    (builtin : Γ.resolve "this" = some (.builtin .this)) (scope : Γ.scope = some c) :
    Source.Typed Γ Decode.thisBalance (.int Source.IntTy.u256) :=
  .balance (typedAddress Γ builtin scope)

/-- The resolved `address(this)` evaluates to the frame's own address at every
sufficient horizon, in any state, changing nothing. -/
theorem eval_address (Γ : Source.Ctx) {c : String}
    (builtin : Γ.resolve "this" = some (.builtin .this)) (scope : Γ.scope = some c)
    (G : Source.Glob Γ.env) (F : Source.Fr) (k : Nat) :
    Source.evalE G F (k + 2) (typedAddress Γ builtin scope).toR =
      pure (.val (.address F.this)) := by
  simp only [typedAddress, Source.Typed.toR, Source.evalE, pure_bind]
  rfl

/-- The resolved `address(this).balance` evaluates, from any locals and state,
to the balance Source observes for the running account, changing nothing. -/
theorem eval_balance (Γ : Source.Ctx) {c : String}
    (builtin : Γ.resolve "this" = some (.builtin .this)) (scope : Γ.scope = some c)
    (G : Source.Glob Γ.env) (F : Source.Fr) (k : Nat)
    (l : Source.Locals Γ.env.layout Γ.tys) (s : Source.St Γ.env) :
    (Source.evalE G F (k + 3) (typedBalance Γ builtin scope).toR).run.run (l, s) =
      (.ok (.val (Source.intWrap Source.IntTy.u256 (Relation.ownBalance G F s).val)), (l, s)) := by
  show (Source.evalE G F (k + 2 + 1)
    (Source.RExpr.balance (typedAddress Γ builtin scope).toR)).run.run (l, s) = _
  rw [Source.evalE, eval_address Γ builtin scope G F k]
  rfl

end Self

/-- **`address(this)` is faithful**: under related globals the model's own
address is value-related to the Source frame's own address, the value of the
decoder's spelling (`Self.eval_address`). -/
theorem selfAddress_faithful {E : Source.Env} {C : Contract} {G : Source.Glob E}
    {F : Source.Fr} {st : Source.St E} {σ : State C []} (h : (rel E C).glob G F st σ) :
    Relation.ValRel E.layout (.address false) .uint (.address F.this) σ.tx.selfAddress :=
  .address false F.this _ h.2.2.2.2.1

/-- **`address(this).balance` is faithful**: under related globals the model's
own balance is value-related to the balance Source observes for the running
account, the value of the decoder's spelling (`Self.eval_balance`). -/
theorem selfBalance_faithful {E : Source.Env} {C : Contract} {G : Source.Glob E}
    {F : Source.Fr} {st : Source.St E} {σ : State C []} (h : (rel E C).glob G F st σ) :
    Relation.ValRel E.layout (.int Source.IntTy.u256) .uint
      (Source.intWrap Source.IntTy.u256 (Relation.ownBalance G F st).val) σ.selfBalance := by
  have same : Source.IntTy.u256.wrap ((Relation.ownBalance G F st).val : Int) =
      ((Relation.ownBalance G F st).val : Int) := by
    simp only [Source.IntTy.wrap, Source.wrapBits, Source.IntTy.u256, Bool.false_eq_true,
      false_and, if_false]
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr (Relation.ownBalance G F st).isLt)
  unfold Source.intWrap
  exact .uint Source.IntTy.u256 rfl _ _ _ (h.2.2.2.2.2.1.trans same.symm)

end Version

end Solidity.Correctness.Lowering.Total
