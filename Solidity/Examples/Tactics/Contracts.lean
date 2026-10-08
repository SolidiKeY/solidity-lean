import Solidity.Calculus.Close
import Solidity.Calculus.Core.Surface
import Solidity.Calculus.Core.Closers
import Solidity.Calculus.Core.FunContract
import Solidity.Calculus.Core.WalkSyntax

/-!
# Calls by contract

A call proved by its callee's contract (`useContract`,
`Calculus/Core/FunContract.lean`) instead of its inlined body: the goal
`"pre"` owes `requires` with the parameters bound to the arguments, the goal
`"post"` assumes `ensures` of a result of the return type, after a
`{havoc}` of storage and ledger for a `nonpayable` callee only.  Each
contract is proved once, from its obligation
`∀ params. requires → [ T r; body ] ensures` (`hc`), by the strategy.  The
callee's locals are the call's fresh names: `se1` the parameter, `se2` the
return variable (`addOne`), `se1` the return variable (`getTotal`).  A
contract's formulas are read at the callee's frame (`cdlIn![…]{ … }`, the
locals outermost first).

`core_contract μ req ens` takes the call at the head of the goal's box,
behind its parameters and preconditions; the mutability `μ` is checked on
the callee's body (`Prog.within`, by `rfl`): `addOne` is `pure`,
`getTotal` reads storage (`view`), `deposit` writes it (`nonpayable`).
The statements read scoped (`open scoped Solidity.Core.Surface`).
-/
namespace Solidity.Examples.Tactics.Contracts

open Proves

/-- A `pure`, a `view` and a `nonpayable` function. -/
def ContractsExample : Contract := contract!{
  uint total;
  function addOne(uint x) pure returns (uint r) { r = x + 1; }
  function getTotal() view returns (uint r) { r = total; }
  function deposit(uint v) { total += v; }
}

local instance : InContract := ⟨ContractsExample⟩

open scoped Solidity.Core.Surface

/-- `y = addOne(x);` by `addOne`'s contract, a `pure` callee: nothing but
the result is forgotten. -/
theorem callAddOne : ⊨ dl!{ x == 4 → [ y = addOne(x); ] y == 5 } := by
  core_contract .pure cdlIn![uint se1]{ se1 <= 100 } cdlIn![uint se1, uint se2]{ se2 == se1 + 1 }
  case hc =>
    sol_symex
    sol_close
  case pre =>
    sol_symex
    sol_close
  case post =>
    sol_symex
    sol_close

/-- `y = getTotal();` by its contract, a `view` callee: `total` is still
`7` after the call, so `ensures` gives `y`. -/
theorem callGetTotal : ⊨ dl!{ total == 7 → [ y = getTotal(); ] y == 7 } := by
  core_contract .view cdlIn![]{ total == 7 } cdlIn![uint se1]{ se1 == total }
  case hc =>
    sol_symex
    sol_close
  case pre =>
    sol_symex
    sol_close
  case post =>
    sol_symex
    sol_close

/-- `deposit(4);` by its contract, a `nonpayable` callee: storage is
forgotten (`{havoc}`), and `ensures` is all that is known of it. -/
theorem callDeposit : ⊨ dl!{ total == 3 → [ deposit(4); ] total == 7 } := by
  core_contract .nonpayable cdlIn![uint se1]{ total == 3 ∧ se1 == 4 }
    cdlIn![uint se1]{ total == 7 }
  case hc =>
    sol_symex
    sol_close
  case pre =>
    sol_symex
    sol_close
  case post =>
    sol_symex
    -- `{se1 := 4} {havoc} (total == 7 → total == 7)`, past the parameter's
    -- hidden binder: what the callee leaves is forgotten, and `ensures` is
    -- all that is known of it (today's closer does not read `{havoc}`)
    intro σ _
    simp only [Core.holds]
    intro v
    unfold Modality.afterC
    split
    · intro σ' _ _ st nt hA
      split
      · rename_i τ h
        intro σ'' hσ'' _
        have hg : σ''.erase.glob = (σ'.havoc st nt).erase.glob := by
          rw [hσ'']
          cases h
          rfl
        simp only [Core.Tm.eval, Core.Tm.denote, hg] at hA ⊢
        exact hA
      · trivial
    · trivial

/-- `callAddOne`, its two goals derived one rule at a time (`⊢`). -/
theorem callAddOneWalk : ⊨ dl!{ x == 4 → [ y = addOne(x); ] y == 5 } := by
  core_contract_walk .pure cdlIn![uint se1]{ se1 <= 100 }
    cdlIn![uint se1, uint se2]{ se2 == se1 + 1 }
  case hc =>
    sol_symex
    sol_close
  case pre =>
    apply unfold .localValueDeclInitDrop
    apply update .localValueAssign
    refine close ?_
    sol_symex
    sol_close
  case post =>
    apply unfold .localValueDeclInitDrop
    apply update .localValueAssign
    apply allRight
    apply impRight
    apply update .localValueAssign
    refine close ?_
    sol_symex
    sol_close

/-- Whether the first call of a formula's first program has a body within
`μ` (`Prog.within`). -/
def calleeWithin (μ : Mutability) : {Γ : Core.Ctx} → Core.Fml ContractsExample Γ → Option Bool
  | _, .modal _ P _ _ => progWithin μ P
  | _, .imp _ ψ | _, .all _ _ ψ | _, .bind _ _ _ ψ | _, .upd _ _ ψ => calleeWithin μ ψ
  | _, _ => none
where
  progWithin (μ : Mutability) : {Γ Γ' : Core.Ctx} → Core.Prog ContractsExample Γ Γ' → Option Bool
    | _, _, .nil => none
    | _, _, .cons (.call _ _ _ body) _ => some (Core.Prog.within μ body)
    | _, _, .cons _ P => progWithin μ P

/-- `addOne` is `pure`, `getTotal` `view` only, `deposit` `nonpayable` only. -/
example : [Mutability.pure, .view, .nonpayable].map
    (calleeWithin · dl!{ [ uint y = addOne(1); ] true }) = [some true, some true, some true] := by
  decide
example : [Mutability.pure, .view, .nonpayable].map
    (calleeWithin · dl!{ [ uint y = getTotal(); ] true }) = [some false, some true, some true] := by
  decide
example : [Mutability.pure, .view, .nonpayable].map
    (calleeWithin · dl!{ [ deposit(1); ] true }) = [some false, some false, some true] := by
  decide

/-- The frame fact of a `view` callee: its typed run leaves storage and
ledger as they were (`Prog.trun_frame`). -/
example {Γ Γ' : Core.Ctx} (P : Core.Prog ContractsExample Γ Γ')
    (hw : Core.Prog.within .view P = true) (σ : Core.TState ContractsExample Γ)
    (o : Core.Out ContractsExample σ.H Γ') (h : Core.Prog.trun σ P = .ok o) :
    o.st.storage = σ.storage ∧ o.st.net = σ.net :=
  (Core.Prog.trun_frame P hw 0 h).1.keeps (by decide)

end Solidity.Examples.Tactics.Contracts
