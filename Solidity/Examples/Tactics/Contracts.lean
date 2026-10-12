import Solidity.Calculus.Close
import Solidity.Calculus.Surface
import Solidity.Calculus.Closers
import Solidity.Calculus.FunContract
import Solidity.Calculus.WalkSyntax

/-!
# Calls by contract

A call proved by its callee's contract (`useContract`,
`Calculus/FunContract.lean`) instead of its inlined body: the goal
`"pre"` owes `requires` with the parameters bound to the arguments, the goal
`"post"` takes the snapshots `{old := storage ‖ oldNet := net}` that `\old`
reads, forgets storage and ledger (`{havoc}`) for a `nonpayable` callee
only, and assumes `ensures` of what the call leaves: no result, one, several
(`callPair`), or a memory return (`callFresh`).  Each contract is proved
once, from its obligation
`∀ params. requires → {old := storage ‖ oldNet := net} [ T r; { body } ] ensures`
(`hc`), by the strategy.  The callee's locals are the call's fresh names:
`se1` the parameter, `se2` the return variable (`addOne`), `se1` the return
variable (`getTotal`).  A contract's formulas are read at the callee's frame
(`cdlIn![…]{ … }`, the locals outermost first: the parameters, then for
`ensures` the snapshots `old` and `oldNet`, then the return variables).
`sol_close` reads `{havoc}` (`Calculus/CloseScoped.lean`), so every goal
closes by the strategy.

`core_contract μ req ens` takes the call at the head of the goal's box,
behind its parameters and preconditions; the mutability `μ` is checked on
the callee's body (`Prog.within`, by `rfl`): `addOne` is `pure`,
`getTotal` reads storage (`view`), `deposit` writes it (`nonpayable`).
The statements read scoped (`open scoped Solidity.Scoped`).
-/
namespace Solidity.Examples.Tactics.Contracts


/-- A `pure`, a `view` and a `nonpayable` function. -/
def ContractsExample : Contract := contract!{
  uint total;
  function addOne(uint x) pure returns (uint r) { r = x + 1; }
  function getTotal() view returns (uint r) { r = total; }
  function deposit(uint v) { total += v; }
  function pair(uint x) pure returns (uint lo, uint hi) { lo = x; hi = x + 1; }
  function fresh() pure returns (Person memory p) { }
}

local instance : InContract := ⟨ContractsExample⟩

open scoped Scoped

/-- `y = addOne(x);` by `addOne`'s contract, a `pure` callee: nothing but
the result is forgotten. -/
theorem callAddOne : ⊨ dl!{ x == 4 → [ y = addOne(x); ] y == 5 } := by
  core_contract .pure cdlIn![uint se1]{ se1 <= 100 }
    cdlIn![uint se1, old, oldNet, uint se2]{ se2 == se1 + 1 }
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
  core_contract .view cdlIn![]{ total == 7 } cdlIn![old, oldNet, uint se1]{ se1 == total }
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
    cdlIn![uint se1, old, oldNet]{ total == 7 }
  case hc =>
    sol_symex
    sol_close
  case pre =>
    sol_symex
    sol_close
  case post =>
    sol_symex
    sol_close

/-- `deposit(4);` by a contract that reads `\old`: `total` grows by `v`
over the storage the call was entered with (`find(old, total)`), which the
snapshot `{old := storage}` of "post" keeps past `{havoc}`. -/
theorem callDepositOld : ⊨ dl!{ total == 3 → [ deposit(4); ] total == 7 } := by
  core_contract .nonpayable cdlIn![uint se1]{ total <= 100 ∧ se1 <= 100 }
    cdlIn![uint se1, old, oldNet]{ find(storage, total) = find(old, total) + se1 }
  case hc =>
    sol_symex
    sol_close
  case pre =>
    sol_symex
    sol_close
  case post =>
    sol_symex
    sol_close

/-- A call that leaves two results (`CallRet.rets`) for the tuple's
targets: "post" binds both (`∀ T r₁ r₂`), the frame dropped from under
them.  The targets are declared first, a step each. -/
theorem callPair : ⊨ dl!{ x <= 10 → [ (uint a, uint b) = pair(x); ] b == a + 1 } := by
  sol_step
  sol_step
  core_contract .pure cdlIn![uint se1]{ se1 <= 100 }
    cdlIn![uint se1, old, oldNet, uint se2, uint se3]{ se2 == se1 ∧ se3 == se1 + 1 }
  case hc =>
    sol_symex
    sol_close
  case pre =>
    sol_symex
    sol_close
  case post =>
    sol_symex
    sol_close

/-- A memory return: "post" declares the fresh object the callee is
entered with (`[ Person memory r; ]`), which a `pure` callee leaves as it
is; storage is untouched. -/
theorem callFresh : ⊨ dl!{ total == 3 → [ Person memory m = fresh(); ] total == 3 } := by
  core_contract .pure cdlIn![]{ true } cdlIn![old, oldNet, Person memory se1]{ true }
  case hc =>
    sol_symex
    sol_close
  case pre =>
    sol_symex
    sol_close
  case post =>
    sol_symex
    sol_close

/-- `callAddOne`, its two goals derived one rule at a time (`⊢`). -/
theorem callAddOneWalk : ⊨ dl!{ x == 4 → [ y = addOne(x); ] y == 5 } := by
  core_contract_walk .pure cdlIn![uint se1]{ se1 <= 100 }
    cdlIn![uint se1, old, oldNet, uint se2]{ se2 == se1 + 1 }
  case hc =>
    sol_symex
    sol_close
  case pre =>
    apply unfold .localValueDeclInitDrop
    apply update .localValueAssign
    sol_leaf
    sol_close
  case post =>
    apply unfold .localValueDeclInitDrop
    apply update .localValueAssign
    apply updIntro
    apply allRight
    apply impRight
    apply update .localValueAssign
    sol_leaf
    sol_close

/-- Whether the first call of a formula's first program has a body within
`μ` (`Prog.within`). -/
def calleeWithin (μ : Mutability) : {Γ : Ctx} → Fml ContractsExample Γ → Option Bool
  | _, .modal _ P _ _ => progWithin μ P
  | _, .imp _ ψ | _, .all _ _ ψ | _, .bind _ _ _ ψ | _, .upd _ _ ψ => calleeWithin μ ψ
  | _, _ => none
where
  progWithin (μ : Mutability) : {Γ Γ' : Ctx} → Prog ContractsExample Γ Γ' → Option Bool
    | _, _, .nil => none
    | _, _, .cons (.call _ _ _ body) _ => some (Prog.within μ body)
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
ledger as they were (`Prog.run_frame`). -/
example {Γ Γ' : Ctx} (P : Prog ContractsExample Γ Γ')
    (hw : Prog.within .view P = true) (σ : State ContractsExample Γ)
    (o : Out ContractsExample σ.H Γ') (h : Prog.run σ P = .ok o) :
    o.st.storage = σ.storage ∧ o.st.net = σ.net :=
  (Prog.run_frame P hw 0 h).1.keeps (by decide)

end Solidity.Examples.Tactics.Contracts
