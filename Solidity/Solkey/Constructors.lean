import Solidity.Frontend.Problems
import Solidity.Calculus.Close

/-!
# Constructors, imported from solc's AST

Two of solkey's contracts with a constructor, through the front end
(`Frontend/SolcJson.lean`): `contracts/Counter.sol` (solkey `a764703bf1`,
its first constructor example) and `benchmark/EtherWallet.sol` (the pinned
`1b4341a303`).  `scripts/solc-ast.mjs --source … --out … --wrapper
Solidity/Solkey/Constructors.lean` writes each fixture and rewrites its
hash below.

A constructor is a row named `constructor` and, when it elaborates, the
program `N.constructor`, a deployment `constructor(x̄);`
(`Solidity/Frontend/Import.lean`).  `Counter`'s is specified (its contract
has an invariant), so it has no plain statement; `EtherWallet`'s is not,
and `solc_problems` states it as solkey does, from the deployment update
(`Problem.ctorFml`).
-/

open Solidity Proves

solc_import "../../tests/solc/Counter.ast.json" hash 0x2d54a4ea32c96108 as Solkey.Counter

solc_import "../../tests/solc/EtherWallet.ast.json" hash 0x381a46a368c7fa67 as Solkey.EtherWallet

solc_problems Solkey.EtherWallet

/-! ## `Counter.sol`

The initializer `limit = 5` is the contract's, and the constructor its own
member: a deployment runs the first, then the second.  Both functions are
specified (the contract has an invariant), so neither has a plain
statement. -/

/--
info: 2 functions (0 diamond, 0 box, 0 skip, 2 specified): 2 elaborated, 0 skipped, 0 excluded, 0 unsupported
-/
#guard_msgs in
#eval IO.println (Solidity.Frontend.ImportRow.summary Solkey.Counter.report)

/-- info: [constructor, increment] -/
#guard_msgs in
#eval IO.println (Solkey.Counter.report.map (·.name))

/-- info: [(limit, 5)] -/
#guard_msgs in
#eval IO.println (Solkey.Counter.inits.map fun (x, e) => (x, e.toStr))

/-- A deployment with `7`: the initializer, then the body. -/
theorem counterDeploy :
    (Solkey.Counter.deploy sol[Solkey.Counter]{ constructor(7); } {}).map (·.storage) =
      .ok [("limit", .prim (.int 5)), ("count", .prim (.int 7))] := by
  simp only [Contract.deploy, Contract.deployState, Contract.initStorage, Solkey.Counter, List.map,
    Semantics.defaultForTy]
  rfl

/-! ## `EtherWallet.sol`

The constructor is unspecified: its obligation is solkey's
`{storage := mtSt ‖ net := … ‖ selfBalance := msgValue} ⟨ constructor(); ⟩ true`. -/

/--
info: 3 functions (2 diamond, 0 box, 0 skip, 1 specified): 2 elaborated, 0 skipped, 0 excluded, 1 unsupported
unsupported receive: EtherWallet.sol:14: a `receive` function
-/
#guard_msgs in
#eval IO.println (Solidity.Frontend.ImportRow.summary Solkey.EtherWallet.report)

/--
info: \problem {
    {storage := mtSt || net := storeSt(mtSt, at(msgSender), msgValue) || selfBalance := msgValue} \<{ constructor()@EtherWallet; }\>(true)
}
-/
#guard_msgs in
#solkey_problem Solkey.EtherWallet.constructor

/-- The deployment obligation, derived.  `sol_prove`'s closer refuses a
context that holds `mtSt` (`Decide` has no clause for it yet), even with
`true` to prove, so its one leaf is closed by `sol_close_mt`. -/
theorem Solkey.EtherWallet.constructor.proved : ⊢ Solkey.EtherWallet.constructor.problem := by
  sol_prove
  refine Proves.close ?_
  sol_symex
  sol_close_mt

/--
info: 3 functions: 1 derived, 0 pending, 2 other
unsupported receive
specified withdraw
pending:
-/
#guard_msgs in
#solkey_obligations Solkey.EtherWallet
