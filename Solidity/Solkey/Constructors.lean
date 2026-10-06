import Solidity.Frontend.Problems
import Solidity.Calculus.Close

/-!
# Constructors, imported from solc's AST

Two of solkey's contracts with a constructor, through the front end
(`Frontend/SolcJson.lean`): `contracts/Counter.sol` (solkey `a764703bf1`,
its first constructor example) and `benchmark/EtherWallet.sol` (the pinned
`1b4341a303`), and two of this repository's, `tests/solc/CtorGap.sol` and
`tests/solc/InitGap.sol`, which pin what the import leaves out.
`scripts/solc-ast.mjs --source … --out … --wrapper
Solidity/Solkey/Constructors.lean` writes each fixture and rewrites its
hash below (for the last two, `--solkey` a directory holding solkey's
`keyext.solidity.core/build.gradle` and the sources at `tests/solc/`).

A constructor is a row named `constructor` and, when it elaborates, the
program `N.constructor`, a deployment `constructor(x̄);`
(`Solidity/Frontend/Import.lean`).  `Counter`'s is specified (its contract
has an invariant), so it has no plain statement; `EtherWallet`'s is not,
and `solc_problems` states it from the deployment update
(`Problem.ctorFml`).  That is solkey's specified constructor's update:
solkey's unspecified problem writes `{storage := mtSt || net := mtSt}`, and
Lean books the payment there too (`docs/solkey-feedback.md`).
-/

open Solidity Proves

solc_import "../../tests/solc/Counter.ast.json" hash 0x2d54a4ea32c96108 as Solkey.Counter

solc_import "../../tests/solc/EtherWallet.ast.json" hash 0x381a46a368c7fa67 as Solkey.EtherWallet

solc_import "../../tests/solc/CtorGap.ast.json" hash 0x8cab24cd55b14f16 as Solkey.CtorGap

/--
warning: solc_import: the initializers are left out: an initializer calls `cap`, which is left out: the modifier `always`: its code would be dropped
-/
#guard_msgs in
solc_import "../../tests/solc/InitGap.ast.json" hash 0x83328c56fa8af038 as Solkey.InitGap

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

The constructor is unspecified: its obligation is
`{storage := mtSt ‖ net := … ‖ selfBalance := msgValue} ⟨ constructor(); ⟩ true`,
the update of solkey's specified constructor problem (solkey's unspecified
one writes `{storage := mtSt || net := mtSt}`). -/

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

/-! ## What the import leaves out

`CtorGap`'s constructor has a modifier, so it is left out (a row), and
its initializer `limit = 5` with it: the implicit constructor would run
the initializer alone.  `InitGap`'s implicit constructor has an
initializer that calls `cap`, left out for its modifier: the initializers
are left out, with a warning at the import. -/

/--
info: 2 functions (2 diamond, 0 box, 0 skip): 1 elaborated, 0 skipped, 0 excluded, 1 unsupported
unsupported constructor: CtorGap.sol:15: the modifier `positive`: its code would be dropped
-/
#guard_msgs in
#eval IO.println (Solidity.Frontend.ImportRow.summary Solkey.CtorGap.report)

/-- info: [] -/
#guard_msgs in
#eval IO.println (Solkey.CtorGap.inits.map fun (x, e) => (x, e.toStr))

/-- info: [] -/
#guard_msgs in
#eval IO.println (Solkey.InitGap.inits.map fun (x, e) => (x, e.toStr))
