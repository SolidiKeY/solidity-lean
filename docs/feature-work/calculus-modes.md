# Calculus modes O10–O13

Status (2026-11-05): **authorized; not yet implemented.** Ideas from a
comparison with verity (Profile, `--deny-*` gates, AdversaryModel,
EntryPointInvariants). Rule ([options.md](../options.md)): a mode is an
argument of the validity statement, as `ValidT`/`ValidTail` are, never a global
setting. SolKey has only `transferSemantics`, so solkey's readings stay the
defaults and TestSuite counts must not move; each new mode gets an options.md
row marked Lean-only. Every lane starts with an inventory of `Bridge/`,
`Solidity/Tools/` and `docs/`.

Existing pieces: `TailMode`/`ValidTail` (`Calculus/TailMode.lean`), `ValidT`
(`Calculus/CallbackHolds.lean`), `StateInv` (`Semantics/Callback.lean`),
`StateInv.cleanTail` (`Calculus/CleanTailBoundary.lean`), `CallMode`
(`Syntax/Scoped.lean`), `Mode.readOnly` (`Semantics/ContractWorld.lean`),
`Contract.evalOrder` (`Syntax/Raw.lean`), the CLI in `scripts/solidity-lean.mjs`.

## Groups

| Group | Deliverable | Depends on |
|---|---|---|
| O10 | **Assumption policy.** Each `verify` row records the modes it was proved under (callback reading, overflow default/checked/ignoringOverflow, TailMode, evaluation order, opaque hash, address 0 has no code). `--require`/`--deny` flags: a row that holds only under a refused mode is reported not-proved. Per-row JSON assumption report. Docs: cli.md, options.md. | — (mode record `Calculus/Assumptions.lean` owned here; O11–O13 add fields by request) |
| O11 | **Caller-model lattice** `none < staticOnly < nonReentrant < any`, generalizing noCallback/withCallback; `staticOnly` reuses `CallMode.static`/`Mode.readOnly`; `nonReentrant` allows callbacks only into functions outside the reentrancy lock. Weakening theorem (valid under a stronger attacker ⇒ valid under a weaker one) over `StateInv`; separating examples in the `Tactics/Callback.lean` style. | — |
| O12 | **Reachable starting states.** A `reachable` mode: storage from deployment plus a finite sequence of public calls; a contract invariant proved once by induction over entry points (rollback on revert); `TailMode.clean` follows. Orthogonal to O11: callbacks inside the sequence follow the chosen caller model. | O11 interface (stub) |
| O13 | **Target profile.** One named bundle of solc version, legacy/via-IR (selects O9 order) and EVM fork, carried in result rows. Built over VS4's compiler and fork parameters (S5.1/S6.1 in [semantics-extensions.md](semantics-extensions.md)); no second fork parameter. | O10, VS4 S5.1/S6.1 |

Out of scope: gas or optimizer modes, a collision-free hash mode (a premise
where needed, never an axiom), more overflow modes.

## Lanes

| Lane | Checkpoints | Owned files |
|---|---|---|
| VC1 | inventory, O10, O13 | `Calculus/Assumptions.lean`, `scripts/solidity-lean*.mjs`, docs/cli.md |
| VC2 | inventory, O11 | new `Calculus/CallerModel*.lean`, `Theory/CallerModel/**`; sole editor of `Semantics/Callback.lean` and `Calculus/CallbackHolds.lean` in this batch |
| VC3 | inventory, O12 | new `Theory/Reachable/**`; sole editor of `Calculus/TailMode.lean`, `Calculus/CleanTailBoundary.lean` |

All three run in parallel; each adds only its own section to options.md and
correctness.md. VC3 states its O11 needs against a stub and adapts after VC2
lands; VC1's O13 waits for VS4's S5.1/S6.1 and otherwise backfills.

## Handoffs

### VC3 — O12 reachable starting states (branch `cloud/modes-20261105/reachable`)

**Inventory (step 0).** Reused, not rebuilt:
- `Semantics/Lifetime.lean`: `System` (deploy, entry calls, payable,
  environment predicates), `Init` (successful `Contract.deployT`), `Step`
  (commit, rollback of revert/revertWith/panic, wait), `Reachable`,
  `Invariant` with `Invariant.ofRuns` (rollback needs no proof). This is the
  O12 starting-state relation; nothing new was needed below it.
- `Calculus/Lifetime.lean`: `post_of_deploy_box`, `System.preserves_of_fml`.
- `Typing/CleanTailRun.lean`: `Prog.exposesNone`, `Prog.run_cleanTail`,
  `ReachableBy` (storage-only, no rollback, no transaction frame: kept
  distinct, as `.claude/rules/typing.md` asks).
- `Calculus/TailMode.lean` (`ValidTail`, `holds_cleanTail_of`),
  `Calculus/CleanTailBoundary.lean` (`StateInv.cleanTail`,
  `Prog.CleanTailCallbackBoundary`, `_exit`, `_noViolation`),
  `Semantics/Callback.lean` (`StateInv`, `ExecP`, `COut`).
- Not reused: `Typing/Reachability.lean`'s `Reachable` (any single program
  from `State.init`: storage constructibility, not a transaction sequence);
  `ContractWorld.Reachable` (multi-contract, rooted at an empty world);
  `Bridge/SolidityBridge/AdversaryPolicy.lean` and `CallbackTrace.lean`
  (traces inside one callback). Nothing in `Solidity/Tools/` applies.
- Deployment/dispatch facts: `Contract` keeps no visibility, so the
  interface `M` is a model obligation (as in `docs/lifetime.md`); no
  selector dispatch exists in the typed core.

**Delivered** (`Solidity/Theory/Reachable/`): `Mode.lean` (`StartMode`,
`ValidStart`, `EntryState`, `ValidStart.of_invariant`, `PersistentFml`,
`PersistentFml.invariant`, `ValidStart.of_persistent`), `CleanTail.lean`
(`Storage.resetTransient_cleanTail`, `cleanTail_invariant`,
`ValidTail.validStart_reachable`), `CallerModel.lean` (`Exec`, `RunE`,
`StepE`, `ReachableE`, `InvariantE`, `ValidStartE`, the stub `CallerStub`,
monotonicity, `reachableE_noCallback_iff`, `cleanTail_invariantE`,
`ValidTail.validStartE_withCallback`), and `PersistentFml.ofStorage`.
Witnesses and negative controls are in `Solidity/Examples/Tactics/Reachable.lean`
(contracts `Bag` and `Counter`), outside `Theory/Reachable/**`: `Theory/` is
core, and `scripts/check-layers.mjs` refuses a core module that reaches the
elaborator (`contract!{}`, `sol[…]{}`, `dl[…]{}`, `sol_prove`). Docs:
options.md O12 (row and section, Lean-only), correctness.md paragraph,
module-map rows in `docs/module-map/theories.md` and
`docs/module-map/examples.md`. No edit to `Calculus/TailMode.lean` or
`Calculus/CleanTailBoundary.lean` was needed.

**O11 adaptation (for after VC2 lands).** `CallerStub` stands for VC2's
lattice. To adapt: (1) give each caller model of the lattice its `Exec C`
(`none` ↦ `CallerStub.noCallback.exec`, `any` ↦ `ExecP J`; `staticOnly`
and `nonReentrant` from VC2's relations); (2) prove VC2's order gives
`Exec.Le` between their relations, so `ReachableE.mono`,
`InvariantE.weaken` and `ValidStartE.weaken` instantiate to the lattice's
weakening; (3) replace `CallerStub` in `ValidTail.validStartE_withCallback`
by the lattice's top. Nothing else in the lane reads the stub.

**Requests to other owners.** VC1 (`Calculus/Assumptions.lean`): a start-mode
field (`any` | `reachable`) in the mode record, `any` the default.
