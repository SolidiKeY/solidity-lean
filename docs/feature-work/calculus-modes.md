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

### VC1 (inventory, O10, O13) — 2026-11-05

**Inventory (step 0).** Reused, not redefined: `TailMode`/`ValidTail`,
`ValidTail.clean_of_solc` (`Calculus/TailMode.lean`); `ValidC`, `TransferSem`,
`ValidT`, `validC_false_iff` (`Calculus/CallbackHolds.lean`); `OFMode`
(`Syntax/Raw.lean`, the blocks' modes; the record's `OverflowReading` adds
`default`, neither block); `EvalOrder`/`EvalOrder.viaIR`/`Contract.evalOrder`
(`Syntax/Raw.lean`, O9); `keccakBytes` (`Semantics/Heap.lean`, irreducible,
no collision resistance); O8's address-`0` reading (`TRun.tryCall`). Rows:
`#solkey_test` (`Frontend/Testing.lean`) writes `reading` (the tail mode,
`contractTailMode`) and states a calling-back obligation as
`ValidT (.noCallback invariant[N])`, a plain one as `⊢ N.f.problem`
(O7); `scripts/test-solidity.mjs` adds `source`, `contract`, `sourceHash`,
`range`; `scripts/solidity-lean.mjs` wraps them in the schema-1 envelope
(`docs/cli.md`). Compiler: `scripts/solc-ast.mjs` loads solkey's pinned
`ext.soljsonFile` (0.8.34; 0.8.38 is also an audited pin), `viaIR: false`
unless `--via-ir`, `evmVersion` default `osaka`; the fixture header records
`solcVersion`, which rows do not carry. `Bridge/` and `Solidity/Tools/` hold
no assumption or profile record; no fork type exists (Osaka appears only as
pinned constants, `Stipend/Rule.lean` `osakaCold`, `Yul/*`). VS4's branch
`cloud/semantics-20261105/nondeterminism` was not on origin.

**O10, done.** `Solidity/Calculus/Assumptions.lean`: `Assumptions`,
`ValidA`, `Entails`/`ValidA.weaken`, `Policy`/`verdict`
(`verdict_proved_iff`, `verdict_refused`, `admits_sound`), `ProvedRow`;
the runner's statements as cases (`validA_iff_validT`,
`validA_of_validTail`). Witnesses and controls:
`Examples/Tactics/Assumptions.lean`. CLI: `--require`/`--deny`,
`assumptions`/`policy` per row, status `refused`
(`scripts/solidity-lean-assumptions.mjs`, mirrored decision table in
`scripts/solidity-lean.test.mjs`). Docs: options.md O10, cli.md, correctness.md.

**O13, done.** `Solidity/Calculus/TargetProfile.lean`: `TargetProfile`
over G01's `Roadmap.Pipeline`/`Pipeline.order` (on master; missed by the
first inventory, which defined a duplicate `Pipeline`, now removed) and
VS4's `ForkSpec` (S6.1), with `fits`, `evalOrder_of_fits`,
`not_validA_of_not_fits`, `pinned_pin`. VS4's branch was merged into this
lane to build on it; no second fork or pipeline type remains. Rows carry
`profile`.

**Reviews.** Finder and skeptic (read-only, no Lean server) on O10/O13.
Fixed: the docs claimed every record field is read by `ValidA` (now
`ValidA.labels` and the docs say overflow, hash and address `0` are labels);
`verdict_refused`'s docstring overclaimed (reworded; the guarantee is
`admits_sound`); the JS policy was checked on 13 cases only (now an
exhaustive 3192-line table, `tests/cli/assumption-policies.txt`, checked
against `Policy.verdict` when the examples build); `table_notProved` was
definitional (removed; real controls `solc_record_not_allowed`,
`clean_row_not_admitted_solc`); the callback control changed the invariant
too (now `withdrawUnsafe_validA_inv`, same invariant); `list`/`inspect` and
obligation-free rows carried records they were not stated under (now only
`verify` rows that stated an obligation); `SOLKEY_ROOT=""`; the exit table
and the CLI example. Documented, not fixed: the callee invariant and
`--self-address` premise are not record fields; a mixed `EvalOrder` has no
reading; the CLI's `solc` is the pin, not the compile's.

**Requests to other owners.**
- `Frontend/Testing.lean` / `scripts/test-solidity.mjs` owner: emit the row's
  record from Lean (whether the obligation called back, its order, its
  callee invariant), and the fixture header's `solcVersion` per row; the CLI
  derives the first and reads the pin for the second today. A `--via-ir`
  runner option would make `pipeline`/`order` vary.
- VC2: replace `Assumptions.callback` by the caller model and add its
  weakening theorem as a case of `Assumptions.Entails` (and to
  `weakenings` in `scripts/solidity-lean-assumptions.mjs`).
