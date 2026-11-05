# Calculus modes O10–O13

Status (2026-11-05): **VC2 (O11) and VC3 (O12) done and integrated; VC1 running** (see Handoffs). Ideas from a
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
| VC1 | inventory, O10, O13 | `Calculus/Assumptions.lean`, `Calculus/TargetProfile.lean`, `scripts/solidity-lean*.mjs`, docs/cli.md |
| VC2 | inventory, O11 | new `Calculus/CallerModel*.lean`, `Theory/CallerModel/**`; sole editor of `Semantics/Callback.lean` and `Calculus/CallbackHolds.lean` in this batch |
| VC3 | inventory, O12 | new `Theory/Reachable/**`; sole editor of `Calculus/TailMode.lean`, `Calculus/CleanTailBoundary.lean` |

All three run in parallel; each adds only its own section to options.md and
correctness.md. VC3 states its O11 needs against a stub and adapts after VC2
lands; VC1's O13 waited for VS4's S5.1/S6.1 (built over them once pushed).

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
  `Calculus/CleanTailBoundary.lean` (`StateInv.cleanTail`;
  `Prog.CleanTailCallbackBoundary` is a box, which rules out a panic, so the
  lane uses the weaker `KeepsCleanC` and derives it from the boundary),
  `Semantics/Callback.lean` (`StateInv`, `ExecP`, `COut`, `ExecP.eq_run`,
  `ExecP.of_run`).
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
`Exec.LeOn` and monotonicity, `reachableE_noCallback_iff`,
`leOn_of_callsBack`, `KeepsCleanC`, `cleanTail_invariantE`,
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
`Exec.Le` (or `Exec.LeOn M` on an interface) between their relations, so
`ReachableE.mono`, `InvariantE.weaken` and `ValidStartE.weaken` instantiate
to the lattice's weakening. Caution: the deterministic run is not below
`ExecP J` in general (`ExecP` may report a violation where the run
succeeds); the lane proves the order only for entries that call nobody back
(`leOn_of_callsBack`), so VC2's weakening needs a no-violation or
`callsBack` premise at `none ≤ any`; (3) replace `CallerStub` in
`ValidTail.validStartE_withCallback` by the lattice's top. Nothing else in
the lane reads the stub.

**Reviews (checkpoint 1).** Finder and skeptic (read-only, no Lean server)
found, and the lane fixed: `EntryState` ignored the payable guard and
`allowCall` (now required); `cleanTail_invariantE` demanded a box that rules
out panics (now `KeepsCleanC`) and had no witness (now
`pushRead_withCallback`); no rollback was exercised (now
`entry_after_rollback`); `Exec.Le` was never instantiated (now `Exec.LeOn`,
`leOn_of_callsBack`, used once) and the violating control used an ad hoc
relation (now `Exec.top`, `top_refutes`); `PersistentFml.invariant` had no
control for its per-entry premise (now `eleven_refutes`); examples lacked
Solidity in docstrings and stated `dl` goals as raw constructors (fixed);
two theorems named `pushRead_reachable` (renamed `pushRead_validStart`);
re-entry frames are not entry states (documented). Kept: `pushRead`
repeats `Examples/Tactics/TailMode.lean`'s program over a contract with
entry points (`Tokens` has none); the shared-namespace lemmas
(`SFields.all_anon`, `Storage.resetTransient_cleanTail`,
`Lifetime.System.refuses`) live in the lane's files, the owners of
`Typing/` and `Semantics/` may move them.

**Gates (checkpoint 1).** MCP diagnostics clean on the four Lean files;
`#print axioms` on every main theorem and control: `propext`,
`Classical.choice`, `Quot.sound` only; no `sorry`, no `maxHeartbeats`;
`scripts/check-layers.mjs` 0 core modules reach the elaborator;
`register.sh --check` clean; `./run-lean.sh`: `Build completed successfully
(3839 jobs)` (SolkeyTestSuite included, its pinned report unchanged), then
`check-solkey.sh` exits 1 with 57 annotation mismatches against the sibling
`../solkey` checkout; the lane touches no `SortCheck/` file, so that drift
is not this lane's. `check-doc-paths.sh` fails only on
`Calculus/Assumptions.lean`, VC1's planned file, as on the base commit.

**Requests to other owners.** VC1 (`Calculus/Assumptions.lean`): a start-mode
field (`any` | `reachable`) in the mode record, `any` the default.
### VC2 — O11 caller-model lattice (2026-11-05)

**Inventory (step 0).** `Bridge/` has no callback or attacker notion.
`Solidity/Tools/` has none either (its counterexample `Tri` reads runs, not
callers). Reused: `StateInv`, `ExecS`/`ExecP`/`ExecF`, `Prog.exec_run`,
`ExecS.eq_run` (`Semantics/Callback.lean`); `holdsC`, `ValidT`,
`TransferSem`, `validT_noCallback_iff` (`Calculus/CallbackHolds.lean`);
`Upd.afterT_imp`, `Modality.forallB`. `CallMode.static` and `Mode.readOnly`
name the `STATICCALL` restriction but no callback run reads them (O1 "not
done", H22), so `staticOnly` is a model of the callee, documented against
them, not a reading of `ExtCall.mode`. `Semantics/Lifetime.lean`'s
`System` (entries as `Prog C [] []`) shaped `Reentry`; it reads the
deterministic run, so it is not reused for re-entry. The reentrancy-lock
examples in the repository are prose only (`Examples/Tactics/Callback.lean`
has no lock); no lock judgment existed. `docs/options.md` O1/O3/O4 fixed
the orthogonality: the transfer semantics says whether a payment calls back,
the caller model what a callee that does may do.

**Interface for VC3 (stable): `Solidity.Calculus.CallerModel`** —
`CallerModel C` (`none | staticOnly | nonReentrant (R : Reentry C) | any`),
`CallerModel.Allows`, `CallerModel.Le`, `Reentry` (`Entry`, `body`,
`guarded`, `held`; `Call`, `Step`, `StepAny`, `Reach`, `ReachAny`, `Guards`,
`KeepsHeld`), the runs
`ExecSM M J`/`ExecPM`/`ExecFM`, `holdsR M I pay`, `ValidM M ts φ`
(`⊨ᶠₘ[M; ts] φ`). Theorems: `Calculus/CallerModelRun.lean`
(`ExecPM.mono`, `ExecPM.toExecP`, `ExecP.ofExecPM`, `Prog.execM_run`),
`Calculus/CallerModelValid.lean` (`validM_any`, `validM_none`,
`validM_none_iff_noCallback`, `ValidM.weaken`, `ValidM.of_validT`,
`Reentry.reachAny_iff`). For O12, a reachable-states mode under model `M`
should read callbacks inside its transaction sequence by `ExecPM M` for
`M ≠ none`, and by `Prog.run` for `none`: `ExecSM .none` is not `none`'s
reading (its `try` answers any data, and the invariant is owed on exit).

**Done.** Lattice and lock judgment (`nonReentrant` is lock-aware: a
guarded entry is turned away only while the lock is held); `any`/`none` coincide with today's
readings (`validM_any` exact; `validM_none` is `Fml.Valid`, equal to
`ValidT .noCallback` without `try`/value call); weakening theorem; one
separating example per adjacent pair (`Examples/Tactics/CallerModel.lean`),
the two `nonReentrant` pairs with one `R` (`setX`), each with its
`#print axioms` pinned. Docs: options.md O11, correctness.md
"Caller models (O11)", module-map rows.

**Design note.** `ExecSM` is a model-indexed copy of `ExecS` (41
constructors, three with an `Allows` premise more), not an edit of `ExecS`:
an extra premise on `ExecS` would change the arity of `transferResume`,
`sendResume` and `tryOk` in about twenty modules outside this lane
(`CallbackWk`, `CallbackUnwk`, `CallbackFrame`, `CapturePayments`, …). The
copy's agreement with `ExecS` is proved both ways (`toExecS`, `ofExecSM`).

**Reviews.** Finder and skeptic (read-only, no Lean server). Fixed:
`nonReentrant` ignored the lock (`Reentry.Step` now lets a guarded entry
through while the lock is free; `Static.lean`'s inertness is relative to a
storage predicate, `Prog.LockedAt`); the `nonReentrant` separations used two
`R`s and the lock state played no part (now one `R`, `open_setX`/`lock_setX`;
`lock_setX` reads `setX`'s flag and the lock, its body by `setX_guards`);
docs overstated `none`'s coincidence with `noCallback`, the `none <
staticOnly` example's reason, and `ExecSM .none`; stale name
`holdsR_modal_inert`; missing docstrings. Kept, documented: re-entry with
no value, nested callbacks under `any`.

**Limitations.** No `ProvesC`-style calculus for `staticOnly` or
`nonReentrant`: a proof there is a `ValidT` proof weakened, a `Fml.Valid`
proof where callees change nothing (`Theory/CallerModel/Static.lean`), or by
the runs. A re-entrant call carries no value, and its own callees read as
`any`. The weakening theorem needs positive modalities. The `none <
staticOnly` example separates by the invariant owed on exit; the sharper
separation (two equal calls answered alike only under `none`) is true but
not provable by `sol_close`, which forgets the oracle's correlation.
The separating examples live in `Examples/Tactics/CallerModel.lean`, not
under `Theory/CallerModel/`: they use `dl!{ … }` and `sol_symex`, which
the core library may not reach (`scripts/check-layers.mjs`); the file is
new and no other lane's. Other lanes' needs: none.
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
lane to build on it; no second fork type, and the duplicate `Pipeline` is
gone (`OrderReading`, the record's O9 reading, is bridged to `Pipeline` by
`ofPipeline`; making `Assumptions.order` a `Pipeline` is a possible
follow-up). Rows carry
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

**O13 review** (finder and skeptic in one read-only pass). Fixed: the
"no second pipeline type" claim (reworded: `OrderReading` is bridged),
cli.md attaching `profile`'s shape to `assumptions`, a redundant control
(replaced by `viaIR_profile_not_fits`, `legacy_record_not_valid_viaIR`),
stale lane lines, `pinned_pin`'s naming against `Evm.pinned`, and a CLI test
that `profile.pipeline` is the record's order. Documented: the version and
fork are data `fits` ignores; the CLI's `solc` string is the pin read at
run time, Lean's `pinned` a constant; no lemma links a profile to S5.1's
`CompilerChoice` beyond the shared `Pipeline`.

**Requests to other owners.**
- `Frontend/Testing.lean` / `scripts/test-solidity.mjs` owner: emit the row's
  record from Lean (whether the obligation called back, its order, its
  callee invariant), and the fixture header's `solcVersion` per row; the CLI
  derives the first and reads the pin for the second today. A `--via-ir`
  runner option would make `pipeline`/`order` vary.
- VC2: replace `Assumptions.callback` by the caller model and add its
  weakening theorem as a case of `Assumptions.Entails` (and to
  `weakenings` in `scripts/solidity-lean-assumptions.mjs`).
