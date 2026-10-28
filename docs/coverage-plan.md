# Feature coverage plan

How to take the language inventory (`docs/solidity-features.json`,
`docs/solidity-feature-inventory.md`) from mostly `partial` to `present`,
in parallel: each step is one cloud VM (16 GB of RAM, several hours, a
fresh clone of `origin/master`, one branch, one reviewable patch), and every
step of a wave runs at the same time.

The yardstick is the upstream corpus (`docs/solidity-upstream-tests.md`): a
step is done when its fixtures agree in every pipeline they require, with
no observation dropped, and its inventory rows move. Proofs are the second
gate: no step lands a rule without its soundness proof.

## Where it starts

The current feature classifications and evidence are in the generated
[feature inventory](solidity-feature-inventory.md); its summary is regenerated
from the manifest. The fixture counts below are the historical pre-cloud
baseline, not a fresh measurement of current support.

Recorded baseline (`tests/upstream/results/`, base `cadb628c`): of 1,662
`lean-runtime` fixtures, 229 work, 308 are broken and 1,125 blocked. Of the
inventory's 211 features: 13 present, 151 partial, 7 missing, 40 not
applicable; 32 are excluded by the profile.

The broken rows, by cause: 194 frontend import gaps (91 of them inline
assembly, excluded), 67 missing callable entry points (getters, overloads,
inherited functions), 27 transient storage, 18 physical storage layout
(excluded), 2 real via-IR modifier mismatches. The blocked rows: 334 host
behaviour (block/tx fields, self address, other contracts), 325 dynamic or
aggregate ABI vectors, 85 revert data and panic codes, 77 gas expectations
(excluded), 49 `revertStrings` settings, 39 multi-source imports, 27
noncanonical calldata, the rest EVM-version constraints and harness
settings.

Cloud groups 01–10 have been integrated. The
[01–09 record](feature-work/cloud-integration-01-09.md) and
[task 10 record](feature-work/cloud-integration-10.md) identify their committed
scope, validation and remaining exclusions. The uncommitted recursive-storage
migration is not included. Each new step first reproduces its assigned rows on
current master, so it targets what those patches left.

## Rules every step follows

- **Inventory first.** Before writing code, read the rows and docs the step
  names and quote what already exists (`docs/module-map.md`, the feature's
  `localEvidence`); target only the gap. Reproduce the assigned fixtures on
  current master first: some will already pass.
- **Memory.** Treat 16 GiB as a budget to measure, not a proven cold-build
  bound. Run a build or the MCP, not both; start with `LEAN_NUM_THREADS=1`
  and explicit `-j1`, and keep only a small number of MCP files open. Enforce
  a hard process-group limit and leave room for the VM's OS (for example, a
  12 GiB build cap on a 16 GiB VM). Monitor available RAM and stop before
  exhausting it. The [bounded validation record](refactoring-progress.md#resource-bounds-and-resuming-work)
  covers a passing warm/private-cache run, not a cold 16 GiB guarantee. Build
  in the background, inspect errors, and measure the cold path in step 0.
- **Parallel without conflicts.** Every step of a wave starts from the same
  master. A step that edits the core (`Syntax`, `Semantics`, `Rules`,
  `Decide`: the `core` column) keeps its change additive and in modules of
  its own, and touches the shared types (`State`, `THalt`, `Stmt`) only
  through what step H added. Shared front-end files (`Frontend/SolcJson/`)
  get narrow edits, listed in the hand-off. Each VM has its own RAM, so the
  local limit of two Lean agents does not apply across VMs.
- **Soundness.** A new `Stmt` constructor needs its rule and soundness proof
  in the same step (`Stmt.step` has one rule per statement). Until a
  feature's rules are proved, the elaborator refuses it with a named gap.
  No `sorry`, no new axioms (`./scripts/check-trust.sh`), no
  `maxHeartbeats` raised.
- **Never pass by weakening.** Blocked never becomes working by dropping an
  observation, changing an expectation, weakening a premise or raising a
  fuel or proof limit. Timeouts are blocked.
- **Gates.** The step's fixtures (`node scripts/solidity-upstream.mjs
  … --filter`), `node --test` of the scripts it touches, `node
  scripts/check-orphans.mjs`, `node scripts/check-layers.mjs`,
  `node scripts/check-automatic.mjs --strict`, and `./run-lean.sh` if it
  touched the core. Then a read-only finder and skeptic review, the inventory
  row updated (`scripts/solidity-feature-audit.py`), and the feature's doc
  updated in place: what works, what is refused and why, what is left.
- **Hand-off and merging.** Per-fixture before/after, commands, pipelines,
  axioms, build time and peak memory, what is left. Steps merge as they
  finish, in finish order: before its final gates a core step rebases on
  the master of that moment; the coordinator merges, runs the combined
  build and pushes. A step that does not finish in its VM hands off what
  it has and its rest goes to the next wave.

## Decisions for the user

These change the profile (`docs/solidity-scope.md`), so no step takes them
alone:

- **D1. Block and transaction fields** (`block.number`, `chainid`,
  `basefee`, `tx.origin`, …) are excluded today. Moving them to `abstract`
  (an environment the obligation quantifies over, like `timestamp`)
  unblocks part of the 334 host rows. Recommended: yes.
- **D2. Observable logs.** Events run their arguments but the log is
  erased. Making logs observable (a trace in the state) lets specs talk about
  events and unblocks the `~ emit` rows. Recommended: yes.
- **D3. Assembly, `delegatecall`, gas, physical layout** stay excluded: they
  need a Yul or EVM layer (`docs/solc-validation.md` I), a separate project.

## Steps

Three waves. Every step of a wave runs at once, each on its own VM; a wave
starts when the steps it needs are merged. `core`: edits the core (merged
with a rebase, see above).

| # | Step | Inventory rows | core | wave |
|---|---|---|---|---|
| 0 | Baseline | all | no | 0 |
| H | Core hooks | — | yes | 0 |
| 1 | Entry points left | `publicGetters`, `receiveFunction`, `fallbackFunction`, `overrideDeclarations` | no | 1 |
| 2 | Imports and source units | `imports`, `sourceUnits`, `usingFor`, `errorDeclarations` | no | 1 |
| 3 | Expressions and references left | `tupleExpressions`, `conditional`, `rangeAccess`, `implicitConversions`, `shifts` | no | 1 |
| 4 | Panic codes and revert data | `panicCodes`, `revertPayloads`, `revertStatement` | yes | 1 |
| 5 | Environment (D1) | `blockNumber`, `blockChainid`, … `txOrigin`, `blockhashBuiltin` | yes | 1 |
| 6 | Contract world | `newContract`, `creationTry`, `externalLibraryCalls`, `externalTypedCalls` | yes | 1 |
| 7 | Recursive types | `recursiveTypes`, `structTypes` | yes | 1 |
| 8 | Transient state, rest | `transientState` | yes | 1 |
| 9 | Logs (D2) | `emitStatement`, `eventDeclarations` | yes | 1 |
| 12 | Specs, loops, callbacks left | `whileStatement`, `forStatement`, `staticCallRestriction` | no | 1 |
| 13 | Closer gaps | (automation) | no | 1, on the user's go |
| 14 | Generated differential tests | all | no | 1 |
| 15 | solkey re-pin | — | no | 1 |
| 10 | Revert-outcome modality | `revertPayloads`, `catchClauses` | no | 2 (after 4) |
| 11 | Diamond calls | `tryStatement`, `sendTransfer`, `callbackSemantics` | no | 2 (after 6) |
| R | Rerun and second pass | all | — | 2 |

Wave 0 is two VMs for a few hours, wave 1 up to fourteen, wave 2 three plus
whatever wave 1 left. Step 0 replaces the hour guesses with measured times.

### 0. Baseline and H. Core hooks

**0. Baseline.** Merge state check: which of the ten groups' patches landed. Rerun the whole
upstream corpus on master (`docs/solidity-upstream-tests.md`, "Reproduce"),
into a new results directory, keeping the historical one. Add a `gap` field
to each `partial` row of `docs/solidity-features.json`: the concrete shape
still refused or unproved, taken from the fixtures' `variants[].gaps` and
from the "Left" section of the feature's doc. Measure a cold and a warm
`./run-lean.sh` on the VM and write the times here. Output: the next steps'
fixture lists, regenerated from the new results. No Lean edits.

**H. Core hooks audit.** Reuse existing typed frames and halt transport before
adding shared declarations. `THalt.revertWith`, `THalt.ofData` and `THalt.data`
already carry revert bytes to catch consumers; computed/custom error paths also
exist. Remaining panic-code coverage and any environment/log extensions need
only the missing hooks, not a second revert representation. Update affected
matches with their proofs in the same change. Warn first if a representation
change may slow checking, inspect Git history for earlier speed decisions, and
compare bounded before/after checks.

### 1–3. Front end

Lowering to constructs the core already has: no new rule, no proof beyond
the elaborator's. They run in parallel; keep shared edits to
`Frontend/SolcJson/` narrow and list them in the hand-off.

1. **Entry points left**: reference getter results, enum-valued and
   contract/function getter results, general tuple external returns, receive
   and fallback registration, inherited renamed function
   values sharing one ABI identity
   (`docs/feature-work/declarations-metadata.md`, "Left").
2. **Imports and source units**: multi-source compilation-unit provenance
   (39 blocked rows), remappings, file-level `using for` and qualified
   custom errors (`docs/feature-work/source-admission.md`).
3. **Expressions and references left**: reference-element slices, effectful
   nonlocal tuple targets, UDVT aggregates and numeric/literal edge cases that
   still fail assigned fixtures. Primitive tuple captures, tested mixed
   storage/memory joins and signed operator lowering already exist; reproduce
   the remaining shapes before extending them (`docs/feature-work/aggregates.md`,
   `docs/feature-work/numeric-operators.md`).

### 4–9. Core semantics

In parallel, each in modules of its own on top of step H. Each adds the semantics, its elaborator and
import support, its rules with soundness, and the tests. Closer support
can stay with the step or go to its own step.

4. **Remaining panic/payload coverage**: extend the existing revert-byte
   transport for still-missing panic cases, allocation failure and supported
   `revertStrings` settings (`docs/solc-alignment.md`, "Remaining deltas";
   `docs/semantic-gaps.md`, "Revert data"). Existing catch transport and
   computed/custom reasons are not new work. Keep resource exhaustion distinct
   from arithmetic/assertion panic, and preserve the original fixture
   observations and pipeline requirements.
5. **Environment** (after D1): the block and transaction fields as
   quantified environment inputs, like `timestamp`; the host adapter for the
   rows that need only these.
6. **Contract world**: world-aware `new C` and calls, `try new`, library
   arguments and aggregate results, certified as `Reachable` operations
   (`docs/feature-work/contract-world.md`, "Left"). This unblocks most of the
   remaining host rows. The biggest step: split it at `new` and at library
   calls if it does not fit in one VM.
7. **Recursive types** in the ordinary pipeline: `ObsEq` congruence, path
   commutation, importer admission, the state and term migration, the
   heap-cycle copy policy (`docs/feature-work/recursive-types.md`, "Left").
   Warn first: this changes the state's representation, and may slow
   checking.
8. **Transient state, what group 09 left**: composed source-world/delegate
   execution and source shapes outside the supported primitive/function-tag
   fragment. Ordinary transient declarations, disjoint logical roots, self-call
   sharing, transaction reset and rollback already exist. Reuse that joint
   model and its frame laws (`docs/feature-work/transient-storage.md`); physical
   assembly/layout and gas remain outside the profile.
9. **Logs** (after D2): the log trace in the state, emitted in pipeline
   order, rolled back on revert; named and qualified emits
   (`docs/feature-work/calls-exceptions.md`).

### 10–13. Calculus and closer

10. **Revert-outcome modality**: a formula that reads the data a run halts
    with, so specs can state which error a function reverts with
    (`docs/semantic-gaps.md`, "Revert data"). It has no solkey taclet: mark
    it Lean-only in `docs/lean-key-rule-map.md`.
11. **Diamond calls**: the diamond `try`/`transfer` rules and the
    `net/*-withcallback.key` problems (`docs/kernel-port.md`, "Still
    open"); diamond automation across external `try`, so source tests
    need no `@custom:key box`.
12. **Specs, loops and callbacks left**: quantified loop invariants under
    the diamond, modifies sets finer than a root and through aliases
    (`docs/loops.md`); `view` callees without callback semantics, a recursive
    call returning a reference under callbacks, self-calls of later functions
    (`docs/options.md` O1, O3, O7, O8); diamond specs over reachable states
    and the `sol_decide` reads of `old`/`net` (`docs/function-specs.md`,
    "Still open").
13. **Closer gaps**: the six pinned `DecisionTheorem` gaps and M7-next
    (`docs/automation.md`). Only on the user's go.

### R. Rerun and second pass

After wave 1 merges: rerun the upstream corpus and the inventory audit on
master, then one VM per step that handed off a rest.

### 14–15. Validation

14. **Generated differential tests**: harness D of
    `docs/solc-validation.md` (a `Stmt` → Solidity printer, `lake exe
    solcases`, a solc and EVM runner outside the Lean package), on the
    bounded enumeration E. It finds what hand-picked fixtures miss.
15. **solkey re-pin** past `473da8944c` (`docs/solkey-migration.md`,
    "Re-pinning"), and the uniform proof run and strict comparison not
    rerun since.

## Done when

Every `scope: model` row is `present`, or `partial` with a `gap` that is a
named proof limit, not a refused shape; every `abstract` row has its
environment stated; the upstream corpus has no broken row outside the
excluded families; and the TestSuite gate stays at 0 pending.

## Current-master baseline (2026-10-28)

The fresh baseline starts at `f4dee4a29c2e208b36db4a4161a4723c735cd775`.
All ten collected cloud snapshots are ancestors; unmerged work is excluded.
The combined 9,660-fixture report has **4,135 working, 196 broken, 5,329 blocked**.
Its 1,662 Lean-runtime fixtures have **657 working, 196 broken, 809 blocked**.
The 3,478 pinned-solc diagnostic agreements are reference evidence, not Lean
coverage. Every input, required source mode, completed observation and resource
block is retained in the [new evidence](../tests/upstream/baseline-20261028/README.md).
The immutable bulk report and 22 isolated follower reports remain separate.

The inventory currently has 212 rows: 13 present, 160 partial, one missing,
38 not applicable. The new diagnostic index provides reviewed boundaries for
65 partial rows and explicitly leaves 95 needing feature-specific attribution.
It does not promote statuses or infer completeness from absent fixtures. The
manifest/schema is unchanged; generated inventory files remain reproducible.

Cold/warm performance measurement is pending in this branch. This baseline is
diagnostic evidence, not a universal semantics or lowering-equivalence proof.
