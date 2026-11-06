# H28 semantic mutation testing

Status: the declared 30-operator manifest is fully run: no entry is unrun and
none is in error. The remaining queue obligations are not claimed:

- the clause-level inventory (dispositions are per constructor and per
  declared operator site);
- `scope_complete` acceptance;
- an immutable seal.

The repository gates are reported under [Gates](#gates). See also
[Limits](#limits).

| Recorded run | `runs/full-20d7b77c` |
|---|---|
| Head | `20d7b77c2e0c9e97559e8f3e8332ad9f4487edc4` |
| Manifest | `manifests/h28-full.json`, schema 3, sha256 `bb3f1f97…` (full value in `summary.json`) |
| Census | 215 constructors; 194 site mutants on 117 constructors plus 4 `Tms` helper edits (198) |
| Proof oracle (census) | 146 detected, 5 equivalent-certified, 47 invalid-compilation, 0 error, 0 unrun |
| Semantic witnesses | 20 of 20 scored cases killed, 0 witness-failed, 0 error, 0 unrun. The cases were chosen because a witness exists, so this is witness validation, not a census score |
| Controls | 4 manifest controls plus 1 pilot control (label renamed), all as declared (`controls_pass: true`) |
| Baselines | full `Calculus/Taclet.lean`, every row and link alone, `CallbackTaclet.toTaclet`: all pass |

The lane moved from a Codex VM to a Claude VM on 2026-11-05. Its earlier
history, which used a Docker backend and caches that exist only on the Codex
VM, is kept unchanged under [History (Codex VM)](#history-codex-vm). The
sections up to there describe the work redone on the Claude VM.

- Branch: `cloud/moved4-20261105/mutation-testing`.
- Start: `origin/cloud/mutation-testing-move` (e25db89b) merged at master
  `aec9adf1ad8666a7e591e42a537069a93dc858cb`.
- The production inputs are byte-identical to the original semantic base
  `6f3eedf0`: `Calculus/Rules.lean`, `Calculus/RuleShapes.lean`,
  `Calculus/CallbackRules.lean`, `TestSuite/Refuted.lean` and
  `tests/upstream/README.md`.
- No production file, statement, premise, exclusion, budget, shared root or
  module registration changed. The lane writes only
  `tests/h28-sol/mutation-testing/**`, this file and its docs/README row
  fragment.

## Method (Claude VM)

### Runtime

The Codex VM's runner needed a Docker daemon, `/workspace` caches and an
off-Git bulk archive. None of these exist here, and this VM's settings deny
direct `lean`/`lake` calls. The new runner
([tools/mcprun.py](../../tests/h28-sol/mutation-testing/tools/mcprun.py), see
its [README](../../tests/h28-sol/mutation-testing/tools/README.md)) runs Lean
only through the repository's language-server bridge,
`scripts/coord-tools/lean-mcp` (three daemons, one open file each). It reads
only committed inputs, so queue item 1 (self-contained tooling) is met
without the H44 bulk digests. The old Docker tools and `bulk-data.json` stay
as a record and are marked legacy. 65 of their 71 unit tests still pass here.
The other six need the Codex VM's off-Git evidence or its runtime.

A check is one scratch file in the ignored `.scratch/`:

1. the imports;
2. the target module's text, production or one-change mutant, inlined in
   place of its import;
3. an oracle's text.

Production files are only read. Each record keeps:

- the bridge command and its exit;
- the elapsed time;
- the scratch file's sha256;
- the one-change diff;
- every diagnostic, including the `#print axioms` output;
- the decision.

The bridge reports no per-process RSS. VM memory stayed under 10 GiB with
three workers.

### Census

[tools/sites.py](../../tests/h28-sol/mutation-testing/tools/sites.py) reads
every constructor of `Taclet`, `LeanTaclet`, `CallbackTaclet` and `Rule`
(215). It applies each declared family operator at every match in a
constructor's premise text (after `⇝`). Each match is one mutant, whose edit
replaces the whole constructor span, so it is attributed to exactly one
constructor. Four `Tms` helper edits come on top.

The census covers every match of these 30 declared operators, not every
conceivable fault. The operators, with their census sites, are:

| Family | Operators (sites) |
|---|---|
| Family | Operators (sites) | Total |
|---|---|---|
| guard-polarity | branch guard `true`↔`false` (5), loop guard `b = TRUE`↔`FALSE` (7), assert check (1) | 13 |
| overflow | push-arithmetic operator swaps (7), `± 1` step dropped (12), compound and inc/dec operand swaps (2 helpers) | 21 |
| division-minimum | `/`→`*` (1), `%`→`/` (1), zero guard negated (2), fixed binop operand swap (1 helper) | 5 |
| index-bounds | index `[ie]`→`[0]` on arrays (32) | 32 |
| push-tail-length | length `+ 1`→`+ 2` (19), new slot shifted (6), last slot shifted (18), recycled tail cleared (1 helper) | 44 |
| pop-delete | storage deletion dropped (5), memory deletion dropped (4), pop length `- 1`→`- 2` (2), popped slot shifted (1) | 12 |
| alias-capture-once | each receiver capture's later uses re-evaluate the receiver (39) | 39 |
| rollback-payment | revert/transfer/try closings flipped (4), send flags flipped (4), amount zeroed (3), `0 <= se`→`0 < se` (1) | 12 |
| callback-frames | the same payment and flag edits on the `CallbackTaclet` table (8) | 8 |
| other (kept, outside the nine) | loop-invariant `inv = TRUE` and `¬broke` edits (9), other closings (3) | 12 |

Per-constructor dispositions are in `runs/full-20d7b77c/dispositions.json`:

- **sites-run (117):** every site was run.
- **no-family-site (85):** the premise text matches no operator. The
  heuristic tags of `inventory.draft.json` (kept unchanged) came from names
  or captures, not family clauses.
- **no-premise-text (13):** the premise is a named function (`blockEmpty`,
  `tryCallSelfBox`, `catchDataBox`, …) or the constructor is a `Rule`
  wrapper. Those functions are outside the read-only inputs.

### Proof oracle

The production evidence that each premise is `Stmt.step`'s
(`Calculus/Taclet.lean`) is re-checked against the mutated table. For each
affected constructor:

- its `#replay_toStep` row is re-run alone. Rows are independent
  declarations, and `#h28_toStep_row` makes the same `addToStep` call as the
  table;
- a hand-proved lemma states its premise itself, so its link to the
  constructor is checked as the closing `cases h <;> apply_toStep` does it:
  `#h28_toStep_link` proves the constructor's own `toStepType` by
  `intros; apply X.c.toStep <;> assumption`;
- `CallbackRules.lean` mutants are checked by its own `CallbackTaclet.toTaclet`.

The baseline `rules-taclet-rows` runs every row and link this way on the
normal table and passes, beside the full production file.

How a mutant is classified:

- **detected:** an error is attributed to an affected constructor. Errors
  that cascade from it (unknown lemma, closing theorems, error-recovery
  `sorry`) are allowed.
- **error, never detected:** heartbeat, recursion or timeout messages, and
  a lemma that depends on `sorryAx` (the `H28 TRUST` guard reports it).
  There is one exception: the `sorry` that error recovery leaves after a
  hand lemma fails in a way already attributed to the same constructor. That
  is a cascade of that failure. In the record, a trust error's internal
  reason reads "runtime limit"; the label is inexact, the outcome is not.
- **equivalent-certified:** the unchanged evidence still passes. The
  mutant's premise is then provably `Stmt.step`'s for every admitted
  instance, hence the original's.

Detection means "differs from `Stmt.step`". It is not a soundness claim, and
over compiled mutants it is total by construction, so no detection rate is
reported as a score. Some detected mutants are semantically harmless; the
operand swaps of commutative operators, for example, are detected.

### Semantic oracle

An owned witness proves `¬ Premise.Sound m s p σ` at a concrete inhabited σ.
Its `source_link` is `Taclet …` (or `LeanTaclet`, `CallbackTaclet`) proved by
the mutated constructor. A case is **killed** only if:

1. its normal baseline passes;
2. on the normal table, the witness is rejected inside the `source_link`
   span, with a mismatch naming the linked constructor, and that constructor
   is the case's;
3. on the mutant, the witness passes with no error, no oracle warning, only
   `propext`, `Classical.choice` and `Quot.sound`, an export for every
   theorem, and a `checked_kill` whose printed type is `¬ Premise.Sound …`.

The owned-file scanner refuses all of these: `sorry`, `admit`, `axiom`,
`native_decide`, `maxHeartbeats`, `unsafe`, `opaque`, `implemented_by`,
`extern`, `debug` and non-`pp` options. A completed witness failure is
`witness-failed`. A bridge, target or trust failure is `error`, never a
survivor.

## Results

### Census by family (census entries only, `runs/full-20d7b77c/summary.json`)

| Family | detected | equivalent-certified | invalid-compilation |
|---|---|---|---|
| alias-capture-once | 36 | 0 | 3 |
| callback-frames | 8 | 0 | 0 |
| division-minimum | 1 | 0 | 4 |
| guard-polarity | 9 | 0 | 4 |
| index-bounds | 32 | 0 | 0 |
| overflow | 14 | 0 | 7 |
| pop-delete | 9 | 1 | 2 |
| push-tail-length | 21 | 4 | 19 |
| rollback-payment | 12 | 0 | 0 |
| other:closing | 3 | 0 | 0 |
| other:loop-invariant | 1 | 0 | 8 |

Totals include the four helper edits. `summary.json`'s `by_family` and
`all_entry_counts` also include 8 extra proof entries: the 6 pilot cases
that are not census mutants, the label-renaming control and the
invalid-syntax control. Together these give 152 detected, 6
equivalent-certified and 48 invalid.

What the run found:

- **Equivalent-certified (5): the rule DSL lowers by shape.** It lowers
  `save(delAt(storage, darr[…]), darr.length, darr.length - 1)` to
  `STerm.pop` and `save(save(storage, sp[…], v), sp.length, sp.length + 1)`
  to `STerm.push`, whatever index text is written. So shifting that index
  (`storagePopSave`, `storagePushValueSave`, `storagePushValueCopySource`,
  `storagePushMemoryCopySource`, `pushFixedCopySave`) yields the identical
  premise. Only the printed-rule round trip (`scripts/check-rule-text.sh`)
  can see such a text change; that check is outside this lane.
- **Invalid-compilation (47): the DSL refuses the shape.**
  - Length arithmetic other than `len ± 1` is refused ("a length is not a
    storage path").
  - So are push-arithmetic operator swaps (typed fixed shapes), loop
    invariant and guard edits that leave the accepted `inv = TRUE` /
    `b = TRUE` forms, some division edits, and three receiver re-evaluations
    whose receiver is not a path.
  - Two `whileInvariantBox` `¬broke` deletions are plain parse errors
    (`unexpected token '∧'`). They are artifacts of the operator, not
    evidence about the DSL.
  - None is scored.
- **No error and no unrun entry.**

### Semantic kills (20 scored, all killed)

The scored set is 13 earlier hand-selected cases, rechecked fresh, plus 7
new ones; the earlier known-kill and equivalence controls are not scored.
The new ones are:

- `ifElseSplit` then-guard and else-guard flips: `IfThenPolarityKill`,
  `IfElsePolarityKill`;
- `transferNoCallbackBox` with amount `0`: `TransferZeroKill`. The balance
  stays 10 while the run pays 5, and `mutant_update_applies` shows the box is
  not vacuous;
- `LeanTaclet.transferDiamond` closing to `true`: `TransferDiamondTrueKill`,
  an unfunded transfer that reverts;
- `storageRootDelete` with the update dropped: `RootDeleteSkippedKill`;
- `storageRootIncrement` with the step dropped: `RootIncSkipKill`. It uses
  the uint256 maximum, though dropping the step is killable at any state;
- the separate callback table, `CallbackTaclet.sendWithCallbackBox` with the
  failed flag `true` (`CallbackTacletFailureKill`, queue item 4). Its kill
  uses `holds`, as `toTaclet` makes that premise the no-callback one. The
  holdsC theorem `checked_callback_frames` is required too.

14 census mutants carry a scored witness: 13 table sites and the `pushSlot`
helper edit. The other 6 scored cases are pilot edits that are not census
mutants: 2 `binopC` helper edits and 4 hand-typed rules. The known-kill
control covers the census mutant `revertDiamond`.

The tool does not compare the source links of helper-linked kills: `binopC`
linked to `localOpAssign`, and `pushSlot` linked to
`storagePushLengthSaveReferenceElement`.

Per family, these semantic verdicts are thin:

- index-bounds, alias-capture-once and division-minimum each rest on one
  hand-typed or helper pilot edit, not on a census site;
- push-tail-length has the census `pushSlot` helper edit and one hand-typed
  pilot;
- guard, rollback/payment, callback, pop/delete and overflow have census
  mutants with witnesses.

This is a witness-validation rate over cases chosen because a witness
exists. It is not a semantic mutation score of the census: the other 132
detected census mutants have no semantic verdict. Some of them are probably
sound; the receiver re-evaluations, for example, only differ when the
receiver has an effect.

Every new witness has a normal baseline (`IfElseBaseline`,
`TransferBaseline`, `TransferDiamondBaseline`, `RootDeleteBaseline`,
`RootIncBaseline`, `CallbackTacletBaseline`). Each is registered in the
lane's local `registration.json`.

### Controls and backfill

| Control | Expected | Actual |
|---|---|---|
| `control.proof-invalid-syntax` (malformed guard) | invalid-compilation | invalid-compilation |
| `pilot.control.guard-label-equivalent` (branch label renamed) | equivalent-certified | equivalent-certified |
| `control.guard-label-equivalent` (universal equivalence witness) | equivalent | equivalent |
| `control.revert-diamond-true` (independent known kill) | killed | killed |
| `control.cross-witness-survivor` (guard mutant, pop witness) | link-mismatch | link-mismatch |

The 29 runner self-tests in
[tools/test_mcprun.py](../../tests/h28-sol/mutation-testing/tools/test_mcprun.py)
cover false kills and false passes:

- unattributed, runtime and trust errors;
- region boundaries;
- rejection outside the link span;
- a kill that does not state unsoundness;
- refused options;
- unrun, bridge-error and witness-failed accounting.

### Run provenance

`full-91c9631d` (head `91c9631d`, manifest sha256 `e243fdd3…`) ended with 2
proof errors and 4 semantic errors:

- the `binop` and `pushSlot` helper mutants, whose hand-lemma cascade was
  reported through the trust guard;
- the two `transfer*` cases, whose rejection lay on the second line of a
  multi-line `source_link`;
- the two `ifElseSplit` cases.

The classifier fixes turned the first four into detections and kills
without re-running Lean. The two `ifElseSplit` witnesses were edited
(`hj := rfl`) and re-run.

`full-20d7b77c`, with a different manifest (the two edited witness hashes),
re-classified every check with the final code. Reuse is matched by scratch
file hash, which covers import names but not the imported modules. It is
valid here because `git diff 91c9631d 20d7b77c` touches no `Solidity/`
file. Reused records keep their original elapsed time and bridge.

- 297 checks reuse the diagnostics of byte-identical scratch files from
  `full-91c9631d` (`--reuse`, matched by scratch sha256);
- 4 checks were fresh: the edited `ifElseSplit` witnesses on both tables.

`full-91c9631d` ran all 301 checks at its own head. Its first 108 records
predate a container restart; the remaining 193 resumed from the same head
(`--resume` accepts only records of the same head and manifest).

Both runs' compact records (`checks.jsonl`), summaries and full-record
archives (`runs/*-checks-full.tar.gz`, with sha256 in each `summary.json`)
are committed. They were compacted after the run by `tools/compact.py` as of
`a3716f4b`, which differs from `20d7b77c`'s only in the `in_git` flag and a
docstring. The 3.42 hours of check time are almost all `full-91c9631d`'s
Lean time, carried over by reuse. The checks ran on three bridges, and the
longest single check took 229 s.

## Reviews

Separate read-only finder and skeptic reviews, neither using the Lean
server, audited the tools, census and new witnesses at `4c900cfb`. All
confirmed findings were fixed in `91c9631d` and `20d7b77c`:

- **Survivor accounting.** Any failed witness check, bridge errors included,
  counted as a survivor. Now only a completed, attributed failure counts as
  `witness-failed`; anything else is `error`.
- **Proof score.** The proof "score" was 100% by construction; it was
  replaced by counts. Pilot entries that duplicated census mutants were
  dropped.
- **Census patterns.** The `± 1` pattern missed the local increments. The
  receiver operator saw only a capture that comes first, and its stutter
  form was not a double evaluation; it is replaced by re-evaluating the
  receiver. Memory deletes had no operator. Several families were mislabelled
  (slots, closings, invariants).
- **Runtime limits.** Heartbeat and recursion failures could count as
  detections.
- **Hand lemmas.** A hand lemma's `sorry` passed silently; the `H28 TRUST`
  guard now reports it.
- **Regions.** The target and oracle regions overlapped by one line.
- **What witnesses state.** Kill signatures and source-link constructors were
  not checked, and target-region warnings could fail a witness.
- **Resume.** `--resume` could merge stale records.

Two further defects surfaced in the first recorded run and were fixed before
the final one: the rejection checker read only the `source_link` header line,
and a failing hand lemma's cascade was reported through the trust guard.

A second finder and skeptic pair reviewed the evidence and this document at
`e0f5c8bf`. Their outcomes are recorded under
[Final reviews](#final-reviews).

## Final reviews

Separate read-only finder and skeptic reviews at `e0f5c8bf`; neither used
the Lean server.

The **finder** recomputed the evidence and found it consistent:

- recomputing `summarize` gives exactly the stored summary;
- all 301 records exist, with none missing or extra;
- every scratch hash and region rebuilds from the files at `20d7b77c`;
- re-running the classifiers changes 0 of 301 decisions;
- all 297 reused records are byte-consistent with `full-91c9631d`;
- every invalid compilation's first error is within two lines of its edit;
- every scored kill has no error or warning, only the three permitted
  axioms, and exactly one normal-table error, inside its `source_link` span.

Its remaining findings were documentation-level and are fixed above:

- the trust-cascade exception;
- the `¬broke` parse artifacts;
- unchecked helper links;
- reuse validity;
- the version of `compact.py`.

The **skeptic** found wrong numbers and overclaims in this document, all
corrected above:

- the per-family table had summed the pilot and control entries;
- several operator counts in the census table were wrong;
- the Status line had claimed queue items 1–5 done;
- the run-provenance section had hidden the six errors of `full-91c9631d`;
- the limits on per-family semantic coverage, the backfill, timeouts and
  survivors were missing.

## Gates

GATES-PENDING

## Limits

- **Proof-oracle verdicts.** These are about premise identity with
  `Stmt.step`, not soundness. Only the 20 scored cases have semantic
  verdicts.
- **Census scope.** The census covers the 30 declared operators. It does not
  reach the term semantics of checked arithmetic, division by zero, the
  minimum ÷ −1 case or array bounds, which live in `Tm.denote` and
  `Stmt.runR`, not in the read-only rule table. Those behaviours are
  exercised only by the semantic witnesses (overflow, division and bounds
  pilots).
- **Clauses with no operator:**
  - the pushed value of `storagePushValueSave`;
  - the variant clause of `whileInvariantDiamond`;
  - `tryCall*` branches and binders;
  - the term-built premises of the 13 no-premise-text constructors;
- **Not re-certified here:** the Codex VM's evidence, caches, seals and H35
  transport. The pilots were re-run fresh instead.
- **Runner outcome coverage.** Timeouts fold into `error`; the runner keeps
  no separate timeout class. No real survivor (`witness-failed`) occurs in
  the run: that outcome is exercised only by the unit tests. The
  cross-witness control ends in `link-mismatch`, which the runner checks
  before running the witness.
- **Backfill.** The negative controls cover only the guard and
  rollback/payment families. The other seven families have none of their
  own.
- **Census, helpers.** 51 of the 55 `Tms` helpers have no operator.
- **Resource measurement.** No per-process RSS is available through the
  language-server bridge, and VM memory was observed by hand, not recorded.


## History (Codex VM)

The text below is the Codex VM record as it was moved. Its paths under
`/workspace`, its Docker backend, caches, bulk archive and seals are not
available on the Claude VM, and nothing below was re-certified here except
through the fresh runs above. Old status line:

Status: partial. Three concrete guard/control development cases have checked
semantic witnesses; the frozen assignment is not complete. The full candidate
manifest is not frozen, the general runner has passed its committed six-case pilot, and no full-assignment mutation
score or scope-complete acceptance is claimed.

Base: `6f3eedf0788ee1f8a3bcf230558c712ecdca04d5`.
Repository: `/workspace/solidity-lean`.
Branch: `codex/solidity-h28-sol-20261104/mutation-testing`.
No production input, statement, premise, exclusion, refusal, intrinsic type,
proof budget, shared root or producer implementation has changed.

### Checked concrete witnesses

The development cases are
[guard-cases.draft.json](../../tests/h28-sol/mutation-testing/guard-cases.draft.json).
They are a source-hashed subset for developing the checker, not the exhaustive
assignment manifest.

| Exact ID | One-change edit | Inhabited counterexample |
|---|---|---|
| `guard.require-success-false` | `requireSimple` success guard `true` to `false` | `require(true)` succeeds, but both mutant antecedents are false, so the premise admits a false postcondition. |
| `guard.require-revert-true` | `requireSimple` revert guard `false` to `true` | `require(false)` reverts, but the mutant again admits the false postcondition. This adds the opposite-polarity negative control. |
| `control.revert-diamond-true` | `revertDiamond` closes to `true` instead of `false` | The actual revert cannot satisfy a diamond, while the mutant closes even with a false postcondition. Its edit is independent of the two guard edits. |

Each witness proves an actual constructor instance (`source_link`), an inhabited
`State`, premise acceptance of false, real modal rejection of false, and
`¬ Premise.Sound` for the same statement, premise and state. The proof uses a
concrete continuation, frames and postcondition to refute the universally
quantified soundness interface; it does not replace that interface or weaken it.
The normal baselines independently check the original constructor and typed run.

[Isolated evidence](../../tests/h28-sol/mutation-testing/evidence/guard-checked-isolated/result.json)
contains all 18 validated checks: for each case, fresh normal and mutant source
trees each compile production Rules, check the original oracle, and check the
semantic witness. The original oracle passes only on the normal tree; the
witness passes only on the mutant tree. Rejections must be exactly the expected
source-link type mismatch; errors are never semantic kill evidence by themselves.
The successful witness and its source link supply the checked semantic evidence.

Actual theorem signatures, axiom sets, executed oracle snapshots, commands,
exits, timings, RSS, hashes and one-change diffs are retained per case.
Successful declarations use only `propext`, `Classical.choice`, `Quot.sound`.
Expected failing source-link checks can print Lean's error-recovery `sorryAx`;
those nonzero checks are not accepted proofs. The successful-proof validator
rejects `sorryAx`, unexpected axioms, warnings, missing signatures and errors.
No source `sorry`, axiom, unsafe code, native_decide or heartbeat increase was added.

The isolated run took 103.795428 seconds across 18 checks; maximum actual Lean
child RSS was 1,461,844 KiB. Cgroup peak charged memory was 548,257,792 bytes.
These are different measurements: shared mapped pages may be charged to a
parent cgroup. Neither number is substituted for the other.

### Bounded execution and cache trust

[bounded.py](../../tests/h28-sol/mutation-testing/tools/bounded.py) runs one Lean
process at a time with `LEAN_NUM_THREADS=1`, explicit `-j1`, unchanged stack and
heartbeat settings, a hard 6 GiB Docker limit, zero swap allowance, no network,
read-only source/runtime/cache mounts and a 4 GiB headroom guard. Only `.lake`
artifacts are writable. Docker inspection checks the requested bounds, mount
permissions, network mode, OOM status and measured exit consistency. The
external [measure.c](../../tests/h28-sol/mutation-testing/tools/measure.c)
helper records wait4 child RSS and elapsed time; it is instrumentation, not a
Lean trust mechanism. Tool/runtime and log hashes are recorded in the latest
backend controls.

The supplied old `.lake` artifacts were stale. The
[dependency bootstrap](../../tests/h28-sol/mutation-testing/evidence/cache-bootstrap/manifest.json)
rebuilt all 68 oracle dependency modules from the exact pinned base, without
reusing any existing olean, in 424.262461 seconds. Source and output hashes and
all commands/exits/cgroup peaks are retained. Those earlier bootstrap checks
predate the wait4 helper, so per-process RSS is unavailable there; cgroup peaks
are explicitly labelled. Cache tree:
`/workspace/h28-runtime/prepared-base-6f3eedf0`.

Every probe has a fresh private artifact overlay. Cached reverse dependencies
of Rules are unavailable; the allowlist excludes the original Rules, Taclet
and CallbackRules artifacts. `/cache` is not on LEAN_PATH. The reviewed oracles
import only Rules and PremiseSound, so no cached theorem about a changed rule
can be reused. Input source hashes are checked before and after Lean commands.
This older scoped development driver supports Rules targets only; the
committed-manifest engine and its executed pilot are documented below.

### Validation and reviews

[Final launcher controls](../../tests/h28-sol/mutation-testing/evidence/backend-controls-final/result.json)
pass all four actual checks: an allowed cache import succeeds; an excluded
cached Taclet import is refused; a source write fails and its hash is unchanged;
a timed-out container is removed. These IO fixtures are external launcher tests,
not semantic proof oracles.

[Initial unit controls](../../tests/h28-sol/mutation-testing/evidence/validator-selftests-final.log):
27 passed at the pre-engine checkpoint. They cover false-kill classifications, missing/extra diagnostics,
axioms/signatures, malformed output, infrastructure errors, unrun accounting,
unique edits and disabled general execution. Synthetic parser messages are
never used as semantic proof evidence.

[Saved-output replay](../../tests/h28-sol/mutation-testing/evidence/validation-replay.log)
revalidates the exact six phase keys, executed-source snapshots, log hashes,
18 semantic checks and four final backend controls. This is validation of saved
results, not a new Lean run.

Separate read-only finder and skeptic reviews, neither using Lean server,
confirmed the substantive witnesses. They found the unfiltered cache fallback
and an infrastructure-error false-pass path in two launcher controls. Both
were fixed, with isolated reruns and regressions. Final verdict: safe as the
three-case partial development checkpoint, not assignment acceptance. See
[reviews](../../tests/h28-sol/mutation-testing/evidence/reviews-guard.json).

Actual Lean: 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`.
Lake: 5.0.0-src+797c613. The earlier permitted KeySort probe passed with explicit
`-j1`, an 8 GiB hard cap, zero swap and over 4 GiB headroom:
[KeySort gate](../../tests/h28-sol/mutation-testing/evidence/runtime-keysort.json).
RUNTIME_GATE_PASS applies to that runtime readiness probe only.

Failed development attempts remain visible: the initial stale/missing artifact
probes and the signature parser's refusal of abbreviated #check names. Their
logs are retained in `evidence/guard-development` and `evidence/guard-checked`.
The fully qualified signature probes and rebuilt cache address those failures.
Earlier unit timing collection also records that `/usr/bin/time` was absent;
Python resource accounting was used for those Python test processes.

### Inventory, publication and full queue

The reproducible
[draft census](../../tests/h28-sol/mutation-testing/inventory.draft.json)
contains 215 constructor rows: 181 Taclet, 28 LeanTaclet, four CallbackTaclet and
two Rule wrappers, with source hashes. Family classification is heuristic;
clause/operator-instance coverage and the exhaustive candidate manifest remain
unaccepted. Eight standalone oracle files have a
[local registration manifest](../../tests/h28-sol/mutation-testing/registration.json).
No central root or shared module map changed.

The coordinator's published master update was fetched and verified as
`b419c3cf4f642ae519b66bebc26cdf2f7cf93574`, including ancestry from the H28 base.
The assigned branch was not merged or rebased; H28 production inputs stay frozen
at its original base. The new producer APIs are not duplicated or needed by
these pinned rule probes. The coordinator's global gates are not claimed as
this lane's final acceptance.

1. Inventory: partial. Finish every constructor clause and operator-instance
   disposition in the nine assigned families, select exact edits and semantic
   oracles, review and freeze the exhaustive manifest.
2. Runner: partial. The committed-manifest engine now implements provenance checks, dynamic
   reverse-dependency filtering, fresh source-audited trees, checked kill and
   equivalence certificates, visible survivors and score denominators. The frozen six-case pilot passes; integrate the remaining families
   and whole-assignment acceptance.
3. Semantic witnesses: partial. The three cases above are checked; they do not
   complete the whole guard family. Overflow, division/minimum, index bounds,
   push dirty tail/length ordering, pop/delete, alias capture once,
   rollback/payment and callback frames remain open, together with any remaining
   selected guard clauses. Preserve inhabited controls and exact axiom signatures.
4. Full manifest execution, final repository gates, independent scope-complete
   acceptance and the final immutable seal/handoff: pending.
5. Backfill: partial. Opposite guard polarity is covered; continue additional
   negative controls within the selected families, never producer repairs.

The persistent goal remains unfinished and needs no new scope authorization.
Continue in the same VM and branch. Keep every statement, premise, exclusion,
refusal, observation, budget, intrinsic type, H16/H19/H25 Source freeze, frozen
H22 Core ExtCall and H21/shared registry boundary intact. Do not push or merge.


### Committed runner implementation and executed pilot

`tools/engine.py` requires a clean assigned branch, exact base ancestry, a
committed schema-2 frozen manifest, committed inventory/cache metadata/oracles,
all frozen source and theorem signature hashes, and unchanged runtime binaries.
It dynamically excludes every cached reverse dependency of the mutated module.
A single advisory writer lock covers each run. Evidence is written outside the
checkout, preserving clean input provenance. Checks retain commands, exits,
timings, RSS, hashes, source inventories and actual one-change diffs.

`manifests/runner-pilot.json` freezes exactly six cases with scope `pilot`: the
two guard mutations, the independent revert known kill, a branch-label semantic
equivalence control, malformed guard syntax for invalid compilation, and a
transparent duplicate guard edit observed by a deliberately weak primary oracle.
The last case must remain `surviving` even though its concrete semantic witness
and stronger regression demonstrate the defect. The regression must pass on
the normal baseline. It is an unscored runner self-test, not a relabelled scored
mutant. Known-kill independence and every score exclusion are explicit.

`GuardEquivalent.lean` has a real universal constructor link and equality of
premise formulas for all contracts, contexts, simple conditions, modalities,
fresh counters, continuations, frames and postconditions, plus an inhabited
input. It passes against the normal production rule. The executed pilot also checks it against the actual changed-label constructor;
the universal certificate passes on both normal and mutant trees.

The implementation unit gate passes 61 tests. The final actual launcher gate
passes four controls in `evidence/backend-controls-engine-final`. Read-only
finder/skeptic reviews confirmed fixes for control-gated scoring, independent
baseline regression validation and cleanup priority. Unconfirmed teardown now
aborts subsequent heavy checks before parsing can mask the cleanup failure.
Neither runner completion nor a pilot score can set `scope_complete=true`.

Two conservative memory-guard refusals remain visible in
`evidence/backend-controls-engine*`: no Lean ran in the first; only the allowed
import ran in the retry. The retry's raw intermediate JSON incorrectly emitted
pass=true for a completed subset although its CLI exited 1. A retained
failure.json explains this defect; control summaries now require all declared
checks and list unrun IDs. No failed attempt is counted as a passing gate.

The available-memory guard now distinguishes strictly unused cgroup bytes from
estimated reclaimable clean inactive-file cache, subtracts dirty/writeback
bytes, caps against OS MemAvailable, and records each quantity. Missing or
malformed counters give zero reclaim or refusal. The reserve is estimated
available headroom after reclaim, not already-unused RAM; hard6GiB/no-swap
limits and the 4GiB reserve are unchanged. Both reviewers checked this
interpretation. OOM, timeout and cleanup failures still remain errors/stops.

The inputs were committed and the entire six-case pilot executed from
`31518385cd7f130e66796faedd730464519cef37` into
`/workspace/h28-runner-pilot-31518385`. The subsequent evidence commit changes
only documentation/evidence; it does not change those executed inputs. Continue
the unchanged nine-family queue; this pilot is not whole-family or
whole-assignment completion.


### Pilot outcomes and immutable input identity

The executed manifest hash is
`16a05d59974830d848051b58873f1004e6f960dd6537f0dbc77f1250bf18fc1d`.
All six cases completed and all 35 phase logs have exact commands, exits,
elapsed times, actual child RSS, cgroup limits/availability, cleanup confirmation
and hashes. Source/archive identities, proof signatures and axioms are retained
in `evidence/runner-pilot-31518385`, with the original SHA256SUMS unchanged.
Both independent reviewers audited the actual run and found no discrepancy;
see `evidence/runner-pilot-audit.json`.

| Case | Actual outcome | Score disposition |
|---|---|---|
| `guard.require-success-false` | killed by checked semantic witness | scored |
| `guard.require-revert-true` | killed by checked semantic witness | scored |
| `control.revert-diamond-true` | killed by independent checked witness | known-kill control, unscored |
| `control.guard-label-equivalent` | equivalent, universal certificate on both trees | equivalence control, unscored |
| `control.guard-invalid-syntax` | invalid compilation | invalid control, unscored |
| `control.guard-weak-oracle-survivor` | surviving; concrete witness and stronger regression checked | transparent duplicate runner self-test, unscored |

The pilot denominator is exactly the two scored guard IDs: 2 killed out of 2.
No unrun case is scored. The survivor remains visible; its stronger regression
passed normally and rejected the actual mutant without relabelling the primary
oracle outcome. These controls and exclusions were declared before execution.
`runner_cases_complete=true` and `scope_complete=false` distinguish pilot
execution from assignment acceptance. This is not the full H28 mutation score.

The peak recorded child RSS across the pilot was 1,454,092 KiB. No phase timed
out or OOMed, and every launched container has confirmed removal. The current
full-queue obligations above remain binding and unfinished.


### Unsigned overflow development checkpoint

Two further source-linked semantic witnesses pass12 fresh normal/mutant checks
in `evidence/overflow-checked-complete`: replacing the typed compound numeric
helper body with subtraction, and erasing the local-increment update. Both
start with a valid maximum uint256 stack local. The original checked addition
or increment reverts; the mutant has an explicit successful typed landing and
admits a true postcondition. Each `checked_kill` is an unconditional negation
of the existing Premise.Sound interface on that same input.

The helper edit preserves its original generic signature, compound-operator
premise and numeric premise. The local-increment edit is an additional negative
control. Separate finder/skeptic reviews replayed all12 validations, exact
source/diff/log identities, theorem signatures and permitted axiom sets without
Lean server use. They approved only these development cases.

The initially attempted fixed-minus schema defaulted to uint and failed generic
typing. It remains an invalid candidate in `overflow-schema-invalid.draft.json`
and `evidence/overflow-checked`; it is not counted as killed. The subsequent
helper witness compiled, but its missing #check typed_landing export caused a
validation refusal; that failure is retained too. The corrected witnesses now
include both axiom and type signatures for the concrete landing proof.

`inventory.py --with-term-helpers` reproduces
`inventory.extended.draft.json`:215 constructor rows plus all55 Tms term-helper
definitions. The original215-row pilot inventory remains byte-for-byte unchanged.
The binopC row identifies seven generic compound-update constructors and five
fixed push arithmetic constructors using it; size arithmetic is excluded by
schema pushArithmetic, and fixed subtraction remains unchanged by this mutant.
Full clause/operator and nine-family inventory acceptance remains pending.

`manifests/overflow-pilot.json` freezes these two selected cases plus the
independent revert known-kill control. Its committed runner execution is still
pending. This is not whole-overflow-family or whole-assignment acceptance.


### Adaptive bounded memory profiles

Two frozen overflow pilot attempts refused before launching Lean because the
6 GiB cap could not leave the required 4 GiB reserve. Their unchanged results
and checksums are retained in `evidence/resource-profiles`; all cases remain
unrun and neither attempt contributes a score. The launcher now chooses the
largest of 6, 4 or 2 GiB that preserves the same reserve, otherwise refuses.
Docker limits, in-container checks and inspection agree on the selected cap;
swap remains zero and OOM/timeouts remain errors. All 62 unit controls and four
actual backend controls pass; separate read-only finder and skeptic approve
this resource-policy change. This does not change semantic proof budgets.

The coordinator publication 89373e34cdfd6bb5db7054b1c204d01edffc5fa7 was
fetched and verified at origin/master. The assigned branch remains based on
6f3eedf0788ee1f8a3bcf230558c712ecdca04d5 without merging producer changes.


### Executed overflow pilot and inventory erratum

The frozen overflow pilot ran from 79041a2834070ad37c79fa0e68381207ce97a462.
All three cases were killed with checked semantic witnesses, including the
independent revert control. The selected denominator is two, both killed; no
case remains unrun. All 18 normal/mutant checks retain exact commands, exits,
timing, RSS, signatures, axiom output and confirmed cleanup in
`evidence/overflow-pilot-79041a28`. `scope_complete` remains false.

Both reviewers identified a draft-inventory omission: binopC is also used
transitively by binopI. The frozen inventory is preserved for reproducibility;
`inventory.extended.errata.json` explicitly marks its affected-use list partial
and records additional increment/decrement candidates. Fixed-sub changes add
increments while leaving sub decrements unchanged. This does not invalidate
the actual localOpAssign source link; full clause/operator coverage is pending.


### Division development checkpoint

A distinct conditional helper-body edit substitutes subtraction only for div,
preserving all numeric/compound typing premises. Six fresh normal/mutant
checks pass in `evidence/division-development-landing`. The Boolean family
uses signed minimum divided by -1 and 1 divided by zero. Both actual runs
revert; both mutant updates have explicit typed landings and unconditional
negations of Premise.Sound. The two inputs share one source-linked mutant ID
and count as one selected mutation, not two denominator entries.

Three earlier development refusals remain immutable: ill-typed literal, unused
binder warning, and an open local-valuation proof. No refusal is called a kill.
The final source-linked witness has no open obligations or placeholder axioms.
`manifests/division-pilot.json` freezes this case plus the independent revert
control; committed execution and full-family acceptance are still pending.


The frozen division pilot executed from
`a887c1a5f81ca572f81a5318f8365fdaad0c7363`: both cases killed in 12 checked
phases, including the independent known-kill. The selected denominator is one
mutation with two distinct boundary witnesses, killed; no case is unrun. The
byte-identical sealed evidence is `evidence/division-pilot-a887c1a5`. Scope
acceptance remains false; full family/operator and assignment gates are pending.

Separate read-only finder and skeptic audits pass for these 12 phases; see
`evidence/division-pilot-audit.json`. Peak child RSS was 1,454,904 KiB; all
checks used 4 GiB/no-swap profiles and preserved at least 4 GiB reserve.


### H35 VM build, axiom inventory and cache transport

H35 adds cache transport as a checkpoint acceptance requirement. Previous
pilot execution results remain valid, but H35 integration acceptance is pending
a transport receipt. A normal source-linked oracle and a mutant-only kill
witness must be compiled in their respective disposable trees; the latter
is intentionally rejected against normal source. No witness is weakened to
make all modules compile together against normal production.

The runner now produces and retains successful `.olean` outputs after exact
diagnostic, frozen signature and axiom validation. Files are isolated by case
and baseline/mutant phase, with source/output SHA256 and size. Missing, empty,
symlinked or overwritten artifacts refuse acceptance. Expected negative checks
retain no compiled artifact. These outputs are not represented as Lake cache
mappings or a transport receipt.

Every theorem in each owned oracle, including unselected helper theorems, must
now have exactly one #print axioms export and only the existing permitted
axioms. The shared restricted source scanner handles nested and line comments,
refuses string/quoted-identifier/quotation syntax and anonymous proofs, and is
used by both trust preflight and theorem inventory. Independent reviews found
and closed the string-comment hiding and anonymous-example gaps. All 65 unit
controls and four actual launcher controls pass in `evidence/h35-controls`.

The requested pinned `ship-cache.sh` was actually run twice. Its default
coordinator-only head check exited 2. With documented lane-head override and
the actual local Lake cache it exited 1 because the coordinator poll-state
catalog is absent; vmexec.py is absent too. It generated local shipment data
but transported nothing. `evidence/h35-shipping-preflight` retains commands,
exits and complete logs. Q-H35-TRANSPORT asks which VM-to-coordinator transport
to use. No receipt or H35 completion is claimed while that question is pending.


Fresh runs from `6b5d1fdb758a68d417b9ec92691099643f954933` pass all
65 phases across the three frozen pilot manifests. They retain 46 regular
compiled artifacts and 103 theorem axiom exports across 25 successful owned
source checks. Both independent final reviews pass. Every check used -j1,
4 GiB/no-swap, required reserve and confirmed cleanup; peak child RSS was
1,466,216 KiB. Dispositions and pilot denominators are unchanged.

`evidence/h35-vm-build` contains text receipts and a catalog referring to the
full external runs and 96,188,452-byte local export archive. The archive
includes the compiled proof worlds, all fourteen oracle source snapshots and
the exact pinned dependency cache. Its SHA256 is
`aeceb8036520bfa9df52a225053b8de6597747f8b3c46de299d630a22268c168`.
The renamed EXTERNAL-RUN-SHA256SUMS apply to the complete external directories,
not the text subset. Mutant Rules/witness artifacts must remain isolated from
normal production caches. This export is not a Lake mapping shipment.

The requested shipping script was also called after the fresh VM gates and
again refused the lane head. No cache transport receipt exists. All H35
integration checkpoint statuses remain partial pending that receipt, although
the recorded pilot executions and VM proof builds pass. Original full-queue
obligations remain unchanged.


### Q-H35-TRANSPORT

Sources: H35; pinned scripts/coord-tools/ship-cache.sh (coordinator relay).
The actual VM calls failed: default master-only check, then absent coordinator
poll-state catalog/transport after the documented lane-head override. Which
transport should this lane use for its completed local export?

1. Provide a VM-to-coordinator exporter and destination; run it here and retain
   its actual receipt before H35 acceptance.
2. Have the coordinator retrieve the sealed VM archive and issue a transport
   receipt; retain H35 status partial until that receipt arrives.

No option is assumed or recommended. The existing persistent full objective
remains unfinished; no goal has been created, reset or completed.


### H41 cache pull and continuation

H41 authorizes leaving VM cache packs with path and SHA256 for coordinator
pull. This resolves Q-H35-TRANSPORT without an invented transfer receipt. The
existing 96,188,452-byte archive was rehashed successfully on resume;
`evidence/h41-cache-pull.json` records its absolute path and hash. The 65 VM
checks, 46 artifacts and 103 axiom exports remain the accepted local gate
evidence. Coordinator pull has not been observed. Continue the original queue.

Published master 8bf8321873befa3f35ca31e97e5339a1baee93e6 was fetched and
its ancestry verified. The owned branch and immutable 6f3eedf0 base are
unchanged; no producer changes were merged.


### Index-bound development checkpoint

`bounds.array-read-skipped` changes only storageIndexReadArrayFind RHS from
find(storage, arr[ie]) to the target local v. It preserves every typed receiver,
array-kind and simplicity side condition while omitting the indexed read.
Six fresh normal/mutant phases pass in `evidence/bounds-skipped-checked`.
The actual generic source link covers dynamic and fixed array roots. The
concrete dynamic-empty read and fixed index equal to length both revert, while
the mutant has explicit inhabited identity landings. Both nonempty live-read
controls execute and store 7; the initial local and mutant result are 9.

The initial default-value DSL edit failed generic typing and remains an
invalid, unscored candidate in `bounds-default-schema-invalid.draft.json`.
Other development failures preserve a mismatched Out type, closed controls
requiring existing irreducible definitions unfolded, source-link attribution
format/implicit-side-condition errors, and an unfinished local landing read.
No failure was scored or relabelled as killed. The final statements retain
their original strength, explicit typed states, premises and proof budgets.

`manifests/bounds-pilot.json` freezes the reviewed selected edit, both boundary
witness exports, positive controls and an independent revert known-kill.
Committed execution, artifact build/axiom gate and H41 cache pack follow; this
is not complete index-clause or whole-assignment acceptance.

Separate read-only finder and skeptic reviews pass for the six development
phases and exact frozen inputs (`evidence/bounds-review.json`). Fresh runtime
gates on the resumed VM pass: Lean 4.24.0, Lake 5.0.0-src+797c613 and KeySort
exit 0; all 65 unit controls and four actual launcher controls pass. Their
commands, exits, timings and RSS are in `evidence/bounds-runtime-gate`.


The frozen bounds pilot executed from
`e852854de93f20e1529549db1be5b9a6d0811b79`: 12 checked build phases, eight
compiled artifacts and 27 theorem axiom exports pass. Both the selected mutant
and independent control are killed, denominator 1/1, no unrun cases. Separate
read-only finder and skeptic audits pass. Every check used -j1, 6 GiB/no-swap
and confirmed cleanup; peak child RSS was 1,456,132 KiB. Full scope stays false.

`evidence/bounds-pilot-e852854d` is an explicit text receipt subset; its H41
pack receipt identifies the complete external cache archive and SHA256. The
prior H35 pack provides the exact pinned dependency cache. Coordinator pull
has not been observed. These pilot outcomes do not complete the full queue.


### Pop/delete development checkpoint

Two distinct constructor RHS edits omit the storage update: storagePopSave
and storageIndexArrayDelete. The original simple-receiver and nonmapping
side conditions remain explicit. Twelve fresh development phases pass in
`evidence/pop-delete-development`, with no earlier rejected attempt. Empty
pop and an indexed delete at length zero really revert; each mutant has
inhabited successful identity landings on empty and populated typed states.
The live controls prove exact Out results: pop removes 7 and clears the shadow
slot to zero, whereas delete clears 7 without changing the live length.

`manifests/pop-delete-pilot.json` freezes these two cases plus the distinct
revert control. The pilot denominator is two, including the independently
declared delete negative control; development evidence remains score=null.
All 65 runner unit controls pass in `evidence/pop-delete-controls`. Committed
execution, all-theorem axiom inventory, compiled outputs and H41 pack follow;
full pop/delete constructor coverage and the original assignment remain open.


The committed pop/delete pilot ran from
`5b488a1159a149ca5f8950f9fcbf9de3008bf2c3`. All 18 phases pass, with
12 compiled artifacts and 34 theorem axiom exports. The two selected cases
and independent control are killed; denominator 2/2, no unrun, scope false.
Separate read-only finder/skeptic final audits pass. All checks used -j1,
6 GiB/no swap and confirmed cleanup; peak child RSS 1,466,808 KiB.
`evidence/pop-delete-pilot-5b488a11` holds text receipts and the H41 cache-pack
path/hash, referencing the unchanged pinned dependency pack. Coordinator pull
is not observed. Continue the original queue with push-tail/update ordering.


### Push recycled-tail and update-order development

`push.reference-tail-cleared` wraps the typed STerm.pushSlot helper result in
a deletion of the just-appended slot, leaving the original helper interface
and rule side conditions intact. On a concrete recycled reference slot the
actual push exposes an inner array of length 1 containing 7; the mutant has an
explicit typed landing with that inner array cleared to length 0. The clean
slot control is unchanged. The postcondition is evaluated through the actual
Theory term bridge, not a separate model of execution.

`push.compound-updates-swapped` reverses the two original updates of
storagePushAddAssign. On an empty array its first update fails ordinarily,
without exhaustion, so the mutant box premise admits false while the actual
compound push succeeds. On a populated array both mutant updates have actual
typed landings linked by the same intermediate state: [7] to [8] to [8,0],
while the actual statement returns [7,1]. This is not an always-failing or
empty update relation.

The selected six tail phases in `evidence/push-tail-order-development` and
six order phases in `evidence/push-order-checked` pass. The first tail attempt
retains a strict source-link formatting refusal; the first order attempt
retains an ill-typed intermediate heap declaration. That declaration was
replaced by the stronger explicit concrete-state landing conjunction. The
constructor diagnostic also records unavailable PairLands under the fixed
import boundary; it is diagnostic-only, not a passing proof gate. No failure
is scored, no theorem/premise weakened and no budget increased.

`manifests/push-pilot.json` freezes the two edits and the independent revert
control. All 65 unit controls pass in `evidence/push-controls`. Committed
artifact builds, complete axiom inventory and H41 pack follow; exhaustive
helper-callsite/operator and whole-assignment acceptance remain pending.


The committed combined push pilot ran from
`ea111ccfa14f9c7ad65691e4f2188c5488af2848`. All 18 phases pass, with
12 compiled outputs and 47 theorem axiom exports. Both selected cases and
the independent control are killed, denominator 2/2, no unrun, scope false.
Separate read-only finder/skeptic final audits pass. Every check used -j1,
6 GiB/no swap and confirmed cleanup; peak child RSS 1,451,232 KiB.
`evidence/push-pilot-ea111ccf` contains the explicit text receipt subset and
H41 pack path/hash with the separately pinned dependency cache. No observed
coordinator transfer or full-family/assignment completion is claimed.


### Authorized delivery rebase onto e6849d3b

The coordinator explicitly instructed rebasing onto
e6849d3bdf516099d20c33d3581d523449764018 before the next commit. Fetch and
ancestry checks pass; all 18 owned commits replayed without conflict. The old
head and alias WIP are preserved by a backup branch and retained stash, listed
in `evidence/rebase-e6849d3b/setup.json`. No work was reset or discarded.

The semantic source/cache base remains
6f3eedf0788ee1f8a3bcf230558c712ecdca04d5: all 68 cached dependency sources
and the pinned production inputs are byte-identical at the new delivery base.
The runner now checks exclusive writes relative to the explicitly authorized
delivery base, while retaining the original source/cache hashes, clean-tree,
committed-input, branch and runtime gates. A real-Git control rejects any new
producer edit after that base and any branch missing its ancestry. Historical
run heads remain factual; their original commits are retained by the backup.

Separate finder/skeptic rebase reviews pass after closing a rename-detection
blind spot: scope diff now uses --no-renames and a real-Git producer-to-owned
move control. All 66 unit controls pass. The alias WIP has an explicit
200000-heartbeat failure in its pure two-call control; its budget and statement
remain unchanged, no mutant run or kill is claimed. That proof will be split
compositionally after the provenance checkpoint is validated.


The fresh six-case pilot from
`f664b046340d0a43374d535ef2fb51654afdfccf` passes all 35 checks, 26 compiled
outputs and 53 theorem axiom exports after the authorized rebase. Separate
read-only finder/skeptic audits pass. Expected kills, equivalence, invalid
compilation and genuine survivor remain distinct; denominator 2/2 and scope
false. Every check used -j1, 6 GiB/no-swap and confirmed cleanup; peak RSS
1,459,724 KiB. `evidence/rebase-pilot-f664b046` provides text receipts and the
H41 pack path/hash with the unchanged dependency pack. This validates delivery
provenance, not completion of the remaining semantic-family queue.


### Alias receiver captured once development

`alias.receiver-getter-twice` evaluates the storage-returning getter twice,
then appends exactly once. The disposable rule uses an explicit typed premise
because the canonical source DSL deliberately accepts only a single capture.
All quantified constructor input types, names, LHS and defaultability premise
are identical before/after (both full signatures are printed in the logs);
only the semantic RHS changes. Production source remains read-only.

The effectful getter increments a storage counter: the actual statement ends
at 1, the mutant at 2, with one array element in both states. The pure getter
control has the same result after one or two calls. Actual call/append and
capture-pop frame executions provide inhabited typed intermediate/result
states. The first monolithic pure-control proof hit the existing 200000
heartbeat limit and remains unscored in `evidence/alias-development`. The same
control and budget now pass using small call/append lemmas composed with the
existing Prog.run_cons_ok. No budget, statement, input or side condition was
weakened. Six fresh phases pass in `evidence/alias-compositional-development`.

`manifests/alias-pilot.json` freezes this case plus the distinct revert control;
all 66 unit controls pass in `evidence/alias-controls`. Committed artifact/axiom
gates and H41 pack follow. Full alias/callsite inventory, rollback/payment,
callback frames and final original assignment gates remain pending.

The frozen alias pilot from64d7def6ef0a417ceb3a964450220930d6f1588c now passes all12 VM checks,8 retained compiled outputs and48 complete owned theorem axiom exports. The selected alias denominator is1/1; independent revert control passes, unrun=[] and scope_complete=false. Separate actual-run and H41 archive finder/skeptic reviews PASS. All checks used -j1,6GiB/no swap and confirmed cleanup; peakRSS1,467,752KiB. Evidence is `evidence/alias-pilot-64d7def6`; its cache-pack.json records the verified6,034,421byte H41 pack path/SHA, ready for coordinator pull with no transfer observed. Full family/assignment obligations above remain pending.

### Payment success flag development

`payment.success-flag-false` changes only the sendNoCallbackBox successful return flag from true to false. Both branches and the payment booking remain present. A funded accepted send books -5 at receiver9, leaves balance5 and returns true. A concrete recipient refusal returns false and preserves the full original state except that return local. The mutant admits a false-return postcondition contradicted by the actual accepted run. Actual typed landings of both mutant updates, with exact paid/unchanged ledger and balances, prevent vacuous box controls. Finder requested these explicit landings; added without changing statements or budgets.

Initial configuration, term notation and local-function conversion failures remain immutable and unscored in payment-development, payment-development-v2 and payment-inhabited-development. The earlier weaker development run passed but is superseded by the strengthened six-phase `payment-typed-development`; all six phases and all66 runner unit controls pass. `manifests/payment-pilot.json` freezes exact sources, edit, theorem signatures and independent revert control. Committed VM builds/complete axiom inventories and H41 pack remain pending; this is not full payment/callback or original-assignment acceptance.

The committed payment pilot from5b2317f359f9105050012ae6a249252357f0c3bb passes all12 VM phases,8retained compiled outputs and27full owned theorem axiom exports. Selecteddenominator1/1, independentcontrol killed, unrun=[], scope_complete=false. Separate finder/skeptic actualrun andH41 archive reviews PASS. Checks used -j1,6GiB/no swap/confirmedcleanup; peakRSS1,455,308KiB. `evidence/payment-pilot-5b2317f3` contains exactcommands/exits/timings/axioms/hashes and verified5,970,900byte pack receipt, readyforpull with noobservedtransfer. Original Work queue1 remains partial (candidate draft not exhaustive clause/operator/fixture acceptance); queue2 runner implementation and controls pass but assignment acceptance remains pending; queue3 selected pilot witnesses pass except callback-frame work remains open; queue4 wholecombinedmanifest/finalrepositorygates/finalreviews remain pending. No backfill or producer repair was substituted for those obligations.

### Coordinator automerge 32dd5bef provenance

The coordinator merged published master32dd5befce264eb9a5d1b622b9270e71c50a0f5a into owned headb5e2d9c97c1ef5c7d6f1512eac8357ad63b840ec, producing clean head9bd8e542c463b4dc08f42c2ab081f16f3139758d. Delivery/patch scope now anchors at32dd; immutable semantic/cache base6f3eedf0 is unchanged. All71unique pinned input files remain byteidentical. No production source was edited. The scope guard retains --no-renames and real-Git producer-edit, rename and missing-ancestry rejection controls; all66 tests pass. Exactsetup/unit receipts are in `evidence/automerge-32dd5bef`.

### Callback semantic cache and frame development

The original68-module cache remains unchanged. The authenticated extension adds exactly FirstOrder, Semantics.Callback and CallbackHolds from pinned6f3eedf0, with71source/output identities. Separate finder/skeptic reviews caught and closed mutable-receipt and output-validation gaps before execution: reuse now requires committed receipt bytes plus its fixed SHA, exact module inventories and regular nonempty artifacts; CLI acquires the writer lock. All70unitcontrols pass, including real-Git receipt forgeries, diagnostic fault cases and callback import requirements.

The first cache attempt stopped on the pinned producer's existing unused-simp warning atCallback.lean:1319 despite compilerexit0. Its incomplete evidence remains immutable. Fresh v2 builds all3modules serially, with exact warning JSON identity accepted only for that producer. Owned witness checks still reject every warning. The normal H41 delta receipt and verification are in callback-cache-bootstrap-v2; no transfer is claimed.

`callback.failed-send-flag-true` changes only the shared sendNoCallbackBox failed return flag from false to true; its successful payment remains unchanged. Besides an unconditional deterministic recipient-refusal kill, it checks funded actual ExecS.sendFailed and sendResume outcomes, changed callback ledger/balance with local13 preserved, inhabited capture-pop ExecF outcomes, universal frame preservation/drop landing, and a callback premise whose admitted postcondition actual execution with frames refutes. Both input states have concrete mutant update landings. This tests the shared Taclet under the real callback model; it does not mutate the separate CallbackTaclet table or discharge its additional producer obligations.

The initial oracle's four elaboration failures remain unscored in callback-development. All six strengthened phases pass in callback-typed-development with37owned theorem axiom exports and separate finder/skeptic PASS. callback-pilot.json freezes exact sources, signatures, edit, cache and distinct revert control. Committed pilot artifacts/axioms/H41pack follow. Exhaustive constructor/clause/operator/fixture coverage, combinedmanifest and original final repository gates remain open.

### H44 reviewable delivery split

H44 requires bulk evidence/fixtures out of Git. The exact pre-split snapshot atbe546c1dc41728361a687eeb979f3b9261a08d4a is preserved in a local backup ref and bundle. All1029data files (6,446,281bytes) are copied byte-for-byte under `/workspace/h28-h44-bulk-be546c1dc/files`, indexed in its files.json and sealed in its bulk-data.tar.gz (885,301bytes). The compact committed `tests/h28-sol/mutation-testing/bulk-data.json` records absolute paths, sizes and SHA256 identities. Existing repository paths remain ignored mirrors for unchanged commands. Prior evidence references in this document refer to these authenticated VM files, not tracked dumps.

Only Lean oracles, tools, docs and compact manifests remain in the reviewable increment, rebuilt on authorized delivery base32dd5bef. No theorem, observation, side condition, input, budget or gate changed. Tracked inputs still require exact HEAD bytes; off-Git frozen inputs require the committed bulk manifest, its hashed per-file index, exact external bytes and matching local mirrors. Mutable manifest/index, forged external/mirror bytes, unregistered files and symlinks are rejected by real-Git controls. The new lookup authenticates the same frozen input hashes rather than trusting ignored files. `python3 -B tests/h28-sol/mutation-testing/tools/verify_bulk.py` checks every bulk file, archive and preserved bundle. Full assignment acceptance is still pending.

The sealed snapshot contains1029files:1012generated bulk files move offGit;9frozen pilot configuration manifests and8small verifier scripts remain tracked as reviewable support, with backup copies in the archive. The H44 pointer records this split. Local module registration remains tracked.

The fresh committed callback pilot at9863cd532396595cccd57ab021cbb8e398f9c0a2 passes12actualchecks,8compiledoutputs and45ownedtheoremaxiomexports, with separate finder/skeptic actualrun/archive PASS. Selecteddenominator1/1, independentcontrolkilled,unrun=[],scope_complete=false. A VMrestart interrupted the first run, retained explicitly unscored; the freshR2run is the accepted one. New proof/cache/validation archives stayoffGit; only their path/size/SHA receipts are appended to bulk-data.json. H44split andbulkverification pass, all71unitcontrols pass. Exhaustive fullinventory/coverage, combinedmanifest and originalfinalgates remain unfinished.
