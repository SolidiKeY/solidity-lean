# Ledger quantifier lane

Base `f4dee4a29c2e208b36db4a4161a4723c735cd775`, branch
`codex/next10-quant-ledger`, repository `/workspace/solidity-lean`, origin
`https://github.com/SolidiKeY/solidity-lean.git`. The fetched master is exactly
that base and its ancestry check succeeded. Lean 4.24.0, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake 5.0.0-src+797c613.
The attached executor initially lacked Lean/Lake on PATH; the pinned release
was installed in a task-specific disk directory on the same executor.

The unchanged original `gapQuantLedger` is now proved by the kernel in
`DecisionQuantLedger.original_proved` and `original_goal_proved`.
The named semantic assignment and its required task validations are finished.
The full build, strict static gates, per-file MCP error checks, 24 pipeline
results and exact frozen-input SolKey sort check passed. The global
whole-tree documentation path gate remains red with the same 20 baseline
findings. This is historical documentation debt, not an unresolved ledger
proof or a claim that every repository gate is green.

## Implementation and scope

`QuantLedger.lean` adds exact expansion/hoisting followed by the existing
ledger cut before abstraction. `QuantLedgerBody` retains the ledger-aware
main arithmetic, typed parameter positions and two unrestricted natural codes
per ledger integer. The domain constrains only primitive inputs. Definitions
use `Rep` and `QArith.compile`; exactness and countermodel reconstruction
preserve quantifier polarity, address definedness, alias consistency and all
queried ledger entries. Refutations use query-certified `readValsQ` at the
final reconstructed state, followed by the existing ledger pullback.

Closed definitions may use compact local binder positions only under exact
`freeParams = []`, retaining global fresh-reference bounds. Failed recognition
falls back to the existing compiler. A separate exact truth certificate also
requires `refs = []`: a refuting arithmetic assignment then establishes
uniform falsity at every typed state, not just nonvalidity. Exact intrinsic
formula replacement commutes with negation, conjunction and implication.
The equivalent quantifier-free leaf uses `FlattenedArithmeticZ`; its failed
recognition or 511-node check falls back to the generic quantified verifier.
The original `QArith.compile`, APF and ledger-block pipelines are unchanged.

`decideLeaf` tries this lane after all earlier pipelines, retaining their
returned verdicts and counterstates. `Fml.quantLedgerCovered` means successful
certified reduction; no independent source-fragment characterization or full
`DecisionTheorem` completeness is claimed. The unchanged `netOK` guard requires
remaining binders to read no ledger. This lane does not add unbounded anchors,
raw unbounded binder encoding, memory-gap proofs, a `Residue`, new profile
choices, exclusions or waivers. The six original gap statements and their
`inTarget` certificates are retained. Other gap owners remain independent.

## Fixtures and evidence

The original module built unchanged before edits: 310 jobs, exit 0,
3,310.7 seconds, exact cgroup peak 10,466,168,832 bytes, no OOM kill.
The original leaf then returned `unknown` in 3 seconds. Additional control
baselines used those published-master compiled artifacts before rebuilding
the changed decision module; both public pipelines returned unknown.

The final runner checks both public pipelines, fixed expected verdicts, every
storage root in contract order including retained slots, the complete ledger,
transaction fields, heap-object and external-response counts. It additionally
checks that `highBad` exhibits an entry above the word range and `negativeBad`
a negative entry. All twelve fixtures and 24 pipeline results first passed in
266.978 seconds, exit 0. The resumed run also passed in 255.968 seconds with
identical full ordered observations. Initial per-pipeline times below include
observation output.

| Fixture | Before Leaf / Goal | After Leaf / Goal | After milliseconds Leaf / Goal |
|---|---|---|---|
| original | unknown / unknown | proved / proved | 8 / 2 |
| bad | unknown / unknown | refuted / refuted | 120 / 115 |
| aliasOk | unknown / unknown | proved / proved | 118 / 110 |
| aliasBad | unknown / unknown | refuted / refuted | 110 / 116 |
| distinctBad | unknown / unknown | refuted / refuted | 363 / 387 |
| paymentOk | unknown / unknown | proved / proved | 117436 / 116538 |
| paymentBad | unknown / unknown | refuted / refuted | 117 / 119 |
| highOk | unknown / unknown | proved / proved | 533 / 509 |
| highBad | unknown / unknown | refuted / refuted | 131 / 127 |
| negativeBad | unknown / unknown | refuted / refuted | 103 / 103 |
| paramOk | unknown / unknown | proved / proved | 8757 / 9363 |
| paramBad | unknown / unknown | refuted / refuted | 3980 / 4070 |

`highBad` returned an entry of `2^257 - 1`; `negativeBad` returned `-1`.
`parameters_use_generic` kernel-checks that both parameter fixtures retain
one free typed parameter and cannot use the closed arithmetic route.
`shifted_codes` checks different natural pairs for the same negative entry;
`unbounded_codes` realizes `2^256`. These fixtures are logical leaves and
Theory-level payment updates. No new solc/compiler/external-EVM parity is
claimed; there is no Solidity source fixture whose required EVM pipeline was
silently omitted. The runtime evidence is Lean VM output; the exactness,
soundness, representation laws and original verdict equalities are kernel
proofs. No production JavaScript/Python harness was changed.

## Resources, commands and reviews

Writes and checks acquire the documented writer lock. Heavy groups are
serialized; Lean starts with `LEAN_NUM_THREADS=1` and explicit `-j1` through a
temporary untracked Lake configuration or the direct command line. Docker
cgroups report `memory.max = 12884901888` and `memory.swap.max = 0`.
`systemd-run --user` was unavailable. Caches and logs stay on disk. There is
no extra per-VM 12 GiB reservation. Later gates sample aggregate process RSS
and PSS each second and OS available RAM, alongside exact charged cgroup peak.
The historical baseline retained cgroup peak, not continuous RSS/PSS samples.
The outer VM cgroup is 16 GiB. Two tool-session resets interrupted host
sampling, but the same build container continued under its original limits.
A detached 128 MiB observer ultimately retained complete daemon stdout and
exit status; it ran no Lean or checks. Its PSS reads were unavailable, not
zero. Sampling gaps and partial PSS coverage are explicit in the evidence
index. The charged peak covers the whole build, including both gaps.

The 24-result runtime gate sampled RSS/PSS peaks of 2,401,058,816 /
2,332,703,744 bytes, cgroup peak 826,122,240 bytes, and minimum OS-available
RAM 17,088,086,016 bytes. RSS/PSS and cgroup charging differ for mapped shared
imports. The explicit example rebuild passed in 934.004 seconds, sampled
RSS/PSS 7,416,885,248 / 7,349,118,976 bytes, cgroup peak 5,758,799,872 bytes,
minimum OS-available RAM 12,138,770,432 bytes.

Passing commands: KeySort runtime gate; unchanged `DecisionKInt` build;
per-file MCP errors on core, integration, example and runner; explicit core
and example builds; original kernel recognition/verdict proofs; the full
runtime runner; `./run-lean.sh` (687 default jobs and 259 TestSuite jobs);
`check-orphans`, `check-layers`, `check-automatic --strict`, `check-trust.sh`;
and locked feature-inventory regeneration/check. Reproduce the runner with:

```sh
lake env lean -j1 --tstack=131072 --run tests/quant-ledger/Run.lean
```

Run builds inside the documented writer lock and hard 12 GiB / zero-swap group;
the exported task-local `bounded.py` / `bounded.sh` and temporary TOML retain
the exact commands, resource samples and stdout. Evidence lives in
`/workspace/quant-ledger-runtime/` and the exported evidence index.

All actual new headline axiom audits report only `propext`,
`Classical.choice`, `Quot.sound`: body exactness/verification, source reduction
verification, compact-position transport, closed truth, intrinsic replacement,
definition compilation, both original verdict theorems, generic-route control
and representation laws. Their output and enforced guards are retained.
No sorry, new axiom, heartbeat/fuel/node/test-budget increase or observation
waiver was introduced.

Interrupted probes are not passing gates. A combined APF-preparation probe
and a buffered combined probe were interrupted without a final result. New
scalar preparation omits unnecessary APF flooring. The generic global-layout
payment probe was interrupted at 638.209 seconds; compact layout alone also
had no verdict after more than ten minutes. The existing quantifier-free
payment control proved in 126.129 seconds; the certified arithmetic route then
proved the unchanged quantified payment control in 120.778 seconds. Formulae
and expected verdicts stayed unchanged. A stale-import MCP attempt was stopped
when its implicit setup build omitted explicit `-j1`; explicit bounded builds
then refreshed imports before passing per-file diagnostics. Early probe and
runner type/name errors were fixed, not bypassed with forced evaluation.

Independent read-only finder and skeptic reviews used no Lean server or
checks. They confirmed the shared-code layout, countermodel pullback, compact
closed-position transport and uniform closed-truth reasoning. Confirmed
findings fixed: stale APF/flooring docstrings and an inadequate positive-only
large-value control; refuted high/negative controls and nonclosed parameter
controls were added. Both whole-scope reviews found no remaining implementation,
fixture or evidence defect. The finder identified two integration docstrings
that omitted the new lane; those and the overview now document it. Their
cleanup changed only comments and passed the Decision MCP error check.
The full build preceded this documentation-only cleanup, as permitted by
`docs/contributing.md`; executable and proof code stayed identical. Exact
replacements and before/after hashes are retained in `doc-only-cleanup.json`.

Shared edits: narrow Decision imports/fallback/soundness/completeness and
covered-class extension; Solidity module registration; original KInt example
docstrings only; automation/module-map documentation. Core types, semantics,
program rules, target policy and generated inventory support statuses are
unchanged. No push, merge, rebase, other-VM change or prior-batch work was used.

## Final repository gate record

`./run-lean.sh` ran from 16:16:48 to 17:58:27 UTC on 2026-10-28,
6,099 seconds, exit 0. Its exact charged cgroup peak reached the configured
12 GiB cap (12,884,901,888 bytes); no cap was raised. The largest sampled
aggregate RSS was 12,287,762,432 bytes. The largest available partial PSS
sample was 8,359,971,840 bytes; this is not a full-run PSS peak. Minimum sampled
OS-wide available RAM was 6,535,692,288 bytes. Outer VM OOM and OOM-kill
counters remained zero. Charged peak includes reclaimable file cache; the
cap was reached, so this is not evidence for a smaller build budget.

That historical script invocation printed `SKIPPED` for its missing sibling
rules file. On resumption, the documented frozen snapshot was verified and
the sort checker was run separately with the exact `SOLKEY_RULES` filename;
it passed. These are distinct actual commands, not a claim that the original
invocation performed a check it skipped. No checkout was fabricated,
re-pinned or borrowed from another agent.

| Command / gate | Exit | Seconds | Charged peak bytes |
|---|---:|---:|---:|
| Original KeySort runtime gate | 0 | timing not retained | 25767936 |
| Final timed KeySort confirmation | 0 | 2.004 | 24272896 |
| Unchanged DecisionKInt baseline | 0 | 3310.7 | 10466168832 |
| Final 12-fixture / 24-pipeline runner | 0 | 266.978 | 826122240 |
| `./run-lean.sh` | 0 | 6099 | 12884901888 |
| `node scripts/check-orphans.mjs` | 0 | 1.001 | 63131648 |
| `node scripts/check-layers.mjs` | 0 | 2.001 | 63520768 |
| `node scripts/check-automatic.mjs --strict` | 0 | 2.003 | 18317312 |
| `bash scripts/check-trust.sh` | 0 | 7.029 | 165007360 |
| Final root MCP errors | 0 | 7.097 | 1105850368 |
| Final Decision documentation MCP errors | 0 | 47.378 | 1326387200 |
| Global documentation paths (current) | 1 | 5.013 | 8601600 |
| Global documentation paths (exact base archive) | 1 | 5.012 | 160931840 |

Orphans: 702 reachable, zero orphaned/not-allowed. Layers: 152 core modules,
zero reach the elaborator. Automatic: 491 automatic, 61 step-budget, zero
manual, 11 refuted, zero pending. Trust: 716 sources, 240 inventoried recovery
sites, zero findings. The generated feature inventory is current: 212 features,
151 modeled, 23 abstracted, 30 excluded, eight upstream, 783 symbols. The audit
regenerated it without changing generated files or support statuses.
Per-file MCP results for core, Decision, original KInt, new example, runner and
root all report success, no errors, no failed dependencies and no timeout.
Some sessions print a Python event-loop cleanup exception after that successful
result and exit 0; the raw output is retained. Short static commands may finish
before a process sample, so sampled RSS zero is not actual zero RAM.

All six original declarations/certificates and the protected policy suffix
passed the byte comparison in `pins-preserved.json`. The original gap proof,
build, strict automatic/trust/layer/orphan and assignment runtime gates pass.
Whole-tree documentation hygiene remains blocked by `scripts/check-doc-paths.sh`: both
the final staged tree and an exact disk archive/separate index of published
base exit 1 with identical 20 missing references and six ambiguity notices.
Nineteen missing references are in unchanged upstream-validation JSON; one
is the unchanged vendored `Eqns.lean` provenance citation. The checker and
all three implicated files are byte-identical to base. There are zero new
findings. `doc-path-nonregression.json` retains the exact comparison and hashes.
Both independent read-only reviewers confirmed the baseline comparison.
Their resumed review distinguishes the finished semantic assignment from
this unrelated whole-tree debt. This is not a passing global path gate.
Repairing the handling or resolution
of these pre-existing foreign references remains repository work; test-output
JSON and checker policy were not changed or weakened in this lane.

Other limits are partial process sampling,
and interrupted generic-payment performance probes already described above;
none is represented as a passing probe or broader decision completeness.

Exports are `/workspace/next10-quant-ledger.patch`,
`/workspace/next10-quant-ledger-handoff.md`,
`/workspace/next10-quant-ledger-evidence.json`,
`/workspace/next10-quant-ledger-evidence.tar.gz`, and
`/workspace/next10-quant-ledger.sha256`. The evidence index records the final
commit and every log's hash, command, exit, timing, resource samples and actual
axiom output. The patch is cumulative from the published base.

## Saved-VM completion follow-up

The retained branch and clean checkpoint HEAD were verified as
`codex/next10-quant-ledger` / `8b61b160fe5413ffb94ddeface6bf62f891cbf4b`.
Bash, Lean 4.24.0 and Lake 5.0.0-src+797c613 were verified before restoring
only the task-owned temporary single-thread configuration. The setup script
was inspected and preserved; its four-thread default was not used. The same
executor and branch were reused, with no new VM, clone or implementation
thread. The original checkpoint exports are preserved under
`/workspace/quant-ledger-runtime/checkpoint-8b61b160/`.

The migration conventions require the immutable snapshot, not a sibling
checkout. `node scripts/solkey-migration.mjs verify tests/migration/solkey`
verified commit `473da8944ca7329e6b76819863591407db26e7ec` and manifest/file
hashes. The actual sort command was:

```sh
SOLKEY_RULES=/workspace/solidity-lean/tests/migration/solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key \
  ./scripts/check-solkey.sh
```

This ran through the existing bounded wrapper and temporary Lake configuration
with `LEAN_NUM_THREADS=1` and Lean `-j1`. It reported 377 parsed taclets,
131 read-bearing entries, table coverage 131, and `OK`, exit 0. This establishes
sort-annotation matching against that frozen file; it does not claim live
upstream parity, a re-pin, or new compiler/EVM conformance.

An independent Python enumeration read published-base blobs with `git show`
and compared current tracked files using the checker's resolution rules.
It reproduced all 20 missing references and six ambiguity notices with zero
new findings. All concern unchanged files outside this task. The single
vendored citation explicitly identifies external Mathlib provenance that is
not imported; the other 19 missing references occur inside archived validation
JSON. No moved/renamed module or stale task-local Lean reference was found.
Task-document Markdown links also resolved. An initial evidence-only Markdown
scanner mistook `new T[](n)` inside code for a link; code spans were excluded
and the corrected audit passed. The repository checker was not altered.
`resume-doc-applicability.json` records classifications, checked task references
and local links. This scoped nonregression evidence does not override the
red whole-tree gate or rewrite archived observations/provenance.

The fresh runner passed all 12 fixtures and 24 pipeline results. Every verdict
and full ordered observation is byte-identical to the retained passing runner,
recorded in `resume-observations-unchanged.json`. Sixteen freshly printed axiom
audits, including exactness, verification, closed transport/truth, both public
soundness/refutation theorems and the original exact verdicts, use only
`propext`, `Classical.choice`, `Quot.sound`. The strict static/trust and inventory
checks were rerun successfully. No Lean, fixture, policy or expected-output
source changed after `8b61b160`; this follow-up changes only this handoff.
The retained full 687-job default build and 259-job TestSuite build remain
applicable; the separately completed frozen sort check closes their historical
skip. No new full-build invocation or kernel/EVM coverage is invented.

| Resumed command / gate | Exit | Seconds | Charged peak bytes |
|---|---:|---:|---:|
| Snapshot verification | 0 | 1.001 | 18378752 |
| Exact frozen sort check | 0 | 2.012 | 378908672 |
| 12 fixtures / 24 pipelines | 0 | 255.968 | 1104642048 |
| 16 actual axiom audits | 0 | 14.433 | 176750592 |
| Independent documentation applicability | 0 | 6.015 | 58712064 |
| Orphans | 0 | 2.002 | 62955520 |
| Layers | 0 | 2.001 | 77078528 |
| Automatic --strict | 0 | 2.002 | 20811776 |
| Trust | 0 | 7.033 | 169213952 |
| Generated inventory check | 0 | 2.001 | 10379264 |

The resumed runner sampled aggregate RSS/PSS peaks of 2,401,177,600 /
2,330,470,400 bytes. Its exact cgroup peak was 1,104,642,048 bytes. During it,
the outer 16 GiB VM cgroup charged 8,305,975,296 bytes, with OOM counters zero;
this is a measured instant, not a full-run VM peak. OS-wide available memory
and estimated inactive-file reclaimability are separately labeled in
`resume-vm-headroom.json`. All heavy checks remained serialized inside the
verified 12 GiB / zero-swap build cap, with caches on disk.

Read-only finder and skeptic reviews confirmed the resumed frozen sort result,
no stale task-local links, and this semantic-completion/historical-debt
boundary. They used no Lean server or checks. There is no remaining blocker
to the named `gapQuantLedger` assignment. Whole-tree documentation hygiene
continues to fail at baseline and is not reported green.

## Combined integration proof repair (2026-10-29)

The retained attempt-4 combined build failed in
`DecisionKInt.twoAnchorNegative_refuted`: its old `change` step assumed
`decideLeaf` reduced directly to `decideKEnc`. The added final ledger fallback
wraps that result in a match. The proof now unfolds `decideLeaf`, rewrites with
the existing KEnc refutation hypothesis, and closes by reflexivity. The exact
theorem signature and shared typed countermodel across KEnc, Leaf and Goal
remain unchanged; dispatch, target predicates and proof budgets are unchanged.

Per-file Lean MCP diagnostics for `Solidity/Examples/DecisionKInt.lean` completed
with no errors or warnings. Its existing axiom report for the repaired theorem
contains only `propext`, `Classical.choice`, and `Quot.sound`. No full build was
run for this repair; the coordinator must rerun the combined validation gates.

Read-only finder review checked the failed-log location against the current
dispatcher and focused diff, finding no other content conflict in the repaired
file. Read-only skeptic review checked that the rewrite returns the same
refuted state, retains the unknown-only ledger fallback, and introduces no
axiom, weakened claim or gate change. These reviews used no Lean server.
