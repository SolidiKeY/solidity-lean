# Current-master upstream baseline

The [attribution follow-up](attribution/README.md) assesses each of the original
84 unresolved feature IDs. It records 59 source/documented boundaries and 25 exact
missing-evidence questions; ten rows have direct fresh fixture/variant links.
The original gap index and unresolved list below remain historical evidence.

Source base: `f4dee4a29c2e208b36db4a4161a4723c735cd775`, freshly fetched origin/master.
Branch: `baseline/current-master-20261028`. All collected cloud groups 01–10 are
ancestors. Active unmerged work is excluded; no Lean semantic source changed.

| Stage | Working | Broken | Blocked |
|---|---:|---:|---:|
| Typed Lean runtime | 657 | 196 | 809 |
| Pinned-solc diagnostics | 3478 | 0 | 64 |
| Multi-source importer adapter | 0 | 0 | 39 |
| Other native/upstream harnesses | 0 | 0 | 4417 |
| Total | 4135 | 196 | 5329 |

The immutable bulk counts are 4121 / 190 / 5349. One isolated replay of each
of 22 uncheckpointed follower candidates yields 14 working, seven broken and one
blocked. Six previously blocked fixtures become broken; one fixture was already
broken through its other mode. The first uncheckpointed fixture in each
interrupted batch is not retried, and its unfinished modes retain blocked
verdicts; it is not assumed to be the proven cause. No timeout, loop fuel,
expectation, premise or required mode was relaxed. Observation-prefix and
complete-mode guards passed for all 22 reports before merging a separate copy.

The snapshot preserves all 11,622 files; the selected fixture ledger has 9,660
rows. `complete` means each selected file has a verdict, including blocked.
Compiler diagnostics are not Lean coverage. Runtime observations are not a
universal semantics, compiler, EVM/SSA or extraction-completeness proof. No
new theorem was added, so new-theorem axiom checks do not apply; the existing
trust-inventory gate passes with zero findings. Assembly, delegatecall, gas,
physical layout and environment/log profile decisions remain unchanged.

## Reproduce

Use the attached published environment and activate `/workspace/.setup/activate.sh`.
The external compiler is SHA-checked 0.8.38; its download command remains in
[the runner guide](../../../docs/solidity-upstream-tests.md). Pre-pull the pinned
Ubuntu image digest in `scripts/run-solidity-baseline.sh` using the managed daemon.
From the repository root, choose fresh output directories:

```sh
bash scripts/run-solidity-baseline.sh corpus \
 /workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js \
 /workspace/solidity-lean/.lake/upstream/new-baseline \
 f4dee4a29c2e208b36db4a4161a4723c735cd775
python3 scripts/solidity-baseline-retries.py select \
 .lake/upstream/new-baseline/results --fresh-run --out .lake/upstream/selection.json
bash scripts/run-solidity-baseline.sh retries \
 /workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js \
 /workspace/solidity-lean/.lake/upstream/new-isolated \
 f4dee4a29c2e208b36db4a4161a4723c735cd775 .lake/upstream/selection.json
```

Copy the bulk results before invoking the existing retry merger, using only
`runs.json` entries with `mergeEligible: true`. `merge.json` records the exact
actual merge command. Never select followers from a resumed run: its actual
job queue differs. All isolated commands/pipelines/results are retained.

`portable-evidence.tar.gz` preserves the immutable bulk, combined and isolated
reports plus prepared importer AST inputs and their final batch/checkpoint.
Extract from the repository root with `tar -xzf` before browsing those ignored
raw directories. `prepared-inputs.json` records each prepared input's SHA256,
original fixture SHA256 and source-mode identity; original fixture/expectation
bytes remain in the unchanged pinned snapshot archive. The final batch wrapper
is not an archive of every transient batch wrapper.

`summary.json` and the three verdict `.txt` lists are readable exports. The
`gaps/` index retains exact variant gap objects, conservative many-to-many work
queues and the historical/current status changes. At the original checkpoint it reviewed boundaries for
76 of 160 partial features and left 84 requiring feature-specific review. The
follow-up assesses all 84; it does not claim semantic completeness for the
25 rows whose precise evidence questions remain open.
No manifest status/schema changed. Keyword routing is triage, not attribution
or proof. An empty runtime queue says nothing about proof-interface completeness.

## Measurements and reviews

The actual Lean version is 4.24.0 (797c613eb9b6d4ec95db23e3e00af9ac6657f24b);
Lake is 5.0.0-src+797c613. The KeySort smoke build passed. Dependency rebuilding
passed 77 jobs in 481.53 s, cgroup peak 1060544512 bytes. Bulk replay took
2285.72 s and hit its hard 12 GiB cap: unfinished modes remain blocked.
Isolated replays took 159.12 s, cgroup peak 729632768 bytes, no OOM events.
Max-child RSS and cgroup peak are distinct measurements; file/shared-page
accounting means they need not agree. The bulk timer's peak is cumulative
within its container (dependency build plus replay).

The cold command hit its initial 90-minute bound: **exit 124, 5400.005 s**,
546/685 default targets completed, with `Examples/Tactics/FunctionTypes.lean`
active at the last five-second sample. Kernel cgroup peak was **8195923968
bytes (7.633 GiB)**; zero OOM events. This is **blocked**, not a passing build.
SolkeyTestSuite and the final frozen-sort execution were not reached. Warm
timing was not run: no successful-cold fingerprint exists. The original cache
was restored and partial cold artifacts remain in `.lake/baseline-cold/build`.
See performance.json and build-evidence.tar.gz. Raw timeout rusage accounts
only for reaped children; its CPU/max-RSS numbers do not represent the whole
build. The kernel cgroup peak is authoritative; tail RSS values are samples.

A cold project-artifact cache disables Lake
artifact restoration, retains the original cache, enforces 12 GiB/no swap,
uses `LEAN_NUM_THREADS=1` and explicit `-j1`, and has an initial 90-minute wall
bound. A warm run requires a successful cold marker with matching base/model/
configuration. This is not an OS-page-cache or toolchain-install benchmark.

Read-only finder and skeptic reviews used no Lean server. Confirmed fixes
cover exact model-path ordering, whole-suite/provenance/zero-count checks,
blocked pipeline guards, conservative retry selection, observation retention,
default build-path preservation, successful-cold provenance, precise isolated
versus aggregate counts, and safe container
cleanup before cache restoration. Static gates and final evidence review are
recorded in validation manifests; the pre-existing documentation-path gate
has 20 missing references and is not counted as passing.

Shared tracked edits: docs/coverage-plan.md and docs/solidity-upstream-tests.md.
No shared frontend or Lean source edit, push, merge, re-pin or external message.

The actual retry selector source is preserved at invocations/retries/selector.py;
its hash matches the source used by retry-selection.json. Current tooling only
clarifies its policy prose: unfinished modes remain blocked, while an overall
fixture can already be broken through a conclusive companion mode.

Path-gate diagnostic logs are losslessly gzip-compressed to avoid recursively
scanning copied missing-path citations. The first new scan repeated 13 old
targets; no historical diagnostic was removed. This gate remains failing.

Final report refinement adds eleven feature associations from exact fresh
fixture diagnostics and source review (76 reviewed, 84 unresolved). Examples
include calldata return/copy boundaries, nested uint24 metadata, fixed-byte
copy widths, explicit calldata byte/string casts, logical-base literals and
contract-qualified function-valued state access. Qualified revert calls are
distinguished from selector projection. No inheritance or do/while gap was
inferred from misleading fixture names. Each observed association carries
its exact original gap objects in gaps/gaps.json.

validation.json/reviews.json preserve the baseline checkpoint;
final-validation.json/final-review.json record the final scope and blocked
performance gate. The raw baseline archive remains unchanged.

For an independent measurement with no existing private cold directory:

```sh
bash scripts/run-solidity-baseline.sh cold \
 /workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js \
 /workspace/solidity-lean/.lake/upstream/cold-results \
 f4dee4a29c2e208b36db4a4161a4723c735cd775
# Only after successful cold completion:
bash scripts/run-solidity-baseline.sh warm \
 /workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js \
 /workspace/solidity-lean/.lake/upstream/warm-results \
 f4dee4a29c2e208b36db4a4161a4723c735cd775
```

This VM retains the incomplete private cold directory. The script refuses to
overwrite it; preserve it under the writer lock before any independently
requested fresh measurement. Do not interpret its artifacts as a completed
warm baseline. No second cold attempt was made here.

## Attribution follow-up validation

This resumes the same VM and branch at `66629757`, without a Lean build.
See [the reviewed input table](attribution/reviewed.tsv),
[full source/variant evidence](attribution/index.json), and
[exact validation commands and resource measurements](attribution/validation.json).
Every original partial ID is accounted for: the inherited 76 associations plus
84 individually assessed rows. A documented limit is distinct from a new
runtime counterexample, and missing correspondence evidence is a diagnostic
question rather than proof that a feature is absent. No manifest status or
schema changed; generated inventories need no rewrite.

Independent read-only reviews corrected two false gap candidates: storage-pointer
delete is compiler-invalid, and retained external/self-frame modular-zero guards
already emit Panic 0x12. The follow-up also excludes dynamic bytesN array-copy
failures from fixedArrays, enum conversion from typeBounds, runtime ERC7201
overflow from numericLiterals, and for-loop conditions from doWhileStatement.
The original keyword queues remain unchanged. No D1/D2 or excluded machine
semantics decisions are made. No theorem/axiom audit is newly applicable.
The cold stop remains exit 124 at 546/685, peak 8,195,923,968 bytes; warm timing
remains unrun. All existing inputs, observations, expectations and required
pipelines are untouched.

## Bounded executable attribution discriminators

The [40-question matrix](probes/README.md) pairs the exact25 evidence-needed
IDs and15 documentary questions with pinned0.8.38 inputs, both pipelines,
compiler/provenance/source-reader results and current declaration limits.
Three feature rows share two observed source-reader refusal shapes: pushed-member
postfix increment and a UDVT struct field. These are separate probe inputs, not
new corpus verdicts. Original66629757/13edcbe4 evidence is retained.

Native typed import, production specification parsing, proof listing and replay
remain blocked: one narrow API refresh stopped at900seconds, exit124, peak
2,342,395,904bytes, zeroOOM events. The cached lightweight source reader runs;
its emitted text is not a typed admission or execution claim. All failed first
wrappers, compiler-invalid candidates, valid companions, full emitted/dropped
metadata, commands and logs remain in the new hash-checked probe archive.
The original cold stop and unrun warm measurement are unchanged.

## Native diagnostic follow-up

The [native cache/evidence index](native-cache/README.md) supersedes the earlier
blanket native-harness blocker: existing production Import/Upstream artifacts
were valid, while Testing's broader proof closure was stale. No project build
or configuration change was needed. Both pipelines now have actual typed-import,
bounded replay and positive/negative/refusal observations. These are not new
corpus verdicts, kernel postcondition proofs or generated EVM observations.

Historical document hashes belong to their recorded checkpoints. Later appended
clarifications do not rewrite those reports; historical generator reproduction
must use the corresponding checkpoint. The new native index and archive carry
current diagnostics. Nonzero-payment entry discrimination remains unavailable
in the unchanged replay input; nativeValidationComplete stays false for that
precise reason. Testing proof listing/search remains a separate stale prerequisite.
