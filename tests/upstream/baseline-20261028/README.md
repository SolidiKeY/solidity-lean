# Current-master upstream baseline

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
queues and the historical/current status changes. It reviews boundaries for
65 of 160 partial features; 95 still require exact feature-specific gap review.
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

Cold/warm measurement is pending. A cold project-artifact cache disables Lake
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
