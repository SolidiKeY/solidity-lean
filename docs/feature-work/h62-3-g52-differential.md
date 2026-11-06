# H62 item 3: G52 differential pipeline

**Partial checkpoint; original persistent goal remains unfinished.** No release,
merge, pre-gate, push, deployment or whole-G52 completion is claimed.

## Identity and ownership

- Batch `solidity-h62-3-20261106`, task `g52-differential`.
- VM checkout `/workspace/solidity-lean`; branch
  `codex/solidity-h62-3-20261106/g52-differential`.
- Exact base `c6f550e281a7e5affa9a99bc2cdaed556dec00e4` was fetched from origin,
  confirmed an ancestor of published origin/master, and branched under the
  repository writer lock. The older clean `work` branch was preserved.
- Original rendered-prompt identity:
  `cfb57e23877434d2124fa671a4edff190a9a6e6f2b6b473cef22b2d220d8965b`.
- Only the two assigned new script/test directories and this document changed.
  V17 keeps every existing validation/release file. H55 owns G49/G50; this lane
  does not implement or alter that producer. No original Lean declaration,
  frozen statement, premise, exclusion, observation or proof budget changed.
  New Lean declarations/helpers: zero; new axioms/sorry/trust shortcuts: zero.
- Coordinator inputs at `/workspace/h62-coordinator-inputs` passed all five
  provided SHA256 checks. `ownership.json` confirms this additive scope and
  records G52's V17 incumbent and HOST1 relay dependency.

## Checkpoint status and exact counts

| Queue item | State | Evidence and remaining work |
|---|---|---|
| 1: deterministic contracts and pinned Osaka fixtures | Partial | 48 sources, 366 unique source/input pairs across 8 seeds and 6 families; pinned EEST v5.3.0 develop archive, 19,093 Osaka post-state variants with original fixture path, case and indexes. Fixture execution remains open. |
| 2: native solc 0.8.38, both pipelines | Done for acquired generated corpora | Official native binary SHA/version verified; 48 sources × 2 modes plus 160 real-producer sources × 2 modes; optimizer enabled, runs 200, target osaka explicitly set. No soljson/npm compiler used. |
| 3: real semantics versus independent EVM | Partial | 320 real primitive-fragment observations match. Separately 732 observations have reference execution only and are **unsupported**, with zero differential matches. All 19,093 EEST rows are pending execution. |
| 4: minimize, classify and relay | Partial | Finite boundary-pool minimization preserves family, pipeline and differing-field signature. The 320 real comparisons produced zero mismatches, so no root-cause ticket was fabricated. General minimization, owner classification and relay remain required when broader execution produces mismatches. |

The 366-input corpus covers checked/unchecked addition, division, storage/event
writes, write-and-event-before-custom-revert rollback, and branching. Reference
execution produced 564 returns, 168 reverts, 122 retained logs and zero failed
rollback invariants. Both pipelines execute every case. Its missing semantics
adapter produces 732 unsupported outcomes, never successful comparisons.

The separate real-semantics corpus comes from the unchanged
`Solidity.Tools.SolCases.emit` / `Prog.run ... withPanics` producer. It accounts
for all ten original families and all 160 original seed-0 cases without padding.
Both native solc modes execute the emitted source on `@ethereumjs/vm@10.1.3`.
Comparison includes exact return/revert bytes, complete contract storage trie
(hashed slot keys, canonical RLP values, absent zero slots), logs and failed-call
rollback. This admitted source printer has no event constructs, so empty logs
are a property of this fragment, not general event support. The source model is
gas-free: reference message gas is retained and **not** represented as source
gas agreement. Execution starts from installed runtime bytecode and encoded
initial storage; deployment/world behavior is untested. These limits stay
explicit in `typed-differential.json`; `full_g52_complete` is always false.

## Pins and H44 storage

Bulk inputs/results and private build products stay at
`/workspace/h44/g52-differential`; the independent replay is at
`/workspace/h44/g52-reproduction`. Only generators, runners, controls, dependency
integrity lock and the SHA256 manifest are committed.

| Input | Pin |
|---|---|
| solc-bin source | `62f89f31914359ec2e153f1bc0614a1bdf2c8e17` |
| Official linux-amd64 list SHA256 | `b44c1d0e598ed0bcbf4ee49c86c5ae85b63718c1591689b02d12d7a11d45a2ac` |
| Native solc SHA256 | `65c3180a336eabb6bdc4bbd49cc405aeb233976964ae6c11fba2a6c8be8f3243` |
| Exact version | `0.8.38+commit.1835d247.Linux.g++` |
| EEST release / embedded source commit | `v5.3.0` / `6824474c2ae99e6a67be6093e9a1edc1c82091ea` |
| Osaka-filled develop archive SHA256 | `5dd08fee0fb41bc2a59bc4ab1dc75b19723fc71fe6af2f855454d3283fba09b9` |
| Reference EVM | `@ethereumjs/vm@10.1.3`, full npm integrity lock under assigned tests directory |

The upstream archive uses fork selection (`post.Osaka`), rather than a literal
`for_osaka` directory. The census preserves every Osaka post-state variant.
Other fork rows and blockchain/engine formats are outside this **state-test
census**, and must be accounted for before claiming whole upstream-suite coverage.
The exploratory stable archive is retained as historical evidence: its metadata
uses `--until=Prague`, so it is never used as Osaka conformance evidence.
The develop archive's pinned hash and embedded source commit/ref are checked
before accepting any fixture row. No archive paths are extracted to disk.

## Reproduce

Run from the checkout. Set BULK to an absolute directory outside the repository.
The bootstrap verifies the official native compiler bytes against the pinned
upstream list and downloads the hash-pinned fixture archive; npm supplies only
the optional independent EVM, never solc.

```sh
BULK=/workspace/h44/g52-differential
python3 scripts/h62/item3/g52-differential/bootstrap.py --bulk "$BULK"
python3 scripts/h62/item3/g52-differential/pipeline.py generate --bulk "$BULK"
python3 scripts/h62/item3/g52-differential/pipeline.py compile --bulk "$BULK"
node scripts/h62/item3/g52-differential/reference.mjs "$BULK"
python3 scripts/h62/item3/g52-differential/pipeline.py census --bulk "$BULK"
python3 scripts/h62/item3/g52-differential/pipeline.py compare --bulk "$BULK"
python3 tests/h62/item3/g52-differential/test_pipeline.py
```

For the real producer, select the original repository's Lean 4.24.0 toolchain
and acquire the writer lock. This is not a migration lane: the coordinator's
v4.35.0 migration pin is preserved without cutting over this branch or reusing
a migration cache. The original official 4.24.0 release archive is retained off
Git (observed SHA256 `b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec`).

```sh
flock /tmp/solidity-lean-feature-groups-20261025/writer.lock \
  python3 scripts/h62/item3/g52-differential/serial_semantics.py \
  --repo /workspace/solidity-lean --bulk "$BULK" \
  --lean-bin /workspace/h44/g52-differential/toolchain/lean-4.24.0-linux/bin
node scripts/h62/item3/g52-differential/typed.mjs "$BULK"
python3 scripts/h62/item3/g52-differential/pipeline.py manifest --bulk "$BULK"
```

The serial runner builds only the existing producer's 29-module import closure
from current source in a fresh private directory, one Lean process at a time,
`LEAN_NUM_THREADS=1`, explicit `-j1`, `--tstack=131072`, 12 GiB address-space cap,
aggregate RSS guard, 4 GiB available reserve, swap prerequisite zero and bounded
per-process timeout. It uses no Lean server or systemd-run and writes no shared
build cache. No proof option is raised. Version/source/artifact receipts are
retained. The typed runner refuses an incomplete producer build or changed
producer source hashes.

## Actual gates and reviews

- Lean: `4.24.0`, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
  Lake: `5.0.0-src+797c613` (Lean 4.24.0).
- Bounded fresh KeySort: exit 0, 1.506 s, 402,141,184 sampled RSS bytes;
  successful output is empty. Actual command/output receipt:
  `evidence/serial-build.log` and `evidence/lean/results.json`.
- All 29 existing producer modules and real `--run SolCases.lean 0` passed:
  92.835 s total, peak sampled RSS 1,279,344,640 bytes, no resource stop.
  This is the affected producer closure, not a default/full/release build.
- Ten accounting controls pass, including malformed data, failed rollback,
  per-field negative controls, wrong fork, incompatible gas metrics,
  duplicate inputs, empty manifests, archive tampering and stale result input.
  `evidence/gates.json` retains commands, exits and decisive output.
- 96 generated native compilations pass; reference executes 732 observations.
  The fail-closed comparator reports `unsupported=732`, `complete=false`.
- 320 real primitive native compilations/EVM executions match the real source
  producer; gas remains unsupported, and full-G52 completion stays false.
- A second clean bootstrap completed in the reproduction directory. All 241
  generated/compiled files and compiler/reference/comparison receipts are byte
  identical. A second bounded real-producer run emitted identical JSONL bytes.
  `evidence/reproducibility.json` contains exact counts/hashes/commands.
- Finder and skeptic each independently reviewed read-only without Lean/server,
  found provenance/empty-case/duplicate-input/schema/rollback/manifest issues,
  and verified fixes. Both independently verified all 249 reproduction-manifest
  hashes; finder also verified all 29 producer-source hashes. Both cleared only
  this partial checkpoint. `evidence/reviews.json` records findings and closure.
- No checking-speed refactor occurred, so a before/after Lean checking regression
  delta is not applicable. Raw bounded timings remain available. The required
  >10% regression stop remains binding for any future refactor.
- No `RUNTIME_GATE_PASS`, full `./run-lean.sh`, G54/G55, full theorem, fixture
  conformance, deployment or general source/compiler correctness claim follows.

An exploratory comparison failed while validating the initially unprefixed
storage-trie schema; it was corrected to the actual canonical `0x` encodings
and rerun successfully. An attempted control run in the read-only shell could
not create temporary files; the authorized writable run passes. These setup
failures are not counted as passing observations.

## Original goal handoff and remaining queue

This is the required fresh-thread handoff after three completed bounded work
items: pinned generation/compiler acquisition, reference plus real-fragment
execution, and independently reviewed accounting/reproduction. It does **not**
complete the four-checkpoint assignment or authorize a replacement goal.
Resume this same VM, branch and original persistent goal. `get_goal` is not
exposed; coordinator explicitly says that absence is not a blocker. No second
goal, timer or competing continuation was created. The final saved report gives
the full committed head and artifact checksums.

Next work, still within the exact assigned scope:

1. Implement and validate the pinned EEST state-test execution adapter against
   the reference EVM, preserving all 19,093 variants and fork/transaction/gas
   observations. Run negative controls; never turn unsupported formats into
   passes. Expand the archive census to account for other formats explicitly.
2. Coordinate V17/VT1/VY5 on the full executable source/runtime producer and
   exact retained observations. The registry names HOST1 `979c7444` as ready
   once relayed; that object and `relay.sh` are unavailable on this VM.
   `docs/feature-work/roadmap-g03-ledger.md` records G52 -> G49.02. H55 owns
   G49/G50. Do not duplicate that producer, edit its files, adopt stale profiles,
   or replace real semantics with a Python/JS arithmetic oracle.
3. Connect the 366-input corpus to that actual executable producer, then connect
   all admitted Osaka fixtures. Preserve explicit unsupported counts for every
   missing observation and model/fork limit. Full gas/deployment/world claims
   remain open; primitive matches are not substitutes.
4. Exercise minimization on actual broader mismatches, isolate one confirmed
   root cause per ticket and send through coordinator relay to the owning lane
   with source/bytecode/input hashes, exact seeds and minimized reproducer.
   No mismatch ticket is currently owed by the 320 matching primitive cases.
5. Complete original final affected/full acceptance gates, independent reviews,
   before/after timings when applicable, committed checkpoint handoffs, H44
   manifests and patch exports. Keep the persistent goal unfinished until all
   four checkpoints and assigned backfill are actually complete.

Typed dependent-item blockers (not blanket permission to stop useful work):
`B-PRODUCER-G49.02` (full composed runtime producer, H55/V17-owned),
`B-RELAY-V17` (incumbent coordination/relay transport absent locally), and
`B-SOURCE-GAS` (existing primitive source model has no gas observation).
Independent EEST/reference and accounting backfill can continue while these
are resolved. No scope exclusion or premise change is requested or approved.
