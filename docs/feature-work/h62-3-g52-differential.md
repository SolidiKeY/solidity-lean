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


## EEST reference milestone and authorized master update

The coordinator explicitly instructed merging origin/master before the next
commit. The lane backed up its uncommitted work under H44, verified that the
published master contains d448d0f7658bec8e4a41e0d35b00dea98154c580, and fast-forwarded
to 5f14596531efea2be64f1a5e7a83afa5e151e865. Existing lane work was preserved.
The original base/goal and branch remain unchanged in identity. This explicit
merge authorization does not authorize pushing, publishing, or another merge.
H82 now replaces exact-file agreement for statement-preserving work; no such
agreement request is pending here. Frozen statements/interfaces/budgets and
axioms remain unchanged. All29 previously checked producer sources retain their
original recorded hashes after this integration.

New reference evidence supersedes the earlier pending-only EEST census:
all19,093 unique Osaka state-test variants were selected;18,315 match the pinned
fixture state-root and logs-hash expectations;778 expected-invalid transactions
remain unsupported by the rejection adapter. There are zero reference mismatches
or engine errors in the corrected bounded run. These results are **not source
semantics differential matches**: all19,093 source adapters remain unsupported,
reference_complete=false and differential_complete=false. Strict exit2 means
incomplete conformance, never a gate pass. Return/revert bytes and gas are retained
as observations; the fixtures provide no direct expectations for those fields.

The deterministic gzip stream retains every original fixture identity, post-state
variant/index, pre-state, environment, transaction bytes and expected post-state.
Its SHA256 is d7dcc3b6f969359d44bfdaec88b7dffcbd80cddacc2b06b8a135964e2cbbc602.
Export verifies the archive and census/fixture bytes; the runner verifies the
stream/census binding and every selected identity. It runs a fresh VM and full
signed transaction for each fixture, checks all fork blob parameters, and compares
complete state-root and log-hash commitments. The archive's absent block history
uses the explicitly recorded zero-hash state-test convention.

Real cryptography is pinned: micro-eth-signer0.20.1 and
@paulmillr/trusted-setups0.3.0, full npm integrity lock and127 installed public-file
hashes at evidence/kzg-pin.json. No stub is used. All cryptographic package loads
are serial to avoid an observed Node CJS/ESM loader race.

The engine's optional step tracer caused huge-memory REVERT allocation errors
before gas validation; the isolated index6551 stack trace is retained at
 evidence/eest-reference-memory-reproducer.jsonl. The production adapter instead
counts calls to the unchanged original Interpreter.runStep with a transparent
Reflect.apply forwarding wrapper. The five-million-instruction bound is preserved;
no opcode implementation or installed engine file is edited. Index6551 now matches
its fixture. This is a reference-observer root cause, not a Solidity theorem or
compiler mismatch; no source-semantics mismatch ticket is fabricated.

Each case runs serially in an owned worker with a60-second limit,4GiB V8 old-space
limit,12GiB aggregate RSS guard,4GiB available-memory reserve and zero-swap
prerequisite. Worker replacement waits for termination. The full bounded replay
required352.501seconds and peaked at1,059,794,944 sampled aggregate RSS bytes.
No resource stop occurred. No checking-speed refactor or Lean budget changed, so
checking regression delta remains inapplicable. No speedup is claimed from the
interrupted exploratory run.

Reproduce after bootstrap/census:

```sh
python3 scripts/h62/item3/g52-differential/eest_export.py --bulk "$BULK"
node --test tests/h62/item3/g52-differential/eest_observation.test.mjs
node scripts/h62/item3/g52-differential/eest_reference.mjs "$BULK" 19093 bounded
```

Optional arguments select LIMIT,LABEL,INDEX. Partial/rejected cases return exit2;
engine errors/mismatches return1. Read the summary boolean and exact counts, not
just process success. The complete-run evidence is
 evidence/eest-reference-bounded-summary.json and its JSONL; provenance and
regression gates are in evidence/eest-acceptance.json. Historical failed KZG and
loader runs remain saved as failures; they are never added to successful counts.

Independent finder and skeptic reviewed read-only without Lean/server. Both
verified exact fixture accounting, unchanged executor forwarding, and explicit
unsupported semantics. Finder found a queued IPC-success/resource-stop race;
it is fixed by guardedResult and a negative control. Three Node control tests pass,
including changed roots/logs, altered fork parameters, and stop-over-success.
The full-run adapter hash records the actual pre-race-fix source; no resource stop
occurred in that run. A final20-case pilot verifies the unchanged normal path;
the targeted race control verifies the changed stop path. Earlier ten accounting
controls,732 generated reference observations,320 real primitive comparisons and
fail-closed unsupported accounting were rerun successfully with the new lock.

Continue the existing goal. Next independent items: implement expected-invalid
transaction rejection classification for all778 cases, reproduce the deterministic
export, expand archive-format census, and inspect newly integrated
scripts/roadmap-v17-differential.py for the live producer adapter. Dependent waits
must be reported as {lane,item} per H82; they never justify stopping independent
backfill. Full source/runtime integration, applicable gas/world/deployment evidence,
actual mismatch minimization/owner relay, and final original gates stay open.

Finder's final lifecycle review also required ignoring queued messages after a
stop request until onExit resets the worker; this is implemented and cleared.
The final20-case pilot reports20reference matches and strict incomplete exit2.
No independent work is blocked by these completed fixes. The pre-merge source
backup retains the actual full-run adapter before the targeted IPC-stop fixes.


## Expected-invalid transaction classification and H70 binding answer

This checkpoint executes and classifies all778 formerly unsupported invalid
transactions. The observed rejection category is derived from pinned engine
validation diagnostics, actual transaction type, and engine-computed intrinsic
and calldata-floor gas. Expected labels are consulted only afterward. Unknown
host errors remain unsupported; an accepted expected-invalid transaction is a
reference mismatch. Classification requires unchanged pre/post state roots,
the exact fixture post-state root, and the expected empty-log commitment.
Validation rejections do not provide captured execution logs; the empty-log
commitment is inferred from the recognized pre-execution validation refusal.

All778 cases match. They cover19 observed categories and22 expectation/alternative
forms. In91 cases both intrinsic and calldata-floor constraints fail; both facts
are retained and only explicit expected alternatives can match. No skip or
arbitrary exception is counted as a match. New control module docstrings name
the guarded regression as required by H90; no new phase/roadmap folders exist.
Nine pure controls and one real-worker accepted-invalid contradiction control
pass without skips. Wrong expected roots, overlapping gas failures, unknown host
errors, and incompatible rejection categories are covered.

The complete serial replay now has19093unique reference matches:18315valid cases
and778observed rejections, zero unknown rejections, errors, or mismatches.
It took351.765seconds with sampled aggregate RSS peak
1191260160bytes. The earlier replay took352.501seconds but
skipped778transactions; these are different workloads, so no checking-speed
improvement is claimed. No Lean representation/refactor/budget changed; the
checking-regression comparison remains inapplicable. Resource and instruction
limits remain unchanged.

The full reference command exits0 and reference_complete=true **only for pinned
state-root/log commitments and expected transaction admission/refusal**. All19093
source semantics adapters remain unsupported; differential_complete=false.
Return/revert and gas data lack direct expected values in these fixtures. This
is neither source/compiler agreement nor RUNTIME_GATE_PASS/full-G52 closure.
The invalid-only778case command still exits2 because it leaves18315unselected.
Evidence: evidence/eest-reference-rejection-complete-summary.json, its JSONL,
rejection-acceptance.json, rejection-controls.log, rejection-integration-control.log,
and rejection-reviews.json. Both independent reviewers verified the complete
result SHA256 e4d572dd0dec3f202dc62256a92174919fd85438320e6c2fa90de37a39305a55,
all rejection invariants, and explicit source incompleteness; neither used Lean
or a server. This checkpoint creates no Lean declarations, axioms, sorry,
frozen statement changes, exclusions, or proof-budget changes.

Reproduce the rejection subset and controls:

```sh
node scripts/h62/item3/g52-differential/eest_reference.mjs "$BULK" 778 rejected-classified all invalid-only
node --test tests/h62/item3/g52-differential/eest_rejection.test.mjs tests/h62/item3/g52-differential/eest_observation.test.mjs
G52_BULK="$BULK" node --test tests/h62/item3/g52-differential/eest_rejection_integration.test.mjs
node scripts/h62/item3/g52-differential/eest_reference.mjs "$BULK" 19093 rejection-complete
```

H70 owner answer: V17 at e13a151f8f5252a038ff051dde797cc00e173f87 confirms
scripts/roadmap-v17-differential.py, scripts/roadmap-v17-runtime.mjs and
scripts/roadmap-v17-compare.mjs, last adapter change21a2807ddd1f7cd8315d6b2202e904d64162c10f.
The domain is the complete ordered schema1 SolCases enumeration, seed0,
indices0-159,kinds0-9, four viaIR/optimizer combinations, pinned solc0.8.38,Osaka.
Runtime binds exact records, settings, hashes, revision, toolchain and before/after
inputs. This resolves the bounded lookup wait only. The answer is read-only
source inspection, with no new runtime/gate claim. Its existing soljson path
is not substituted for this lane's required official native compiler.
Arbitrary-contract/EEST binding remains unestablished. Exact owner answer and
consumer inspection hashes are saved at evidence/v17-adapter-inspection.json.
G49's current owner is claudecloud/move6-20261106/g49-final; do not duplicate it.

Continue the same original unfinished goal after these three bounded work items
(classification, live-binding inspection, reviewed conformance/control validation).
Next independent work: census/account non-state Osaka archive formats and expand
admitted deterministic witnesses while awaiting arbitrary-contract/EEST source
binding. Record waits for V17/G49 integration and the full G49 producer; do not
stop at either while independent work remains. Full source/gas/deployment/world
integration, mismatch minimization/relay when a real mismatch exists, all remaining
original gates and full four-checkpoint completion stay open. No mismatch or
owner ticket was fabricated from these reference-only matches.


## All-format archive census and admitted boundary witnesses

Resume identity: the actual clean checkout was761bb4865dc5f7702549966061b84acdeecd6ac8,
a pre-existing merge of origin/master into this same branch. Its ancestry includes
the prior checkpoint d45dfa588519efb86e2d264e55cec2850e9e6cd8. This turn did not
reset, merge, publish or push. The original base/goal identity remains unchanged.

The pinned archive now has complete format/fork inventory accounting:
46,928members,46,927JSONfiles, one fixture metadata JSON,11,211fixture JSONfiles,
and35,715engine-X shared allocation JSONfiles. The inventory has248,411fixture
records and35,715separate support rows. The61,756support references contribute
zero fixture variants and no execution passes. Shared data are not extra tests.
An initial parser refused a pre-allocation root shape; the generic support-group
inspector and malformed/zero-padding controls now guard that regression.

| Exact Osaka format | Representations |
|---|---:|
| state_test | 19,093 |
| blockchain_test | 21,105 |
| blockchain_test_engine | 21,124 |
| blockchain_test_engine_x | 21,124 |
| blockchain_test_sync | 9 |
| transaction_test | 53 |
| Total | 82,508 |

Other inventory selections:276Osaka-related/transition representations and
165,627other-fork representations. There are no unresolved fork selectors in the
final census. Transaction-test forks come from their actual result mapping:
53Osaka and53Prague records. Unknown/empty selector shapes remain explicit
unresolved rows in the general inspector rather than disappearing. The existing
state-test count remains19,093. These counts describe fixture representations,
which can overlap in semantic origin across formats; they are not deduplicated
program counts, new theorems or additional successful comparisons. Every inventory
row is inventory-only or support-data-only; inventory execution_passes=0.

`archive_census.py` reuses the existing pinned archive SHA/commit and emits the
bulk inventory to `/workspace/h44/g52-differential/archive-inventory.jsonl.gz`.
Its SHA256 is f7f19d170ea0ae9fea4d85ea2fb344a21b16bfa494c34d6084345541abca2959.
A second full census regenerated identical compressed bytes and summary bytes;
it took38.222seconds. Five pure controls cover state variants, non-state networks,
transition forks, transaction result forks, unknown/empty records and shared
allocation groups. The source, generator and controls stay in existing assigned
folders and their docstrings name the guarded regression as H90b/H112 require.

The additive22-line standalone BoundaryWitness.lean driver reuses the unchanged
`Solidity.Tools.SolCases.emit` and actual `Prog.run ... withPanics`. Its uint-word
pool adds2^255-1,2^255,2^255+1,and2^256-2 to the existing four values, and excludes
all original4x4operand pairs. Thus(8²−4²)×10=480new closed witnesses,48per existing
kind, with zero source overlap against the original160. No new semantic family,
signed-type support, arbitrary-contract admission or replacement arithmetic oracle
is claimed. All actual expected observations come from the existing executable
semantics, not host arithmetic.

The witness driver passed bounded Lean -j1 execution in1.513seconds,
peak sampled RSS1140264960bytes, no resource stop, zero swap,
and unchanged300second/12GiB/4GiBreserve limits. All29original producer source hashes
remain unchanged and match their fresh private build. Actual Lean4.24.0 commit
797c613eb9b6d4ec95db23e3e00af9ac6657f24b and Lake5.0.0-src+797c613 were recorded again.
The prior passing KeySort source/receipt binding remains unchanged. No Lean MCP
was available; the standalone file used the existing serial bounded fallback.

The generic typed.mjs runner now admits exactly two named corpora, preserving the
original default160cases/320comparisons. Boundary mode verifies the exact driver
path, source/output hashes,480count, zero overlap and successful bounded receipt.
Both official native solc0.8.38 optimizer-enabled200/osaka modes executed480cases
each:960new observational matches. The default320comparisons were also rerun and
still match. Their union has640unique sources and1,280mode comparisons, not a
sum including repeated validation runs. Gas remains source-free/uncompared;
deployment/world and general source binding remain outside this admitted fragment.
Every report keeps full_g52_complete=false. No pending778classification or bounded
V17lookup was repeated. Those prior completed items remain completed.

Reproduce after the existing bootstrap/private producer build:

```sh
python3 scripts/h62/item3/g52-differential/archive_census.py --bulk "$BULK"
python3 tests/h62/item3/g52-differential/test_archive_census.py
flock /tmp/solidity-lean-feature-groups-20261025/writer.lock \
  python3 scripts/h62/item3/g52-differential/serial_semantics.py --boundary-only \
  --repo /workspace/solidity-lean --bulk "$BULK" \
  --lean-bin /workspace/h44/g52-differential/toolchain/lean-4.24.0-linux/bin
# This reuses the verified producer build; no second proof implementation.
node scripts/h62/item3/g52-differential/typed.mjs "$BULK" boundary
node scripts/h62/item3/g52-differential/typed.mjs "$BULK"
python3 scripts/h62/item3/g52-differential/pipeline.py manifest --bulk "$BULK"
```

Registration fragment for coordinator: BoundaryWitness is a standalone IO test
entrypoint under tests/h62/item3/g52-differential importing only existing
Solidity.Tools.SolCases; no library root or core module registration is proposed.
One new Lean definition is the test's main; there are no new theorems, axioms,
sorry, frozen statement/definition changes, exclusions or raised proof budgets.
Checkpoint delta against the pre-existing761bb4865checkout: +1Leanfile,+22Leanlines,
no existing Lean file edits. H112's5f1459653baseline(1.21MLeanlines,7,449files,
~24minfullbuild) is context only, not a new measurement or gate result.
No checking-speed refactor occurred; old fresh-closure and new test-driver times
are different workloads, so no before/after checking-speed improvement is claimed.

Finder and skeptic independently reviewed read-only with no Lean/server. They
verified tuple coverage/zero overlap,960real matches, allocation support separation,
format/fork accounting, original default compatibility and named regression guards.
Their manifest clearance is recorded only after regenerated manifests include the
new inventory, boundary compiler artifacts and receipts. Evidence includes
archive-census.json,archive-census-replay.json,archive-census-controls.log,
boundary-generator.json,boundary-differential.json,boundary-toolchain.json,
boundary-validation.log,boundary-default-regression.log and
census-boundary-acceptance.json, all off Git under H44.

The original goal remains active. Next independent queue: a bounded reference
adapter for explicitly admitted blockchain_test records, with exact refusal and
transition/fork accounting; do not claim engine/engine-X/sync support from the
census. Keep waits for V17/G49 arbitrary-contract/EEST source binding and
claudecloud/move6-20261106/g49-final's full producer. Full source/runtime agreement,
applicable gas/deployment/world observations, real mismatch minimization/owner
relay and original final gates remain open. Reference inventory and finite witness
matches do not close the full assignment.

The final generic emitter CLI was also checked for guard races: a recorded
resource stop now fails directly even if the process exit code is zero. A
synthetic CLI control asserts nonzero exit and absence of a success receipt,
without executing Lean. The real guarded rerun succeeds and preserves exact
compared output bytes. Both reviewers cleared the implementation after this fix.
The final manifest is regenerated only after all receipt/control updates.

Final manifest clearance: both copies are identical with2,952entries and SHA256
af86aad07e56852bed960d99850a6917ebe09c60124278e1e96e1c382a5debb4.
The skeptic independently verified every required census/boundary artifact and
all1,920boundary compiler files against those hashes. No outstanding findings.
