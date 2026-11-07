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


## Coordinator re-baseline and blockchain input preparation

The coordinator authorized re-baselining on origin/master advertised at
5da4771e63a4278ed53932ac39a032e3d7aea6ed. Fetch showed that it did **not** contain
local6a68fe831eaa6b4a9132499e243c3a7a80732dcf in ancestry, despite the merge notice.
The common ancestor was761bb4865dc5f7702549966061b84acdeecd6ac8; the remote owned
lane files were unchanged from that ancestor. Fast-forward correctly refused.
The worker performed a normal authorized merge into this lane, preserving both
heads at2cd1303a269a129ef2a84a1478e9ec5d1a3f1470. No reset, discard or push occurred;
no owned file changed as a result of the merge. The original c6f550e base and
persistent goal remain unchanged. Evidence:blockchain-rebaseline.json. Coordinator
retrieval must retain the local6a68checkpoint, rather than assuming it was already
published; the integration patch includes it.

The existing generic exporter now accepts --format blockchain_test. It reuses
the pinned archive, verifies the full inventory hash/census binding, selects only
exact-Osaka blockchain_test rows, rejects duplicate identities, checks every
actual fixture's network and format, and verifies exhaustive selection coverage.
It preserves complete genesis/pre-state/block/expected-post fixture data without
interpreting those values as successful execution.

All21,105selected records across2,693files were exported, with contiguous indices
and status input-only-not-executed. No blockchain execution or source agreement
is claimed. The stream is /workspace/h44/g52-differential/blockchain-inputs.jsonl.gz;
SHA256:89082881102be9e9a6cf021c95636375c21810bb631844f8c345a336749866a3.
A second export produced identical bytes and exact identity coverage. The original
state-test input stream remains byte-identical at
 d7dcc3b6f969359d44bfdaec88b7dffcbd80cddacc2b06b8a135964e2cbbc602;
its completed rejection classification/runtime comparisons were not repeated.

Reviewer inspection exposed an in-progress publication weakness: truncating a
stream while its prior receipt was visible. The shared exporter now writes a
partial stream and replaces the published path only after exhaustive validation;
it publishes the receipt through a temporary file too. Stream and receipt hashes
must still be checked together. A synthetic failed-export test proves the prior
completed stream and receipt survive a wrong-fork refusal. All3controls pass.
The final atomic full export matches the same reviewed hash. Module docstrings
name guarded wrong-format/fork and partial-publication regressions per H90/H112.

Read-only finder and skeptic independently verified coverage, identity, exact
network/format, input-only status, default-state compatibility, and publication
fix. Neither used Lean/server or executed blockchain EVM cases. Evidence includes
blockchain-export.json,blockchain-export-replay.json,blockchain-atomic-export.log,
blockchain-export-controls.log and blockchain-export-reviews.json. Bulk streams
remain off Git and are included in the committed H44 manifest.

Reproduce input preparation only:

```sh
python3 tests/h62/item3/g52-differential/test_blockchain_export.py
python3 scripts/h62/item3/g52-differential/eest_export.py --format blockchain_test --bulk "$BULK"
```

Inspection of the pinned VM runBlock path found it requires a real
blockchain.validateHeader method when header validation is enabled. The next
independent work is to pin/provision that real provider, establish genesis/history
and block validation bindings, then execute bounded admitted fixtures. Do not
set skipHeaderValidation or fabricate a validator to turn preparation into a
match. Engine, engine-X, sync and transition records remain outside this adapter's
currently selected input format and explicitly accounted by the full census.

Checkpoint Lean delta:+0files,+0lines; no existing theorem, definition, exclusion,
axiom or proof-budget change. No Lean/full build or new checking-speed measurement
was performed; H112's1.21Mlines/7,449files/~24min baseline remains context only.
All full-goal obligations stay open. Waits remain V17/G49 arbitrary-contract/EEST
source binding and claudecloud/move6-20261106/g49-final's full composed producer;
independent reference-provider work remains actionable. No source mismatch ticket
or complete-goal result is fabricated from input preparation.


## Checkpoint: validated Osaka blockchain reference provider

The checkout was already at fetched origin/master
ba3c0f1539c8b64ac0c6c89e729481d3d398ee83. Strict ancestry checks confirm both
053803649a3ed7809c6eed957361e07d68399ec0 and the original c6f550e base are
ancestors; no reset, discard or additional merge was needed. Evidence:
block-provider-baseline.json. Original branch, goal and ownership remain intact.

The optional reference integration now pins @ethereumjs/blockchain@10.1.3 in the
existing test package lock. The dependency-free Lean core has no new dependency.
The real provider validates fixture genesis/history and supplied block headers;
runBlock uses generate:false, skipBlockValidation:false,
skipHeaderValidation:false and validateBlockSize:true. Fixture genesis activates
Osaka from block zero rather than Mainnet historical heights. The adapter checks
genesis pre-state, block commitments (state/receipt roots, bloom, requests and
gas), tip hash and declared post-state account/code/full storage tries. It refuses
wrong domains, expected-invalid blocks, nonlinear histories and partial post-state
shapes rather than converting these into matches.

Review exposed a missing block-size-validation option in the initial run; those
7,581 provisional rows were stopped and excluded from acceptance. The real
oversize-block control then failed because the pinned Common defaults omit Osaka
EIP7934 activation. The corrected configuration explicitly enables EIP7934 with
8,388,608 bytes, taken from the immutable EEST v5.3.0 spec at commit6824474
(SHA256 21b08f2757e5f9f6d3be31eb98acfa26f07c8e7694a0456156481b596bad88fc).
The pinned source, failed-control history, excluded-run receipt and final passing
control are preserved off Git. No installed reference implementation was edited.
The negative controls exercise the actual provider's timestamp rejection and
actual block-size validation; temporary test serialization is restored in finally.

Corrected exhaustive command (raw exit2 means intentionally incomplete):

```sh
node scripts/h62/item3/g52-differential/eest_reference.mjs "$BULK" 21105 block-size-bounded all none blockchain_test
```

All21,105 unique, contiguous inputs were accounted for:19,479 reference fixture
matches and1,626 unsupported expected-block-rejection cases; zero errors,
mismatches or resource stops. Every source-semantic result remains unsupported.
Both reference_complete and differential_complete are false. Result SHA256:
d138d806f1cd893a1d3edfb2c9ee37947f77a8151c51da3badeedecdc84ea20e.
The full corrected run took687.619s, peak aggregate RSS1,308,512,256 bytes,
under unchanged serial time/memory/step bounds. This is a new workload, not a
before/after checking-speed measurement. Evidence: block-provider-acceptance.json,
eest-reference-block-size-bounded-summary.json and matching JSONL/run log.

NoProof scope means execution/header checks only: no beacon consensus, signatures
or fork-choice proof is claimed even though the provider validation option is
true. Per-transaction return/revert bytes and raw logs are not yet retained and
compared by this block adapter; receipt commitments alone do not close that
original observation obligation. The native-solc source corpus and source/EEST
binding also remain separate from these reference fixture matches.

Commands recorded in block-provider-acceptance.json and control-0..3.log:

```sh
node --test tests/h62/item3/g52-differential/blockchain_adapter.test.mjs
G52_BULK="$BULK" node --test tests/h62/item3/g52-differential/blockchain_header_integration.test.mjs
G52_BULK="$BULK" node --max-old-space-size=4096 --test tests/h62/item3/g52-differential/blockchain_size_integration.test.mjs
node scripts/h62/item3/g52-differential/eest_reference.mjs "$BULK" 1 state-provider-compat
```

The first three commands exit0 (four tests, no skips). The default-state
compatibility probe returns one reference match with expected incomplete exit2;
it does not repeat or add to the completed19,093-state-case accounting. Finder
and skeptic independently inspect source, exact hashes, exhaustive result counts,
NoProof/source boundaries and controls without Lean/server or heavy execution.
Their final findings and fixes are recorded in block-provider-reviews.json.

Checkpoint Lean delta:+0files,+0lines,+0declarations/helpers; frozen statements
untouched, axioms/sorry/trust additions0, proof budgets unchanged. No Lean or full
build was rerun, and no RUNTIME_GATE_PASS is claimed. Prior actual Lean4.24.0 /
Lake5.0.0-src+797c613 and bounded KeySort success remain historical evidence;
H112's1.21Mlines/7,449files/~24min baseline is not a new measurement.

Next independent work: retain transaction return/revert/log/gas observations and
classify expected-invalid block rejections without weakening incomplete status;
nonlinear histories and other census formats remain explicit pending coverage.
Waits: V17/G49 arbitrary-contract/EEST source binding and
claudecloud/move6-20261106/g49-final full composed source/runtime producer.
No source mismatch or owner ticket is fabricated from this reference-only run.
Original persistent full goal remains active and unfinished; this is a committed
handoff checkpoint for the coordinator, with no push or publication.


## Checkpoint: native transaction observations and block rejection classification

The existing adapter now retains native runBlock transaction results: ordered
transaction hash/type, exact return/revert bytes, execution exception, raw logs,
receipt status/cumulative gas, total/execution gas, gas limit and the native
refund counter. The refund counter is not necessarily the capped applied refund.
No step tracer or reference engine patch was added. Receipt logs/status and
transaction gas totals are checked against the native validated block result.
There is no independent fixture expectation for return/revert bytes, and no
isolated per-transaction storage-snapshot claim.

Expected-invalid blocks now run real provider validation before native execution.
Finder review caught the importance of completing validateBlock (including blob
transaction checks) before deciding admission. Known native diagnostic categories
must match an expected alternative, with both unchanged state root and canonical
head. Gas classifications bind the diagnostic's transaction index to the actual
decoded transaction and computed intrinsic/floor facts. Accepted-invalid blocks
remain mismatches; unknown diagnostics remain unsupported. No expected label is
used as evidence of the observed reason. Final tip/post-state checks still apply.

Full command:

```sh
node scripts/h62/item3/g52-differential/eest_reference.mjs "$BULK" 21105 block-transactions-final all none blockchain_test
python3 scripts/h62/item3/g52-differential/pipeline.py block-acceptance --bulk "$BULK"
```

All21,105cases are unique/contiguous:21,099reference matches,6reference mismatches,
zero unsupported classifications or engine errors. The former1,626unsupported
negative cases now comprise1,620observed rejection matches and6native admissions
that disagree with expected SYSTEM_CONTRACT_CALL_FAILED. Every source adapter
remains unsupported; reference_complete and differential_complete remain false.
Strict deterministic acceptance records exit1. The full PTY process exit was not
retained before session expiry; its receipt records null rather than inventing
an exit. The exact fixture replay separately captures actual exit1. This capture
limitation does not turn six observed mismatches into a passing gate.

The full stream retains23,289transaction observations:20,823returns,265reverts,
2,201faults and1,858raw logs. Of these,23,283transactions belong to21,562accepted
blocks;6transactions belong to the mismatched candidate blocks. Finder caught
that the first aggregate omitted the latter six. The committed deterministic
block-acceptance action now checks both locations and reports separate subtotals;
these candidate observations add no fixture matches. Synthetic controls add no
fixture matches either. Result SHA256:
a44cb1a7b52a6ba27b792e2ba84681a6cbfae80cbff72d4d0bfc413a4526a12a.
Runtime714.003s, peak aggregate RSS1,509,691,392bytes under unchanged serial bounds.
No checking-speed comparison is inferred from different observation workloads.
The earlier7,581provisional rows remain excluded.

One root-cause ticket, G52-REF-001, covers fixture indices18780,18782,18783,19914,
19916,19917. Native EIP7002/7251 request accumulators return call output without
checking execResult.exceptionError. Four reduced probes (two predeploys, bytecodes
0xfe and0x5f5ffd) independently show invalid-opcode/revert failures followed by
normal accumulator returns. These are minimal native probes, not claimed fully
minimized blockchain fixtures. All six original fixture identities and hashes
remain pinned in tests/h62/item3/g52-differential/reference-tickets.json.
Reproduction commands and actual exits are in system-request-reproduction.json:

```sh
node --max-old-space-size=4096 scripts/h62/item3/g52-differential/system_request_reproducer.mjs "$BULK"
node scripts/h62/item3/g52-differential/eest_reference.mjs "$BULK" 1 system-request-fixture-replay 18783 none blockchain_test
```

Both commands return1 and preserve the disagreement. The probe's initial missing
VM parameter initialization was corrected; its setup error is saved separately,
never counted as a reproduced mismatch. No native engine code was changed.
The ticket is staged for coordinator routing to V17/G52 reference validation:
relay.sh and the coordinator filesystem are unavailable on this VM. No external
publication or former-Claude follow-up occurred. This is a reference-engine
conformance ticket, not a source/compiler/proof mismatch.

Fourteen distinct controls pass without skips:11classification/observation unit
controls,2real-provider header/admission controls and1real block-size control.
Read-only finder/skeptic reviews cover runtime source, all rows/hashes, minimizer,
controls and ticket boundaries; findings and fixes are in
block-transactions-reviews.json. Independent G49 adoption reviews are recorded
separately in g49-h121-reviews.json. Reviewers used no Lean/server or heavy run.

## H121: composed producer ownership and exact remaining obligations

H121 transfers the frozen Claude G49 producer to this same lane and original
persistent goal; no new goal or former-Claude follow-up is created. We merged
origin/master254c60df6, then exact frozen producer8e9a052f115cb12c2549db8654422a1728046a01,
then the coordinator's latest master7683091e7c35d265b3b76fdf2a93d0197ce9f556.
Integration head before local checkpoint edits is6039dfe7b7122e8d178f4b18ea055feea1ec1c0e.
All ongoing owned edits were preserved. No push/default-branch publication.

The existing bridge request metadata records current collector ownership while
retaining historical provider routes and unchanged H68 Approved_i requirements.
Remaining external factory families:

| Factory | Producer obligations still retained by other lanes |
|---|---|
| bare_prefix_bridge | Actual canonical producer owner; cannot infer an owner from RefinesUnder alone |
| compiler_agreement_bridge | V07/V09/V11/V12 and recorded memory/copy/internal-call producers |
| p1_frame_bridge | V12 ordinary/recursive/profile; MRS calls; V17 thunks; V13 bare reverts |
| v08_world_phase_bridge | V08 creation/libraries/world/source-unit/transient composition and original dependencies |
| p10_execution_bridge | V15 opcode execution, with V14/V11/PAR dependencies |

Two actual P1 examples exist, but neither closes the full independently approved
H68 domain. V1 is explicitly trivial/coarse; V2 uses a handwritten image and a
depth-constant Boolean-cell family. They do not preserve the complete original
Local, canonical emitted-code identity, full domain agreement or public-map
compatibility required for production acceptance. All five full factories remain
pending; no successful-fragment filter or certificate premise is accepted.

A fresh existing serial H49 checker rebuilt the unchanged FoldedPublic closure
and controls in a private cache: H64_SOURCE_AND_CONTROLS_CHECK_PASS, actual exit0.
Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b;
Lake5.0.0-src+797c613. KeySort passed bounded -j1, exit0,1.306s, empty diagnostic
log. Command/evidence: g49-adoption-check-command.json and g49-adoption-check/.
No Lean MCP was available. This framework check is not a concrete producer,
PublicObligations proof, migration cut-over, final full build or RUNTIME_GATE_PASS.
The existing three full certificate inputs and all15PublicObligations fields
remain open. Exact fields and source-hashed candidate census appear in the
existing tests/h55/g49-final-theorem/bridge-requests.json:h121Adoption.

Own Lean delta:+0files,+0lines,+0declarations/helpers; frozen statements touched0,
new axioms/sorry/trust shortcuts0, budgets unchanged. No refactor or paired timing
measurement occurred; H102's accepted historical timing protocol stays binding.
Next owned work is canonical production endpoint/code/admission binding, actual
stage construction and the full public residuals, reusing existing generic
coverage machinery rather than another conditional wrapper. G49 is now owned
pending work, not a wait on the frozen Claude lane. V17 arbitrary-contract/EEST
binding and the five external factory families remain typed dependencies.


## Checkpoint: deterministic Engine, Engine-X and sync inputs

The resumed checkout was clean at23c622eb31fc4a7f7ef768516561251f7e329b56 on the
assigned branch. Its existing coordinator merge/bookkeeping commits were
preserved. Fetch/merge of origin/master05d2c25872c4bb963a0ca7f605905e6e1e99eedc
returned0; originalc6f550e and previousf53f026ac are ancestors. No reset, discard,
push or default-branch publication. Evidence:engine-input-baseline.json.

The existing generic exporter now supports blockchain_test_engine,
blockchain_test_engine_x and blockchain_test_sync. All fixtures retain their
complete original payload/configuration/expectation fields, exact archive member
hash and identity. They are explicitly input-only-not-executed, never execution
or source agreement. Related representations may describe the same underlying
cases; they are not added to unique semantic witness or passing-case counts.

| Format | Exact Osaka inputs | Stream SHA256 |
|---|---:|---|
| Engine | 21,124 | 290feabb7d26c5cfcc32c861447e6ae860a840d94031115948ff7b530cee00e3 |
| Engine-X | 21,124 | 26117239c2da1b20734ed3f56bac609bc076bdaff535ec69e4e651cb5b4cbdae |
| sync | 9 | 76b3eb1d653a953a89a1cc2a467b091490d2f22b9e744cc3ad606276ce1bef4e |

Engine-X preHash references now bind to a seekable canonical allocation stream
and offset/length index. All11,568Osaka allocation groups and all21,124declared
case memberships are referenced exactly, with zero dangling refs. Each lookup
checks canonical record SHA, path/source SHA, actual network and exact testId
membership. Allocation records preserve pre-state, environment and genesis from
the pinned archive; these fields have not undergone native execution validation.
No ad-hoc allocation or fabricated genesis is supplied.

All files stage under partial names. The allocation stream/index and input stream
publish only after exhaustive input validation, with receipt last. Replacement
of the full set is not transactional; consumers must verify every receipt hash.
Failed membership validation preserves all four prior published Engine-X files.
The reader closes on failures. New negative controls cover missing preHash,
wrong case/network, corrupted bytes/offsets and mismatched path/source provenance.
All8export controls pass with ResourceWarning treated as error; all10existing
accounting controls also pass.

Reproduce each input preparation twice (no EVM/RPC execution):

```sh
python3 scripts/h62/item3/g52-differential/eest_export.py --bulk "$BULK" --format blockchain_test_engine_x
python3 scripts/h62/item3/g52-differential/eest_export.py --bulk "$BULK" --format blockchain_test_engine
python3 scripts/h62/item3/g52-differential/eest_export.py --bulk "$BULK" --format blockchain_test_sync
python3 -W error::ResourceWarning tests/h62/item3/g52-differential/test_blockchain_export.py
python3 tests/h62/item3/g52-differential/test_pipeline.py
```

The existing serial resource guard ran each export:12GiB cap,4GiB available
reserve, no swap,300s per command, one heavy job. All first/replay exports exit0
without resource stops. First/replay seconds:Engine-X176.902/176.330,
Engine47.878/48.371,sync25.703/25.234. Largest observed exporter RSS370,302,976bytes.
All three streams, both Engine-X sidecars and full receipts reproduce identical
bytes. Evidence:engine-input-export-runs.json,engine-input-export-replays.json,
engine-input-first-receipts.json and engine-input-acceptance.json. The sidecar
SHA256s are452fc176dfd074d9e460887efed298609055e0f2f568728d9edcac69d460a45c
(allocation stream) and7254fcd67e353229b453695e7a353af0633fbffa54938e218cbd65c6c0cbf43b
(index). Bulk remains outside Git and covered by the committed H44 manifest.

Independent read-only finder and skeptic checked exact inventory coverage,
uniqueness/order, actual format/fork, all allocation edges, gzip integrity,
receipt hashes, failure controls and reproduction. Both cleared the milestone;
neither ran Lean/server, native EVM or an archive export. Findings and fixes:
engine-input-reviews.json. No new execution pass or source match is counted.

Sealed state/block inputs and the six-mismatch native result are byte-identical.
Strict block-acceptance still records actual exit1 and six reference mismatches;
Engine inputs cannot close that gate. H70 reports the coordinator retrieved
G52-REF-001 and routed summary+hash to V17. Its local committed bytes still hash
f8b2151cf40f1fa9e373e64c273cb649f4220ebb4d7ec1b6581e301e1bdd9d6f.
The sealed ticket is unchanged; routing is recorded separately in
g52-ref-001-routing.json and is not validation/integration evidence.

The native official solc0.8.38binary still passes exact SHA/version verification.
Actual software versions are saved in engine-input-versions.json. Existing
H49checked source hashes still match the successful prior bounded closure;
no Lean run is added here. Historical Lean4.24.0/Lake5.0.0-src+797c613 and KeySort
exit0/1.306s/empty diagnostics remain historical framework evidence only.
No RUNTIME_GATE_PASS, migration, full build or whole-producer acceptance.
Own Lean delta0files/lines/declarations; frozen statements touched0; new axioms,
sorry/trust shortcuts0; proof budgets unchanged. No Lean refactor/checking timing
comparison occurred. Input export timing is an external measurement only.

Remaining exact-Osaka input format:53transaction_test records. Existing state,
blockchain and these three new format exports prepare82,455of82,508inventoried
Osaka representations; preparation is not execution coverage. Next independent
items are transaction-test inputs/admission checks and real native Engine payload
binding with explicit RPC/fork-choice/sync limits. Owned canonical source/session
and emitted-code binding, five full H68factory families and all15public residuals
remain open. Full Approved_i domains and original conclusions stay unchanged.
Waits remain V17 arbitrary-contract/EEST binding; MRS/full P1 and other original
frame owners; V08 world-phase; compiler-family owners; V15 P10 via coordinator
under H118; bare_prefix_bridge actual producer owner unresolved. No owner is
inferred, no former-Claude follow-up, and no new/reset/completed goal. H110 permits
continuation on this same original thread when fresh-thread machinery is absent.


H70 downstream clarification received after this checkpoint: V17 release head
 a2b8558db548751e414f71d1d3c7889f64cc0ee8 waits on our H121b full composed
producer and arbitrary-contract/EEST executable binding. V17 is a consumer of
those deliverables, not their provider; the generic V17 binding wait above is
superseded. These are owned unfinished work. No complete producing files/head
are available; conditional G49 framework and input exports do not satisfy them.
This dependency notice changes no scope, paused-goal state or acceptance gate.


H121c authorized adoption: full p10_execution_bridge is now owned by this lane;
the frozen Claude V15 is no longer its provider. Master1ab348cf7 and exact V15
implementation90153461127d8d0f1f188021e79bc1ccb256e1e5 were merged, preserving the
clean prior head070e511a2 and all original task commits. No general paused-queue
resume or goal mutation occurred. External inputs remain VY1 assembly sessions,
VY4 unified events/world coupling, VY2 physical refinement, VY3 concrete pass
certificates, V13 actual callee/world execution, executable-bytecode P10
body/signature/site-origin application and original V14/V11/PAR dependencies.
Canonical assembly/Osaka endpoints, full Approved_opcode coverage, all missing
InstrV2 macro correspondence and complete map/resource/prefix bridge remain open
owned work. No complete producing files/head or new acceptance is available.
See roadmap-v15-p10.md H121c section and bridge-requests.json P10 ownership record.
Source adoption does not discharge the15public obligations or six native FAILs.


## H82 continuation: remaining transaction inputs and native admission

H82 explicitly authorized independent work after the blocked pause; the existing
goal was not created or reset. Clean assigned checkout9fdb074cfa1f5ca4a6e435bc7b78fd10fd9cb30c
was preserved, fetched master merged without new local source changes, and
original c6f550e/H121c759da340c ancestry passes. No push/default-branch publication.

The existing exporter now handles transaction_test using the actual result.Osaka
object, preserving every original fixture field and its exact selected expected
result. It rejects wrong format, absent Osaka or transition-only selectors. All53
unique inputs reproduce byte-identical streams/receipts under the existing serial
12GiB cap/4GiB reserve/no-swap/300s guard. Export/replay exit0,25.085/25.077s;
peak observed RSS76,128,256bytes. Stream SHA256:
23e3e680d3e361c528bb3ae025f5015c51d7b794964fb7eb5b56e7d00df7f892.
All82,508inventoried exact-Osaka representations now have prepared input streams.
Related formats overlap semantic cases; preparation is neither execution nor
source agreement. Transition/other-fork inventory remains separately accounted.

New transaction_admission.mjs uses the pinned native @ethereumjs/tx,common,util
10.1.3 packages, explicit Mainnet/Osaka configuration, installed/committed lock
identity, export/archive/inventory hash bindings and exhaustive case identities.
It executes serialized decoding/basic validation only. These fixtures have no
account world, so no balance/nonce/basefee admission context, storage, logs,
rollback or execution-gas comparison is claimed. A valid-fixture profile remains
unsupported until its sender/hash/intrinsic expectations are implemented.

All53cases are invalid type4transactions and all53are rejected during native
decoding. Exact diagnostic/stage/type bindings classify49matches:40authorization
format,8authority-field/signature bounds,1empty authorization list. The8matches
use actual r/s/yParity overflow diagnostics, not the outer signature verifier as
a substitute for authority validation. Ambiguous leading-zero fields require the
native verifyAuthorizationList stack provenance. Generic host errors stay
unsupported; no expected fixture label supplies the observed rejection category.

Four RLP cases, indices6–9, remain unsupported. Native diagnostics are
“remainder must be zero” or “total length is larger than the data”; they do not
independently locate the expected authorization-format fault. No blanket RLP-to-
authorization mapping is introduced. This is an owned classification gap, not
an excluded case or a source/compiler mismatch. All53expected intrinsicGas0
values are rejection sentinels and are not compared to measured gas.

Both bounded native runs exit2 (incomplete),1.005/1.004s, no resource stops;
peak observed RSS66,867,200bytes. Results and summaries reproduce identical bytes.
Result SHA256:4c396db7cdf5351f37ca0f76dada6bd8e6bc5a5bfd81ed14ded60f3c0043e89c.
fixture_admission_complete, execution_complete and differential_complete remain
false; all53source adapters remain unsupported.49serialized-admission matches
add0transaction execution matches and0source matches. Initial53unsupported probe
and its source snapshot remain separate historical evidence, never padded into
final coverage. Output/summary publication is receipt-last, not a multi-file
transaction; consumers must check the result hash.

Reproduce under the writer lock and existing resource guard:

```sh
python3 scripts/h62/item3/g52-differential/eest_export.py --bulk "$BULK" --format transaction_test
node --max-old-space-size=4096 scripts/h62/item3/g52-differential/transaction_admission.mjs "$BULK"
python3 -W error::ResourceWarning tests/h62/item3/g52-differential/test_blockchain_export.py
node --test tests/h62/item3/g52-differential/transaction_admission.test.mjs
python3 tests/h62/item3/g52-differential/test_pipeline.py
```

All23controls pass (10export,3admission,10accounting), no skips. Independent
read-only finder and skeptic verify exact coverage, observed error mappings,
validator provenance, source hashes, rejection sentinel boundary and replay.
No reviewer used Lean/server, native execution or archive generation. Evidence:
transaction-export-runs.json,transaction-admission-runs.json,
transaction-admission-acceptance.json,transaction-final-checks.json and
transaction-reviews.json. Bulk stays off Git; generator/adapter/controls and
updated sha256 manifest are committed.

All3,079prior sealed H44entries were rehashed unchanged before augmentation.
Existing state/block adapters and their rejection module were not edited. Strict
block-acceptance still exits1 for the same6reference mismatches; no new ticket is
fabricated from four unsupported category bindings. The H121b composed producer,
arbitrary-contract/EEST source binding, owned H121c P10 bridge and all15public
obligations remain open. V17 is downstream; frozen V15 is not a provider wait.
Required real inputs remain MRS/full frame, V08world-phase, original compiler
factories, VY1/VY4/VY2/VY3, V13callee/world, executable-bytecode body/signature/site
application and original V14/V11/PAR facts. Core/reference CALL representation
remains owned integration; bare-prefix owner is unresolved and not guessed.

Own Lean delta0files/lines/declarations; frozen statements touched0; new axioms,
sorry/native_decide0; budgets unchanged. No Lean run/refactor/timing comparison,
performance STOP release or RUNTIME_GATE_PASS. Historical toolchain/KeySort
records remain historical evidence only. Next independent work includes exact
RLP category binding and real Engine payload execution; canonical producer
endpoint/premise integration remains owned unfinished work. The full assignment
is not complete or blocked merely because one producer is missing. H110 permits
continuation on this same original thread; no competing goal/thread is created.

Coordinator merge receipt during this checkpoint: published master
65e69b6426a9a4fc3fb5541f41726a4bfefda5d0 was fetched, verified against origin,
and fast-forwarded before committing. Reviewed transaction edits were preserved;
no reset, discard or push. Evidence:transaction-latest-rebaseline.json.


## RLP envelope binding: supersedes the four unsupported classifications

Before this item, origin/master was fetched and its log/code inspected. Published
master65e69b642 had no transaction_admission.mjs; existing owned checkpoint3927e347
was reused. No duplicate upstream implementation was created.

The immutable fixture-pinned EEST test at commit6824474c2ae99e6a67be6093e9a1edc1c82091ea
explicitly assigns TYPE_4_INVALID_AUTHORIZATION_FORMAT to two whole-type4-envelope
mutations: rlp()+0x00 and rlp()[:-1] (test_invalid_tx_invalid_rlp_encoding,
lines601–633). Exact source SHA256:
838423a917650eb9282911b6a66c034f2d96e76572cd4b92cb8b216010683770.
This is a versioned upstream category binding, not a claim that a generic RLP
message identifies an authorization-list location. Pinned client mappings were
also inspected; no broader authorization/RLP mapping is inferred.

The adapter recognizes only those exact diagnostics and byte transformations.
Removing one trailing zero or appending one zero must produce a transaction
accepted by native createTx/basic validation/outer sender recovery, and native
serialization must reproduce the repaired bytes exactly. No expected fixture
label or case ID is consulted to construct the witness. All other RLP failures
remain unsupported. The append-zero witness establishes existence of a canonical
one-byte repair; it does not recover the original missing byte, original signer,
or validate authority signatures generally. These remain context-free checks.

All53native rejections now have category matches; only indices6–9 require these
repair witnesses. Two bounded runs exit0 with identical results/summary,1.007s
first run (see transaction-rlp-admission-runs.json for both actual measurements).
fixture_admission_complete is true for this pinned53invalid-case set only.
execution_complete and differential_complete remain false; all53source adapters
unsupported. No EVM/world, storage/log/rollback/executiongas or source match added.
New result SHA256:
7524b84caa4881147f7d322821fba30feb12e12b9375eb80ee8c87b6847bf2d2.
The previous49+4result/summary and source are preserved as before-rlp snapshots;
old digest4c396db7 remains historical, not the current result. No old witness is
padded into a new fixture count.

Five classifier/envelope controls pass, including wrong type/tail/diagnostic,
failed/thrown native validator and mismatched witness/category negatives.
Read-only finder/skeptic cleared code and exact upstream binding; their limits
above are preserved. Neither reran native/archive/Lean jobs. Evidence:
transaction-rlp-controls.log,transaction-rlp-checks.json,transaction-rlp-reviews.json.
Only the two canonical result paths changed among prior sealed H44entries; exact
prior hashes are retained in snapshots. Strict block acceptance still exits1
for the original six reference mismatches. No new owner ticket or exclusion.

Reproduction requires the pinned source at
$BULK/evidence/transaction-category-sources/test_invalid_tx.py, retrievable from
https://raw.githubusercontent.com/ethereum/execution-spec-tests/6824474c2ae99e6a67be6093e9a1edc1c82091ea/tests/prague/eip7702_set_code_tx/test_invalid_tx.py
and verified by the adapter's fixed SHA before classification. Then run the
same node transaction_admission.mjs command from the prior checkpoint.
No Lean statement, dependent definition, interface, budget, axiom or exclusion
changed. Full H121b/H121c producer/world/source obligations remain open. Next
independent item is real native Engine payload/history support, after fetching
and inspecting master again. No RUNTIME_GATE_PASS or full-assignment completion.


## Engine payload execution and real history, with full byte replay

Before this item, origin/master was fetched and its log/code inspected; no
existing Engine payload runner was found. Before the next checkpoint commit,
origin/master advanced to1b3ab0676e24620af56e1408c1aabde9cb4bbdb7 and was merged
cleanly asac34aa548add7acae7d0df5cbc51ae9dddd1950f. Owned additions were preserved;
the five execution/guard/adapter source hashes stayed unchanged. Received
central registration/pin updates are upstream merge contents, not own pin edits.
No reset, discard, push or default-branch publication.

The additive engine_payload_reference.mjs reads every pinned exact-Osaka
blockchain_test_engine fixture in inventory order. It verifies export, compressed
input, inventory and installed/committed dependency-lock identity. Genuine native
Osaka block constructors with the pinned KZG setup recompute genesis and payload
hashes, transaction/withdrawal roots, blob-versioned hashes and EIP7685 request
commitments from exact parameter bytes. Converted blocks retain original
pre/post worlds and history, then run through the unchanged strict native block
worker/provider. Header, complete block-size, state, receipt, log/gas and final
fixture-declared account/storage checks remain enabled. No synthetic case is
counted as an original fixture; the original Engine input stream is unchanged.

This is payload execution/history support only. Negative API profiles, unknown
versions and unimplemented protocol behavior remain unsupported. Fork-choice
RPCs are not executed, and Engine-X allocation joins and sync protocol behavior
remain pending. The original full assignment is not restricted to this positive
profile: engine_fixture_conformance_complete, engine_rpc_complete and
 differential_complete remain false. Every source adapter remains unsupported.
Native payload matches do not establish Engine RPC or source/compiler agreement.

Both complete runs selected21124unique contiguous records:19479
payload_reference_match,1645unsupported (all engine-rpc-negative-or-version-profile-pending),
zero payload mismatches or engine errors. Actual exit2 correctly preserves
incomplete conformance. The19479matches contain21183executed blocks,261multiblock
fixtures (maximum68blocks),22849transaction observations (20383returns,
265reverts,2201faults) and1858raw log entries. Counts overlap other fixture formats;
they are not added as unique semantic witnesses. Native return/revert bytes and
gas are retained observations: these fixtures have no direct expected return
bytes, and no isolated per-transaction storage snapshot or source rollback claim
is added. Receipts/state commitments and final fixture-declared storage are checked.

Full result streams are byte-identical, SHA256
b96194ec9e143a544f616e45d7c95c83147f0f8a8482a9062291d1af59736093.
Only sampled peak RSS differs between summary files. First run693.873s,
external peak1390759936bytes; replay696.108s,external peak1422544896bytes.
The first internal sampled peak1391923200bytes is a separate measurement.
No resource stop. Native replay delta+0.322percent measures unchanged runtime
code, not a Lean refactor or checking-speed claim. All3122previously sealed H44
entries were rehashed unchanged before adding this evidence.

Commands, under writerlock and serial_semantics.run process-group guard:

    node --max-old-space-size=4096 scripts/h62/item3/g52-differential/engine_payload_reference.mjs /workspace/h44/g52-differential 21124 engine-payload-full
    node --max-old-space-size=4096 scripts/h62/item3/g52-differential/engine_payload_reference.mjs /workspace/h44/g52-differential 21124 engine-payload-replay
    G52_BULK=/workspace/h44/g52-differential node --max-old-space-size=4096 --test tests/h62/item3/g52-differential/engine_payload_reference.test.mjs

Three controls pass with no skips: wrong domain/profile refusal, native bad
payload hash/blob parameter rejection plus real wrong-post-state detection, and
oversized parent-heap refusal. Native worker60s/5million-step limits are unchanged.
The external full-job timeout is1200s, with12GiB aggregate RSS/address-space
limits,4GiB available reserve and no swap. Streaming output, process-tree polling,
worker-close-before-replacement and final publication checks preserve refusals.
The first pre-execution launch refused because Node24 adds192MiB of young-gen
heap to4096MiB old-space; the detector allowance was corrected to256MiB. That
refusal is preserved separately and adds no fixture observation. Node24.19.0;
no dependency/compiler installation or systemd-run.

Finder and skeptic independently verified source, all21124case identities,
hashes, native block/transaction/log counts and incomplete claim boundaries.
Neither used Lean/server or reran native jobs. Their initial resource/cleanup
findings were fixed before the full run; summary publication now rechecks the
guard after hashing. Evidence under$BULK/evidence:engine-payload-accounting.json,
engine-payload-reproducibility.json,engine-payload-checks.json,command receipts,
controls.log and engine-payload-reviews.json. Strict block-acceptance still exits1
for the same six existing reference failures. No new mismatch/owner ticket.

Received producer inspection is recorded separately with exact source hashes:
P1V2ReadAtBridge is a constant ordinary-call family retaining external approved
profile agreement; P1V2ValueBridge retains its physical/profile duties; V13's
P1RevertBridge states a core totality domain excluding assert. These useful
results do not supply the complete independently approved P1 production factory.
No owner is inferred for bare_prefix_bridge. This is textual inspection, not a
new Lean check or a proof that no differently named producer exists.

Own Lean delta0files/lines/declarations; frozen statements/dependent definitions,
interfaces, budgets, exclusions and axiom set unchanged. No new axiom, sorry,
native_decide or trust shortcut. Historical Lean4.24.0/Lake5.0.0-src+797c613 and
bounded KeySort evidence remain historical; no fresh Lean/full-build or
RUNTIME_GATE_PASS is claimed. Full H121b composed source/runtime producer,
H121c p10_execution_bridge, canonical source/session/emitted-code identities,
full Approved_i coverage and all15PublicObligations remain open. Real external
factory/session/world/physical/body inputs remain listed in the handoff; V17 is
downstream and frozen Claude V15 is not a producer wait.

Next independent queue: reuse strict native payload machinery for Engine-X
allocation-bound inputs, account actual sync/history and negative RPC support,
and construct the owned canonical production endpoints and premise integration
when their original inputs permit. Do not repeat completed53case rejection
classification, count unsupported rows as passes, or accept a conditional wrapper
as the full producer. Original persistent goal stays unfinished; H110 permits
this same thread when fresh-thread handoff machinery is unavailable.
