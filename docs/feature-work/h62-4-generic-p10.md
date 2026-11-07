# H62 item 4: generic-p10

The full four-checkpoint assignment remains **unfinished**. Source accounting,
an intrinsic BYTE execution lemma, a typed nine-row table, all 21 original public
proposition correspondences, and full affected standalone-package validation
now pass. Timing acceptance passes with a 5.009% slowdown, within the 10% limit.
V15's original-file migration and integration gates remain pending.
No original declaration or frozen interface changed.

The assigned branch is `codex/solidity-h62-4-20261106/generic-p10`, based exactly
on `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. The VM checkout is
`/workspace/solidity-h62-4-generic-p10`. The initial clean checkout at
`/workspace/solidity-lean` on `work`, head
`6cf853aea0417155aca29ddb91f1767d3f3a3cc4`, was preserved. Fetching the exact
published base and `origin/master` succeeded; `git merge-base --is-ancestor`
confirmed the assigned base belongs to the remote history. No push, merge, PR,
deployment, generated-root write, or H55/Yul generator work occurred.

## Census and audit matching

The deterministic scanner visits every `.lean` file in the RoadmapV15 family,
including controls outside filenames ending in `Controls`. It records exact
UTF-8 source hashes, named and anonymous declarations, statement hashes, source
locations, complete structure fields, declaration hashes, and diagnostic/trust
commands. Anonymous examples and the local anonymous instance receive ordinal
IDs within their files. Whole-file hashes also freeze namespaces, imports,
options, attributes, comments, and proof bodies.

| Inventory | Count |
|---|---:|
| Original family files | 198 |
| Files ending in Controls | 76 |
| All theorems / anonymous examples | 1,525 / 33 |
| All definitions / abbreviations | 501 / 1 |
| All structures / local instances | 7 / 1 |
| Total original declarations | 2,068 |
| Controls theorems / anonymous examples / fixture definitions | 787 / 33 / 307 |
| Guarded diagnostic commands / axiom print commands | 190 / 1,270 |
| Repeated private-name candidate groups within Controls | 32 |

The complete original inventory, with every captured statement and source
hash, is the off-git `census.json`; its SHA256 is committed in
`tests/h62/item4/generic-p10/census-receipt.json`. This is the full declaration
inventory, not a claim that a conjunction contains only one semantic case or
that every candidate is equivalent. Every original conjunction remains verbatim.

| Audit item | Application and boundary |
|---|---|
| 9: parameterize twin packets/controls | Inventory makes the P10 per-case declarations available for comparison. The audit's specific Backend/Evm paths belong to other families and were not changed. Similar names are candidates, not proof of semantic equivalence. |
| 11: shared helpers and fixtures | 32 repeated private-name groups identify candidates such as `seed` (19), `u` (17), `execute` (16), `site` (15), `spill` (15), `expected` (13), and `shape` (8). Their signatures and bodies remain independently hashed. A name match does not authorize replacing its semantics. |
| 16: per-case packets to typed table plus lemma | The approved P10 assignment uses this transformation pattern. ByteObservation's nine positive execution controls are a concrete candidate. H28/NumericLiteral/Yul Raw work and the H55 vector generator remain excluded. |

The scanner is a bounded lexical source tool, not a Lean parser or elaborator.
It refuses unsupported indented/inline-attributed declaration forms and missing
or empty family directories. In this pinned corpus, independent reviewers
confirmed the declaration counts and source hashes. Candidate flags for errors,
negative conclusions, binders, and kernel decisions require semantic review.
They must not determine proof acceptance or justify dropping cases.

## Acceptance and independent reviews

Reproduce from the assigned checkout:

```sh
python3 -B scripts/h62/item4/generic-p10/census.py \
  --output /workspace/generic-p10-artifacts/evidence/census.json
python3 -B scripts/h62/item4/generic-p10/accept.py \
  --inventory /workspace/generic-p10-artifacts/evidence/census.json
python3 -B tests/h62/item4/generic-p10/negative_acceptance.py \
  --inventory /workspace/generic-p10-artifacts/evidence/census.json
```

Acceptance checks the committed inventory receipt, exact base file set, each
source against `git show` at the published base, byte-identical reproduction,
branch ancestry, and staged/unstaged/untracked write scope. Generating a new
inventory does not update the committed receipt. H44 forbids bulk output inside
the repository. All commands, exits, durations, and log hashes are recorded in
`/workspace/generic-p10-artifacts/evidence/gates.json`.

| Gate | Outcome |
|---|---|
| Scanner adversarial unit tests | PASS: 18 tests, including defaults, nested lets/comments, strings/chars, anonymous cases, malformed input, field weakening, and guard-output mutation |
| Source reproduction acceptance | PASS: all 198 pinned files, exact inventory, base ancestry, sole write scope |
| Negative acceptance | PASS: checksum tamper, missing source, forged base hash, empty inventory, and changed theorem statement all refused |
| `node scripts/check-layers.mjs` | PASS: 857 core modules, zero reaches to elaborators or checked parser adapters |
| Frozen-family diff / `git diff --check` | PASS: no family diff, no whitespace errors |
| Generic lemma / typed fixture proofs / correspondence | PASS in the additive test package; original-file migration pending |
| KeySort prerequisite / full affected package checks | PASS; 48 headline axiom guards checked; assignment-wide integration remains pending |
| Same-condition original versus proposed proof timings | PASS: 5.777562s before, 6.066986s after, +5.009452%; 10% limit |

Independent read-only finder `/root/census_finder` and skeptic
`/root/census_skeptic` used source/Python inspection, no Lean server or heavy
jobs. They found the omitted local anonymous instance, incomplete structure-field
statement hashes, empty-family false pass, and an index-only write-scope gap.
All were fixed and regression coverage added. Trust commands were also added
to the inventory. Both final rechecks report no remaining concrete finding
within the source-accounting scope. Their read-only sandboxes could not create
the temporary test directory; the parent ran all 18 tests and five forgery
challenges successfully. These reviews do not accept any semantic proof.

## Runtime and ownership state

The VM has a 16 GiB cgroup memory cap and no host swap. At the first source
checkpoint, no heavy Lean job had run. The resumed v4.24 work is recorded below.
Future checks remain serial, with explicit `LEAN_NUM_THREADS=1`, Lean `-j1`,
bounded memory and a 4 GiB available reserve. No `systemd-run` is allowed.
The writer-lock path is
`/tmp/solidity-lean-feature-groups-20261025/writer.lock`. The initial scanner
addition preceded acquisition of a sustained writer lock; subsequent edits,
checks and commit preparation held that lock. No other writer was observed.

All five coordinator-input SHA256 values were checked against the supplied
manifest; the hashes are retained in the receipt. The coordinator's
`toolchain-pin.json` names the official v4.35.0 Linux archive, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
The downloaded archive matches. Its binary reports:

```text
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
```

The assigned base's tracked pins remain v4.24.0. Installing elan succeeded, but
attempting to provision that toolchain through its release service failed with
proxy CONNECT HTTP 403. No v4.24 cache was used, no tracked pin was changed,
and the v4.35 binary was used only to report its version. Goal inspection is
not exposed by the worker tools; the coordinator explicitly resolved that
optional absence as nonblocking. No replacement goal was created.

| Typed state | Required next action |
|---|---|
| `TOOLCHAIN_RESOLVED` | The coordinator answered Q-TOOLCHAIN-01: this lane stays on v4.24.0; v4.35.0 applies only to batch solidity-h62-6. Actual v4.24 versions and a passing bounded KeySort diagnostic are recorded below. |
| `OWNER_RELAY_REQUIRED` | V15 owns original family files. No `relay.sh` or exact-file owner agreement is available locally. Additive work is permitted; original-file migration remains prohibited. The saved exact-file request identifies the proposed ByteObservation control file. This is coordination, not a request to the human to waive ownership. |
| `ADDITIVE_PROOFS_PASS` | Intrinsic word-parameterized execution and typed fixtures are proved using actual native semantics. No whole execution is decided by the table. |
| `ADDITIVE_CORRESPONDENCE_PASS` | Kernel proposition equalities cover all 21 public originals, with all negative/refusal/resource-order controls retained. |
| `VALIDATION_PARTIAL` | Version/KeySort, per-file diagnostics, 48 transitive headline guards, full affected package and matched timing pass. Owner-applied migration/integration/full gates remain pending. No gate is waived. |

Historical `Q-TOOLCHAIN-01` (now resolved), sources: coordinator toolchain update and base
`lean-toolchain`. Does “Migration ONLY” apply the pinned v4.35.0 requirement
to this generic-controls lane? The mutually exclusive options are:

1. Retain v4.24.0 for generic-p10; v4.35.0 applies only to migration lanes.
   Generic proof validation then needs the base toolchain provisioned.
2. Validate generic-p10 on pinned v4.35.0 using an isolated overlay; retain the
   assigned base and ownership boundaries. Dependency/source migration must be
   provided by its owners; this lane cannot edit their files.

The coordinator selected option 1: “Your lane stays on master's toolchain
v4.24.0; do not install or overlay v4.35.” No exclusion, premise, theorem statement,
interface, resource budget, axiom allowance, or proof budget is weakened.
New Lean helpers and proposition comparisons are listed below. Frozen statements
touched: zero. New axioms/sorry/native_decide: zero. The measured 5.009% checking
slowdown is below the 10% gate; no speedup is claimed.

The original patch, committed-head receipt, handoff, complete inventory,
individual gate logs, review record, and checksum manifest are saved under
`/workspace/generic-p10-artifacts`. The off-git handoff records the full commit
head after committing; this document deliberately cannot contain its own commit
hash. No checkpoint or elapsed time is treated as completion of the full queue.

## Resumed v4.24 runtime prerequisite

The official v4.24 GitHub release downloaded successfully through the permitted
proxy route. The release archive SHA256 is
`b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec`;
the unchanged `bin/lean` SHA256 is
`8fadc3ed92cc9decb94c96ee9c0876e91e03a3a5e69138f32114f02789e2766c`.
The actual binaries report:

```text
Lean (version 4.24.0, x86_64-unknown-linux-gnu, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release)
Lake version 5.0.0-src+797c613 (Lean version 4.24.0)
```

`scripts/coord-tools/lean-mcp diag Solidity/KeySort.lean` passed with
`diag: 0 errors`. The MCP run's observed tree RSS peak was 1,038,266,368 bytes;
minimum available memory was 15,093,714,944 bytes. Evidence is in the off-git
`resume-versions.log`, `resume-keysort.log`, and
`resume-core-mcp-resources.json`. These establish the runtime prerequisite,
not the generic lemma, correspondence, or full validation gate.

`provision_runtime.py` reproduces an off-git launch tree around the unchanged
official binary. It checks v4.24's version/githash, preserves unexpected paths,
and creates shell-quoted per-session environment files. The launcher supplies
explicit `-j1`, `-M11264`, and `--tstack=131072`, rejects conflicting resource
arguments, and serializes file compiler invocations. Tracked toolchain pins,
Lake files, proof options and owner sources remain unchanged.

`bounded.py` enforces a sampled 12 GiB aggregate RSS limit and a 4 GiB reserve;
the separate hard limits are the VM's 16 GiB cgroup cap and Lean's 11,264 MiB
allocation option. It requires zero host swap. It tracks the launched session
and observed descendants with PID start-time identities, rejects orphaned
workers after launcher exit, and applies TERM/KILL cleanup to every surviving
owned process. This is for foreground Lean/Lake/MCP processes; a program that
daemonizes and reparents entirely between samples is outside its containment
assumptions. No systemd invocation or global swap change is made.

Independent finder and skeptic reviews found and then accepted fixes for
orphaned/TERM-resistant child cleanup, PID identity checks, conflicting launch
flags, and unexpected provisioning symlinks/files. Four real process-lifecycle
tests pass. The provisioning regression also refuses three unexpected output
or parent-path cases while preserving their targets. These are external tool
tests, not Lean proofs.

The pinned Bridge repositories cloned successfully. The selective Mathlib
cache request failed: all 900 requested files received proxy CONNECT 403.
The same BYTE dependency closure built from pinned sources: 1,146 jobs, exit 0,
2,446.174 seconds, 4,721,393,664-byte peak tree RSS and 9,386,577,920-byte minimum
available memory. That warm-up started before the guard lifecycle review fixes;
subsequent validation uses the corrected guard. This provisioning duration is
not a before/after refactor measurement.

The additive BYTE generator retains all 32 original declaration signatures
and every nonmigrated body; only the nine positive proofs and the private
semantic wrapper are intended to change. Two source-preservation tests pass.
An explicit P10 namespace opening was added after finder review. Kernel
correspondence now checks that name resolution preserves every public type.

## Additive proof and correspondence checkpoint

The standalone package is under `tests/h62/item4/generic-p10`; its own pin is
v4.24.0, matching the untouched parent/Bridge pins. Its dependency manifest
retains every frozen Bridge remote revision and shares only ignored storage.
No central generated root, module map, or axiom pin was edited.

`GenericP10.ByteFixture` provides:

- `execute`: parameterized over intrinsic `Scalar.Word` inputs/results, an
  actual `Site .BYTE`, tail, gas, capacity and fuel. Its sole observation premise
  is byte algebra; `byte_fetched` proves actual driver execution and continuation.
- `ByteFixture`: word-sized `Fin UInt256.size` index/value and a `Fin 256`
  result, carrying its native byte-equation witness.
- `ByteCase`, `fixtureValues`, `fixture_word`, and `fixture`: all nine original
  positive cases, including index 32, maximum index and maximum word. The byte
  equations prove by `cases c <;> rfl`; no new `decide` table proves execution.

`GenericP10.ByteControls` retains all 32 original declaration signatures. The
original `observed` statement is an exact wrapper around `execute`; the nine
positive declarations are exact table instances through `table_case`. Every
other declaration body is unchanged. The 21 original public propositions
include nine positives and twelve other observation/negative/refusal controls;
these are original cases, not duplicated progress counts.

`GenericP10.Correspondence` proves 21 explicit equalities in `Prop`, each by
`rfl`, between the complete original proposition and its candidate proposition.
The private `proposition` selector returns a proof term's type. This is not an
equality of proofs justified by proof irrelevance. The candidate itself imports
only the helper/native semantics, not the original control proofs.

`GenericP10.AxiomAudit` pins all 48 helper, candidate and correspondence
headlines against the fixed allowlist `propext`, `Classical.choice`, `Quot.sound`.
The pin generator refuses missing, duplicate or additional headlines and any
other axiom. Whitespace comparison is lax only to accommodate namespace-driven
line wrapping; names and axiom sets remain exact. An actual failed guard report
with CLI exit 0 is retained as a regression: transport success cannot establish
Lean success. Five parser tests cover failure, partial/missing payloads and real
complete diagnostic/build shapes.

Reproduce the combined source/semantic acceptance after provisioning MCP:

```sh
python3 -B scripts/h62/item4/generic-p10/accept_semantics.py \
  --evidence /workspace/generic-p10-artifacts/evidence
```

The acceptance passed source reproduction/refusals, generator checks, trust and
budget scan, full affected package build, all five per-file diagnostics, the
owner-proposal kernel check, layer checks, frozen-source diff, and whitespace
checks. Actual commands, semantic outcomes and durations are in
`semantic-acceptance-gates.json`. Stricter response-shape validation was also
applied to every captured Lean response without repeating unchanged proofs.

Independent finder and skeptic semantic reviews accept the lemma/table boundary,
all 32 retained signatures and all 21 complete proposition correspondences.
They found no semantic weakening, vacuous execution premise, indexed-family
match, trust shortcut, budget increase, ownership violation, or H55 overlap.
No reviewer ran Lean. Timing and integration are expressly separate gates.

The exported single-file owner proposal places the helper/table in the existing
control module under `SolidityBridge.RoadmapV15.P10.ByteTable`; it adds eight
helpers while preserving all original signatures and public names. Keeping it
in that file avoids an additional module-load step. Its exact combined body and
21 original proposition equalities passed a separate MCP kernel check. The
patch is `tests/h62/item4/generic-p10/owner-migration.patch`; it has not been
applied. V15 must explicitly agree to the exact file and apply/review migration.
No new production module registration is required for this inline proposal.

The completed timing gate is `measure.py`: a predeclared five-pair, alternating-order
comparison, with both warmups, identical native imports, full original controls
and helper/trust-command costs, equal-length fresh namespaces, one guarded MCP
backend and scratch slot, and strict complete Lean-success checks. Median wall
times measure elaboration/kernel checking only. A backend change or timeout
rejects the run; cleanup signals only the originally captured owned guard.
Any slowdown above 10% stops the refactor.

## Timing acceptance and original-VM handoff

The valid run is saved in
`/workspace/generic-p10-artifacts/evidence/timing-fresh`. All ten measured
trials and both warmups reported complete Lean success on the same captured
MCP daemon, guard and Lean watchdog. Both independent reviewers recomputed
the medians, checked all 12 result payloads plus header priming, and verified
the source/trial/driver/plan/recovery hashes.

| Checking measurement | Median |
|---|---:|
| All original BYTE controls | 5.777561817 seconds |
| Inline helper/table plus all retained BYTE controls | 6.066985985 seconds |
| Slowdown | 5.009451689% |
| Maximum authorized slowdown | 10% |

This is elaboration/kernel checking with warm identical imports and fresh body
namespaces. It includes the new helper/table and trust commands. It is not a
native compilation or whole-repository timing claim. The dedicated session's
observed peak RSS was 3,761,250,304 bytes, minimum available memory
10,138,951,680 bytes, no swap and no resource stop. It was administratively
terminated after completing the run; no live Lean job remains.

The first attempt is preserved separately under `evidence/timing`. Its initial
original-control warmup hit the 300-second client bound without producing a
sample. Cleanup confirmed no remaining owned workers. Source inspection by
both reviewers found that changing the reused scratch document's import header
crosses Lean 4.24's worker-restart/barrier path; this is a plausible infrastructure
boundary, not a proved timeout cause or a measured slowdown. A stale stopped
backend also produced one startup broken-pipe response before the fresh daemon
started. The valid recovery uses a fresh dedicated session and explicitly
primes the identical common header before warmups. It preserves the exact
source hashes, five-pair order, metric and threshold, links the old plan hash,
and discards no measured samples. No completed failed verdict was retried.

The four requested checkpoints have additive evidence: the complete original
inventory, intrinsic lemma/typed table, exact correspondence with retained
negative coverage and deterministic acceptance, and bounded matched timings.
The **entire assignment is still blocked**, because no exact-file V15 relay
agreement has been received, the original source has not been migrated, and
owner-applied integration/final gates (including the repository's required
`./run-lean.sh --bridge` confirmation) have not run. Only the BYTE packet is
proposed for migration; all other inventoried P10 files remain unchanged.

This is the fresh-thread handoff after the reviewed census/proof/correspondence/
timing work items. Continue the existing original goal on this same VM and
branch; do not create/reset a goal or launch a replacement. Original environment:
`ccarenv_b64_Y2NhcmVudl9iNzZmYzNjOWFjYjg4MTkxODMwOWQ1NGZjYjVlYmM5Nw`.
Original frozen prompt SHA256:
`17aa1362ea9e9c3746093f07c4d24c34d17f86a684d229b1506f5d604c66d8de`.
The remaining next action is coordinator relay of the saved exact-file request
to V15, followed by owner application/review and complete integration gates.
The committed timing receipt and off-git handoff record the exact committed
head, artifact hashes, commands and remaining obligations. Questions are empty;
the v4.24 toolchain question was resolved by the coordinator.

## H82 retirement preservation

The lane-specific stop-and-handoff names successor
`solidity-parallel-20261103/executable-bytecode`. No new proof implementation
was performed. H82 standing permission withdraws the old exact-file agreement
wait for the proof-only BYTE proposal; actual production integration and final
gates remain open. A subsequent standing-rules message said continue, so its
relationship to the explicit retirement was queried without resuming proofs.
See `tests/h62/item4/generic-p10/retirement-handoff.md`, the complete original
thread assignment in `original-assignment.txt`, and the full original queue and
scope in `queue-and-scope.json`. These files travel in the cumulative patch and
bundle; bulk evidence stays off git with SHA256SUMS. The exposed goal tool
cannot set PAUSED, and no available H71 permission authorizes a lane push.

Coordinator resolution: KEEP RETIREMENT AND HANDOFF to solidity-parallel-20261103/executable-bytecode. Generic Continue now broadcasts do not revoke retirement. No human decision pending. Coordinator will set existing goal PAUSED after final head report and idle turn because worker lacks pause tool. No further proof implementation.


## H82 successor source acceptance

The authenticated final member head `dcb2efa56558cfd7c056b8c8fcda724b9683750a`
is merged into the successor branch
`codex/solidity-parallel-20261103/executable-bytecode`. The retired worker is
stopped; this does not establish its historical gates or finish the queue.
The successor retains the original branch-bound acceptance entry point unchanged.

The additive `scripts/h62/item4/generic-p10/successor_accept.py` checks the exact
retired receipt and scanner, final-head ancestry, all 198 original family files
against the frozen Git base and current bytes, staged family fidelity, inventory
checksum and byte-identical reproduction. It requires the assigned successor
branch. The inherited census is byte-identical to the committed receipt, including
all 2,068 declaration records. The current-head identifier and verifier hash are
saved separately from the inherited historical `base` field.

This is source reproduction only. It does not certify the successor's entire
merge diff, kernel checking, correspondence, runtime, gas/fork, migration or
performance. Twelve adversarial tests include changed premises with unchanged
counts, forged statements and hashes, missing or additional files, changed
receipt/scanner, wrong branch or ancestry, symlinked sources and staged-only
corruption. The scanner is authenticated before any of its code executes; a
modified-scanner regression confirms executable tampering is refused without
executing it. An initial missing-source test reported the scanner's empty-family
error; the gate now checks the exact file set first. Both receipts are retained.

Run from the successor checkout, with fresh off-Git output:

```sh
python3 -B -m unittest discover -s tests/h62/item4/generic-p10 -p test_successor_accept.py -v
python3 -B scripts/h62/item4/generic-p10/successor_accept.py \
  --inventory /workspace/parallel-20261103/executable-bytecode/h82-integration/evidence/generic-p10-current-source-census.json \
  --output /workspace/parallel-20261103/executable-bytecode/h82-p10-source/evidence/source-acceptance-FRESH.json
```

The original no-push rule, live production partition and overlay-only migration
restriction remain. H82 removes obsolete proof-only exact-file permission waits;
it does not authorize live production edits outside the partition. BYTE production
integration, inherited families, affected Lean/Bridge gates and final performance
acceptance remain open. Four historical MCP evidence files are absent locally;
their dependent tests are not replaced with fabricated fixtures. Current H81
resource-policy text remains requested before new heavy work. No runtime pass or
whole-assignment completion is claimed.

Independent read-only finder and skeptic reviewed this successor check without
Lean or builds. The finder requested binding the final committed verifier to the
receipt. The skeptic found and prompted the pre-authentication import repair
described above; original acceptance and all production statements remain unchanged.
