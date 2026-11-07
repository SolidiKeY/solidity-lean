# H55 result, size and cache: work in progress

H145 archival notice: historical receipts, source-hash manifests, routing/chain
records and handoffs named below now live in the private coordination repository:
https://github.com/SolidiKeY/solidity-lean-coord/tree/4cb216278ddc62582604b4348d65749fcf9bfeb6/evidence/solidity-h62-5-20261106/statement-graph/
The private archive preserves their exact bytes and source revision. References
to “committed evidence” in older milestones describe those earlier revisions.
Current checker inputs, executable fixtures and checksum constants remain here;
evidence records are no longer code-branch inputs.

The scripts and controls in `scripts/h55/result-size-cache/` and `tests/h55/result-size-cache/` are prototypes. No producer or consumer owner file has been edited. No checkpoint is complete or adopted.

## Size check

At base 4d3790eadb8a5212233bc7d5e345817476b2f590 the regular-blob census has 14,271 files, 249 over 100 KiB, 27 over 1 MiB and a 333,160-byte largest Lean source. The proposed 100 KiB data and 1 MiB source thresholds are provisional. The helper reads source approvals from the supplied base and binds them to SHA256; it cannot establish that the caller chose the coordinator-trusted base. The pinned base has no approved-source file. A coordinator-owned base/approval flow and production adapter are required. This prototype is not a safe production gate.

## Result schema and poller

The JSON Schema draft and validator reject duplicate keys, non-JSON constants, invalid marker pairs and schema errors. `jsonschema` is an external Python dependency in strict mode. The patch was produced against supplied poll.py SHA256 `32aa42866f73297bae955a086f93103eab9f8513beb6e92c993fa2743c916ac5`; isolated tests apply it to a copy and run the complete poller against a mocked API with a simulated backup. It is not deployed. A future deployment must verify the target digest, install the dependency and schema, and preserve `poll.py.bak-h55` before adoption. No real host backup exists yet.

The patch preserves the original parser for legacy batches and enables strict parsing only for explicitly configured `H55_STRICT_BATCHES`. In strict mode a completed turn requires exactly one `agentMessage` with `turnId` equal to the completed turn ID and `phase` equal to `final_answer`; missing or ambiguous association fails closed. An error clears a prior result from the strict batch digest and saved poll state in the tested simulated environment. If digest replacement fails, the poller logs the failure and continues, but the old digest remains readable; a fail-closed reader/adoption protocol needs coordinator review. The supplied snapshot does not establish that the real inspect API emits those metadata fields or includes the final message in the requested page. Strict mode must remain disabled until the coordinator verifies an authoritative or sanitized live fixture. The supplied snapshot also does not list this H55 batch in ACTIVE/WATCH: catalog selection and service configuration remain coordinator-owned.

ESCALATE: strict result validation and existing handoff producers use different formats. Coordinator options: (1) migrate affected producers and enable strict mode for their batch after verifying turn metadata, requiring coordinated rollout; (2) retain the existing parser for legacy batches and enable strict mode only for batches whose producers and API metadata have been verified. The isolated controls demonstrate the compatibility boundary; they do not establish production deployment or turn metadata truth.

## Cache

H62/H63 supersedes the v4.24 per-master cache item. No cache implementation or roundtrip was completed. The v4.35.0 migration and Lake remote cache are assigned to solidity-h62-6-20261106/migrate-root-gate, with cut-over controlled by the coordinator. Retain H41 cache-inbox; do not freeze master or publish a cache.

## Checks and reviews

`PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/h55/result-size-cache -p "test_*.py" -v` passed 21 tests. Independent finder and skeptic reviews used no Lean server. Size-review fixes include bounded reads, explicit hidden-index rejection, history inspection, data/source digest binding and deletion census; trusted base and operational approval remain open. Result-review fixes include strict SHA length, opt-in legacy compatibility, fail-closed synthetic turn association, stale digest invalidation, and missing-validator startup compatibility. Controls use the real legacy producer and a mocked API with a temporary backup. Live API turn association, service configuration, real-host backup, producer rollout, and a final review remain open. No Lean proof result or KeySort pass is claimed.

## H82 standing rules and waits

H82 supersedes the previous exact-file agreement protocol for statement-preserving edits; interface and semantic changes still require the applicable owner. The draft schema now requires typed, nonblank `waits` entries and forbids nonempty waits for `done`. Independent finder and skeptic reviews identified those validation gaps and they were fixed. A simulated digest-write refusal leaves an old digest readable even though the poller continues and records the error; a fail-closed consumer or independent invalidation protocol remains a coordinator dependency. The source approval/base trust, real inspect metadata, owner-controlled rollout and final proof gates also remain open.

## Post-merge controls

Coordinator-reported `d86c7faf15ec9e4df3702b208622b2a7720cdb94` is an ancestor of fetched master `20e492ee99a3fa8679aa526de0b6e731d85e4134`; the lane fast-forwarded to that master. Five added isolated controls check staged paths containing newline/tab and binary content, forced staging of ignored oversized data, skip-worktree flags, non-UTF-8 leading-dash paths, and oversized renamed content. The full helper test suite passed 26 tests on the merged head. Finder and skeptic reviews, read-only without Lean server, found no defects in the first three controls; reviewer-identified path and rename gaps motivated the last two. The skeptic then identified that the initial rename fixture was too dissimilar to prove rename handling; the replacement asserts Git reports R100 for unchanged oversized content and checks both deletion and rejected destination. These tests do not establish full bypass resistance. The owner gate must protect the interval between census and use, and coordinator-trusted base and reviewed approval integration remain open. No proof or runtime gate pass is claimed.

## H82 successor: versioned report compatibility

The authenticated H82b assignment/scope and final stopped receipt were verified;
exact final head `6c93ebcd6f7125bd0c9913cf211565a50b4241b1` was merged before this
work. The optional integer `schema_version: 1` field now accepts the coordinator's
v1 report envelope while preserving legacy unversioned inputs. Unknown fields,
unsupported versions, booleans, strings, null and fractional versions remain
rejected. Versioned done reports retain all existing completion constraints.
JSON Schema treats numerical `1.0` as integer one; no lexical-number restriction
is claimed. Independent read-only finder and skeptic found no blocker and used
no Lean server. Final local controls ran 23 tests: 20 passed, 3 skipped because
the original host poll.py snapshot is unavailable on this VM. Evidence:
`/workspace/h62-statement-graph-evidence/h82/h55-schema-final-tests.log`.
This does not establish host deployment, real inspect metadata, fail-closed
consumer adoption, trusted-base integration or completion of either H55 item.

## H70/H90 successor size controls — stopped proposal

Disposable Git controls reproduced three false passes before the fix: a trusted-
base approved .py containing a >4300-digit JSON integer, deeply nested JSON, and
oversized content added in an unrelated root commit then deleted before merge.
Syntax-only JSON number parsing now avoids conversion limits; recursion failure
is conservatively data. Root commits receive root-aware diff-tree enumeration.
Replace refs are ignored and shallow/grafted histories are refused. New controls
also exercise replacement refs, filters hiding raw worktree bytes, and staging
a new oversized file after inventory capture. The prototype refuses transforming
attributes/autocrlf and rechecks HEAD, index/path identity and untracked inventory.
These are fail-closed refusals, not support for normalized raw-byte census.

Actual external controls: 30 run, 27 pass, 3 host-snapshot controls skipped.
Independent read-only finder and skeptic confirmed the stable-repository fixes,
without Lean/server/test calls. They retained limitations: metadata fingerprints
are not an atomic snapshot, global/system config/attributes and concurrent
history changes are not fully frozen, and per-parent merge comparisons may
conservatively flag an unchanged baseline blob. Trusted base, approvals, writer
protocol and production host adoption remain external inputs.

PERFORMANCE STOP: one warmup plus seven runs on the same persistent disposable
approved-source fixture measured median 0.063232468s before and 0.076785400s after,
+21.4335%, exceeding the 10% bound. Output SHA256 is identical; wait4 maximum RSS
is 13440 KiB for every measured invocation. The proposal is stopped and unaccepted;
passing functional tests do not override STOP. No unchanged rerun or deployment.
The earlier JSON/root-only stage measured +8.3606%; that does not validate the
later guarded version. Reproduction/timing generator measure_size_check.py and
regression docstrings name the guarded H44 cases per H90. Payloads are generated
only in disposable repositories and bulk output stays off Git. Detailed evidence
and hashes: tests/h55/result-size-cache/h82-size-evidence.json and
/workspace/h62-statement-graph-evidence/h82-h55-size/.

H86 unavailable original worker/host raw evidence remains a regeneration limit;
no synthetic fixture is claimed to authenticate it. H58 audit HOLD, the separate
pin pause/+46.58% STOP and H67 reconciliation remain unchanged.

## H97 envelope compatibility — functional checks pass, performance STOP

The coordinator's H97 notice replaces the current v1 envelope requirements.
The prior local validator rejected its minimal example because artifacts were
mandatory. The new profile requires batch, slug, status, branch, full 40-hex head,
gates, reviews, limitations, questions and waits. Artifacts and owner_tickets are
optional. H97 question options are objects with label/consequence; sources are
optional. Ticket payloads are opaque because the notice specifies no inner
contract; validation cannot establish owner agreement. H97 waits are arrays of
objects; this lane continues to emit H82 lane/item records. Known optional
legacy fields remain typed. Completion still requires nonempty all-pass gates
and no questions/waits; provided checkpoints/artifact paths retain their guards.

Unversioned legacy reports retain their separate profile, including nullable
partial heads and string question options. Explicit schema_version=1 selects
H97 exclusively; it cannot fall through to legacy. Earlier documentation that
v1 accepts nullable legacy heads is superseded. JSON Schema treats numeric 1.0
as integer one; no lexical-number restriction is claimed. Duplicate keys,
non-JSON/non-finite numbers, marker errors and decoder limits fail explicitly.

Schema checks are cached by exact source contents, with an eight-entry bound.
The file is reread each call, so changed, invalid or missing schema content cannot
reuse stale acceptance. The full union decides acceptance; complete profile
validators only improve diagnostic paths. Shared rules were factored without
removing constraints. Static finder/skeptic reviews found no acceptance/cache
blocker and used no Lean/server. Profile and union corpus checks accompany the
standard controls. Actual report suite: 23 run, 20 pass, 3 host-snapshot skips.
No host/API metadata or production adoption is inferred from synthetic reports.

The first candidate and three changed equivalent layouts all exceeded the cold
CLI time budget; every result and stopped source variant is retained. Final
candidate: warm-call median 14.657222 ms to 0.252894 ms (-98.2746%); fresh CLI
median 103.651028 ms to 116.877156 ms (+12.7602%, above 10%). Output is identical.
Measured CLI max RSS is 17920 KiB before and 18172 KiB after; warm helper lifetime
high-water is 17920/49284 KiB, not per-report allocation. Warm improvement does
not override the cold STOP. The final proposal is stopped and unaccepted; no
host deployment, budget waiver or unchanged timing rerun. The earlier size
+21.4335% STOP and pin pause/+46.58% STOP remain separate and untouched.

measure_result_validation.py records replayable fixed-input warm/CLI controls,
source hashes and RSS. It relies on the caller's writer lock, matching runtime
and resources; it is an observational helper, not a standalone trusted-host
gate. It does not attest baseline runtime/library identity or enforce child
timeouts. Those limits are recorded instead of inventing provenance. One initial
after-driver setup error split a marker twice and failed before measurement;
corrected and measured runs are distinguished in evidence.

Coordinator master ac9d8db2ad2b29d4f04ed2391d78b5f19b4c97a6 was integrated after
remote ancestry checks; WIP source hashes matched before and after the merge.
Repo-relative source pins and the off-git archive SHA are committed in
h97-validation-evidence.json. Payload names and hashes are relative to the
manifested archive, addressing the review's VM-only pin limitation. Source
regenerators and synthetic inputs are provided; unavailable original host/raw
worker evidence remains an H86 limitation. H58 HOLD, original goal identity,
frozen statements, axioms, premises, exclusions and proof/resource budgets remain
unchanged. No Lean files or shared roots/maps/pins were edited.
