# H62 item 4: generic V08 controls

Owner: `solidity-h62-4-20261106/generic-v08`. Frozen base:
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. Checkout:
`/workspace/solidity-lean`; assigned isolated branch:
`codex/solidity-h62-4-20261106/generic-v08`.

Status: unfinished. Census implementation and independent static reviews pass.
The generic execution lemma, exact original theorem instances, correspondence,
family measurements and full final validation remain required. Existing family
files are read-only. No permission to migrate them has been received.

## Census checkpoint and handoff

The deterministic scanner includes all 220 V08 files, not only filenames ending
in Controls. It retains 4,428 declaration rows: 2,619 theorems, 1,616 definitions,
138 abbreviations, 20 instances, 18 inductives and 17 structures. Controls files
contain 2,951 declarations, including 1,589 theorems. No original is removed.
Each source file is hashed; each declaration has its exact lexical header and
SHA256, source path, line, kind, written name and ordinal. Anonymous declarations
retain ordinal identities. Consumers must key by `(path, ordinal)`, since nested
namespaces can repeat written names. Multiple conjuncts and cases within a
statement remain verbatim, rather than being silently split or dropped.

Header hashes are lexical fingerprints, not elaborated Lean statement hashes.
Full file hashes additionally protect section variables, namespaces, imports,
proof bodies and all negative/refusal controls. The scanner is not an evaluator,
compiler, theorem prover or H55 vector generator.

Full original inventory: `/workspace/generic-v08-evidence/inventory.json`.
SHA256: `be03b64ac04c24940e39e24a75b806abf042524233bc465b1ed5109aad406096`.
Bulk stays off git. The committed manifest retains every original file hash,
counts and the full inventory checksum; the committed generator reproduces the
complete inventory from the exact base. Acceptance refuses any source change.

Commands (from this checkout):

```sh
python3 -B tests/h62/item4/generic-v08/test_census.py
python3 -B scripts/h62/item4/generic-v08/accept.py
python3 -B scripts/h62/item4/generic-v08/census.py --revision c6f550e281a7e5affa9a99bc2cdaed556dec00e4 --write "${GENERIC_V08_EVIDENCE:?set an external evidence directory}/inventory.json"
python3 -B scripts/h62/item4/generic-v08/census.py --check "${GENERIC_V08_EVIDENCE:?set an external evidence directory}/inventory.json"
```

Twelve mutation/parser and acceptance tests pass. They cover nested comments and strings,
proof-body versus statement mutations, default binder values, equation-style
definitions, complete match and let theorem conclusions, named instances,
anonymous cases, nested module discovery and malformed-source refusal.

## Audit applicability

Source: coordinator-supplied `refactor-audit-20261106.md`, SHA256
`31ab16906906a9b22fd28700aacc72d2ee0ffe81cea723ae209eb28e5299286a`.
All five supplied inputs match `/workspace/h62-coordinator-inputs/sha256.json`.

| Item | Exact audit target | Application to this lane |
|---|---|---|
| 9 | Backend/Evm twin controls and compiler families | Generic-proof strategy is relevant; those named families are outside V08 and are not edited. V08 inventory provides the exact candidate source set. |
| 11 | Backend/Evm shared lemmas and memory fixtures | Shared semantic lemmas inform the approach. No Evm/Backend helper or fixture migration is claimed. |
| 16 | StatementGrammarH28/NumericLiteralProofs packets; Yul Raw | Typed table plus generic proof is the method. Those packets and Yul Raw are outside this lane. H55 remains owner of Yul Raw/vector generation; no generator is duplicated. |

This applicability map does not assert that every V08 control has the same
statement shape. Runtime frames, admission, payloads, source and target state
relations and their existing exclusions must stay distinct where their exact
statements differ.

## Independent census reviews

Separate read-only finder and skeptic agents used no Lean processes or server.
Both found three truncated match-conclusion headers in `SourceCallPhase`.
The skeptic also found nonrecursive current-tree discovery and resource-reporting
issues. Named instance names were lost, and path/name pairs were ambiguous.
All confirmed defects were fixed. Regressions were added for match conclusions,
let binding, named instances and nested modules. Re-reviews pass for the current
220-file/4,428-declaration inventory. Reviewers ran ten tests read-only; the
remaining temporary-directory test passed in the authorized main-worker run.
The final skeptic also found assert-based checks could be disabled by Python
optimization. Acceptance now uses explicit failures, with a mutation regression
and an optimized-mode passing test run.
The resource harness now labels requested threads, per-process address-space
limits and nonaggregate RSS accurately and refuses surviving process groups.

## Environment and validation boundary

Setup recovered an older clean checkout at `6cf853aea0417155aca29ddb91f1767d3f3a3cc4`.
Fetched the exact base and master without discarding work; verified the base is
an ancestor of fetched `origin/master`; no remote task branch existed. Assigned
branch was created at the exact base under the repository writer lock.
`get_goal` is not exposed; coordinator explicitly says its absence is optional
and not a blocker. No second goal was created.

The official coordinator-pinned archive is Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake 5.0.0-src+eb6cafb.
Archive SHA256:
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
It is extracted at `/workspace/generic-v08-tools/lean-4.35.0-linux`.
The original tracked toolchain and cache are untouched. New artifacts are under
`/workspace/generic-v08-evidence/v435/lib`, exclusively built with that release.
The initial 4.24 build is historical setup evidence only and is not an accepted
migration gate (its checker invocation also had an invalid extra `--`).

VM memory cap: 16 GiB, no configured host swap. Checks are serial with explicit
`-j1`, `LEAN_NUM_THREADS=1`, a 12 GiB per-process address-space limit, a sampled
4 GiB available-memory reserve and a 300-second per-file timeout. No systemd-run.
The reserve check is sampled, not a hard aggregate RSS cap. No Lean MCP tools
are exposed; pinned per-file CLI checks provide actual diagnostics. Final
repository build validation remains pending.

| Gate | Actual outcome / decisive evidence |
|---|---|
| Official archive and all coordinator input hashes | PASS, exact published checksums |
| KeySort under pinned release | PASS, exit 0, 1.758 s, `v435/KeySort.log` |
| AST under pinned release | PASS, exit 0, 7.773 s, `v435/AST.log` |
| SortCheck annotations | PASS, exit 0, 1.505 s, `v435/solkeycheck.log` |
| SortCheck parser prerequisite | FAIL, exit 1; `Parser.lean:76` uses removed `String.trim`, followed by dependent errors; `v435/solkeycheck.log` |
| ABI dependency closure | FAIL at unchanged `Hash/CollisionBound.lean:407`, `:660`, `:680` and guarded outputs; `v435/Solidity.Hash.CollisionBound.log` |
| Complete solkeycheck and `./run-lean.sh` | PENDING behind failed prerequisites; no RUNTIME_GATE_PASS |

The blocked prerequisite files are outside the sole write scope. Neither is
patched or bypassed. Runtime/provisioning checks are not semantic proofs.

## Outstanding queue and typed blockers

1. Census source integrity and audit map are available; full elaborated statement
   fingerprints and runtime milestone validation remain pending.
2. Required generic *execution* lemma, full typed case migration and exact original
   declaration instances: pending. Isolated width-admission backfill is separate.
3. Required source/target correspondence, all negative/refusal semantic checks and
   runtime reproduction acceptance: pending. Static reproduction acceptance passes.
4. Full family before/after measurements under matching tree/cache/resources:
   pending. Timing delta is **unavailable**, not zero. No speedup is claimed and
   no refactor has been deployed. Stop if a future measured migration exceeds 10%.

`DEPENDENCY_TOOLCHAIN`: owners must migrate the parser and collision-bound proof
prerequisites to the pinned release, or the coordinator must provide their
approved isolated overlay. No family semantic proof gate can be claimed now.
`OWNER_RELAY`: no exact-file owner agreement exists; existing V08 files remain
read-only. No relay tool or coordinator host relay script is installed here.
Registration fragments must be supplied for owner/coordinator application; no
central map, generated root, axiom pin or frozen interface is changed.

No merge, push, PR, publication, pre-gate or deployment was performed. Preserve
the existing goal as unfinished; do not create a replacement continuation.

## Isolated admission backfill and handoff

`tests/h62/item4/generic-v08/IntrinsicWidths.lean` adds five proved lemmas:
`fixedBytes_widening`, `fixedBytes_identity`, `fixedBytes_narrowing`,
`fixture_identity`, `table_identity`. It uses the existing intrinsic
`Source.STy.implicit` relation and structural order proofs; it does not replace
semantic proofs with a finite decide table. Two bounded fixture rows preserve
the exact width/old/rhs inputs of the original `binary_client` and
`maximum_client`: `(2,[255,128],[0,1])` and `(32,[],replicate 32 255)`.
The raw payload lists are retained inputs, not intrinsically sized values or
proved evaluations. The admission lemmas quantify over every legal width and
all supplied declaration-base relations. Strict narrowing refusal remains
explicit. This backfill does not complete queue checkpoint 2 or 3.

The final per-file pinned Lean check passes without warnings, exit 0, 0.502 s;
log `v435/IntrinsicWidths.log`. All five printed axiom sets contain only
`propext`, `Classical.choice`, `Quot.sound`. There are no new axiom declarations,
sorry terms, native_decide calls, heartbeat changes or touched frozen statements.

Independent finder and skeptic reviews both pass for isolated admission.
They verified both fixture rows against the originals and the published
`STy.implicit` definition. Both requested unused-binder cleanup; that cleanup
was applied and the final warning-free check rerun. They explicitly reject any
interpretation as original execution/correspondence proof.

Deterministic reproduction rebuilds the three-module Source.Types dependency closure into a
separate output directory and then checks the helper, serially with the official
release and bounded wrapper. It neither consumes the old master cache nor edits
an owned source file:

```sh
python3 -B scripts/h62/item4/generic-v08/reproduce-width.py \
  --toolchain "${GENERIC_V08_TOOLCHAIN:?set the pinned toolchain directory}" \
  --archive "${GENERIC_V08_ARCHIVE:?set the verified release archive}" \
  --output "${GENERIC_V08_EVIDENCE:?set an external evidence directory}/reproduce-width"
```

Proposed registration for coordinator review only, contingent on exact-file
owner agreement: `Solidity.Lowering.V08.GenericWidths` — intrinsic all-width admission
composition, identity and strict-narrowing refusal; imports `Source.Types`.
The actual helper remains under the assigned tests directory. No registration
or production migration is performed by this checkpoint.

Fresh-cache reproduction passed: Source.Syntax, Source.Const, Source.Types and
the helper all exited 0; `reproduce-width.log`. The helper took 0.503 s on
that run. These isolated times are not a before/after family comparison.

## Final static checks and review closure

Layer check, generated-root check, generated-fragment check and whitespace check
pass. The documentation path checker initially refused the proposed nonexistent
module path; it now passes after the proposal was written in module notation.
It reports 115 pre-existing ambiguous references that resolve (non-strict mode).
Normal and optimized Python runs each pass all 12 tests; normal and optimized
source-integrity acceptance pass. The final independent finder and skeptic
re-reviews pass for this explicitly partial deliverable after all findings were
fixed. Evidence: `census-tests.log`, `census-tests-optimized.log`,
`census-accept.log`, `census-accept-optimized.log`, `doc-paths-final.log`,
`reviews.md` and `final-gates.json` in the external evidence directory.

Checkpoint commits are reviewable local commits only. The exported original
patch, bundle, evidence archive, final committed head and SHA256 manifest are
recorded in `/workspace/generic-v08-export/HANDOFF.md`. Overall status remains
blocked with all four original queue obligations preserved; no full completion
or runtime-gate pass is asserted.

## Successor lexical drift accounting (2026-11-06)

The acknowledged final member head `4a78ae839e026e1a9f8f575cd10fec4478e52305`
was merged only after the captured assignment and scope/retirement hashes were
verified. This is source adoption, not independent validation of external gates.
`drift.py` retains all 4428 baseline and 4430 current declaration rows plus both
full file-hash inventories. It reports 4355 equal lexical-header groups, 2 added
groups, 5 unpaired anonymous groups and 27 ambiguous duplicate-name groups. Group
counts are not declaration counts. Named keys omit namespace/section context;
no lexical equality establishes elaborated statement or semantic preservation.

Independent read-only finder and skeptic reviewed without Lean/server/builds.
Finder identified unstable anonymous-ordinal pairing; anonymous rows now remain
unpaired, and an insertion regression checks ordinal reuse. Both reviewers
confirmed the fix. Five tests pass in normal and optimized Python. A file-only
hash-change control preserves imports/body/context drift visibility. Original
and corrected reports remain separately under the successor evidence directory.
These checks do not close execution correspondence, semantic refusal acceptance,
complete family census, proof validation or same-condition Lean timing. No Lean
source, theorem, admission, toolchain, resource guard or frozen pin changed.

### Checked execution consumers in the existing test module

The original execution draft is preserved off Git. Its six additive declarations now live in `tests/h62/item4/generic-v08/IntrinsicWidths.lean`, avoiding an unregistered `tests` import prefix under the approved per-file Lake gate. Existing width declarations remain unchanged. `source_execution` consumes the actual published evaluator law; `joint_execution` consumes the complete actual-client result and reached local relation. Binary/maximal equalities are proof-term instance identities, with separate fixture field equations; they are not independent target-run proofs. Full generic-family correspondence, refusal coverage, migration-overlay acceptance and matched performance measurements remain open. Cache seeding was skipped; the environment toolchain was activated with one thread.

Actual axiom reports retain the five original axiom-free width declarations. The new source/joint execution consumers and two instance identities depend on `propext`, `Classical.choice`, and `Quot.sound` through the existing producers; both input-field equations are axiom-free. No new axiom declaration is introduced. The preserved standalone draft has the same qualified names and must remain unregistered; do not import both copies. The final focused run took 2.245 seconds with one Lean process and 812314624 bytes sampled aggregate peak RSS. These are focused-check observations, not matched full-family performance acceptance or a full gate.

## Explicit resume after coordinator integration

The coordinator explicitly requested merging `origin/master` and continuing,
superseding this worker's prior local retirement disposition. The checkout was
already clean at published lane head `c6b1d20e933b8b4a822442dcb4676798d7dc7cce`,
which contains retirement head `4a78ae839e026e1a9f8f575cd10fec4478e52305`.
Fetched and verified the published ancestry, then fast-forwarded the original
lane branch to `20e492ee99a3fa8679aa526de0b6e731d85e4134` without conflicts.
No new/reset goal, push or default-branch write was performed. Coordinator
reported touched/Bridge gates passed upstream; these are not new local gates.

Independent authorized census backfill continues under the original additive
scope. The current V08 family has 221 files and 4,430 declarations. All 220
original files and 4,428 original declarations are unchanged. The sole added
module is `Solidity.Lowering.V08.CallableBodyPremises`, with `Inputs` and
`complete`. That producer-premise contract does not itself prove a populated
execution witness or discharge this lane's correspondence obligations.

New `audit_current.py` reports original integrity and every current addition;
it does not weaken or replace strict `accept.py`, which still correctly refuses
an expanded inventory. Four new addition/mutation/removal tests pass normally
and under optimized Python; all twelve prior tests pass. Separate read-only
finder and skeptic reviews pass, with no Lean processes/server or source edits.
The report and complete current inventory stay off git with SHA256 in the report:
`/workspace/generic-v08-evidence/resume-20e492ee9/current-audit.json`.
Commands and outcomes: that directory's `verification.json`.

No new Lean proof, trust pin, source definition, frozen statement or budget
change. Historical SortCheck and Roadmap axiom-guard source files are unchanged;
known heavy failures were not rerun. The all-width admission helper remains
isolated backfill, not execution/correspondence proof. Original queue steps 2–4
and runtime/elaborated validation of step 1 remain unfinished. Waits continue
for the SortCheck migration and the axiom-preserving Roadmap prerequisite fix.
H82 removes the former proof-only exact-file agreement wait. No automatic
completion or passing family runtime gate is inferred from the merged work.

Successor merge note: both independent documentation updates are retained as historical reports. This merge does not resume any retired goal or alter the H82 chain ownership supplied by coordinator messages.

## Scheduled rebaseline and portable invocation (2026-11-07)

Coordinator-reported merged lane head `f050ca921ad94ff44b0378f28838f989a5fd0398`
is an ancestor of fetched `origin/master` at
`4f0a2d6abe3a920d8c5a20c8c06d373a1014824d`. The original lane fast-forwarded
cleanly to that published baseline; no reset, rebase, push or master write.
Coordinator's touched-gate PASS/review MERGE is upstream evidence, not a new
local runtime result.

Live examples above accept caller-supplied toolchain/archive/evidence locations.
Set all three variables to absolute paths, with the evidence directory outside
the checkout; create that directory before the census write command. Commands
in those examples run from the checkout root. The scripts themselves locate
that root from their own files. Existing absolute paths in historical prose are
original VM evidence coordinates and are retained for retrieval; frozen prompt,
scope and retirement captures are unchanged.

The portability checks launch the real audit CLI from an unrelated temporary
working directory using a relative external output path, and launch reproducer
help there without installing or running Lean. They verify root discovery and
complete output accounting; they do not certify that the checkout was relocated,
or claim Lean validation. They accept a genuine original-integrity refusal as
exit 1 rather than masking it as success.

No generic semantic proof or frozen interface changes accompany this portability
backfill. The source axiom-guard STOP in Roadmap remains unresolved in the
published migration notes; it is not rerun unchanged. Original execution,
correspondence, semantic negative/refusal gates and family timing comparison
remain required; no RUNTIME_GATE_PASS.


The preservation audit at this **2026-11-07 baseline fails**, as intended for
unreconciled drift: 61 original files differ, none are removed; the current
inventory has 221 files and 4,433 declarations. Header multiset comparison finds
73 original lexical headers absent in their exact old form and 78 additional
current headers. Those counts preserve multiplicity for repeated written names.
Complete original and current headers, file hashes and checksums are exported
beside `current-audit.json`; the frozen manifest and strict acceptance are not
rewritten. The unchanged-original claims in the earlier 20e492ee9 section apply
only to that historical baseline, not this one.

Examples of inherited drift: `CallableMetadata.argsFit_length` now has a map-free
parameter; `EnvironmentProjection.fundsOf` and associated statements now use
`liftBalance` rather than `liftWord`. These are not edits made by this resumed
checkpoint. No equivalence, original-statement preservation or validation in the
current type/definition context is asserted. Passing comparison/portability unit
tests mean the reporting and refusal behavior work; they do not pass the failing
source-preservation gate.

Scope question **Q-FROZEN-RECONCILE** is pending. Sources: original frozen
checkpoints 1–3 at c6f550e281a7e5affa9a99bc2cdaed556dec00e4, and integrated
4f0a2d6abe3a920d8c5a20c8c06d373a1014824d. How should the original obligations
be retained alongside current API changes? Options are (1) owning lanes supply
versioned compatibility declarations preserving the original statements while
current-master validation remains separate, or (2) validate original obligations
in an isolated frozen-source checkout and prove a separate transport bridge to
current master. Neither option approves weakened premises/exclusions, changed
axiom sets or replacement of frozen hashes. No option has been selected.

Independent read-only finder and skeptic reviews pass the audit implementation
and confirm the reported failure counts/checksums. The skeptic requested these
explicit failure/context qualifications; they are now recorded. No Lean process
or server was used in these reviews. Seven comparison tests pass normally and
optimized; two real CLI unrelated-CWD checks and twelve original scanner tests
pass. Current integrity audit exits 1 and remains an unmet gate. Known semantic
STOPs and the scope question remain recorded while independent audit work is
preserved as a reviewable checkpoint.

### Live execution-consumer diagnostic

The approved live per-file route was run on tracked `IntrinsicWidths.lean` using actual Lean4.24.0, serially under the inherited stricter 300-second bound and retained memory limits. It fails in 1.688 seconds, peak sampled aggregate RSS 810,938,368 bytes, no resource STOP: the five original width-admission headers omit the now-required `mapFree` argument of `STy.implicit`. This is current API drift, not evidence that the original propositions are false. Source bytes and frozen acceptance remain unchanged. Later execution-section info messages do not make the failed file a passing proof.

Existing Q-FROZEN-RECONCILE remains the disposition wait for retaining original obligations alongside current API changes. No statement rewrite is performed. The execution declarations are in tracked `tests/h62/item4/generic-v08/IntrinsicWidths.lean`, in namespace `Solidity.H62.GenericV08.ExecutionTransport`. A separate VM-only untracked duplicate diagnostic remains preserved locally; it is not a repository dependency and is neither registered, imported, edited nor counted as accepted execution evidence. This live diagnostic is not pinned Lean4.35 migration acceptance; known Hash/Roadmap trust STOPs were not rerun or waived. No execution correspondence, original-instance acceptance or family timing completion is claimed. Exact source, wrapper and failure log hashes are in `tests/h62/item4/generic-v08/live-execution-diagnostic-manifest.json`.
