# H62/H63 Tools migration overlay — blocked

Owner: `solidity-h62-6-20261106/migrate-tools`.
Repository: `/workspace/solidity-lean`.
Branch: `codex/solidity-h62-6-20261106/migrate-tools`.
Pinned base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.

The old directory build and inventory checkpoint is complete within the measured
serial library-facet boundary below. The full migration is unfinished and blocked.
No original Tools file, tracked toolchain, generated root, module map, trust pin,
default branch or live producer ownership changed. No push, merge, PR, deployment,
pre-gate or freeze announcement was made. New Lean helpers remain under the
assigned tests directory and require no central registration.

## Checkpoints

| Checkpoint | State | Evidence |
|---|---|---|
| 1. Pinned census/API baseline and clean old build | Done within serial library-facet boundary | 30 files, 581 source declaration candidates, 2,283 kernel constants, 390 theorem-kind constants; full old407-module closure passes |
| 2. Official v4.35 provision and Tools adaptation | Blocked | Exact pinned archive verified; external Syntax.Raw fails before any Tools module |
| 3. New builds, acceptance and matched performance | Blocked/STOP | New prefix fails; successful KeySort sample is 20.09% slower; no complete-directory ratio |
| 4. Migration handoff | Partial | Tooling/fixture patch, frozen baseline interfaces and dependency report ready; completed migration patch awaits owner dependency and gates |

The serial measurements emit the same `.olean`, `.ilean`, and C artifacts as
Lake's library `leanArts` facet. They exclude Lake orchestration and hashing,
native object/link facets for executables, and the full repository acceptance
pipeline. They do not replace `./run-lean.sh`. No RUNTIME_GATE_PASS is claimed.

## Toolchain identity

All five coordinator-input hashes in `/workspace/h62-coordinator-inputs/sha256.json`
passed. The new archive hash equals the coordinator's `toolchain-pin.json`.
Toolchains are invoked by absolute path; tracked `lean-toolchain` remains v4.24.0.

| Toolchain | Official linux archive SHA256 | Actual Lean/Lake |
|---|---|---|
| v4.24.0 | `b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec` | Lean 4.24.0 commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake 5.0.0-src+797c613 |
| v4.35.0 | `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d` | Lean 4.35.0 commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc; Lake 5.0.0-src+eb6cafb |

Archives/unpacked assets remain off Git at
`/workspace/migrate-tools-evidence/toolchains/`. Bounded KeySort passes on both.
No v4.24 per-master cache was restored.

## Reproduction and fixed resources

From this repository, with no other Lean job and a fresh output path:

```sh
python3 scripts/h62/item6/migrate-tools/release-cache.py --output /workspace/migrate-tools-evidence/cache-release-before-old-lean-arts-1.json
python3 scripts/h62/item6/migrate-tools/serial-build.py --root /workspace/solidity-lean --toolchain /workspace/migrate-tools-evidence/toolchains/lean-4.24.0-linux --output /workspace/migrate-tools-evidence/old-lean-arts-1 --lean-arts
```

The completed old run used those paths. For the new probe, replace v4.24.0 with
v4.35.0 and the output with `new-lean-arts-1`; release-cache ran immediately before
that probe too. Do not rerun or continue migration checks while the STOP below
is unresolved. Existing output paths are deliberately rejected by the runner.

The VM has a hard 16 GiB memory cap, 4 CPU quota and no swap device. Checks ran
serially, one Lean process at a time, with `LEAN_NUM_THREADS=1`, explicit `-j1`
and repository `--tstack=131072`. A 0.2 s monitor guards 12 GiB process-group RSS and
at least 4 GiB host/cgroup available-memory reserve; these are sampled guards,
not a claimed 12 GiB kernel cgroup limit. The VM hard cap remains 16 GiB. CORE dumps
are disabled; no virtual-address limit or `systemd-run` is used. No proof budget,
maxHeartbeats or original representation changed.

`release-cache.py` holds the writer lock and advises DONTNEED only on regular
lane-owned evidence files, skipping symlinks. It preserves contents and does not
use system-global cache dropping. The policy is best-effort file-page release,
not a fully cold OS/source cache. Both measured attempts used it. Clean means
fresh isolated build artifacts, with no artifact restores or old `.lake` inputs.

## Measurements and STOP escalation

| Measurement | Outcome | Wall | Sampled peak aggregate RSS |
|---|---|---:|---:|
| Old matched-facet closure | All 407 modules pass, all 30 Tools included | 2046.698747s | 3885170688 bytes (3.62 GiB) |
| New matched-facet probe | KeySort/AST/SpecSyntax pass; Syntax.Raw fails; zero Tools checked | 16.129358s failed prefix | 1534996480 bytes |

Receipts and exact per-module commands/artifact paths:
`/workspace/migrate-tools-evidence/old-lean-arts-1/result.json` and
`/workspace/migrate-tools-evidence/new-lean-arts-1/result.json`.

Successful shared-prefix observations, one fresh-artifact sample per version:

| Module | Old wall | New wall | Wall delta | RSS delta |
|---|---:|---:|---:|---:|
| KeySort | 2.014405s | 2.419012s | +20.09% | +25.38% |
| AST | 9.278652s | 8.458920s | -8.83% | +27.06% |
| SpecSyntax | 2.214833s | 2.018575s | -8.86% | +39.78% |

STOP/escalation to migrate-root-gate: KeySort's successful-prefix wall sample
exceeds 10%. Further migration checks are halted pending root investigation.
These short measurements include 0.2 s polling overhead; they are not a full
assigned-directory regression percentage. The complete-directory delta is null
because the new build failed. No threshold exception or gate bypass is approved.
All observed prefix resource increases are reported in
`/workspace/migrate-tools-evidence/comparison-prefix.json`.

## Exact typed dependency request: DEP-SYNTAX-RAW-435

Owner: Syntax migration lane via migrate-root-gate. Exact file:
`Solidity/Syntax/Raw.lean` at the pinned base. Request an owner-reviewed migration
of its String/Slice API uses at lines 597,650,665,682,684, preserving exact public
types, semantics, visibility and proof budgets. Supply consumption instructions
compatible with isolated-lane no-merge rules. No ownership transfer or edit to
that outside-scope original has occurred here.

New Lean reports `String.drop` returning `String.Slice` where String is expected,
missing `Slice.toList`, missing `String.dropRight`, and a changed first-class
`endsWith` application. Exact new matched-facet failure log:
`/workspace/migrate-tools-evidence/new-lean-arts-1/Solidity.Syntax.Raw.log`.
All 30 assigned modules transitively depend on this file. No relay.sh is available
in this checkout; the coordinator retrieves the saved request and report at
`/workspace/migrate-tools-evidence/cross-directory-dependencies.json`.

## Frozen statements, checked interfaces and axiom audit

`census.py` finds 30 source modules, 581 declaration candidates and 52 distinct
direct imports outside Tools. Nested comments, strings, character literals,
continued strings and same-line attributes have negative controls. This source
census alone is not an elaborated certificate. Whole-file SHA256 checks against
`git show` prove all 30 original files remain byte-for-byte identical to the base,
including all original statements, cases, bodies and budget options.

`tests/h62/item6/migrate-tools/ApiInventory.lean` inspects the checked old environment by recorded declaring
module, including root-namespace extensions and private/generated constants.
`wasOriginallyTheorem` handles original kind under the module system. It matches
all 31 explicit source theorem candidates, and separately audits all 390 owned
kernel theorem-kind constants. Both axiom unions are exactly
`Classical.choice`, `Quot.sound`, `propext`; no sorryAx or native trust shortcut
appears in either union. All 2,283 kernel declaration type representations are
captured. This is ordinary Lean checking/introspection, not lean4checker replay.

`normalize-api.py` requires exact module/theorem coverage and binds its input log
to the unique successful inventory module row and source path in its complete
receipt. It records SHA256 hashes for log, census, receipt, generator source and
normalizer source. Seven controls reject missing/duplicate modules, missing
source/generated theorem audits, unrelated receipts and mismatched logs, and
confirm that changed types produce different fingerprints. The initial six scanner/resource controls also pass.

Frozen data: `/workspace/migrate-tools-evidence/frozen-kernel-interfaces-old.json`.
The hashes are toolchain-specific type-representation hashes, including generated
names; they do not certify cross-version semantic equality or authorize excluding
any original declaration. Inventory receipt `api-inventory-old-3/result.json` is
explicitly non-clean and reuses only this lane's unchanged checked old artifacts;
it provides no performance comparison.

## Isolated fixture proofs and external-test boundary

`tests/h62/item6/migrate-tools/ApiFixtures.lean` checks actual expression construction, instantiation, evaluation,
diagnostics and rejection of an ill-typed application. This is metaprogram
execution, not a theorem proof. It passes both toolchains.

`tests/h62/item6/migrate-tools/StringReference.lean` retains the old operations at the two identified Tools
printer sites. `tests/h62/item6/migrate-tools/StringFixtures.lean` contains new Slice materialization candidates,
eleven matched example/negative cases and three universally quantified proofs:
`slice_chars`, `definitionKey_chars`, `ruleLabel_chars`. They cover every string,
all prefix/suffix lengths and all wrapper branches for the new candidates. Each
proof's axiom printer reports exactly the three standard axioms above. No proof
budget is raised. This is not a universal old-version/original-function equivalence
proof, and no original printer has been edited or certified by these fixtures.

Final fixture evidence: `fixtures-old-3/result.json`, `fixtures-new-4/result.json`
and `string-spec-new-2/result.json` under the evidence directory. Earlier prototype
failures are retained but never counted as passing acceptance gates.

## Independent reviews and corrected experiments

Separate finder/skeptic agents performed read-only reviews, with no Lean checks
or server. Fixed findings: four missed attributed declarations (577→581), quote
character masking, continued-string line drift, child cleanup on exception/SIGTERM
and an exit/signaling race. The interruption regression exercises KeyboardInterrupt;
SIGTERM handling was statically reviewed. Both reviewers independently checked
actual source hashes, inventory coverage/provenance and declaration fingerprints,
and found no remaining issue in the current code/artifacts. Final migration/full
acceptance review is still pending, not implied by these backfill reviews.

TermSize failed to create a thread under the first runner's extra 12 GiB
RLIMIT_AS while RSS remained low; a same-source warm diagnostic passed after
removing that limit. This supports a virtual-stack-reservation diagnosis rather
than proving its cause.
Resident-memory budgets never increased. Later -o-only checking profiles were
intentionally stopped to match Lake's -o/-i/-c library workload. Those profiles
and warm probes are diagnostic history and are excluded from accepted timings.
Warm reuse is limited to one named probe, marked `clean:false`, and assumes
unchanged dependencies; it cannot certify modified dependency trees.

## Remaining obligations and handoff

Obtain the owner migration dependency and root performance review; coordinate
exact-file Tools edits before adapting any original; preserve all original
statements/types/semantics/budgets; build every assigned new module; complete
full affected validation and `./run-lean.sh`; finish the same-settings complete
before/after comparison with STOP>10%/escalation rules; compare frozen interfaces,
perform final independent reviews and export the completed migration patch.
No declaration, premise, exclusion or observation may be weakened to unblock it.

The coordinator retrieves the original patch, bundle, handoff, evidence and SHA256
manifest from `/workspace/migrate-tools-evidence/`. The exported patch is currently
tooling/backfill only, not a completed Tools migration. The original persistent
goal remains unfinished and is blocked, not complete; do not create/reset a goal.

## H70 requester disposition

Coordinator disposition for audited head
`f5866fe2b02d4297ce0b71ae3000d7c4e5613af8`: wait for migrate-syntax's
`Solidity/Syntax/Raw.lean` migration and migrate-root-gate's disposition of
PERF-PREFIX-435 (+20.09% shared-prefix sample). Preserve STOP and all thirty
original Tools files. Owner ticket destinations in this routing pass: none.
Current-owner delivery pending: none. These routing fields do not establish
owner agreement, dependency availability or validation. Host relay journals
determine delivery acceptance; a relay itself grants none of those approvals.
The original goal, branch and limits remain unchanged. No Lean checks resume.

## H70 partial Raw owner ticket and requester relay

The coordinator supplied a partial prerequisite ticket from migrate-syntax head
`72441d298484976c48dd14b4e095c9149b852025`, source commit
`074e62c1840dd2d7ab19c95ca5d437ebfe57dbb8`, source SHA256
`a463aa0f978da5d5bae6ba5cffdfa95861a495a8d69942502b706b7b157ec506`.
The reported host Raw patch SHA256 is
`34fc66ea93a8a2c956ebb51f225b03593109239c5b46631aaa28bfb24efb2a9a`.
Its host receipt path is not present on this VM, so its bytes/hash have not been
independently verified here. The supplied diff is not applied. Thirty reported
axiom-growth entries require root review; this ticket grants no trust acceptance
and lifts no hold.

For requester head `1aa579a535f1f5e6445822acdbef2934613933e7`, the coordinator
reports relay to migrate-root-gate and migrate-syntax, with current-owner pending
none. Host journals determine delivery acceptance; relay is not agreement or
validation. Continue waiting for the Raw prerequisite and PERF-PREFIX-435
disposition. STOP, all thirty original Tools files, the original goal/branch and
all resource/proof limits remain preserved. No Lean checks resume.

## H82 final stop-and-handoff

Retirement takes precedence over generic continue wording. No further proof
implementation or unchanged timing STOP rerun is authorized. Successor is
solidity-h62-6-20261106/migrate-root-gate, responsible for integration after final
stopped/head acknowledgement. Complete original visible assignment, original
queues, exact scope, open schema-v1 waits, latest policy/provenance and verified
review-only Raw patch are committed under tests/h62/item6/migrate-tools/handoff/.
Originals remain unchanged. No H71 push permission was supplied; no push is made.
Available goal tool exposes only complete/blocked, not PAUSED; operational pause
is preserved, with no goal reset/replacement/completion or automatic continuation.

## 2026-11-07 coordinator-authorized re-baseline and static continuation

The latest coordinator instruction explicitly resumes the queue after reporting
merge/touched-gate/review acceptance. The existing lane branch was clean at
93580be8783a33b4d8b9092a2918a9e7047c8197 (already containing the retirement
checkpoint) and fast-forwarded without reset to origin/master
5da4771e63a4278ed53932ac39a032e3d7aea6ed. All prior history and stopped
exports remain preserved. This supersedes the prior operational retirement pause
for this requested continuation, not the separate trust/performance holds. No
new goal, scope takeover, push, master edit or Lean run occurred.

The tracked toolchain remains v4.24.0. Tools and Syntax.Raw still match their
pinned c6 source bytes; no accepted Raw replacement or PERF-PREFIX-435 clearing
disposition is locally available. Other imported source changed on master, so
the old c6 build and type snapshots remain historical evidence and must not be
reported as freshly validated against this working baseline. No timing STOP was
rerun unchanged.

Independent static backfill: h78-ledger.py preserves every one of the 2,283 recorded
module-owned declarations, including private/generated names, with exact old
Expr representation/universe parameters and existing interface fingerprints. It
does not infer visibility or non-theorem kinds, and leaves all new-signature and
shim evidence unset. No shim implemented; compatibility_established remains false.
Six negative/coverage controls pass, including forbidden old-only acceptance and
missing actual-shim signatures. Finder and skeptic independently verified every
record and input hash without Lean/server use; no remaining finding.

The new ledger is off Git at
/workspace/migrate-tools-evidence/h78-evidence-ledger.json. Its generator and
controls are committed under the assigned scripts/tests directories. H78 public
visibility, new exports, comparisons and any producer shim still require actual
evidence. Source-name equality or an unchanged old axiom union cannot substitute.

After this independent item the waits remain: accepted migrate-syntax Raw input
and root trust review, migrate-root-gate performance STOP disposition, and actual
old/new public generated export evidence. No further assigned independent item
can establish those facts from the currently delivered evidence. Full new build,
meaning/axiom checks, complete matched timings and final acceptance stay open.
