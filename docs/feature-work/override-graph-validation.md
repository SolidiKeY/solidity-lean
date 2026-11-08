# Independent override graph validation (SOL-OV / V06 G14)

## Review correction (2026-11-06)

The former final-gate orchestration did not propagate failed exit codes, and
its old control helper could rewrite pin expectations from observed output.
Those paths do not establish acceptance. Historical aggregate PASS statements
below are provenance only, not current certification. The reviewed fixed
`#guard_msgs` expectations remain committed and unchanged; the replacement
control checker compares them without editing Lean sources. Whole-lane gates
remain pending. See the review-fix checkpoint at the end for new checks.

## Status and provenance

The additive candidate implements all five callable families, independent
visible/private-aware graphs, override lists, cut pruning, original implementation
selection and whole-checker equivalence. Historical proof and differential records
are retained; current acceptance requires the corrected gates. Overall
acceptance is **blocked** on central registrations and required repository gates.
No `RUNTIME_GATE_PASS` or whole-assignment completion is claimed.

Repository `/workspace/solidity-lean`; branch
`codex/solidity-sol-20261103/override-validation`; original pinned base
`b6ba0696102a7a038afe2ed333c09dff397cc5b2`. Foundation checkpoint:
`241d97bf5f84269f462fa75e79751974dfaecb66`. Published dependency
`059eb83d4e1d494f42c532513ffbcd3e65adaf75` was adopted by merge
`1f9bff70d108c92959026d69ece9112c9ee11b17`; both bases are verified ancestors.
Pre-adoption work was preserved and hash-verified (`evidence/adoption.json`).
Only Identity was integrated upstream; this does not complete this queue.

All Source/Static/H16/H19/Core ExtCall/shared registry/build files remain
read-only. The 102 frozen Source/Static hashes still match the original base.
There is no producer-interface change or second AST. Additive equality instances
compare the existing indexed Syn and Decl, including bodies, in the kernel.

## Queue and module inventory

| Queue item | State |
|---|---|
| Reproduction and matrix | Complete: all documented false-pass families reproduced, 943 frozen compiler fixtures. |
| Independent rules/checks | Implemented: lists, diamonds, pruning, namespaces and all five callable families. |
| Proofs and consequences | 95 library theorems pass, including whole-validator equivalence, unconditional optimized equality, original selection/body/lookup and validity/identity consequences. |
| Acceptance/reviews/bundle | Owned controls and read-only reviews pass; committed handoff is being sealed. Central registration and required full repository gates remain blocked/pending. |

All modules below are under `Solidity/Frontend/OverrideValidation/`.

| Module | Role / proposed central module-map row |
|---|---|
| Identity | Original Env positions, requested/chosen declaration identity and lookup. Already integrated. |
| Attributes | Existing Source callable-family, attribute and getter-signature projections. |
| Routes | Independent occurrence-consuming routes and sound/complete finite search. |
| Graph | Visible first-owner frontier, original bases/owners/slots and reflection. |
| Compatibility | Independent visibility/mutability/virtual/body/signature obligations. |
| OverrideFrontier | Separate private-aware raw override graph; visible inheritance is preserved. |
| Pruning | Original override edges, active graph, artificial root/top, all-pairs cut vertices and retained relation. |
| OverrideLists | Required/missing/extraneous/duplicate owners, cross-family names and directional getter priority. |
| Validity | Descriptor/attribute/owner/base/C3 obligations and complete reflection. |
| Extraction | Exact typed reconstruction of root/member declarations and original bodies. |
| Selection | Independent first-scope/first-position selection and original dispatch. |
| Validator | OverrideGraphOK, validateB_iff, certificate reflection and consequences. |
| Memoized | Typed materialized tables and unconditional equality to the original candidate. |

H21 reserves the other twelve root imports/module-map rows and new trust/axiom
inventory entries for central integration. No generated root or shared inventory
is rewritten in this lane. The old override helpers baseFns, inheritedVersion,
dedupScope, ownFns and finalVersion are not used by this graph.

## Semantics, identity and trust boundaries

The independent judgment requires exact extraction, graph validity, member
namespace legality, inherited cross-family compatibility, own override legality,
resolved ambiguity and concrete implementations. validateB_iff holds for every
Env without a hidden validity premise. fastValidateB is separately named and
proved equal unconditionally. Pruning uses the general all-pairs articulation
rule, not an unproved root/top shortcut. Private declarations remain in override
refusals but are omitted from visible implementation inheritance. C3 priority is
directional for getters: a higher-priority getter can hide a different-parameter
function; the reverse is refused. Distinct declarations are never quotiented by
name/signature/body hashes.

Selection retains both original positions. dispatch_original, chosen_unique,
accepted_collected_member and owner/slot consequences state the identity and
body obligations. Identity is within one fixed Env, not cross-Env separation.
Exact typed extraction prevents omitted members or substituted same-name bodies.
AdvancedControls has nonempty kernel witnesses for all five families, genuine
certificate/dispatch proofs and omitted/substituted-body refusals. Its modifier
uses Source's original placeholder syntax. GraphControls separates kernel route
and body witnesses from executable graph/pruning pins. DefensiveControls adds
typed malformed helper inputs and deliberately rejected cyclic Source controls;
these are not Solidity-positive fixtures. All their kernel and guarded executable
checks pass. There are 135 unique guarded theorem pins: 95 library, 13 advanced,
four graph and 23 defensive controls, using only permitted standard axioms.

Lower-stage boundaries: Source type extraction/equality, placement/clashes,
nominal lookup and checked C3 order. C3 success is required. G13 body/expression
typing, constructor arguments, using-for/import resolution, G15 admission,
concrete P8 production and whole Source-to-EVM/compiler adequacy are not proved.
External compiler differential execution is not a kernel equivalence theorem.
The runner requests analysis/AST output, not bytecode generation or EVM execution. The compiler
runner requests analysis/AST output, not bytecode generation or EVM execution.
No theorem/premise/exclusion or budget is weakened; no sorry, new axiom or native
decision axiom is introduced. Failed naive/closure-cache timing attempts remain
recorded as failures. Typed vector memoization preserves the original definitions
and independent relation via explicit equality proofs.

## Complete matrix and per-arm mapping

matrix.json freezes 943 rows: full 256-row visibility/mutability products for
ordinary functions, fallback and receive; 16 getter attribute combinations;
four modifier flag combinations; named list/diamond/pruning/body/name controls.
required-controls.json prevents named rows disappearing. coverage.json lists
all 13 modules, 95 library theorems, 943 fixtures and 58 Boolean checkers.
Each checker arm now has specific relation, fixture, kernel or executable
control references, including direct defensive helpers; this is a reviewed map,
not instrumentation coverage. Source projection alternatives are separate.
make_coverage.py checks names and inventory before generating the artifact.

Compiler pin: 0.8.38+commit.1835d247.Emscripten.clang, SHA256
6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390.
All 943 expectations pass. Both replays have 943 ordered rows: 448 parsed,
495 parser-refused invalid-declaration rows. Candidate accepts 90 with zero
mismatches. Every override-control row must parse. Old G14 accepts 175 parsed
rows; replay-summary.json enumerates actual false passes with both inheritanceB
and wellFormedB true, including all four documented special-family families.
No refused compiler expectation was relaxed.

The fail-closed gate checks IDs/order/counts, hashes, strict verdict/diagnostic
shape, full attribute domains, inventory and controls. replay-manifest.json binds
the actual transitive source closure, both harness scripts, matrix/compiler
results, effective Lake configuration, successful fresh dependency build and
both output hashes. It does not rely on stale .oleans. All 25 adversarial controls
pass, including rehashed parser/semantic bypasses, missing transitive files,
resource mismatches and missing explicit serial flags.

## Runtime, commands and actual gates

Lean 4.24.0 commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b;
Lake 5.0.0-src+797c613 (Lean version 4.24.0). Per-file MCP is available through
scripts/coord-tools/lean-mcp. get_goal is unavailable; no goal is created/reset.

Heavy checks are serial, LEAN_NUM_THREADS=1 and explicit -j1, in a Docker scope
with memory.max=10737418240 (10 GiB), memory.swap.max=0 on the 16 GiB VM cgroup.
The limit leaves six GiB outside the scope; runtime-profile.json records parent
and container usage, anonymous/file/cache statistics and system swap availability.
The final observed scope peak reached its 10 GiB cap (19 reclaim-limit events),
with zero OOM/OOM-kill events. Reclaimable file cache is not free anonymous RAM. Effective config is saved as
evidence/serial-lakefile.toml. Finder caught a stale bind mount: it was refreshed
and fresh dependency/replay evidence replaced the old evidence. The gate checks
package and all five library serial flags. The writer lock is
/tmp/solidity-lean-feature-groups-20261025/writer.lock. Unimported test/docs changes
are made only under this worker's lock; no competing Lean process is started.

| Command | Outcome and decisive evidence under tests/sol-override-validation/evidence/ |
|---|---|
| python3 scripts/check-sol-override-validation.py --compiler <pinned soljson> --write-evidence | PASS 943 exact expectations; compiler-gate.log. |
| python3 tests/sol-override-validation/replay.py | PASS fresh bounded dependency build and both complete replays; replay-gate.log, replay-manifest.json, TSVs. |
| python3 tests/sol-override-validation/test_gate.py | PASS 25 adversarial controls; gate-regressions.log. |
| Repository MCP diag for all 13 library and four proof-test files | PASS zero errors; final-diag-*.log and control-gates.json include the completed defensive extensions. |
| lake env lean -j1 --tstack=131072 <Trust/GraphControls/AdvancedControls/DefensiveControls> | PASS all 135 unique guarded theorem pins and executable controls; control-gates.json and m4-proof-*.log. |
| bash scripts/check-solkey.sh with frozen SOLKEY_RULES | PASS 377 taclets, 131 read-bearing, table covers 131; annotations match; final-keysort.log. |
| bash ./run-lean.sh | FAIL at twelve missing central root imports, after layer checks pass (558 modules, zero forbidden reachability); final-run-lean.log. |
| node scripts/check-axiom-pins.mjs | FAIL inventory drift, zero axiom errors, 135 unrecorded changes including final defensive pins; final-axiom-inventory.log. |
| bash scripts/check-doc-paths.sh | PASS; 46 existing ambiguous references all resolve; final-doc-paths.log. |
| lake build Solidity (1800-second bounded checkpoint) | PENDING: environment transition interrupted its host wrapper; bounded Docker build subsequently ended at its time window without completion/available exit. Cache-only readiness exits 3; partial output is not a pass. final-core-observation.json and core-cache-readiness.log. |

final_gates.py records exact commands/statuses/durations in final-gates.json.
The interrupted library wrapper's absent status is explicitly pending; no exit
code or success is inferred. Cache-only readiness confirms more build work is
required. The frozen repository SolKey snapshot resolves the initial missing
adjacent setup pin: static TestSuite audit passes (564 functions, 552 derived,
11 refuted, zero pending, one existing excluded; two skip). Automatic strict
classification also passes (491 automatic, 61 step-budgeted, zero manual/pending),
without claiming cumulative timing. canonical-solkey-gates.json records the retry;
the original failed setup log is retained separately. Original rules/Lean outputs and resource limits are
recorded before any RUNTIME_GATE_PASS, which has not been emitted.

## Reviews and remaining handoff

Separate read-only finder/skeptic reviews cover matrix, graph/reflection,
legality/extraction/pruning and the complete candidate; neither uses Lean/server.
M1 evidence is in reviews.md. Later confirmed fixes include private bases,
non-public override variables, local/inherited cross-family conflicts, independent
fallback shape, exact extraction, directional getters, strict parser/control
separation, transitive fresh-build provenance and actual serial flags. The final
finder required per-arm controls, now saved; their checks and final finder/skeptic reviews now pass. Both reviewers
found no remaining substantive own-lane semantic, mapping or vacuity issue. No required Source representation distinction was missing.

The final handoff, original patch, output inventory and checksum-bound evidence
bundle are recorded in tests/sol-override-validation/HANDOFF.md and the final-bundle
manifest. The verified implementation checkpoint is
41b60f964fc009714008482aa5f5ee68709e6753; the final code and handoff heads are recorded
separately in the handoff/bundle to avoid a self-referential hash. Full gates remain
pending central root/axiom/trust registration and completion of the library/default
target builds. Corpus and default examples/TestSuite Lean compilation are not
claimed passed. The goal remains incomplete with those obligations open.


## 2026-11-04 dependency adoption and getter regression checkpoint

Fresh origin/master 6f3eedf0788ee1f8a3bcf230558c712ecdca04d5 is verified and
merged into this same lane as ebc91f24f7a0bb18b20242623d3e50768615993d. The
original base and accepted producer snapshot83b80fa731b3ce35be01846e06da882daab8ee78
are preserved. All13 lane Lean modules are byte-for-byte unchanged. Upstream now
registers Identity, Attributes, Graph and Routes; nine other modules remain.
The previous section's12-module count describes the earlier checkpoint.

The coordinator's rejected constant-getter finding is independently reproduced,
not applied as a semantic change: constant getters can override pure functions;
regular/immutable getters cannot. Their accepted ABI getters still report view.
The existing Attributes mutability observation is override compatibility, not
an instruction to emit ABI pure. The six sources and twelve exact product cases
in tests/sol-override-validation/getter-pipelines cover constant/regular/immutable,
pure/view bases and legacy/viaIR. Hash-pinned solc0.8.38 produces bytecode and ABI
for all eight accepted cases; four refusals are6959. This supplements the943-row
analysis matrix; bytecode generation is not EVM execution or a kernel theorem.

Fresh serial diagnostics for all13 lane modules, all135 guarded theorem pins,
the943-row checked-Source replay, and25 adversarial controls pass after adoption.
The source/static102-file freeze is unchanged. Actual Lean4.24.0/Lake5.0.0,
10GiB scope/zero swap and explicit-j1 remain checked. KeySort377/131 passes;
trust, static TestSuite and strict automatic audits pass. Full run-lean stops
at nine missing imports; shared axiom inventory has zero errors and135unrecorded
pins. Cache-only library readiness exits3; cache delivery is still pending.
No fresh cold full build or RUNTIME_GATE_PASS is claimed.

REG-01 [H23/H21; coordinator2026-11-04]: the original explicit instruction says
“Register new roots/module-map rows centrally at integration … rather than
placing shared registry edits in lane commits.” The latest general instruction
says regenerate roots while preserving original holds. REG-01 is now resolved:
the central hold remains under coordinator queue REG-OV-1104. No human scope
choice remains, and no shared write has been made. registration-proposal.json lists the exact nine
imports/area rows and135pin inventory source so this is concrete and reviewable.
The question changes no theorem, exclusion, premise or producer interface.

Evidence and review results are under evidence/resume-20261104. The original
sealed bundle remains unchanged; this checkpoint gets its own handoff/manifest.


## REG-01 resolved: central queue REG-OV-1104

The coordinator confirms the existing H21/H23 central registration hold remains.
The reviewed nine-module/135-pin proposal and resumed sealed packet are preserved
byte-for-byte; their hashes and the verbatim resolution are in
 tests/sol-override-validation/evidence/central-registration-20261104/resolution.json.
REG-OV-1104 owns the next scheduled integration: import only verified committed
modules, generate roots and area rows, validate all proposed standard-only pins
against exact imported declarations, then run fresh combined gates and reviews
before publication. Queue ownership is not import, gate or publication completion.

There is no remaining human scope question. The raw nine-import and135-pin
inventory failures and incomplete full/cache gates remain outstanding. No unchanged
full-gate retry is made. Owned implementation,95 library/40 control theorems,
943-row replay,25 adversarial controls and12 getter-pipeline controls are already
checked and reviewed; no further implementation/proof obligation is ready within
this lane's exclusive paths until central integration/cache evidence arrives.
No Source/Static/ExtCall/Lean definition or shared registration file is changed.
The goal remains incomplete; no RUNTIME_GATE_PASS is emitted.


## Scheduled dependency b419c3cf (20261104T122441Z)

Published and remote-verified origin/master b419c3cf4f642ae519b66bebc26cdf2f7cf93574
is adopted on this same branch by merge1cc6d2c725fd61048e7f66237a649e308f8dafb2,
preserving prior reviewed head5a93fc5cfaf7674e5633af4125bf25d09cbc8fad and the
original pinned base. OverrideFrontier and Pruning are now centrally imported,
joining Identity/Attributes/Graph/Routes: six of13 modules registered, seven still
pending. All13 lane module bytes remain identical to the reviewed producer.
The entire prior replay-input fingerprint is unchanged; read-only validation of
its943-row evidence passes. No new compiler/Lean execution is claimed by that
validation. The102-file Source/Static freeze and reviewed9-module/135-pin proposal
and packet hashes are unchanged. The immutable proposal remains historical;
its two newly imported leaves do not imply all135 pins or whole-lane integration.

Changed-root inspection reports the seven remaining imports. REG-01 stays
resolved and CENTRAL hold remains under REG-OV-1104; questions are empty. Only
verified committed modules may be centrally imported; exact-import pin validation,
fresh combined gates/reviews and cache transport remain required. The unrelated
new backend/Yul/producer API leaves are not needed by this G14 checker and are
not duplicated or composed into this lane. No Source/ExtCall or shared registration
write, proof/premise/budget/exclusion change, new goal, or unchanged full-gate retry
is made. Previous raw run-lean/cache/axiom failures remain preserved. No new ready
owned implementation/proof/control obligation appears, and RUNTIME_GATE_PASS or
whole-lane completion is not claimed. Current adoption evidence lives in
 tests/sol-override-validation/evidence/adoption-20261104T122441Z.


## Scheduled dependency89373e34 (20261104T182351Z)

Remote-verified origin/master89373e34cdfd6bb5db7054b1c204d01edffc5fa7 is adopted
on the same branch as merge88440487c55f89f046a7a522bf7a8fa5d7ecbe41, preserving
reviewed producer1f20b062f02daadf0edd74263493b67192196b7d and original base.
Compatibility and OverrideLists now join the six earlier imported modules:
eight registered, five pending (Extraction, Memoized, Selection, Validator,
Validity). All13 lane Lean files match the reviewed producer byte-for-byte.
The entire replay-input fingerprint is unchanged; read-only943-row recorded
execution evidence validation passes. This is not fresh Lean/compiler execution.
The102Source/Static freeze, historical9-module/135-pin proposal and reviewed
packet hashes remain unchanged. Counts in prior sections are historical snapshots.

REG-01 remains resolved with CENTRAL hold under REG-OV-1104; questions are empty.
The changed generated-root inspection reports the five remaining imports. Shared
root/area/pin writes, exact-import validation of135standard-onlypins, fresh combined
gates/reviews and cache transport remain central/outstanding. New backend and
shared executable-AST APIs are not required by this already-resolved-Env G14
checker, so no producer is duplicated or new composition introduced. No new ready
owned implementation/proof/control obligation is found. No Source/ExtCall edit,
proof/premise/exclusion/budget change, new/reset goal, or unchanged full-gate retry
is made. Raw prior gate failures are retained without relabelling or claiming
whole-lane completion/RUNTIME_GATE_PASS. Current evidence and handoff are under
 tests/sol-override-validation/evidence/adoption-20261104T182351Z.


## Scheduled dependency8495f1de (20261105T0200Z)

Published and remote-verified master8495f1deb0a95dd6b9301822d8649ab76b217681 is
adopted on the original branch by merge06ab7ac536a66b8ca4bbc01774a0ecd8a70a0fb0,
preserving reviewed producer380909e5c4bf08a398e641dd2bcfcd995734221b and original
base. Selection and Validity now join the eight previously imported leaves:
ten of13 registered; Extraction, Memoized and Validator remain central/pending.
All13 implementation bytes, the full replay-input fingerprint,102Source/Static
freeze and reviewed proposal/packet hashes are unchanged. Read-only validation
of prior943-row execution evidence passes, not a new proof/compiler execution.
The coordinator's exact-head combined core/Bridge/audit/native-CLI outcomes are
its receipt evidence, not completion of this whole lane or local cache delivery.

The temporary writer-lock directory was absent after environment startup; it
was restored before mutation. Existing owned container sol-ov-session was exited
255 and was restarted only after verifying its10GiB/no-swap settings. Current
Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b and Lake5.0.0-src+797c613
versions, memory.max10737418240/memory.swap.max0 are recorded. No proof, full build
or cache freshness is inferred from that runtime recovery. H21 cache transport
for this exact SHA remains pending its own actual receipt/verification.

Changed-root inspection reports the three remaining imports. CENTRALREG-OV-1104
hold and resolvedREG-01/empty questions remain in force. Exact-import135pin
validation, fresh combined integration gates/reviews and remaining full/cache
validation stay outstanding; prior raw failures are preserved. No unrelated
statement-grammar, VY5/H16, VX1/H38 or VC1 work is taken, no producer duplicated,
and no ready owned implementation/proof/control dependency appears. No Source,
Core ExtCall, shared registry, premise, exclusion, budget or checker definition
is changed. No unchanged full-gate retry or whole-lane/RUNTIME_GATE_PASS claim
is made. Current evidence is in adoption-20261105T0200Z under the owned test area.


## Follow-on dependencyf77cf60d

Published origin/masterf77cf60d3cea8f7f1db8db29cc027532b0cd3fce (including8495f1de)
is verified and adopted as merge3914db01069734c6de01fa549bf871d23ddb012e on the
original lane, preserving producer87c9b2db6414c3d43f3018e4b2f538207a1a284b and base.
All13 lane module bytes and the registration subset are unchanged: ten registered,
Extraction/Memoized/Validator pending. Full replay-input fingerprint is unchanged;
read-only943-row recorded evidence validation passes, not new proof/compiler
execution.102Source/Static freeze and immutable proposal/packet hashes match.
Coverage ownership is unchanged, so no new coverage, root, cache or full-gate
retry is performed; only the adoption/readiness documentation is updated.

New type-grammar ParserBasics/Checks, shared relative obligation builder,
expression-uniqueness Statement target (not proof), and existing-formula storage
havoc helper supply no original G14 dependency. No producer is duplicated or
new composition introduced. Other GateG0/VY5/VX1/V16 holds remain with their
owners; no Source/CoreExtCall write or premise/refusal/budget/exclusion change.
CENTRALREG-OV-1104 remains resolved with questions empty; exact-import135pin
validation and remaining shared registrations/full/cache gates are outstanding.
Coordinator reports first8495cache pass49successes/onecapacityskip/fivefailures
underH30recovery. This is not local cache freshness, transport success or whole
producer completion. Prior raw failures remain preserved. No ready owned
implementation/proof/control work or RUNTIME_GATE_PASS is claimed. Evidence and
handoff: tests/sol-override-validation/evidence/adoption-f77cf60d.


## Dependency9584f9e7 (20261105T0840Z)

Published9584f9e7df09f638d9e0cb8930501d1660aa4b2f is adopted on the original
branch, preserving all13 module bytes. Extraction/Validator are imported centrally;
only Memoized remains unregistered. Existing943-row source-bound evidence validates
read-only; no fresh proof/compiler/full-gate execution is claimed. CENTRALREG-OV-1104
pin validation and remaining full/cache gates stay pending; no whole completion.
H41 is retained: ship-cache.sh is not run on this VM and coordinator shipping
progress does not establish local freshness. No protected/shared source edit,
new producer, premise/exclusion/budget change or goal reset occurs. Current
adoption packet is tests/sol-override-validation/evidence/adoption-9584f9e7.


## Dependencyb86ae456: all13 modules imported

Publishedb86ae4568cef6d6226f4d170360bbb089debe3fb is adopted as
merge4f77b759902003f1de8009ad87b607fb78f8ea70, preserving reviewed4e97b79e and base.
Memoized matches byte-for-byte; all13 lane module bytes and replay inputs are
unchanged. All13 modules are now registered: root/orphan checks pass.
The shared axiom inventory still exits1 with zero errors/135unrecorded entries;
local cache-only readiness exits3. CENTRALREG-OV-1104 pin validation and full/cache
gates remain outstanding. No shared pin write or cache shipping is performed.
Read-only943-row saved-evidence validation passes; no new proof/compiler or
full-runtime success is inferred. H41 is retained. Existing premises, exclusions,
budgets, Source and ExtCall remain untouched; no new owned implementation work
is ready. Current packet:tests/sol-override-validation/evidence/adoption-b86ae456.


## Dependency 8bf83218: preserved scope and remaining gates

Published 8bf8321873befa3f35ca31e97e5339a1baee93e6 was adopted by
f71f285a05c22919dfd3e8b8ca84ee9130a21fa1 without conflicts or owned module
changes. All 13 modules remain registered. Fresh bounded root/orphan and
saved 943-row replay-evidence checks pass. The shared pin inventory still
reports zero errors and 135 unrecorded changes (exit 1); CENTRAL REG-OV-1104
remains responsible. Prior cache readiness exit 3 is historical; no unchanged
cold full-gate retry or cache-shipping operation was performed. Full final gates
remain pending. H41, proof budgets, premises, exclusions and Source/ExtCall
ownership remain unchanged. No whole-lane success is claimed. Read-only finder
and skeptic reviews and exact commands are retained in
tests/sol-override-validation/evidence/adoption-8bf83218.


## Dependency 3ad22f66: unchanged owned implementation

Published 3ad22f66d8fc6431378c22e71823436c79dede7f adopted through merge
707630d9de1077e4bf7db40145698c7264f0a222, preserving the owned branch.
All 13 modules remain unchanged and registered. Fresh bounded roots, orphans
(4127 reachable, zero orphaned) and saved 943-row evidence validation pass.
The shared inventory still exits 1: zero errors, 135 unrecorded pins. CENTRAL
REG-OV-1104 remains responsible; cache/full gates remain pending. Historical
cache readiness exit 3 was not retried; no cache freshness, fresh proof/compiler
execution or whole-lane completion is inferred. H41 and all ownership, premise,
exclusion and budget restrictions remain. Required read-only reviews and handoff:
tests/sol-override-validation/evidence/adoption-3ad22f66.


## Dependency e6849d3b: requested rebase

Rebased onto e6849d3bdf516099d20c33d3581d523449764018, preserving old
6adc875b on the owned pre-e6849d3b backup branch. Post-rebase 57a44904 has
an empty diff across every exclusive path versus that backup; the early Graph
add/add conflict retained integrated master. All 13 modules remain registered.
Fresh roots/orphans and saved 943-row replay validation pass. Shared pin inventory
now reports 614 unrecorded changes and zero errors (lane subset 135 remains
CENTRAL REG-OV-1104). Prior cache exit 3 is historical; final full/cache gates
remain pending. No fresh compiler/proof, cache freshness or whole-lane success
claimed. H41, ownership and proof constraints retained. Packet and reviews:
tests/sol-override-validation/evidence/adoption-e6849d3b.


## H44: reviewable packaging split

The user authorized removing bulk fixture/evidence data from the reviewable
increment. Pre-split acf387973a24cfd81571763c9c5228f144422918 remains on
codex/solidity-sol-20261103/override-validation-pre-H44. A single increment on
260441fd82852fc1c294e62f6818e15de6375ceb retains only existing Lean controls,
scripts, documentation, ignore rules and the bulk manifest. All implementation
and executable script bytes are unchanged; no theorem, gate or budget changed.
The 1246 formerly tracked bulk files (40668073 bytes), plus ignored historical
inputs/evidence, remain local and are archived at
/workspace/solidity-lean/tests/sol-override-validation/runtime/H44/bulk.tar.gz
(125428964 bytes). BULK-MANIFEST.sha256 records its absolute path and digest.
Historical evidence paths above refer to this VM or archive, not tracked files.
Scripts require restored inputs in a clean checkout; extraction at repository
root restores them without changing the scripts or their checks. Current head
is reported by the worker rather than embedded in its own commit.
H44 is a packaging checkpoint; original final gate and central registration
obligations remain outstanding. No whole-lane completion is claimed.

H44 validation: archive SHA256 check PASS; all 1246 removed tracked members
independently verified against original Git blobs by both read-only reviewers.
Finder and skeptic report no findings; retained Lean/Python/JS bytes and existing
implementation tree are identical. Candidate documentation paths PASS; saved
943-row evidence validation PASS; existing 25 adversarial gate controls PASS.
These packaging checks are not a fresh kernel/compiler/full-runtime gate.
Raw outputs remain in tests/sol-override-validation/runtime/H44 outside Git.


## Coordinator review fixes (2026-11-06)

Blocker 1: final_gates.py aggregates every command exit and returns nonzero if
any gate failed, including when later gates succeed. Launch errors fail too.
Both controls scripts include DefensiveControls. Blocker 2: check_controls.py
only executes the four committed guarded proof files; there is no raw-output
pin generation or tracked source rewrite. All existing Lean bytes remain
unchanged. Blocker 3: the compiler checker verifies the H44 committed SHA256
manifest, verifies consumed recorded files against that archive, and always
binds matrix/required-controls/fixture inputs, including fresh compiler mode.
`--bulk-archive PATH --restore-bulk` restores missing untracked inputs after
digest verification, refusing changed existing data, links, traversal and any
tracked-source overwrite. The archive stays outside Git under H44.

Runtime selection is explicit via `--runner 'docker exec CONTAINER'` or `--local`
(and SOL_OV_RUNNER); no container name, PATH, toolchain install or SolKey path
is assumed. Caller prepares its environment, owns writer.lock and retains the
4GiB VM reserve. Resource preflight rejects unlimited/over-12GiB memory, swap,
and missing effective package/library -j1. Live Lean/Lake checks precede MCP
and shell proofs. The replay launcher uses the same configurable runner.

Checks actually run after the fixes: nine targeted Python regressions PASS;
25 existing adversarial evidence controls PASS (test-only historical-input
mock isolates semantic tests from stale fingerprints); archive SHA256 PASS;
943 archived compiler rows PASS with frozen inputs bound. Actual corrected
check_controls.py in the existing 10GiB/no-swap container PASS for Trust,
AdvancedControls, GraphControls and DefensiveControls; all four Lean sources
remain byte-identical. The gate implementation change deliberately invalidates
the prior replay input hash: --replays exits 1, "inputs changed or are incomplete".
No production replay fingerprint or archived output was regenerated to pass.
Fresh replays and final full/runtime gates remain pending; old saved-replay
PASS claims are superseded by this explicit stale result. No RUNTIME_GATE_PASS.

Separate read-only finder/skeptic reviews found fresh-compiler input binding and
pre-MCP surviving-process gaps; both were fixed and reviewers confirmed them
resolved. Replay follow-up also binds archive inputs before execution, fingerprints the
shared runner and puts execution timeouts inside the selected environment.
Raw outputs are local in runtime/H44; no bulk
logs or fixtures were added to Git. Lean/Source/ExtCall, theorem statements,
premises, exclusions, proof budgets and CENTRAL/H41 holds are unchanged.


## H82 continuation and inheritance successor relay

Fresh narrow build (44 jobs) and both actual Source replays PASS at 4bdd5952:
943 rows each, 448 parsed, candidate 90 accepts with zero mismatch; current
checker reproduces documented false-pass families. The earlier stale replay
wait is resolved by actual execution. New bulk archive is 125428585 bytes,
SHA256 a78a6951b658780f93d634acf3da81f5734ea80f502e329c44a5eda47de29163,
at runtime/H82/validated-bulk.tar.gz; committed BULK-MANIFEST anchors it. Old
H44 archive remains intact. Eight output entries refreshed, only two bytesets
differ; frozen fixtures/expectations/member inventory unchanged. Archive-bound
--replays PASS. Fresh compiler 943 rows and getter code-generation 12 rows PASS.
KeySort 377 taclets/131 read-bearing/table covers 131 PASS. Lean 4.24.0 (797c613),
Lake 5.0.0-src+797c613; four committed guarded proof files PASS, nine regressions,
25 adversarial controls, roots/fragments/layers/trust PASS (6147 sources, 289
sites, zero findings). Incorrect initial direct trust invocation retained; its
repository wrapper corrected it. No source/theorem/budget/premise change.

Actual waits remain: central shared pins (zero errors, 4133 unrecorded, including
135 lane pins), full cache-only exit 3 and thus full final gates. No unchanged
cold build retry or VM cache shipping. No RUNTIME_GATE_PASS. Kernel proofs,
external compiler checks and replay executions keep separate boundaries.
The inheritance successor relay is accepted into the same goal. C3 head 70845978
is already an ancestor, but its original final handoff path is absent here and
its remote lane branch is not advertised. Final authenticated bundle, exact
frozen assignment/scope bytes and explicit stopped acknowledgement are still
required; no retiring scope edit/integration/stop request occurs. C3 H70 and
original queue/backfill remain open without scope guessing. Both read-only
reviews found no archive/provenance issue. Details: tests/sol-override-validation/H82-HANDOFF.md.


## H151 current status and historical gaps

The unavailable old C3 retirement runtime/seal export and historical H41 cache
payload are **UNVERIFIABLE** documented gaps, not active waits. Their original
claims remain unproven; authenticated report metadata alone is not their result.
Do not recreate a retired VM or require lost exports before continuing. Available
local/private-archive records and verified member Git/scope/stopped metadata
remain distinct from these gaps. See the H151 ledger in c3-exactness.md.

Fresh C3 per-file diagnostics and nine compiler fixtures have been regenerated
as new limited observations. They do not validate the missing historical run,
seal, timing or cache, and do not waive original acceptance requirements.
The earlier shared-pin wait was cleared by the actual zero-drift inventory check
at 77dbfca8. Current gate/source-pin owner decisions and present-day host-managed
full-runtime readiness remain open. No historical-artifact retrieval wait is
retained, no full completion/RUNTIME_GATE_PASS is claimed, and no theorem,
source, gate, premise, exclusion or proof budget changes. H145 receipts remain
private; H146/H147 shared warming remains a host responsibility.
