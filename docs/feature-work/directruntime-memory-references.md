# Executable array memory/reference reader

Implementation and development controls are committed in this lane's packet.
Consumer integration is published in `70845978ab616a63b13d0dee8b31b28893ccf591`;
Fresh native Identity and mandatory local-memory controls pass; four storage-array
diamond cases remain pending, and browser validation awaits D. Central registration is resolved. Kernel validation does not
satisfy those gates. No runtime acceptance marker is issued.

Repository: `/workspace/solidity-lean`.
Branch: `codex/solidity-directruntime-20261104/memory-references`.
Original base: `b419c3cf4f642ae519b66bebc26cdf2f7cf93574`.
Published interface dependency: `89373e34cdfd6bb5db7054b1c204d01edffc5fa7`.
The original base and published dependency are ancestors of the lane head.
The exact committed head, patch digest and absolute paths are sealed in
`tests/directruntime-20261104/memory-references/evidence/receipt.json`.
The original patch applies after merging the published dependency; it contains
only the lane's changes relative to that dependency, not the other 34 increments.
No push, default-branch merge, PR or publication was performed.

## Queue accounting

| Queue | Result | Remaining acceptance |
|---|---|---|
| Immutable model/interface inventory and waiting backfill | Existing constructors, elaboration, run, calculus and producer boundaries inspected; original compiler fixtures committed before A's interface arrived | Source/Core/physical adequacy gaps remain independent |
| Location-aware locals and allocation | Owned reader implemented; existing index/assignment recursion reused; all 84 valid fixtures intrinsically typed | Consumer wiring is resolved in 70845978; fresh native/browser controls remain |
| Controls and intrinsic proofs | 42 exact source-body box/diamond kernel controls, 12 focused controls, 84 initial-model executions, 20 malformed refusals and two intrinsic type refusals pass | These are development checks; ordinary runtime control results remain pending |
| Source-to-result and handoff | Existing source transport checked; exact API/import and normalization instructions below | Both fresh native and browser binaries and the final full gate |

The original missing-interface blocker was resolved by fetching and merging
89373e34. A's published producer is
`fcdddfcc446b5004860875f772ff6033e60c745f`, supplying Shared/Boundary and
Shared/Translate. The current blocker is integration, not an absent Reader API.
Do not create another translator, change Source semantics, or edit shared roots
or trust pins in this lane.

## Concrete API for A and D

Import `Solidity/Frontend/ExecutableAst/Memory/Reader.lean`:

```lean
import Solidity.Frontend.ExecutableAst.Memory.Reader
open Solidity.Frontend.ExecutableAst
-- Existing contract/function builders, existing intrinsic obligation builder,
-- and existing compiled verifier remain the consumers.
-- Shared.contract Memory.reader contractJson
-- Shared.function Memory.reader functionJson contractJson.compress
```

Public names in namespace `Solidity.Frontend.ExecutableAst.Memory`:
`typeName`, `expressionStep`, `expression`, `statementsStep`, `statements`,
and `reader`. All return the existing Ty/RawTy/RawExpr/RawStmt through Except.
No Lean environment, expression quotation, kernel or evaluator is an argument.

The exported reader retains Shared's typeName callback for contract state roots,
including baseline mapping support. The owned expression/statements callbacks
close over strict Memory.typeName for local/allocated primitive-array types.
For a combined control/tuple reader, select the owner by AST node/shape, then
call Memory.expressionStep with the combined recursive expression callback and
Memory.typeName; call Memory.statementsStep with the combined recursive
expression/statement callbacks and Memory.typeName. Do not indiscriminately
substitute the state-root parser into local/allocation handlers, or retry another
reader after an error. This preserves child failures and existing sequencing.
Primitive/reference parameters and specifications retain Shared's behavior.

The published `70845978` entry point imports Shared.Compose and Shared.Intrinsic,
uses the canonical executableReader, and calls the shared obligation builder.
The earlier private-reader blocker is resolved by A's producer migration; this
lane did not edit DirectRuntime or Shared. The trusted result path is retained.
D must rebuild both ordinary runtimes from that integrated head and execute the
actual source controls; a listing/ready result is not verification.

Use `compileFixture(...).rawAst` / `.rawAsts` from the existing
`scripts/solc-ast.mjs` API. The trimmed `.primaryAst` deliberately drops the
non-UDVT typeIdentifier and tryCall metadata required by the new reader.
The full outputs retain it; no trimmer change or shared edit is necessary.
Restore signed builtin referencedDeclaration IDs using the existing compiler
transport convention (unsigned values at or above 2^31 subtract 2^32 for this
pinned compiler). `prepare-admission.cjs` records raw and normalized digests.
Retain compiler pin, source digest and source selection throughout the real
source-to-result path. Four fresh compilations through compileFixture verify
this transport for exact Identity in both modalities and settings; see
`evidence/source-transport-records.json`. This is external-analysis evidence,
not a compiler-equivalence theorem or an ordinary verifier verdict.

Local central-registration proposal: `registration.json` in the packet. It
proposes the Reader import in Solidity.lean and a frontend module-map row.
Shared generated roots/maps/pins were not edited. Central registration and
ordinary integration must be followed by the full required gates.

## Immutable model and admitted scope

| Boundary | Existing support reused |
|---|---|
| Surface | RawExpr.newArr takes RawTy and RawExpr; RawStmt.declMemory/declStorage take type, name and optional initializer (`Solidity/Syntax/Raw.lean`). |
| Intrinsic admission | `elabNewTy` / `elabSize` in `Solidity/Syntax/Elab/Values.lean` return the existing reference type with newArrOk proof and a simple uint size. New accepts dynamic arrays with map-free, default-wellformed elements. Fixed arrays have defaults but are not new-array constructor types. |
| Locals | `Solidity/Syntax/Elab/Arms.lean` checks the declared/allocated reference types, default/map-free evidence and storage paths. The reader conservatively admits memory/storage array locals; missing/unknown/calldata locations and primitive locations are refused. Unset storage locals and storage locals initialized with new are refused. |
| Aliases/copies | Existing elabMRhs maps matching memory paths to MRhs.alias and matching storage paths to MRhs.copy with map-free evidence. Initializer incompatibility remains an intrinsic error, never successful verification. |
| Allocation | `newArrT` in `Solidity/Semantics/Run.lean` replicates SVal.dflt with newArr_lt proving the uint length bound. MRhs.evalT uses existing copyStToMG; alias returns the same reference and unchanged heap. |
| Reads/writes | MPath.mvalT, MLoc.addrT, Val.evalT and TRun.assignMem route through the existing typed heap; unset references and missing cells fail. No second heap, index semantics or allocation interpreter was introduced. |
| Calculus | Existing Step declaration/rebinding, SoundMem soundness and MemRead spine/laws/definedness/pass components are reused. The successful proof route is Proves.fmlValid with R := RuleSet.all followed by sol_prove. |
| Modalities | Box accepts model revert; diamond does not. Panic from a reached false assert is excluded in both. Existing exhaustion acceptance is unchanged. Positive exact Identity has no such failure/exhaustion prefix and its initial-model execution succeeds. |

Strict local/new types are int256, uint256, bool and their dynamic/fixed array
combinations, including nested references represented by the existing model.
Metadata spelling, canonical identifiers, location, declaration node kind/local
flags, allocation kind/arity/constructor/result, and recursive fixed sizes
0 < n < 2^256 are checked. This range is not a replacement for solc's complete
byte-size/type analysis; valid source provenance remains required. Fixed-size
arrays are not fixed-point numeric types. Local mappings, structs, bytes,
calldata and narrow-width arrays are unimplemented here and remain unknown;
baseline state-root support is preserved through Shared.

Read-only producer reuse points include
`Solidity/Backend/MemoryOps/SourceAlias.lean`,
`Solidity/Backend/MemoryOps/SourceDeclaration.lean`,
`Solidity/Backend/MemoryOps/PhysicalReferenceStore.lean`,
`Solidity/Backend/MemoryCopies/SourceInterface.lean`, and
`Solidity/Roadmap/V16/SSCP2/NewAllocation.lean` (newData_valid, allocation_mem,
eval_new_mem, local_new_mem). V11 operation transports retain their resolution,
representation, heap-shape, bounds, capacity and arithmetic premises. MemoryCopies
V2 allocator witnesses remain necessary; uninhabited draft certificates do not
establish runtime success. No producer/backend, Source, or Core edits were made.

Semantic gaps remain separate: the intrinsic bounds failure is revert while
solc bounds failures panic; Source's allocation-size failure at 2^64 and its
nested-reference default refusal differ from the intrinsic heap. Physical
allocation/gas, complete Source lowering/equivalence and fetched-EVM adequacy
remain producer obligations. These results do not close V11/V16/MRS/CR or any
whole compiler lane, and no gap is assumed away.

## Controls and proof boundary

The 21 scenarios include exact signed Identity; reached false assertion; default
zero; alias writes including -1; false copy assumption; distinct allocations;
zero-length reads/writes; boundary reads/writes; successful empty allocation;
uint Identity; bool default and alias; fixed-array default and alias; nested
reference alias; guarded storage copy; storage alias; successful copy after
push; and an unused mapping-root regression. Each has box/diamond source and
legacy/via-IR compiler settings, totaling 84 full standard JSON AST outputs.
The compiler SHA-256 and exact version are checked before compilation.

The unannotated positive Identity diamond twin is mandatory in both fresh
ordinary runtimes. Its allocate/write/read/assert body must remain unchanged.
Reached false-assertion controls must never prove. Bounds controls deliberately
place assert(false) after an unreachable failing write: box may prove because
the failure is revert; diamond must not. Default/alias/independent-allocation
controls must execute successfully, not merely decode.

Guarded storageCopy is conditionally successful; universal diamond is false
because wellformed empty initial storage fails its require guard. Its box
remains valid. copyAfterPush exercises an actual successful deep-copy path from
empty storage, then writes memory and observes storage unchanged. At the abstract
maximum capacity its push may exhaust; the existing modality policy is retained,
not a new premise or a claim about physical gas.

`Admission.lean` passes all valid inputs through Shared.contract/function,
Memory.reader, the existing elabProgAtS.go in source mode and Prog.run on State.init.
It records 84 typed model executions: 52 success, 24 revert, eight panic.
Twenty schema mutations are refused by decoding. Two metadata-coherent invalid
initializers decode but are refused by intrinsic typing. These phase distinctions
are intentional. Initial-state runs are not universal validity proofs.

`KernelMatrix.lean` is generated from the exact fixture bodies and proves or
refutes the expected universal box/diamond property for all 42 source variants.
`KernelControls.lean` adds 12 focused statements. All 54 kernel reports use only
propext, Classical.choice and Quot.sound (`evidence/owned-axioms.json`). No new
axiom, sorry, unsafe evaluator, larger heartbeat setting, premise/exclusion
weakening or unsupported-as-success result was introduced. The generic closer
alone did not close positive diamond; the existing derivation prover does.
Kernel validation is development-only; ordinary requests must not load a Lean
environment/kernel/frontend/serialized environment. Runtime trust-boundary
validation remains A/D's required integration gate.

`manifest.json` records initial expected obligations with pending runtime fields;
`evidence/coverage.json` records the observed development outcomes separately.
Neither is a source of cached ordinary verdicts. The two ordinary runtime columns
remain pending for every case.

## Actual gates, resources and reproduction

Lean 4.24.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake
5.0.0-src+797c613; Node v24.19.0. The outer VM's 16 GiB cgroup had swap.max=max
and zero host swap, so it was not used as a Lean scope. The owned Docker scope
verifies memory.max=12884901888 and memory.swap.max=0, with one CPU,
LEAN_NUM_THREADS=1, explicit -j1 and an H1 4 GiB available-memory guard.
One retained heavy check runs at a time. No systemd-run or daemon restart was used.

| Command/gate | Actual result / evidence |
|---|---|
| fixtures.cjs | 84 compiler AST outputs, eight compiler-invalid sources, 20 malformed controls; bounded run 3.590 s, 177884 KiB peak aggregate RSS |
| source-transport.mjs | Four fresh compileFixture compilations; full metadata retained; bounded receipt and records separated |
| Admission.lean via coord per-file gate | Pass, 84 typed/executed, 20 decode refusals, two type refusals; 3.671 s, 684296 KiB |
| Reader touched build / per-file MCP | Pass; final touched build 5 s and diagnostic zero errors |
| KernelControls | Pass; 22.957 s, 1267212 KiB |
| KernelMatrix | Pass; 149.236 s, 1503532 KiB |
| KeySort | Pass; 377 taclets, 131 read-bearing, table covers 131; annotations match explicit configured rule file; 4.405 s, 679324 KiB |
| trust / layers | Pass; trust 3798 sources, 285 inventoried sites, zero findings; 565 core modules, zero forbidden reaches |
| run-lean.sh | FAIL at central registration: Solidity.lean missing Memory.Reader import; no claim that the full build passed |
| fresh ordinary native/browser | PENDING integration; no binaries/verdicts invented |

Every bounded command has command, exit, wall time, aggregate-RSS peak and guard
outcome in its evidence JSON. The initial dependency rebuild took 4010.641 s,
peaked at 3401124 KiB and had no headroom stop; the control-file stage then failed
on the test fixture's contract declaration. That failed attempt is retained and
not counted as proof validation. The fixture was corrected to a named contract.
One exploratory MCP multi-attempt launched concurrent scratch workers; it was
stopped and excluded. Subsequent retained proof trials, per-file checks and
builds ran serially. No resource stop was counted as a passing gate.

Prepare this VM's owned alternate configuration with `prepare-checks.py`, which
adds -j1 and the test library without editing tracked Lake configuration. Use
`prepare-admission.cjs` after fixtures.cjs; `generate-kernel-matrix.py` reproduces
the exact checked theorem statements. Run all Lean commands inside the verified
12 GiB/no-swap scope, with the writer lock held, using the owned runtime PATH
wrapper and the repository MCP/coord tools. Stop the MCP server before heavy
builds. The bounded-check.py guard refuses an incorrect scope or thread setting.
Exact command receipts under evidence are authoritative.

## Independent reviews and sealed handoff

Separate read-only finder and skeptic reviews used no Lean server. Confirmed
findings were fixed: guarded-copy diamond expectation, declaration-kind/local
metadata checks, fixed-length range, location-bearing identifiers, allocation
constructor identifiers, and preservation of baseline mapping state roots.
Nested compiler identifier encoding was corrected against real valid fixtures.
The source-trimmer transport issue was resolved by reusing existing rawAst APIs,
not by weakening metadata checks or editing the producer. Final rechecks and
limitations are saved in `evidence/reviews-v2.txt`.

The packet includes the original patch, this handoff, fixtures, source hashes,
source/base/head signature evidence, commands/exits/wall/RSS, registration
proposal, coverage, reviews and checksum manifest. Central registration plus A's
ordinary reader migration and D's exact fresh native/browser Identity and all
controls are still required. Positive diamond Identity in both runtimes is a
required gate, not an optional follow-up. A partial checkpoint or failed full
gate is not completion of the frozen assignment.

The final generated-source whitespace check passes. Captured raw log/tsv
whitespace is preserved through the owned .gitattributes; source checks remain
enabled. Documentation paths pass with 48 ambiguous but resolving baseline
references. Regenerating KernelMatrix is byte-identical to the checked file.


## H35 VM gate and cache shipment follow-up

At code head `e9d5ac2c8825966141f13ee9bb5a93b7fceeb179`, the owned-module
build passed again (0.609 s, 57656 KiB aggregate RSS), the 54 named
`#print axioms` reports contained only propext/Classical.choice/Quot.sound, and
the Admission controls passed again (5.434 s, 684096 KiB). These are development
model/proof gates, not native/browser results. Checks used the existing 12 GiB,
zero-swap container, one Lean thread, explicit -j1 wrapper and host writer lock.
An initial lock invocation inside the container failed before starting Lean;
the retained passing invocation uses the host lock.

The actual `scripts/coord-tools/ship-cache.sh` invocation exited 1 after
creating a cache archive and manifest: coordinator-side
`/home/ubuntu/.local/state/cloudvm-coord/poll-state.json` is absent. This VM
also lacks the coordinator catalogs/transport installation. No destination
was invented and no receipt claims delivery. `evidence/h35/receipt.json` gives
the absolute archive path and SHA256; the archive remains on this VM for
coordinator retrieval, outside Git. The script collected 1638 artifacts and
550 mappings; its counter reported `0 traces without cached outputs skipped`.
That counter excludes traces with absent mapping/outputs. Separate owned-cache
coverage checks confirm Reader and both proof modules are included. At that
checkpoint cache delivery was blocked; the H41 receipt below supersedes that
delivery blocker. Central registration and ordinary native/browser obligations above remain open.


## H41 coordinator pull receipt

H41 amends H35: leave verified packs on the VM with absolute path and SHA256;
the coordinator pulls them. Never run ship-cache.sh on the VM. Future packs
remain coordinator-pending until receipt. The coordinator now reports receiving
this existing pack and verifying its SHA256 against our report. Its receipt is
`/home/guilherme/.local/state/cloudvm-coord/receipts/memory-references-cache-received-20261105T025513Z.json`.
That host file is not directly accessible here; the evidence records the
coordinator message as provenance. The local archive was freshly rehashed and
matches `067205b0b4c324f18b8c643ad5745f63311278e842aff1ebb05d2f3c1c16fa78`.
The absolute archive path and receipt details are in `evidence/h41/cache-received.json`.

Cache delivery is therefore coordinator-received, and its transport blocker is
resolved. Historical H35 failure logs remain intact. This changes no source,
theorem, or validation result. Central registration and A/D integration, fresh
native/browser Identity including the positive diamond twin, and all ordinary
modality controls remain required before assignment completion.


## Published checkpoint adoption: 8495f1de

Merged `8495f1deb0a95dd6b9301822d8649ab76b217681` into the assigned branch at
`1160a431cb7786e1a96ebe8ecd534c7b64759d15`, preserving all owned commits.
The Reader is byte-identical to the published module. Central registration is
now resolved: Solidity.lean imports Memory.Reader, and register.sh --check
passes. Earlier missing-registration failures above are historical evidence.

Fresh VM owned-module build, 54 standard-only axiom reports and Admission
controls pass on this merged tree. KeySort passes against the explicit pinned
SolKey rules: 377 taclets, 131 read-bearing/table entries. Layer checks report
628 core modules and zero elaborator/checked-parser reaches. Commands, exits,
wall times and RSS are in `evidence/published-8495/`. All Lean work used the
existing 12 GiB/no-swap scope and explicit -j1 wrapper. The full merged gate
was not rerun here; the coordinator's published combined gate report has
separate provenance. No RUNTIME_GATE_PASS is claimed.

The ordinary DirectRuntime still has private legacy readers and refuses
reference local declarations; it does not import the Memory/Shared reader.
A's consumer migration and D's fresh native/browser source-to-result checks
remain open. New producer/interface modules do not resolve that consumer gap.
The exact API instructions above remain applicable; no parallel translator or
unowned runtime edit was introduced. H41's received pack remains preserved;
this adoption does not assert cache freshness for the newly merged tree.

The three owned module input/output cache hashes match the H41-received
packet exactly (`owned-cache-reuse.json`); no new owned artifacts need shipping.
This does not establish cache freshness for other merged modules. Separate
read-only finder and skeptic adoption reviews found no defects; neither used
the Lean server. Documentation paths and source whitespace checks pass.


## Follow-on adoption and real shared-builder control: f77cf60d

Merged published `f77cf60d3cea8f7f1db8db29cc027532b0cd3fce` into the same
branch at `ce6a4819bb8bcfdcdbae71df543e9caea2631ca2`. Owned Reader and its
existing proof matrix were preserved. The new Shared.Intrinsic interface is
now available; its reference-parameter refusal and explicit callback
dependencies are retained. The ordinary DirectRuntime still uses its private
readers and obligation builder; this publication does not wire the consumer.

Admission now imports Shared.Intrinsic and checks `Shared.obligation` for each
decoded fixture with `Solidity.Frontend.lowerBodyLoops` and the existing
`Solidity.Frontend.Problem.callPre C Γ false [] false [] true`, exactly the
producer callbacks used by DirectRuntime. All 84 typed fixtures construct a
real obligation; both incompatible initializers are refused. Both source
modalities and compiler pipelines are covered. This is formula construction,
not formula validity or an ordinary compiled-verifier verdict. No callback
semantics or producer proof was copied or changed. A can use this exact
callback application alongside the Memory.reader integration instructions.

The merged VM module build, one-file MCP diagnostics, setup-aware per-file
control, and 54 standard-only theorem axiom reports pass. KeySort again
reports 377 taclets,131 read-bearing/table entries. All Lean runs remain
serial,-j1,12 GiB/no swap with the headroom guard. The first plain per-file
attempts failed because an old materialized monolithic SolcJson.olean
conflicted with the new split cached modules. No artifact was deleted: the
owned wrapper now uses the test module's Lake-generated setup.json, matching
the successful Lake build. Failed receipts are retained separately.

H41 pickup uses `pack-cache.py`, which collects available content-addressed
trace outputs/mappings, verifies every archived member by SHA256 readback,
and never sends data or mutates mappings. Packs remain coordinator-pending
until receipt. The full merged gate and fresh ordinary native/browser
acceptance, including positive diamond Identity, remain open. Neither the
new shared builder nor these development controls discharge that boundary.

Independent read-only finder and skeptic reviewed the follow-on controls and
cache utility without a Lean server. The skeptic requested equality between
trace outputs and mapping outputs before packing; this check is now mandatory.
Fixture filenames choose the mode only inside this development harness;
ordinary source metadata-to-modality selection still awaits runtime acceptance.

The H41 pickup pack for code head `aaeca878738f29b4499f0f14017d561574767243` was created and
fully read back successfully: 1644 artifacts, 552 mappings,
571458939 compressed bytes; packing exit0,35.836 s,60980 KiB peak
aggregate RSS. All five Reader/Shared.Intrinsic/Admission/KernelControls/
KernelMatrix trace mappings and outputs are included. Delivery is
coordinator-pending. Absolute archive: `/workspace/solidity-lean/tests/directruntime-20261104/memory-references/runtime/published-f77/cache-aaeca878/cache.tar.zst`.
SHA256: `c739666161edd563c7156758216fd035855202577039ddf729364cc9101ad2ad`. Manifest, receipt, readback command and
source binding are retained under evidence/published-f77.


## Published checkpoint adoption: 9584f9e7

Adopted `9584f9e7df09f638d9e0cb8930501d1660aa4b2f` at merge
`bde0666398836312311348f35daa72e1c4ee7724`, preserving all owned work.
The publication adds Shared.Scope/control-tuple helpers but leaves Memory
and DirectRuntime unchanged. The consumer integration dependency persists.

Fresh bounded serial VM build and setup-aware per-file controls pass:84 real
shared obligations,84 initial-model cases,two incompatible initializer refusals
and20 malformed AST refusals. All54 matching-source theorem axiom reports
remain standard-only. KeySort passes377 taclets/131 read-bearing/table entries;
registration passes and641 core modules have zero forbidden layer reaches.
The actual toolchain remains Lean4.24.0/Lake5.0.0-src+797c613. No source
change or proof-budget change was needed. Evidence: `evidence/published-9584`.

All five relevant module input/output hashes still match the existing
H41 pickup pack documented above; no replacement archive is required. Its
delivery remains coordinator-pending until receipt. This is not a freshness
claim for other merged modules. The full merged gate was not rerun here.
Ordinary native/browser acceptance including positive diamond Identity remains
blocked on A/D consumer integration; no RUNTIME_GATE_PASS is claimed.


## Published composition adoption: b86ae456

Adopted `b86ae4568cef6d6226f4d170360bbb089debe3fb` at merge
`7ccb1c6a5760d6dd2c307b0b114d158e9346852a`, preserving owned work.
The producer now supplies the canonical composed reader:

```lean
import Solidity.Frontend.ExecutableAst.Shared.Compose
-- Shared.contract Shared.executableReader contractJson
-- Shared.function Shared.executableReader functionJson contractJson.compress
```

Runtime integration should use this published composition. Its recursive
dispatch reuses Memory's strict type/location checks and propagates failures;
no local composition or shared edit was added. The ordinary DirectRuntime
consumer is still unchanged and needs A's migration plus D's fresh binaries.

Admission now runs the same fixtures independently through Memory.reader and
Shared.executableReader. Each constructs84 real shared obligations,executes84
initial models,refuses two incompatible initializers and20 malformed ASTs.
Separate `model-results.json` and `model-results.composed.json` preserve reader
provenance; these are84 compiler-AST fixtures representing42 source variants,
checked by each reader. Pipeline duplicates are not independent sources.
It does not prove reader equivalence,source adequacy,or ordinary runtime
acceptance. The existing54 kernel controls remain unchanged and standard-only.

Fresh bounded VM build,MCP zero-error diagnostics,and setup-aware per-file
controls pass. The doubled development harness takes10.009 s versus6.295 s
for the prior single-reader per-file run; these are separate wall observations,
not a controlled performance comparison. KeySort377/131 passes. Commands,
exits,wall/RSS and proof reports are in `evidence/published-b86`. The new
Admission/Compose artifacts require an updated H41 pickup pack; delivery is
coordinator-pending. Full merged gates and native/browser positive diamond
Identity and all modality controls remain open; no RUNTIME_GATE_PASS.

The refreshed H41 pickup pack for code head `3c155ded9ac4a3f47639337b687bd4933d99dd88` passed
complete member-by-member SHA256 readback: 1650 artifacts,
554 mappings,571626029 bytes. Packing exit0,73.692 s,64716 KiB
peak aggregate RSS. All six relevant module mappings/outputs are included
(`cache-owned-coverage.json`). Delivery is coordinator-pending.
Archive: `/workspace/solidity-lean/tests/directruntime-20261104/memory-references/runtime/published-b86/cache-3c155ded/cache.tar.zst`.
SHA256: `0349a31155afbc11f7875a432d099070d204cae479f7b59b0e3229f39ffdb97c`.
This packet supersedes the prior pickup packet for the expanded Admission
control; prior verified archives remain preserved.


## Published checkpoint adoption: 8bf83218

Adopted `8bf8321873befa3f35ca31e97e5339a1baee93e6` at merge
`e8c38c5ec33240da6ffb6610a0c9ddf44d49527f`,preserving all owned commits.
This publication changes no DirectRuntime or executable-AST interface module.
The canonical-composition handoff above remains current; A/D's consumer and
fresh native/browser integration dependency persists.

Fresh bounded serial VM owned build,both-reader per-file controls,and54
standard-only theorem axiom reports pass. Each reader checks the same84 AST
fixtures representing42 source variants,with84 obligations/model cases,
two incompatible initializer refusals and20 malformed refusals. KeySort
passes377/131; registration passes;646 core modules have zero forbidden
layer reaches. Evidence: `evidence/published-8bf`. No owned source change
or proof-budget change was needed. Full merged gates were not rerun here.

All six module cache identities still match the existing b86 pickup pack;
its archive was freshly rehashed successfully. No replacement pack is needed.
Delivery remains coordinator-pending. This establishes no freshness for
other merged modules and no ordinary runtime verdict or RUNTIME_GATE_PASS.


## Published checkpoint adoption: 3ad22f66

Adopted `3ad22f66d8fc6431378c22e71823436c79dede7f` at merge
`49378ff880612abec20569933992b92cabc3c916`,preserving all owned work.
No DirectRuntime or executable-AST interface changed. Existing canonical
reader/obligation handoff instructions remain applicable; ordinary consumer
integration and fresh native/browser acceptance remain blocked.

Fresh bounded serial VM owned build,both-reader per-file controls,and54
standard-only matching-source theorem reports pass. Each reader checks84
AST fixtures representing42 source variants,constructs84 obligations and
checks84 initial models,with two type refusals and20 schema refusals.
KeySort377/131,registration,and648-module layer checks pass. Commands,
exits,wall/RSS are saved under `evidence/published-3ad`. No source,proof
budget,or premise changed. The full merged gate was not rerun here.

All six cache identities match the b86 pickup pack,and a fresh archive SHA256
check passes. No replacement pack is required; delivery remains coordinator-
pending until receipt. No full-tree cache freshness,ordinary runtime verdict
or RUNTIME_GATE_PASS is claimed.


## Requested rebase onto e6849d3b

Rebased the assigned branch onto `e6849d3bdf516099d20c33d3581d523449764018`
before the next commit,as requested. All13 lane commits replayed without
conflicts. Pre-rebase head `9b0c48430787af55fe1ba54a1a3633a8ea3fb75e`
remains reachable at `refs/backup/memory-references-pre-e684`; immediate
rebased head is `4343d04e4938fb4e5b2f37ba50467489b4ba38dd`. All owned
source,tests and handoff bytes were identical across that rebase. Historical
receipts and cache HEADs remain historical facts; their commits stay reachable
through the recovery ref. No goal was created or reset and nothing was pushed.

Fresh bounded serial VM build,both-reader controls,54 standard-only theorem
reports and KeySort377/131 pass on the rebased tree. Registration and650-module
layer checks pass. Same84 AST fixtures/42 source variants are checked per reader.
All six cache identities and a fresh archive hash match the existing b86 pickup
pack;no new pack is needed and delivery remains coordinator-pending. Evidence
including rebase preservation and range-diff is in `evidence/published-e684`.

The publication changes no DirectRuntime/executable-AST interface. Ordinary
consumer integration,fresh native/browser positive diamond Identity and all
modality controls,and the full merged VM gate remain open. No ordinary proof
closure,full-tree cache freshness or RUNTIME_GATE_PASS is claimed.


## Integrated consumer and isolated native validation: 70845978

Rebased the assigned branch onto `70845978ab616a63b13d0dee8b31b28893ccf591`.
The prior head764d75c2 is an ancestor,and owned files were preserved; recovery
ref `refs/backup/memory-references-pre-708` retains it. This publication also
contains A's DirectRuntime migration to executableReader/shared obligations.
Earlier consumer-blocker notes above are historical and superseded here.

Fresh native validation uses the existing producer build script unchanged,
Lean4.24.0/source797c613 and default-O2,with the exact12GiB/no-swap bound,
serial-j1 and H1 headroom guard. The first build completed its344-module Lean
target but failed before C compilation because cached dependency C was not
materialized. Automatic approval review rejected an attempt to restore shared
.lake C files outside exclusive paths. No rejected action executed. The safer
alternative is a clean detached build worktree under the owned runtime path.
All343 source bytes and cache/trace OLean identities were checked;only new C
files and an identical-source successful setup descriptor were created there.
No shared output overwrite or producer source edit was used.

The new native-source-controls runner freshly compiles84 AST fixtures from42
source variants through compileFixture.rawAst,then calls the real native
compiled verifier with metadata-selected box/diamond readings and records
source/compiler/request/binary/C/bridge identities. A protocol/modality/sourceId
error always forces failure;Identity diamond explicitly requires two cases.
Unknown and unsupported results remain gaps. Separate22 malformed/type-error
API controls are not counted as fresh valid-source cases. Runtime traces and
limited named-symbol/dynamic-link observations do not prove exhaustive binary
closure or compiler/Source adequacy. Final results follow after execution.

This VM currently lacks Emscripten and the pinned WASM leanrt/libuv/GMP stage;
only the Ubuntu build container is installed. D's dependency handoff requires
rebuilding the existing browser producer at the same source bytes and running
the fresh request packet through an actual browser worker. Boot/listing or
Node-only WASM does not satisfy browser acceptance. No browser success or
RUNTIME_GATE_PASS is claimed.


### Actual native source-to-result observations

Fresh isolated native build passed in1230.231 s,sampled aggregate peak RSS
1737064 KiB,without guard stop. Binary20962960 bytes,
SHA256 `5f642fc5771816bdf756e1158bfea934a8a1ef2b0aaf86ae4bcb4a7428503a01`.
Producer C/object reconstruction verified all206 object keys and exact14
frontend-origin candidate bodies. All source/bridge/C bytes matched the
manifest and successful cache outputs. Lean4.24.0,Lake5.0.0-src+797c613,
clang19.1.2 and hostCC14.2.0 identities are recorded.

All84 compiler-AST cases were freshly compiled from42 source variants through
the pinned0.8.34 compiler,then checked by that real native binary,with no cached
verdicts or certificates. Results:64proved,16refuted,4pending,zero protocol
errors. Both exact Identity box and unannotated positive diamond twins prove
in both compiler settings. False assertion and alias-is-not-copy controls
refute in both modes. Default initialization,alias writes,distinct allocations,
uint/bool/fixed/nested-reference cases prove. Zero/OOB read/write cases prove
under box and refute under diamond,preventing an always-revert pass.

The full native matrix command deliberately exits1:storageAlias.diamond and
storageCopy.diamond are pending in both settings. None was falsely proved.
These are proof-closure gaps,not admission failures:existing development
controls refute their universal diamond properties. SourceCounterexample's
existing primitive-storage guard at lines75/109 returns unknown for these
array-root contracts. That guard and all statements/premises remain unchanged.
No exclusion is proposed. A separate real-native gate rejects20malformed ASTs
and two coherent type-error ASTs;these22 are not fresh valid-source cases.

Traces covering all106 requests observe no serialized/source Lean environment access,
extra execve/execveat,or network syscall. Dynamic-link and named-symbol audits
pass. Fourteen frontend-origin candidates have exact compiled-body/object
provenance and disassembly for independent generic-helper classification.
These observations do not prove exhaustive forbidden-functionality absence
over all9953 retained functions,compiler equivalence,or Source adequacy.

Fresh owned-module build,both-reader development controls,54standard-only
axiom reports and KeySort377/131 pass on the integrated source. Final full
merged gates were not rerun here. The full assignment remains incomplete.

`evidence/consumer-708/D-HANDOFF.json` is the explicit dependency packet to D:
it gives the fresh84-request file,hash,case order,source/build manifest,required
actual browser-worker checks,missing pinned WASM/emsdk dependencies,and the
four preserved native unknowns. D must return fresh browser binary/worker
evidence;boot/listing and Node-only WASM do not count. No browser verdict or
RUNTIME_GATE_PASS is claimed. Original source/physical/world adequacy gaps
and producer premises remain independent and unchanged.

Independent read-only finder/skeptic reviewed the actual native binary,all206
object hashes,all84 results,22refusals,85traces covering106requests,and the D
request digest. All pre-execution runner findings were fixed before the real
run. Both classified all14 exact C bodies/disassemblies as six IO-success
initializers and eight generic equality/membership/UTF8/JSON/array helpers;
none of those14 implements forbidden frontend/kernel functionality. This
remains a candidate-specific classification,not exhaustive9953absence.

The explicit signed-int mandatory subset is44/44 decisive as expected
(`native-mandatory-controls.json`):11scenarios×2modalities×2pipelines. This
subset does not replace or weaken the full84-case gate,which stays failed
with four pending conditional-storage diamonds. All required positive cases
in that full matrix are proved;no expected-negative case was proved.

H41 pickup pack for checkpoint `c9230cc9692a5974728959907afa1f60733409ad` passed complete archive
readback: 1707 artifacts,573 mappings,584977490 bytes.
All seven Reader/Compose/Intrinsic/DirectRuntime/Admission/KernelControls/
KernelMatrix output mappings are included. Packing exit0,69.750 s,64352 KiB
sampled aggregate RSS. Delivery remains coordinator-pending.
Archive: `/workspace/solidity-lean/tests/directruntime-20261104/memory-references/runtime/consumer-708/cache-c9230cc9/cache.tar.zst`.
SHA256: `5a25d13aab46396562e7adcf9a2aa4f0bf6ce5f82ba193b0e1c68d43e6953be5`.
Native binary remains at the absolute path recorded in provenance.json and
D-HANDOFF.json,with SHA2565f642fc5771816bdf756e1158bfea934a8a1ef2b0aaf86ae4bcb4a7428503a01.
No ship-cache.sh was run;all prior verified archives remain preserved.

## H82 recovery: independent H44 packaging of available bulk

The restored checkout did not contain worker commit618dda88 or its native
packet. Exact remote fetch returned `not our ref`;no evidence was fabricated.
The missing assigned branch was recreated at pinned baseb419c3cf,then advanced
to verified published master7ae5607c. The original clean work branch remains
preserved. Full618dda88 integration/split still requires the authenticated
original commit/bundle and missing runtime assets. No retiring member scope
was edited or integrated, and no stopped/paused acknowledgement is assumed.

An independent H44 item is complete for the available published data:479
generated fixture/evidence files(4079938 payload bytes)are archived under
`tests/directruntime-20261104/memory-references/runtime/h82-h44/`. Every member
was read back and SHA256-checked;all working files remain at original paths.
Only Git tracking is removed. `bulk-manifest.json` records absolute archive
path,size,hash,coverage and retained source hashes. Functional sources,Lean
statements,proof budgets and gate scripts are byte-identical to this published
base. Local Git excludes prevent accidentally restaging the retained data;
no existing production/configuration file was changed for that exclusion.

For a fresh checkout,verify the archive hash and extract it at the repository
root before running the unchanged gates. Existing fixture/admission generators
remain available;missing data still fails the gates rather than being skipped.
No fresh Lean/native/browser gate is claimed for this tracking-only increment.
Original native/browser validation,full gates,missing worker data,and the
consolidation merge-first handoff remain open.

Separate read-only finder/skeptic reviews verified all479 preserved payload
files,the archive/hash and14 retained-source hashes;neither used Lean/server
or changed files. No findings. Documentation paths and whitespace checks pass.

## H82b authenticated recovery and completed committed-data split

The delivered bundle and D-HANDOFF hashes match the coordinator receipt. Local
bundle verification and prerequisite ancestry pass; the committed D-HANDOFF
blob matches the separately delivered bytes. Recovered head618dda88 is merged
without resetting newer work. Its four native scripts remain byte-identical.
All cumulative committed fixture/evidence bytes are preserved at original
paths and in the second archive in bulk-manifest.json, with full member hash
readback. Bulk is absent from the current Git index. Historical native/gate
results above remain historical; no fresh runtime or Lean pass is inferred.
The original untracked executable and cache remain unavailable, and browser
validation, four storage-diamond pending cases and final gates remain open.
The separately indexed frozen scope package has not arrived in this VM.

Independent read-only finder and skeptic found no defects in bundle identity,
ancestry, D-HANDOFF equality, source preservation, all814 archived payloads,
and current index exclusion. Neither ran Lean. Python AST parsing of all
three recovered Python scripts, node --check of the JavaScript script, and
git diff --cached --check pass. Reader and the three Lean controls are
byte-identical against both parents. The unnecessary recovered whitespace
exemptions were omitted; existing configuration is unchanged.

## H82b final metadata intake

The final intake archive, manifest and SHA256SUMS match the dispatched hashes;
all557 member-file hashes verify. The frozen assignment and live exclusive
scope are present and read. This chain has no retiring members and no missing
final retirements. Its merge-first head618dda88 is already an ancestor of
ce8653db. The earlier missing-metadata wait is resolved; no other chain scope
is absorbed. intake-receipt.json records exact input paths, sizes and hashes.

The original untracked native executable and executable-cache archive remain
unavailable. The restored D-HANDOFF is ready for existing coordinator routing;
no browser relay acceptance or execution is inferred. Browser validation,
conditional storage-diamond proof closure and final validation remain open.
A fresh setup probe found Docker28.4.0 available with no running containers
and no local images; Reader OLean is absent. No Lean/build ran outside a bounded
scope, and no historical gate was relabelled as fresh.

Independent read-only finder and skeptic each verified all557 hashes, five
receipt input sizes/hashes, merge ancestry and the limited metadata scope;
no findings, no Lean/build invocation. check-doc-paths.sh exits0: all Lean
references resolve, with115 ambiguous references reported. git diff --check
passes. No statement, definition, axiom, gate or budget changed.

## Integrated-master VM development gates (H86 regeneration)

Fresh origin/master fetch and merge report already up to date at2e7c1228,
which contains coordinator publication5f1459653 and prior lane7f207811.
No owned source or gate changed. Docker fallback verified memory.max=12GiB,
memory.swap.max=0; Lean4.24.0 commit797c613 and Lake5.0.0-src+797c613.
Every Lean process uses explicit-j1 under the writer lock and headroom guard.

The first build exited1 after1527.182s, peak3442104KiB aggregate RSS, because
Admission needed generated normalized fixture bytes. Reader and both kernel
controls built successfully. The unchanged generator regenerated106 inputs;
the retry passed in2.407s, peak1044512KiB. Explicit per-file Admission,
KernelControls and KernelMatrix gates passed in64.256s, peak1489104KiB.
Both readers check86 admitted and20 malformed cases;84 compatible obligations
and two incompatible initializers are distinguished. All54 theorem axiom
reports contain only propext,Classical.choice,Quot.sound. KeySort passes:
377 taclets,131 read-bearing,table covers131;10.870s,620252KiB. No guard stop.

H41 pickup pack verifies complete archive readback:1653 artifacts,555 mappings,
569342298bytes; all four owned-module output mappings are included. Eight
other traces were omitted, so this is not full-tree cache freshness. Receipt
and absolute archive/evidence paths,commands,hashes and source fingerprints
are in vm-validation-receipt.json. Delivery is coordinator-pending; no
ship-cache.sh ran. Bulk logs remain outside Git.

H86 supersedes recovery waits: original untracked executable/cache bytes are
unrecoverable provenance gaps, not outstanding artifact requests. Regenerate
needed runtime outputs. Fresh native/browser execution, four historical
storage-diamond pending cases and full final gates remain open; these fresh
development gates do not establish RUNTIME_GATE_PASS or source adequacy.

Independent read-only finder and skeptic found no defects: both checked the
raw gate records, initial failure and retry,54 axiom reports, KeySort output,
source fingerprints and cache/evidence archive hashes. Neither used Lean
or changed files. Documentation/whitespace checks pass; no source was edited.

## Fresh native regeneration after H86

Regenerated pinned Lean source797c613 under the owned runtime directory.
The unchanged native producer uses an owned prefix routing Lake through the
existing-j1 wrapper. Exact12GiB/no-swap scope, serial CPU and headroom guard
remain active. After recording the missing cc alternatives link, the supported
CC selector names /usr/bin/gcc-14; generated C/link use pinned leanc. Native
build passes637.285s, peak1679404KiB; binary20963016bytes.

Fresh solc-to-native84-case gate exits1:64proved,16refuted,fourpending. Both
exact Identity diamond twins prove; no required positive is missing and no
negative is proved. Mandatory signed-int44/44 pass. All22 malformed/type
refusals pass. No observed serialized Lean/source environment access, extra
exec or network on these requests; observations are not exhaustive absence.

Named-symbol/dynamic-link checks pass. The owned evidence helper was stale
against current producer object keys; it now verifies every complete-input
snapshot hash and matches206 exact compiled object keys, extracting14candidate
bodies. Producer code is unchanged; old failure is retained. This is candidate
body evidence, not an exhaustive9953-function absence theorem.

Native packet and raw evidence remain outside Git, with paths/sizes/hashes in
native-validation-receipt.json. Fresh browser handoff requests are regenerated.
Four storage-diamond cases remain pending, browser execution and full final
gates remain open. No RUNTIME_GATE_PASS or whole-assignment completion claim.

Independent read-only finder and skeptic verified fresh binary SHA256, all206
objects and60 build-input hashes. Exact14 C/ASM bodies retain six inert
initializers and eight generic helpers; neither reviewer inferred exhaustive
absence. No findings. Corrected helper instrumented gate passes26.875s,
1228652KiB. Both native/evidence archives pass complete member readback.
Refreshed H41 cache verifies1707 artifacts,573 mappings,588286089bytes and
all seven Reader/Compose/Intrinsic/DirectRuntime/three-controls mappings.
Delivery remains coordinator-pending, not full-tree freshness. Existing-owner
counterexample request is recorded in counterexample-owner-ticket.json; no
producer file was edited. Python syntax and whitespace checks pass.

## H70 complete finite runtime/source census

The runtime-boundary-census.py backfill guards the regression where the
previous14-candidate audit is mistaken for a complete inventory. It reuses the
unchanged producer extractor and checks the exact producer build-input path
set before every input hash. It accounts for all343 Lean source fingerprints
against committed HEAD and generated C,1631 traversed C-source fingerprints,
206 selected module/object pairs,9953 selected functions and206 initializers.
All bodies have fingerprints and retained C snapshots. All4987 closed values
also have explicit initializer and initializer-body fingerprint rows. This is exhaustive
enumeration under the existing extractor, not proof of its C-parser completeness.

All14789 defined and298 undefined ELF symbol rows are retained. Of8405 text
rows,3783 lack an exact selected-generated name; these represent3255 distinct
names. All3255 are inventoried:3249 have name-based input-object/archive
candidates and six do not(_start,_init,_fini,__do_init,__do_fini,compact_initialize).
Matches are candidate origins, not a recovered linker map. Six current dynamic
libraries and16 pinned static archives are fingerprinted. The bridge object,
bridge C and generated initializer source receive explicit retained-input
fingerprints. No row is filtered out by an approval/safety classification.

The final census passes35.998s,1230236KiB aggregate RSS in the exact12GiB/
zero-swap serial scope with existing headroom guard. Five isolated refusal
controls pass0.602s,30264KiB: truncated source list,wrong binary hash,wrong
build-input hash,truncated build-input set,and Python optimization disabling
assertions. Neither gate invokes Lean or executes a verifier request. Both
new scripts name their guarded regression in their docstrings(H90).

Finder found the initial input-key completeness gap; skeptic found missing
bridge/initializer fingerprint rows. Both were fixed before the final gates.
Both independent read-only reviewers then verified all223 inventory file hashes
and reconciled every count, with no remaining concrete finding. No Lean/server
was used. Bulk C snapshots/JSONL/symbol dumps stay outside Git; the archive
has complete per-member readback. runtime-census-receipt.json records exact
commands,exits,timings,RSS,source/script fingerprints and absolute archive path.

Zero forbidden lexical hits and14 origin-name candidates are observations,
not semantic absence certification. Indirect calls,native runtime functions,
dynamic code and exact link attribution remain unclassified at that level.
No ordinary runtime trust-boundary/source-adequacy theorem or RUNTIME_GATE_PASS
is inferred. H89 removes the solkey checker from new gates; earlier KeySort
outputs remain historical. Browser ticket was accepted by native-browser and
is not relayed again; live counterexample certification remains coordinator-
owned for the four pending storageAlias/storageCopy diamond cases.

The repository-wide documentation gate exits1 on four unchanged references in
three files outside this lane; exact files,hashes and references are recorded
in doc-reference-owner-ticket.json. Owned-document references and whitespace
checks pass. The global failure is preserved and no overall checkpoint/final
gate pass is claimed. No Lean source,theorem,axiom,budget or producer changed.

Final closed-value addition was independently checked by finder and skeptic:
all4987 unique rows bind matching initializer body fingerprints and all223
output hashes verify. Both report no defect; the global documentation failure
remains explicitly unresolved.

## H70 native entry classification and exact replay attribution

Replayed only the unchanged producer final link, with diagnostic map/trace and
save-temps flags in an owned output directory. The entire20963016-byte ELF is
byte-identical to the original(a3f920a74d53ea9f5201cbafa166900efd2495c65b1bd98e7c7ef26990bd8c6a).
The retained initializer object closes the earlier ephemeral-object gap.
The replay map assigns all8405 text-symbol rows to6639 unique input sections;
zero text rows remain unattributed. All569 input identifiers have object/member
fingerprints or an explicit linker-synthesized classification.

The six previously unmatched names are classified from actual disassembly:

| Name | Replay attribution and observed role |
|---|---|
| _start | Scrt1.o: ABI startup transfers main through __libc_start_main. |
| __do_init | clang_rt.crtbegin.o: guarded exception-frame registration. |
| __do_fini | clang_rt.crtbegin.o: guarded DSO finalization/frame deregistration. |
| _init | crti.o prologue and optional weak profiling hook; crtn.o return tail. |
| _fini | crti.o/crtn.o platform finalization prologue/return. |
| compact_initialize | Retained initialize.o: dispatcher to206 rewritten module initializers. |

All206 dispatcher calls match both retained C source and actual assembly.
Zero-size init/fini symbol extents are not invented; both section input
contributions remain recorded. The map is exact input-section attribution for
a byte-identical replay, not reconstruction of the historical link process.
Weak/dynamic callbacks are not declared semantically harmless or excluded.

Full attribution gate passes4.495s,244804KiB in12GiB/no-swap serial scope.
Six refusal controls pass0.602s,48240KiB: missing range,overlapping ranges,
truncated input domain,changed original ELF,changed census fingerprint,and
Python optimization disabling checks. The first overlap fixture incorrectly
appended a duplicate outside the text section and failed; skeptic identified
it, the duplicate now sits beside the real startup entry, and the failed
receipt/maps remain preserved. Finder and skeptic verified the fix and all
six results, with no remaining finding; neither invoked Lean/server.

Bulk replay ELF/map/objects/disassembly and negative evidence stay outside Git.
linker-attribution-receipt.json records exact commands,exits,wall/RSS,script
hashes and archive path/size/hash with complete member readback. No producer,
Lean source,theorem,axiom,budget or trust boundary changed. No semantic absence
certification or RUNTIME_GATE_PASS is claimed. Existing browser,live four-case
certification and relayed documentation waits remain; no duplicate ticket.

Finder and skeptic also verified final archive/member hashes and compact
receipt consistency. Owned-document paths and Python syntax/whitespace checks
pass. The four unchanged global documentation failures remain with the
existing relayed owners; they were not masked or re-run unchanged. Exact
browser handoff and request-journal hashes still match the accepted bytes.

## H71 exact-journal browser report intake

Fetched native-browser owner headcc62220dcf1a47771536d75599b0ef588d143d62
without merging or editing that lane. Both published replay/reconciliation
manifest hashes match the authenticated dispatch. All343 runtime Lean source
fingerprints match our native build at both owner build0140eb13 and owner
headcc62220; bridge and closure script hashes also match. The local original
537822-byte,84-request journal retains SHAae658ff7, and the committed harness
retains SHA63a01fa7. Earlier field-only reconciliation had zero exact-object
matches; the subsequent exact-wire replay report has84. They are distinct.

The owner reports real native/Chromium WASM replay with64proved,16refuted,
fourpending per backend,including mandatory positive Identity diamond and
paired controls. This clears the functional execution wait by owner report.
Its gate used revalidated prior fresh H81 binaries, not new builds for this
replay;141.646s is functional gate time,not benchmark acceptance. No unchanged
STOP is rerun. Four diamond cases and original whole-lane limits remain.

Local metadata/source/journal checks pass1.806s,15764KiB in12GiB/no-swap
scope. The owner's exact handoff and two raw evidence archives are absent on
this VM. Executed harness SHA37be7c06 and reported report-only lineage cannot
yet be independently checked here from raw bytes. The local committed harness
SHA is verified; no parent-commit equality or local browser execution is
invented. Current exact artifacts are requested through the existing owner
channel in browser-result-artifact-request.json, with source/destination paths
and hashes. This requests evidence delivery, not another execution or build.

Bulk copied metadata/source fingerprints stay outside Git, sealed with complete
archive readback. browser-result-intake-receipt.json records commands,scope,
local checks,owner-reported results and missing raw evidence separately.
Finder/skeptic report no intake defect; neither used Lean/server. No producer,
Lean source,theorem,axiom,budget or trust boundary changed. No source/compiler
preservation,universal machine correctness or RUNTIME_GATE_PASS is claimed.

Final finder and skeptic independently verified the metadata archive hash,
all seven members,checker hash and receipt boundaries. No findings. Owned
document paths,Python syntax and whitespace pass; unchanged global reference
failures remain with their existing relayed owners.

## H77 exact handoff delivery and H30/H86 historical status

The current native-browser handoff is now physically present at the requested
owned inbox path. Its7130 bytes match SHAce3b211c7482f7c23761032aef098129c97152578eae9a6cb0484ab7ed594fe0.
Independent intake checks reconcile its owner/build heads, gate command/exit/
wall/resources and all decisive fields with the authenticated Git manifests.
The local metadata gate passes1.807s,15172KiB in12GiB/no-swap scope.
This verifies the delivered report, not execution of its absent raw evidence.

The replay and reconciliation raw archives remain undelivered. Executed harness
bytes and original-wire/results inspection remain pending. H71 already routed
the exact request; H77 fulfills only the handoff file, so no duplicate request
or runtime/build/STOP rerun is issued. The local status distinguishes verified
handoff from incomplete raw evidence. browser-h77-intake-receipt.json records
that boundary and seals the metadata/handoff archive with full member readback.

Repeated H82b notice is source recovery only:618dda88 remains an ancestor,
its verified bundle/D-HANDOFF and full committed-data H44 split are retained.
The original untracked direct-check and cache-c9230cc9 bytes are explicitly
UNVERIFIABLE underH30/H86,not recovery waits. Their old hashes remain reported,
not locally verified. Regenerated native/cache artifacts have separate actual
hashes and do not retroactively verify the lost bytes. bulk-manifest.json now
also labels historical source/gate hash scope rather than treating old rows as
current-tree pins. No recovered or archived data was discarded.

Finder and skeptic verified these distinctions with no findings; neither used
Lean/server or reran the browser. No Source/producer/theorem/axiom/budget/trust
change,source/compiler preservation or RUNTIME_GATE_PASS is inferred. Four
live storage-diamond certifications and relayed global documentation failures
remain open alongside the two current raw-archive waits.

Final finder/skeptic packaging review verifies all eight metadata archive
members and receipt flags. No findings. Owned documentation references,Python
syntax and whitespace pass; the unchanged global failure remains relayed.

## H77 exact raw archive inspection

Both requested current archives are delivered and locally hash-verified
(da15f10b replay,40436ffb reconciliation). Safe extraction verifies every
member type/path,unique name,manifest size and hash:197members,195payload
files. Exact archived incoming handoff/journal bytes match our originals.
Saved browser wires reconstruct the entire537822-byte journal byte-for-byte;
all84 selectors,wire hashes and native stream/inventory/browser result objects
reconcile. Counts remain64proved,16refuted,fourpending per backend. Exact
Identity diamond is positive in both compiler settings on both backends.
This inspects recorded native/Chromium execution;it does not run new queries.

The executed harness decompresses to SHA37be7c06 and the committed harness
matches63a01fa7 and owner Gitcc62220. Their sole changed line initializes the
report boundary field;remaining lines match. The authenticated committed owner
checker419791ae is reused only for data comparison/selector helpers;no older
checker execution is inferred. Companion source/header/fixture hashes and
recorded WASM boot/backend/environmentImports fields are checked separately.

There are72 concrete fixture halt expectations(48success,16revert,8panic),
plus12conditional labels. They are metadata,not72 independently observed
runtime halt fields. The first inspector assumed every label was concrete and
failed;that attempt is retained. Corrected inspection passes0.201s. Kernel
rusage records self20744KiB and child maximum15416KiB,separate maxima;the
0.2s aggregate sampler missed this short process and reported0. All work ran
inside12GiB/no-swap scope. No browser/build/benchmark/STOP gate was rerun.

Finder and skeptic independently checked all195payload hashes and exact
wire/result/harness lineage with no findings;neither used Lean/server.
Both raw-archive waits are cleared. Bulk and exact archives remain outside Git;
browser-raw-inspection-receipt.json records reproducible commands,hashes and
sealed evidence. Historical lost binary/cache remain UNVERIFIABLE.

The already-present68fd8400 master merge was preserved. Fresh origin/master
e8247d92 and code were checked before this item;the missing SourceCounterexample
extension is not present. The refreshed global documentation check exits1
with five missing references. PanicBytes prior reference is resolved;three
prior references remain and two new references are routed through
doc-reference-master-update.json. No checker policy or source is weakened.
Four live diamond certifications,source/compiler preservation,universal
machine correctness and original final gates remain open;RUNTIME_GATE_PASS
is not claimed. No other completed census/classification work was repeated.

Final finder/skeptic packaging review verified the16-member sealed evidence
archive,inspector hash and current documentation routing. No findings. Owned
references,Python syntax and whitespace pass;global five-reference gate fails
as recorded. No unchanged browser/build/STOP gate was rerun.


## Authenticated V1 producer consumption and retained inputs

Fresh origin/master5414256fdf7b78e8debe5e571c7af06ee55a5563 was merged
before this item; producer9992f6906 is its ancestor. The coordinator identifies
dafny-parity as the live certification owner. V1StorageCases.lean imports the
four original pinned storageAlias/storageCopy diamond fixtures in legacy and
IR modes through the V1 origin companion, declares their scoped obligations,
and calls the candidate API on each actual identity formula. All four admit;
all four return no candidate and no retained certificate. The unchanged
primitive-storage guard still applies. Origin metadata is not certification.
The precise missing proof/declaration/report fields are routed in
v1-storage-owner-ticket.json to the authenticated owner. The prior generic
coordinator ownership wait is replaced by that concrete producer dependency.

The initial build failed on incorrect contract namespace names; its log is
retained. Corrected build passes in3.217s, per-file gate in4.216s, serial
Lean-j1 in verified12GiB/no-swap scope with the4GiB headroom guard. Actual Lean
is4.24.0/797c613 and Lake5.0.0-src+797c613. All eight generated theorem axiom
reports use no axioms or only propext; the two imported metadata lemmas use
propext and Quot.sound. No new axiom, sorry, theorem weakening or budget change.
Per-file MCP diagnostics are unavailable in the tool catalog; the repository
per-file gate was used. No refactor, production edit or new semantic pass.

For module-times55d74692, all260 existing files were byte-verified and packed:
the two requested indexes, all106 normalized Admission inputs and raw originals,
the42 generator source bodies and existing generator/control modules. The input
manifest preserves old expected-status fields as historical obligations rather
than new verdicts. Neither generator nor Admission was executed for this packet.
Its archive, exact index and handoff hashes are in module-times-input-ticket.json.
Consumer checkout absence was worked around by reading its exact published
Git documentation. Delivery is coordinator-pending; receipt is not assumed.

Separate read-only finder/skeptic reviews agree on the corrected probe and all
input/archive hashes. Raw logs/fixtures/cache remain off Git; v1-storage-receipt.json
seals the evidence and partial development-module cache for coordinator pickup.
Four storage diamond certifications remain pending; existing native/browser
results and historical UNVERIFIABLE bytes are unchanged. RUNTIME_GATE_PASS,
source/compiler preservation and whole-assignment completion are not claimed.

Final packaging reviews found no issue; global documentation paths pass with
143 resolving ambiguity warnings. No checker policy changed.
