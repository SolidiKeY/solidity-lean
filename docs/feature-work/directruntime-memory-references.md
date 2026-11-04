# Executable array memory/reference reader

Implementation and development controls are committed in this lane's packet.
The whole assignment remains blocked on ordinary A/D integration, central
registration, and fresh native/browser acceptance. Kernel validation does not
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
| Location-aware locals and allocation | Owned reader implemented; existing index/assignment recursion reused; all 84 valid fixtures intrinsically typed | A must wire the reader into the ordinary verifier |
| Controls and intrinsic proofs | 42 exact source-body box/diamond kernel controls, 12 focused controls, 84 initial-model executions, 20 malformed refusals and two intrinsic type refusals pass | These are development checks; ordinary runtime control results remain pending |
| Source-to-result and handoff | Existing source transport checked; exact API/import and normalization instructions below | Both fresh native and browser binaries, central registration, and the final full gate |

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

The ordinary `Solidity/Tools/DirectRuntime.lean` entry point still uses its
private legacy readers at this head. This lane did not edit it or Shared.
A must replace that reader use through its owned integration while retaining
the existing intrinsic obligation builder and trusted-verifier result path.
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
coverage checks confirm Reader and both proof modules are included. Cache delivery is blocked, so under
H35 no checkpoint is merge-ready solely on these passing VM gates. The
central registration and ordinary native/browser obligations above remain open.
