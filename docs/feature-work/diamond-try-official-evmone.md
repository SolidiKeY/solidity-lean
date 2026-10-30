# Official evmone 0.22 source feasibility addendum

Evidence-only continuation of [backend prerequisites](diamond-try-backend/README.md),
parent `7ec3983ce4606cb39a48cbd2fb8ebd8e690685f1`, same diamond-try branch/VM.
The coordinator positively resolved the earlier uncertain receipt as not accepted;
this is the newly authorized official-source investigation, not a repeated accepted
turn. The physical-memory [design](diamond-try-physical-design/README.md) and its
M1/P4/P5b/P8 remain design proposals awaiting review. No implementation approval
is inferred. A's observational relation, historical runner/backend instrumentation,
physical producer/D3/admission/ABI changes remain unimplemented and unapproved.

Evidence directory: `/workspace/next10-diamond-try-evidence/official-evmone`.
`requests.json` records exact requested official URLs/ref, UTC acquisition time,
HTTP status/response headers, content SHA256/size, and failed paths. The official
source archive was read in memory, not unpacked as a checkout; its whole-content
SHA256, member metadata and selected inert build/source extracts are recorded in
`official-source-archive.json`. No binary was downloaded/loaded, CMake configured,
dependency installed, library built, VM instantiated, bytecode executed or compiler
run. Static source facts, publisher metadata and future runtime obligations below
are distinct. Official responses are trusted as acquired provenance, not signed
source authenticity proofs. No new kernel theorem or axiom audit is claimed.

## Official pins actually obtained

`git ls-remote https://github.com/ethereum/evmone.git refs/tags/v0.22.0
refs/tags/v0.22.0^{}` resolves annotated tag object
`5a1a55f15e936a78e33902d7de79f6e5aa959167` to full commit
`1ea75472f771999a9430d35f382ca0117b495e41`. `tag-resolution.txt` retains stdout.
All successful raw source requests use that full commit, not a mutable tag.
Root CMake sets PROJECT_VERSION 0.22.0. Release HTML obtained through the official
ethereum URL identifies the ipsilon/evmone repository/release links; this is an
observed redirect/repository identity, not a substitute candidate version.

**There is no EVMC submodule pin in this source tree.** `.gitmodules` names only
`test/evm-benchmarks` (ipsilon/evm-benchmarks). The official archive contains real
`evmc/include/evmc/evmc.h`, `evmc/lib`, and CMake files. EVMC is vendored here:
its bytes are pinned by the evmone commit; an independent upstream EVMC revision
is not established. The actual header declares ABI13, SHA256
`16d6440c6114c0b2699884fa23778405be1b98044ee3d6b65b2f9eee5db2c39f`,
**byte-identical** to pinned Solidity1835d247's retained test/evmc/evmc.h.
This resolves the prior source/header uncertainty without treating README version
text as ABI. A future actual loader still must check the built artifact's ABI13;
header equality is not an artifact or successful-link receipt.

`release-metadata.json` extracts official asset URLs and displayed publisher digests.
The Linux x86_64 tarball's displayed SHA256 is
`ce1ee67f55f3c856aec00d8b0d0b878c47f10ccb6c7cbc74bf8e4829969983b6`.
That asset was **not downloaded**, so its contents, ABI, build provenance, runtime
CPU requirements and actual hash were not verified. Companion .sha256 asset's own
HTML digest is a digest of that file, not the archive digest. No signature or
attestation was obtained. Guessed release workflow paths404 and no .github/workflows
members in the acquired archive do not establish how publisher binaries were built.

## Source-level build closure, not a build

| Edge/options read in pinned source | Exact established dependency/condition | Remaining evidence |
|---|---|---|
| Root CMake | CMake3.22...4.2, default Release/shared, Cable0.5.0 vendored, default toolchain label cxx17-pic; evmone target explicitly requires C++20 | Toolchain label does not lower target requirement; compiler/linker versions and successful configure/link unverified |
| evmone target | PUBLIC evmc::evmc + intx::intx; PRIVATE evmone::precompiles; CPU check source for x86 architecture level≥2; default x86 level2 | CPU capability and generated flags/artifact compatibility need future build/receipt; no architecture override applied |
| intx | Hunter config0.15.0, official tag archive, SHA1 571b3f4c5a7b09135755720b478bc03f9d7ba7bb; optional local directory override exists | Archive and its transitive package recipes/toolchain not fetched/verified; no override used |
| precompiles | evmc_cpp (C++17 interface), evmmax (C++20/intx), blst::blst static imported | These are required source target edges even though host EVMHost may serve native precompiles itself |
| blst | cmake/blst.cmake ExternalProject v0.3.16, SHA256 e04805b7d6ef9e1d89b7f511a5b86136c57b455d97924d7324da2305a864673f; build.sh or build.bat, C compiler/AR/RANLIB | Archive/scripts/toolchain transitive closure not acquired or executed |
| Hunter | bootstrap v0.26.0 archive SHA1 b1944539bad88a7cc006b4f3e4028a72a8ae46d1; cache servers disabled; Release package config | Not initialized; no complete reproducible dependency build established |
| Tools/default top-level | EVMONE_TOOLS defaults on for top-level; nlohmann_json3.12.0, CLI11 2.5.0; state/testutils/tools edges | Existing exact versions/hash pins in Hunter/config; extra state dependency options below must be recorded in any future build |
| Testing/fuzzing | EVMONE_TESTING off; requires tools if enabled; GTest1.17.0, benchmark1.9.5; fuzzing forces testing/static | Test benchmark submodule full gitlink commit not established from archive; not needed for a proposed minimal engine-only closure |
| Optional state precompiles | libsecp256k1 option OFF, v0.7.1 SHA256958f204dbafc117e73a2604285dc2eb2a5128344d3499c114dcba5de54cb7a9e; GMP option OFF/find_package | These are optional tool/state edges, not asserted mandatory for engine-only build |

The smallest candidate engine closure would disable tools/testing/fuzzing in a
future explicitly approved build, retaining intx/blst/EVMC/Cable/Hunter and the
pinned core/precompile sources. This is a **proposed configuration**, not one run
or enabled here. Complete root target/link edges and declared external download
pins are inspected; dependency archives/recipes, system libraries/ABI/toolchain,
generated package configuration and the full Solidity host closure are not
reproducibly built or transitively verified. `lib/evmone/CMakeLists.txt` sets
-fno-exceptions on GNU-like compilers, ordinarily -fno-rtti, hidden visibility,
and Linux no-undefined linking (unless sanitizing). These materially constrain
any future hook: exception unwinding is not a supported integration technique.
No installation inventory or standard-interface enumeration was repeated.

## Concrete execution/observer/stop paths

Source references below are paths within official commit1ea75472; copied filenames
in evidence replace slashes by double underscores. `source-locations.json` records
line anchors and content hashes. These are static observations, not execution.

| Path | Observed source ordering | Step/stop consequence |
|---|---|---|
| vm.cpp factory/VM constructor | extern C factory noexcept; default execute baseline; set_option advanced replaces function pointer | Default baseline is source fact; runtime options must still be recorded. Advanced is a distinct path |
| baseline_execution.cpp execute | analyze(container), state acquisition/reset, cost table, tracer start, dispatch; make_result before tracer end | Analysis/setup/allocation and result copying are outside attempted-op callbacks; wall bound must include them |
| dispatch<true> | notify_instruction_start before opcode read/switch/invoke/check_requirements, only offset<original_code.size | Every reached real opcode attempt is observable in this path, including normal/STOP/INVALID/undefined/REVERT and stack/static/dynamic OOG attempts; synthetic padded STOP is skipped. This is source ordering, not tested event parity |
| check_requirements/invoke/handlers | undefined-revision check before stack/static gas; handler does dynamic checks; Result/TermResult updates status/ends dispatch | For Spurious Dragon0xfd is undefined before handler (traits say Byzantium). 0xfe invalid and allowed REVERT handler are distinct. All have prior notification in traced baseline |
| computed-goto baseline | Used only without tracer; tracer branch chooses dispatch<true> | No guarantee from a tracer added to a different backend; no hooks inferred from trace option name alone |
| advanced_execution.cpp | Entry ignores VM argument, analyzes separately, follows compiled instruction function chain; no VM tracer calls | Advanced execution cannot be claimed to share this baseline instruction observer |
| Tracer in tracing.hpp | chained synchronous void notify/on callbacks, noexcept; on_instruction_start sees const ExecutionState and const stack pointer | No return action/cancellation token/status, supported interrupt or orderly abort channel; mutating via const-cast/longjmp/throw/process-exit is not an approved substitute |
| InstructionCounter in tracing.cpp | stack of nested code views, unsigned per-op totals; no top-level reset/limit; destructor writes JSON | A counter/tracer exists, but no 5M enforcement. Totals can wrap eventually. It does not define required whole-call-tree lifetime |
| set_option opcode.count | attaches counter, then falls through to INVALID_NAME | Cannot claim successful option acknowledgement; trace/histogram explicitly return success. Source quirk retained, not patched |
| CALL/CREATE instructions_calls.cpp | noexcept host.call; child raw result, return_data/copy, status→success boolean or handle, gas/refund update; parent instruction resumes | Returning a child failure/negative status alone is not noncatchable host abort: parent can continue/catch. Missing stop must be propagated outside EVM outcomes |
| EVMC C++ host adapter | evmc.hpp Host call wrapper noexcept→Host::call→release_raw | Throwing through callback/noexcept/C ABI is not a valid orderly unwind contract; may terminate rather than preserve a usable checkpoint |
| Pinned Solidity EVMHost.cpp | call noexcept dispatches native precompiles before m_vm.execute; nonnative child uses same m_vm and explicit depth | Same VM could share one tracer object through nested baseline calls, but shared monotone budget and uncatchable stop are absent. Native/precompile calls generate no baseline opcode callback |

The exact reusable part is the **baseline pre-dispatch observer**, not an abort
interface. In the inspected official factory/options/VM/Tracer/baseline/advanced/
call source surfaces, no supported synchronous abort-before-next-instruction API
was found. This bounded source-backed absence claim is not proof that arbitrary
external tooling or another version has none. A custom tracer can observe/count,
but implementing it would still not supply a permitted abort return or host-stop
protocol. No callback, wrapper, exception escape, signal handler, instrumented
backend or engine option was added or executed.

For the original shared5M attempted-step requirement, the first disallowed real
instruction's handler/checks must not run, the parent cannot convert the stop
into success/Error/catch, and the counter must persist across recursive host.call,
new frames and same-VM callbacks until the enclosing top-level operation ends.
Setup/native work is zero opcode events, not free time. Native precompiles remain
bounded by the unchanged120s whole-process envelope, not fabricated step charges.
Baseline omits synthetic padding STOP; exact parity with the existing JS event
contract for empty code/fallthrough/exceptional attempts remains a future explicit
validation obligation. No universal event-equivalence theorem is claimed.
No claim that ordinary gas/trace-line counts satisfy5M is made. All exact original
100M allowance, gas8000,5M,120s, source/order/fullbytes remain unchanged.

## Specific missing primitive, ownership and decision frontier

Published ownership remains the optional reference tooling at
fb379ae20f10e2c92113453ddd9d40d8f2efbe09: scripts/evm-reference/replay.mjs and
scripts/tool-job.mjs, validation in docs/solidity-upstream-tests.md and
[solc-validation](../solc-validation.md). Their exact published blobs are retained
in the preceding backend provenance; no unpublished work was imported or agent
contacted. The JS step event does not transfer to EVMC. Compiler physical-byte
correspondence remains G46.02/R31, separate from this engine/host stop contract.
No published existing theorem/module is claimed to implement EVMC host abort.

B's missing primitive is now precise: an **engine-level pre-dispatch cancellation
contract plus a shared outer-operation host-stop channel**. Candidate affected
surfaces, if later specifically approved, are official lib/evmone/tracing.hpp,
baseline_execution.cpp, vm.hpp and the host-side call/execute transport plus the
optional process supervisor; advanced_execution.cpp must either have an exact
separate step contract or be explicitly disallowed for that future backend.
That is an engine/tooling change outside this source-only turn, not another Lean
physical-memory foundation or a host wrapper already authorized. An engine hook
must be reviewed for ABI/export/versioning and below-limit semantic preservation;
a host stop must not be represented solely by EVMC failure/revert/internal-error.
No exact executable signature is asserted to exist today.

The next unavoidable B choice is whether to authorize a *separate engine/host
cancellation-interface design* over this pinned source, or keep B unavailable and
retain the historical fixtures blocked. Neither option authorizes build/run or A's
R_fixture. This addendum does not re-ask the generic historical runner question.
The source pin/ABI/build-edge gaps are reduced; the abort contract is not supplied.

| Later milestone, only after explicit scope approval | Pass evidence | Fail/stop criterion |
|---|---|---|
| Cancellation interface design | Exact attempted-step semantics, no-throw action/return path, shared invocation ownership, nested propagation and non-EVM stop representation; baseline/advanced coverage explicit | Counter-only/tracing-print/throw/unreviewed status escape or budget-reset design fails |
| Reproducible artifact/host closure (separate permission) | Exact source/dependency/toolchain/options/build hashes, actual ABI13 loader result; upstream genesis/nonce/address/checkpoint/intrinsic/deposit ordering | ABI/load/dependency mismatch, incomplete pin, changed setup or budget stops before historical execution |
| Boundary tests (separate implementation/execution permission) | Before-limit behavior unchanged; limit and one-over normal/invalid/revert/OOG attempts; nested/reentrant same-budget controls; native/setup/process timeout hard-stop receipts | Any catchable host stop, late handler, reset, >120s execution or incomplete process cleanup fails |
| Original historical replay (still unapproved) | Per-source×legacy/viaIR×required historical-fork deployment/ordered call receipts, whole bytes/status/gas/steps/time/build identity; no source/gas8000/budget changes | Unsupported generator/profile, mismatch, timeout/step stop remains explicit blocked/error; no invented fixture pass |

A's fixture-local relation is still unapproved/unproved, with nonce/address/setup
obligations retained; B's pin/ABI evidence does not prove that relation. Historical
fixtures remain unexecuted. Original native12working/8blocked strictEXIT1,
reference18working/2blocked,66native/reference and140reference/frozen ordered
comparisons,217standard-only audits are retained old evidence, not rerun here.
No source fixture has become working through this source investigation.

## Proportionate validation and reviews

This is documentation/source-provenance only. No Lean edit/build/MCP/cold full
build, compiler run, original replay or axiom audit is required or claimed anew.
Artifact checks verify response/extract hashes, tag/ABI facts and protected prior
checksums; they do not prove C++ behavior, build success or runtime compatibility.
Bounded check groups use the documented writer lock, hard12GiB/no-swap, serial
LEAN_NUM_THREADS=1, disk caches and actual OS/disk headroom. No Lean -j1 invocation
was necessary. Small lock-held outer source retrievals are distinguished from
these bounded validation groups; no heavy job ran outside the group.
Final commands/exits/timings/RSS/cgroup peaks and exact current/base documentation
comparison are recorded in [validation](diamond-try-official-evmone/validation.json);
[read-only reviews](diamond-try-official-evmone/reviews.txt) record actual scope.
Raw evidence and response bytes remain in the absolute evidence directory above. Historical documentation exit1 must remain exit1
with identical20baseline findings and zero new findings before the latter is
claimed. Prior full/TestSuite/Corpus/strict/trust/MCP/217audit receipts remain
separate. This checkpoint is not original-assignment completion or integration.

Measured integrity exit0, inventory audit --check exit0, whitespace exit0 and lock/thread/resource invocation exit0. Documentation exit1 is identical20baseline/new0, verified against physical-design/final-doc-paths.log. Maximum sampled group RSS across these checks was23756KiB; largest cgroup peak23285760bytes; hard memory.max12884901888/swap.max0, no max/OOM events. These tiny static checks are not engine or future build resource measurements. Both reviewers found no additional confirmed issue in the complete draft; the source quirks they identified were retained explicitly.
