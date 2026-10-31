# Exact-host backend prerequisite: availability and bounded-step evidence

Evidence-only child of4b9a40542b9637be9f459ab5672014185d17b11f, same VM/thread/
branch. This answers B's concrete availability/ABI/instruction-bound question;
it does not repeat setup tracing, opcode census, maps, compilations, gas or
nonce arithmetic. No network fetch/install/build/library load/backend version
probe/engine/historical instruction/fixture execution is performed. No tracing
callback, wrapper, override, state normalization, evaluator, model relation or
profile is implemented. Original native12/8strictEXIT1,reference18/2,66/140ordered
comparisons and217standard-only audits remain retained, not new passes.
A's R_fixture, B implementation/execution, physical D3 and reference ABI producer
remain unapproved. Original sources/observations/gas8000/100M/5M/120s and all
core/callback/target/exclusion/budget meanings are unchanged.

## Actual retained closure and targeted install inventory

`install-inventory.json` records21specific paths and immediate-directory name
checks, including missing paths. No process environment, credentials, other
workers/VMs, global filesystem traversal or dynamic loader is inspected.
Candidates named evmone/evmc/soltest: **zero in those scopes**. This is not proof
of absence under arbitrary other filenames or hidden locations.

| Scope inspected | Actual evidence | What it does not establish |
|---|---|---|
| /workspace/.setup/tools; /workspace/.setup/cache | Lean4.24.0tool directory/archive; disk Lake/mathlib caches. No backend-named candidate. | Lean, compiler WASM and caches are not EVMC backends. No executable was run to probe engine version. |
| repo .lake/build/bin | solidity-lean and solkeycheck plus hash/trace artifacts. | These are existing Lean tooling, not soltest/evmone. No bytecode backend inferred from filenames. |
| repo build,deps,.deps; retained upstream root CMake/cmake/deps/libsolidity/libevmasm/evmone/.gitmodules | Explicitly absent. Repository root .gitmodules also absent. | Cannot reconstruct full host build/dependency closure from test-only extraction. Prior supplemental GasMeter.h is not a complete build tree. |
| /usr/local/lib,/usr/local/bin,/usr/lib/x86_64-linux-gnu,/usr/bin; /opt/evmone,/opt/solidity,/opt/soltest | Immediate native install names checked; no matching candidate; named /opt paths absent. | No global package/database or unknown-path absence claim. No binary hash/build provenance/runtime-supported-revision result exists to record. |

The pinned Solidity snapshot is1835d247de183f23e7b0e2bc4a50732af525b77c, archive
SHA recorded in closure-and-api.json; manifest top-level content is test-only
plus LICENSE, not root build/lock metadata. Its submodule record identifies
ethdebug-format937e3484cb4cf408a4e808d62f34285a71fece80, **not an evmone or EVMC
source pin**. Each inspected test/header/CMake file is SHA-verified against that
snapshot manifest, copied and hashed in provenance.json. Exact vendored bytes
are pinned by the Solidity commit even where an independent upstream revision
cannot be established.

Retained test/CMakeLists.txt:238 links soltest against
solcli,libsolc,yul,solidity,smtutil,solutil,phaser,Boost::boost,yulInterpreter,
evmasm,Boost::filesystem,Boost::program_options,Boost::unit_test_framework,evmc.
The evmc interface target adds vendored headers and evmc_loader STATIC(loader.c),
linking CMAKE_DL_LIBS. Root targets/compiler configuration/Boost version and
transitive external lock/build artifacts are unavailable in this extraction;
the target list is a **known direct closure edge**, not a verified complete
build. A standalone EVMHost consumer would still need included liblangutil/
libsolutil/libevmasm and other dependencies; no smaller successfully linked
closure is claimed. No build, install or new checkout is attempted.

### Version discrepancy and what the API actually guarantees

Vendored test/evmc/README.md says EVMC12.0.0. The **actual** evmc.h declares
EVMC_ABI_VERSION=13. loader.c:evmc_load_and_create calls evmc_is_abi_compatible;
on mismatch it reports EVMC_LOADER_ABI_VERSION_MISMATCH, destroys VM and returns
NULL. These are exact pinned code facts. Do not choose ABI12 from the README or
assert a canonical upstream EVMC source commit/version that the snapshot does
not provide. This documentation mismatch is retained as evidence, not fixed in
upstream/user files. Host requires actual ABI13-compatible library.

Common.h names libevmone.so (Linux) and v0.22.0 release URL. Common.cpp's vmPaths
configuration/default search is input selection, not an artifact pin. No candidate
binary, source tree, commit, artifact digest, build compiler/options or signed
release metadata is available in the inspected retained scope. Thus even
"evmone0.22.0 supports ABI13/all old revisions/a step hook" is **unverified**.
No version command, dlopen, EVMC factory/get_capabilities or engine object was
called. Loader ABI check would run only after loading/creating a VM, not during
this investigation.

The header enumerates EVMC_HOMESTEAD/TANGERINE_WHISTLE/SPURIOUS_DRAGON etc.;
these are **requestable revision identifiers**, not observed backend support.
get_capabilities reports EVM1/EWASM/PRECOMPILES bits, not a per-revision support
matrix or instruction-limit capability. vm.name/version fields are runtime VM
metadata, not verified static release/build provenance. set_option is optional
and its names/values are backend-defined. loader.h example `engine=compiler,trace,
verbosity=2` is syntax documentation, not evidence these options exist or abort
at a step limit in a suggested backend. No backend source/option schema is
retained to resolve that question.

## Exact5M instruction versus120s process interfaces

| Mechanism | Existing named interface / established code behavior | Gap or limit |
|---|---|---|
| EVMC execution | evmc_execute_fn(vm,host,context,revision,msg,code,code_size), ABI13 evmc.h. evmc_vm fields: abi_version,name,version,destroy,execute,get_capabilities,set_option. Message includes gas/depth/value/data; result includes status/gas/data. | No standard instruction count, per-op callback, shared nesting budget, interrupt/cancel parameter or host-limit provenance field. Missing primitive is an **abortable per-instruction budget across the whole nested message tree**, outside Solidity failure. |
| EVMC host callbacks | account/storage/balance/code/block/call/log/etc methods. Nested host.call may invoke vm.execute again; EVMHost directly serves precompiles before VM execution. | Call/host accesses do not observe arithmetic/stack/jump opcodes, so cannot count every instruction. A per-execute local counter would reset or double-budget nested calls unless shared. No wrapper implemented. |
| Gas | Standard msg.gas and result.gas_left, backend opcode/revision rules. | Not an instruction counter: opcode costs differ, child gas and precompiles have different accounting.100Mgas is not equivalent to5Msteps, and lowering gas to force a step bound changes original budget/behavior. |
| Existing JS reference | replay.mjs machine installs evm.events.on('step',...) and sets metrics.steps=0 once in machine.call, STEP_LIMIT5000000; increments and throws HostLimit when >limit. Interpreter._runStepHook awaits EVM._emit('step'). | This is an existing hook **for A's pinned JS engine**, not an EVMC hook. Existing machine hardcodes Osaka/admission rejects originals; none invoked here. Does not approve R_fixture or historical execution. |
| Nested JS messages | Interpreter._baseCall uses same this._evm.runCall({message:msg}), not outer machine.call. Thus listener/counter is shared while nested; outer reset is not repeated by child. | Must preserve whole top-level-tree scope if a later backend is selected. Count is per public machine.call, not a fresh5M for each callee. |
| Exceptional attempted instructions | Interpreter.runStep emits hook before static gas charge/invalid-op check/handler; dynamic gas errors emit hook in isEVMError catch. Non-VM HostLimit rethrows out of interpreter loop. | Existing count is step-event/attempt semantics, not completed opcode count. On threshold crossing, metrics may reach5000001 but the next handler is not executed. A stop must not become REVERT/FAILURE that parent catch can turn into2. No runtime probe performed. |
| Native/precompile and zero-step work | JS EVM.runPrecompile invokes native JS/function path, and host precompile routines may return without interpreter opcode events. Account/deployment/load/ABI/setup work also occurs before any step. | 5Mopcode events do not bound native/host time or initial setup.120s process protection must include setup, all nested/native work and cleanup. A zero-step result is not by itself a timeout/step pass. |
| Existing process supervisor | scripts/tool-job.mjs creates separate child group, timer at supplied120000ms kills group SIGKILL, writes timedOut/error checkpoint; scripts/test-solidity.mjs supervises with extra cleanup-wait allowance. Retained reference-run.py uses external `timeout 120 node ...`. | Neither EVMC gas nor opcode tracing implements wall timeout. Standalone replay.mjs has no intrinsic120s timer. `timeout120` default TERM has no kill-after hard-stop guarantee for a signal-resistant native backend; a future B process envelope needs verified bounded termination, not assumption. Supervisor cleanup grace is not permission for >120s execution. No process supervisor run/test was repeated. |

Source locations/hashes for these exact mechanisms are in provenance.json;
existing reference-run.py invocation is retained under panic-decoder. No counter,
timer, hook or wrapper was added. Existing JS behavior is an inspected code path,
not new historical or boundary-case runtime evidence.

The standard ABI therefore **cannot alone establish** B's5M requirement. This
is narrower than claiming no evmone extension exists: its implementation/source
metadata is absent, so an abortable trace/step facility is currently unknown.
Tracing after execution, dumping N lines or an optional option named trace would
not suffice. A backend optimization could combine instructions or emit no event
for an exceptional attempted opcode; count semantics must be pinned and shown
compatible, not silently changed. Precompiles need no fabricated opcode counts,
but must remain within the unchanged process bound.

If an eventual backend exposes a step callback, later evidence must establish:
one shared monotone attempted-instruction counter over parent/children; stopping
before disallowed next handler; no catchable EVM result for host stop; original
completed executions unchanged below limit; invalid/revert/OOG hook coverage;
no reset on recursion/reentry/new frame; cleanup and state unusability on stop;
native/precompile/setup wall bound with exact process receipts. A total host
abort flag must propagate through host.call/execute, not merely return child
failure and let Solidity catch2. This is an interface/proof obligation proposal,
not implemented operational semantics or a changed target.

## Consequence for A/B and the smallest reviewable next choice

| Direction | Availability established here | Exact prerequisite / owner boundary |
|---|---|---|
| A: fixture-local correspondence over pinned JS message API | Existing10.1.3step-event listener and process-supervisor code are present. Historical machine path is still disabled; R_fixture is unapproved/unproved. | Later explicit review of fixture-local observational comparison and historical invocation/receipts. Preserve raw/upstream nonce/address/checkpoint/genesis/intrinsic/deposit differences, code/target/frame fidelity and original full outputs. This source task owns comparison documentation, not authority to implement the relation. |
| B: exact upstream host semantics with EVMC backend | Pinned host/header bytes and known link edges only. No verified binary/build/source pin or5Mextension; README12/header13 mismatch must be resolved by actual ABI. No supported-revision result observed. | First supply/authorize acquisition of exact backend source+artifact/hash/build/ABI13 metadata and an existing abortable step contract, plus complete host build closure. Acquisition/build/loading/execution remain outside current permission. Backend/tooling owner would need to establish this named capability; no existing published theorem/module supplies it. |
| B if no suitable existing hook | No standard ABI primitive can replace missing step observation/abort. | New instrumentation/API and below-budget behavioral-preservation work would need its own explicit authorization/review. It cannot be relabeled a free option, use gas as5M, raise host limit or replace native semantics. Not implemented or assigned to an excluded lane. |

Published repository interface snapshot remains
fb379ae20f10e2c92113453ddd9d40d8f2efbe09 (exact blobs in provenance.json).
Upstream host/EVMC vendored bytes belong to1835d247de183f23e7b0e2bc4a50732af525b77c;
backend source pin is **missing**, not invented from a version URL. Missing
primitive owner is the optional reference-backend/bounded-execution integration,
not Lean kernel, D3 physical memory or the pending external-reference ABI lane.
The latter work remains unapproved and untouched. The existing optional runner module is scripts/evm-reference/replay.mjs (exact published blob in provenance.json); docs/solidity-upstream-tests.md and docs/solc-validation.md own its validation/scope record. No existing module exposes a verified EVMC step-budget primitive.

The coordinator now has a specific choice: later authorize review/implementation
of A's restricted comparison/API obligations, or first authorize/provide B's
pinned source/artifact and enforceable-step feasibility evidence. Neither choice
is made here. If B needs new instrumentation rather than a present hook, that is
a further explicit implementation/proof decision. This is not another generic
runner question or invitation to relax original limits. Stop this increment at
that concrete boundary; further opcode inventories/gas arithmetic would not
resolve missing backend capability.

## Pass/stop criteria for a future specifically approved milestone

1. Before any fixture: exact source/compiler/host/backend/ABI/build/dependency
   hashes, requestable versus actually supported revisions, real artifact path,
   step/abort/timer contracts and setup comparison convention. No wrong ABI,
   unknown extension or unavailable build counted as a pass. Base EVMC enums/
   EVM1 bit/release URL alone STOP as unverified.
2. Within unchanged12GiB/swap0 and100M/5M/120s, later control runs would need
   parent+child aggregate count, terminal invalid/revert/OOG, nested reset trap,
   child-host-stop-not-catch2 and native/zero-step process termination evidence.
   These controls are DESIGN only now. Missing hard abort/exception provenance
   or process containment STOP; no returned output can waive it.
3. Only then, if authorized: per exact2sources×2pipelines×declared historical
   fork (12records if all3forks claimed), actual zero-value deployment followed
   by f(true),f(false), original literal ordered32byte1/2+failure=false, complete
   account/code/nonce/frame/selector/argument/child halt/gas/step/process receipts.
   Need intended g failure, not an ABI/precompile/no-code accident; all setup
   differences kept visible. Earlier static/Osaka/kernel evidence never fills a
   missing historical record. FAIL observation/code/frame/order mismatch; STOP
   unknown backend/host stop/unsupported fork/missing prerequisite, never rewrite
   an expected verdict or complete original assignment on that basis.

## Evidence-only validation/review

Actual new artifact-integrity/doc-baseline/resource checks and independent
read-only review are recorded below after completion. No full/Lean/MCP/axiom/
fixture/backend execution is necessary or claimed for this increment.


### Actual proportionate validation and review

validation.json records actual commands/exits/timings/aggregate RSS/cgroup peaks.
New retained provenance/closure/API integrity passes, including3negative controls
for forged artifact hash, README-derived wrong actual ABI12 and promotion of an
unverified step-hook claim. Inventory check, staged whitespace and lock/resource
invocation pass. Documentation paths retains actualEXIT1,same20baseline at
4b9a4054/new0. No absent backend was probed dynamically or counted as a pass.
No prior maps/compiler/gas/nonce/setup calculation, full/Lean/MCP/axiom or original
fixture/backend execution was repeated. Earlier failed gates/checksums remain.

Bounded groups verify12GiB/swap0/max-OOM0, writer lock and LEAN_NUM_THREADS1;
disk/OS headroom recorded, no Lake/configuration/cache/budget changes. The initial
exploratory ls exit2 on absent specified paths is retained in probe-notes.txt and
individual inventory entries; it is not a passing backend probe. No environment
or credential dump/network fetch/build/install/library load occurred.

Finder and skeptic independently reviewed read-only without Lean/server/checks/
builds/writes/backend load/EVM. No confirmed substantive finding. Kept precise
attempted-step semantics: dynamic gas work may precede the event, next opcode
handler is not executed after host-limit throw. Neither reviewer certified
runtime compatibility, backend availability, relation approval or assignment
completion. Exact review scope/raw commands/evidence are under
`/workspace/next10-diamond-try-evidence/backend-prerequisite`.
