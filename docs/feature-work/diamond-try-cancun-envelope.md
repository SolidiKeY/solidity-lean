# Cancun execution approval: mandatory-envelope feasibility stop

The human approved ONLY the two unchanged Cancun groups in
call_de2f04158ee743568e4ab4fcc25b6f1d item0. The subsequent recovery instruction
requires investigating the mandatory shared5M attempted-instruction envelope
BEFORE execution; permission does not waive it or authorize instrumentation.
Actual base is clean9e7a3c35bad428327b4eee02cd967a1dc75793a4 on the same original
branch/executor. Both groups remain **UNRUN**, not failing/passing runtime tests.
No group launch or new automatic-review rejection was attempted. The old M1
rejection and every accepted/uncertain/failed record remain untouched.

## Exact scope, attachments and dependency identity

[Delivery](diamond-try-cancun-envelope/delivery.json) records recovery86c66da6,
receipt710f3d1a-d8b6-4994-b1c1-4959111c7288 positively reconciled_not_accepted by
the coordinator's115completepages/5741items (current user evidence). Accepted
M1/Osaka/design turns were not replayed. A worker-visible journaled resume/receipt
helper or current turnID is not exposed, so no accepted receipt is fabricated
or dispatch repeated. decision.json/scoped-plan.json were not present in the
visible workspace, setup/evidence or supplied library/shared locations after
targeted filename searches (including hidden files, excluding dependencies and
caches). Their contents cannot be claimed read; exact current user decision and
[reviewed plan](diamond-try-c36-path/held-cancun-plan.md) were used, with the
recovery guard taking precedence. Missing attachments are an additional recorded
evidence gap, not a reason to invent broader execution authorization.

Both inspected script SHA256 values exactly match the human pins:

| Group | Local SHA256 | Status |
|---|---|---|
| check-source-admission | e9449a22ef45b337fa38ecdaec70f58e9f03a00076368cc5a98bf94ae177a7cb | unchanged Cancun, UNRUN |
| check-call-exception-vectors | a83aafb32811730547752e6e2832318d480c9d0e085fef497018c275230353ef | unchanged Cancun, UNRUN |

Compiler SHA2566c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390
matched without loading it. Three exact fixed files SourceLiterals.sol,
SourceIdentifiers.sol and CallExceptions.sol matched reviewed hashes. Both
scripts import built-ins and explicit compiler/vm/common/util/ethers only; no
source import, archive discovery, upstream runner or historical fixture route.
The original planned22calls/88vectors, both legacy/viaIR, Cancun/Hardfork.Cancun,
optimizer flags and30Mgas remain unchanged. Inline compiler controls remain only
inside source-admission. Full [input fingerprints](diamond-try-cancun-envelope/fixed-inputs.json).

The dependency trees are NOT interchangeable:

| Existing tree | VM / EVM / common / util / ethers | Relevance |
|---|---|---|
| universal/reference | 10.1.3 /10.1.3 /10.1.3 /10.1.3 /6.17.0 | Existing approved Cancun-script metadata pins; resolves required VM and ethers |
| conditional/reference | absent /10.1.3 /10.1.2 /10.1.2 /absent | Previous Osaka standalone-EVM lock tree; cannot run these scripts unchanged |

A built-in-only node:createRequire.resolve probe loaded no backend/compiler.
The actual Cancun imports resolve to universal VM dist/cjs/index.js, VM->EVM
dist/cjs/index.js and common/util CJS plus ethers/lib.commonjs/index.js.
Authoritative source audit here is therefore **CommonJS**, not an assumed ESM
copy. [Package identities](diamond-try-cancun-envelope/package-identities.json)
and full inspected-file source hashes preserve actual installed paths. They
are installed metadata/source fingerprints, not a claim of newly verified npm
tarball provenance or a reproducible backend build. No dependencies changed,
installed, loaded as a backend or substituted from another tree.

## Existing API: useful hook, no unchanged-script envelope

Exact installed universal @ethereumjs/evm10.1.3 CommonJS sources are copied inert
under /workspace/next10-diamond-try-evidence/cancun-envelope/installed-*.
[Provenance](diamond-try-cancun-envelope/installed-source-provenance.json) gives
SHA256 and actual paths. The relevant API/source chain is:

| Interface / actual source | Established source fact | Limitation |
|---|---|---|
| vm/dist/cjs/constructors.js createVM(opts) | opts.evm or opts.evmOpts can construct/select an EVM; default creates one from common/state/blockchain | Neither approved script supplies a budget EVM/options; changing factory/dependency injection is new instrumentation |
| evm/dist/cjs/types.d.ts EVMEvent.step(data:InterpreterStep,resolve?) | Existing public step event; runCode/runCall options have no maxSteps/attemptBudget/AbortSignal | A capability is not a listener/envelope already attached |
| evm.js281–294 _emit | Iterates listeners; one-argument listener invoked synchronously; two-argument callback awaited | Promise-return from one-arg async listener is not awaited; never rely on unverified async rejection escape |
| interpreter.js217–269 runStep | Dynamic gasHandler runs first; step hook follows on normal path, or in catch for dynamic-gas VMerror; then invalid-opcode check/useGas/handler | Event precedes opcode handler but NOT all dynamic-gas preparation; no strict pre-attempt bound proved from it |
| interpreter.js178–187 catch | Non-EVMError rethrown, ordinary VM exceptions remain ExecResult failures | A generic budget error could propagate, but must not become expected Solidity FAILURE or a new trusted rollback theorem |
| interpreter.js890–915 _baseCall and1052 creation | Nested calls/creation await same this._evm.runCall; runInterpreter creates Interpreter(this,...) | A shared closure could cover nested interpreted opcodes IF explicitly installed; no automatic counter/reset exists |
| evm.js1260–1278 runCode | Calls runInterpreter directly | Existing Osaka machine wrapper is not the approved source-admission runCode path |
| evm.js1302+ runPrecompile, call path542 | Native function called with gas/data, bypasses Interpreter.runStep | Zero interpreted instructions; native host work still needs120s process cap; no precompile abort/step coverage established |

Normal/invalid/STOP/REVERT/static-OOG opcodes pass the observed step point before
handler/base-charge failure when a listener is present. Dynamic-gas VMfailures
emit their event after failed preparation. Non-VM preparation failures can occur
before any event and propagate; zero-code/early host rejection has no interpreted
opcode. No listener is attached by either unchanged script. There is no supported
command-line/env/global-factory setting in these entrypoints that installs one.
DEBUG/profiler output counts/traces are not a shared enforced budget.

Even a newly attached `step` listener which throws at eventN+1 would allow the
N+1 dynamic-gas preparation to begin before abort; that is not a demonstrated
strict bound before the next disallowed attempt. This nuance is a limitation
of the *potential hook*, separate from the decisive current absence of ANY
attached listener in the two unchanged scripts. No step behavior was executed
or changed to settle an off-by-one/attempt definition here.

A generic thrown budget marker is source-backed as escaping Interpreter.run,
awaited nested calls and synchronous emission. EVM message checkpoint rollback
branches handle returned VM errors; an escaping non-VM exception does not by
itself prove equivalent rollback/finalization/afterMessage observations. Any
future host abort must stop/discard that machine, retaining prefix evidence as
blocked and never reusing it as if a completed revert. Precompile-native work,
compiler/WASM work and zero-step setup are outside opcode counts and separately
need an external120s process supervisor; Node timers alone cannot interrupt
synchronous native work. Memory12GiB/swap0 is not an instruction cap.

## Current published tooling, inspected without adoption

Read-only writer-locked fetch origin/master succeeded, resolving
b965d675e260a374401b131e59d501f8ce5da147; local HEAD stayed9e7a3c35.
[Published fingerprints](diamond-try-cancun-envelope/published-provenance.json)
retain exact blobs/paths/hashes and comparisons. Published commit
0f92a28a0b32fe12d0187d3df51c8830e4998a77 switches these scripts' compiler/engine
settings from Cancun to Osaka. It supplies no mandatory5M envelope. It is NOT
imported, cherry-picked, executed or used to reinterpret the human-approved
fixed Cancun hashes. No broader compiler/batch work is taken over.

Published replay.mjs exposes machine(stepLimit=5M)/replayBytecode with its own
Osaka createEVM, host context/gas/setup, step listener and per-root-call reset.
It is not a general decorator for the createVM/runCode calls in these scripts.
Routing tests through it would alter the test execution path and is not an
unchanged invocation. Published tool-job.mjs is a wall-time/process supervisor,
not an EVM attempted-op counter. Targeted published scripts search found only
the reference machine's step-budget implementation and its tests; no supported
unchanged-script envelope. This is a scoped source audit, not a universal claim
about every possible third-party tool. No historical source inventory repeated.

## Precise minimal future tooling proposal — NOT IMPLEMENTED/APPROVED

Current execution cannot proceed unchanged within all required bounds. The
reference tooling owner (scripts/evm-reference; owning docs/solc-validation.md
and docs/solidity-upstream-tests.md) needs a reviewed budget facility; the
hand-written vector/compiler-script owner owns explicit VM construction callsites.
A source-level proposal, not an opaque trusted adapter, is:

1. Define an explicit per-root `AttemptBudget(limit=5M,used,aborted)` contract.
   Reset for each original runCode/runCall invocation only; share the object
   across nested CALL/STATICCALL/DELEGATECALL/creation interpreters. Retain
   source-admission's same-VM storage/order, vectors88's freshVM semantics,
   all original settings/expectations and30Mgas. No state normalization.
2. Require a supported pre-dispatch consume/abort point **before dynamic gas
   preparation and opcode effects**. With used=N reject before attemptN+1;
   count invalid/STOP/REVERT/OOG attempts once, not per event on multiple paths.
   Existing public step event does not establish this stronger point. An
   optional upstream/package API such as `attemptBudget` on EVM opts would need
   a pinned source/API change in evm types/interpreter-run/root+nested lifecycle,
   digest/provenance review and later authorization. It does NOT exist now.
3. Wire the facility explicitly at each of the two scripts' VM factories/root
   calls through a small tracked tooling helper. This changes inspected script
   hashes and requires a separately reviewed scope; current unchanged-script
   execution approval does not authorize it. Do not hide it in --import/preload,
   monkeypatch require/createVM, private opcode overrides, a new evaluator,
   process environment or the previously rejected combined driver.
4. Abort with a distinct non-VM host marker and terminate/discard affected VM;
   no later vector/callback continues, no expected FAILURE pass. External120s
   supervisor owns the one group/descendants; no unrelated worker termination.
   Native precompile/setup has zero interpreted attempts, with honest separate
   gas/time coverage, not an invented native instruction count.

Minimum future validation before using that facility: tiny exactN/N+1 controls,
nested child-sharing (no counter reset), static/dynamic-OOG, invalid/REVERT/STOP,
precompile and zero-code paths, synchronous listener/non-VM escape, forced timeout,
no state reuse after abort, same budgets/expected ordered observations under both
compiler pipelines. Test marker/receipt must distinguish bounded stop from EVM
failure. A trace-only listener,30Mgas, wallclock timer or guessed gas-to-step
arithmetic is insufficient. Conservatively stopping the last allowed opcode
would alter boundary policy; do not silently do that either.

This is the smallest concrete ownership/API decision now: authorize a separate
tracked pre-attempt envelope change (including any necessary pinned API change)
or retain these two groups blocked. Existing source code has no such unchanged
path. No generic Cancun/fork permission question is repeated; that permission is
already granted. No new implementation, backend instrumentation/update or budget
interpretation is inferred. Alternative static worst-case attempted-step proof
for all exact compiled paths is also absent and would require separately scoped
proof work; no evaluator or new operational relation is built to manufacture it.

## Unchanged assignment status and new evidence scope

Both historical assert_pre_byzantium.sol and require_pre_byzantium.sol remain
blocked with original <byzantium/gas8000/observations/catalog rows; neither was
compiled or executed this increment. No historical backend build/load/run,
A/B relation, P4/P5b/P8, source admission/default semantics/target/exclusion,
policy-blocked ABI or proof/budget change. Native12working/8blocked strictEXIT1
and all original full-assignment failures remain. This is an evidence-only
checkpoint, not integration delivery or completion. Previous M1/Osaka/runtime
passes are retained historical inputs, not rerun; no new axiom/MCP/build claim.

Actual new work: current published fetch; inert source/metadata inspection and
built-in-only module resolution; static hash/path/statement checks, exact
documentation baseline comparison and read-only finder/skeptic review. No
compiler cwrap call, engine module load/VM instance or validation group launch.
No decision file or accepted receipt has been fabricated. Old failures/lookups
and missing attachment evidence remain in failed-lookups.txt/delivery.json.

Source-only integrity check exit0,1s: six fixedinput files, seven installed CJS
source files, six published files and all2,554 previous evidence checksums
matched; four static wrong-script/missing-tree identity controls. No VM/compiler
module load, validation group, Lean proof/build/MCP or dependency change occurred.
Memory.max12884901888/swap.max0 verified, max/OOM events0; cgrouppeak31,162,368bytes
and sampled aggregateRSS17,708KiB for that check. Writerlock/threads1/disk caches
and OS/disk headroom maintained; no Lean invocation or temporaryconfig needed.

Independent read-only finder/skeptic reviewed the installed CJS hook/abort/nested
paths, unchanged scripts, package/published distinctions and proposed boundary.
No concrete discrepancy found. They did not run scripts/checks/Lean/server/
compiler/EVM or certify later integrity gates. [Review scope](diamond-try-cancun-envelope/reviews.txt).
Strict documentation output comparison retains actual exit1; details recorded
after the final documentation-only check, with no new full/kernel/runtime pass.

Final strict docs actual exit1 (4s),20missing references and unchanged
ambiguities; complete pre-footer output byte-identical to c36 baseline,new0.
[Exact comparison](diamond-try-cancun-envelope/documentation-comparison.json).
Whitespace exit0. [Actual resource/check results](diamond-try-cancun-envelope/validation.json).
No generated support inventory is affected; no support/verdict entry was changed.
