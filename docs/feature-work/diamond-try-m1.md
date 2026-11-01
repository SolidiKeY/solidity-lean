# M1: computed 36-byte producer and intrinsic typed capture

Explicit approval: call_8fd0594a249440a4ae6b4375a89b805b item0, delivered in the
original active thread, parent32c900fb64ec88cdfa2616d2d109ac48244f8672, same VM/
branch. This implements only M1 from the reviewed [design](diamond-try-physical-design/README.md)
at7ec3983ce4606cb39a48cbd2fb8ebd8e690685f1. It is not an original-assignment
completion or integration delivery. P4 target-byte correspondence, P5b actual
source body/callee transport and P8 source admission are NOT authorized or
implemented. D3, all targets/exclusions/observations/decoder/callback/defaults and
budgets are unchanged. Historical backend work remains source-only; no build/
load/execute/instrumentation/R_fixture work is included. The approval is not a
new coordinator dispatch: worker records the delivered approval in evidence,
without mutating coordinator-owned accepted/uncertain receipt records.

## What is proved

The intrinsic `FrameMem C Γ` side witness keeps existing State/H as fields,
byte cells Fin capacity→UInt8, no incoming memory-local roots, aligned capacity,
resident high-water bound and zeros above resident memory. M1's actual context
is one uint size slot, while its logical heap may retain arbitrary unreachable
caller objects. No typed state, statement, grammar, formula or evaluator changed.
No untyped intermediate program/state or raw Yul interpreter is introduced.

WordSpan uses an actual typed uint offset and natural end+32. ByteSpan uses typed
uint offset/length and permits zero length without accessing its offset. New pure
operations prove exact unaligned byte writes, outside preservation, last-writer
on overlap, zero capacity extension, ordered immutable snapshot/length/empty
laws. Capacity reservation does not itself increase resident words. Snapshot is
an observation, not a target REVERT expansion/gas rule. No certificate refusal
is converted into an execution verdict or a narrowed source target.

The producer constructs zero memory, mstore(64,128), mstore(0,the actual original
selector word), mstore(4,0x43), then snapshots the *actual typed size slot* under
explicit size=36. All raw stores preserve the full State and FrameKey. Three
words are resident; byte95 remains128. Kernel proofs establish computed36 equals
the ordinary Panic67 layout and is decoded by the unchanged approved decoder.
No reference/expected byte vector is a producer argument or proof premise.

`captureBytes`/`captureSnapshot` reuse State.allocPush/bytesObj/byteWord. Proofs
read back the exact list through the real new HRef, establish byte boundedness,
fresh identity=old heap length, no alias with old objects, rejection of wrong
reference type, old heap/value/alias preservation and exact weakening of old
locals. Storage/ledger/transaction/balance stay unchanged. `bytesHalt` composes
this ghost materialization with existing TRun.revertData_mem and proves exact
THalt.ofData(computed bytes), including empty-data normalization. This logical
object is NOT a second physical EVM allocation or an invented callee invocation.

`StorePlan` contains typed word spans/values and an intrinsic parameter Idx.
`StoreShapeCert` proves exact equality with the bounded original plan; it has no
desired halt, expected bytes or assumed hcall field. Certificates and initialized
entries are constructible for both pipelines over every retained caller heap.
`certifiedProducer_exact` derives its own length bound and binds the key's
pipeline/invocation/depth/self/sender/value to the logical input. These are pure
component certificates, not a kernel parser/proof of the C++ solc process or
actual bytecode entry reachability. No SHA injectivity is assumed.

## Exact original identities and provenance checks

Only malformed_panic.sol c()→f(0x24): f#7, size parameter#2 and Yul external
reference#2 at212:4:0; f span17:216:0; caller c#105 span656:231:0; source-unit
original.sol,id0. Full unchanged original source is a literal provenance field,
including its comments; those comments/expected observations do not feed byte
operations. Compiler0.8.38+commit.1835d247.Emscripten.clang, binarySHA256
6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390;
Osaka, optimizerfalse/runs200, appendCBORfalse, distinct legacy/viaIR input/output/
creation/runtime identities retained in the kernel BundleKey and external JSON.

The external source-link checker hashes the actual retained source/compiler/
compile input/output/creation/runtime, compares whole source bytes to the literal,
validates every f-body operation/operand/parameter external reference and complete
c try/catch/assert/return reference shape, and matches each named BundleKey field
and pipeline exactly. It does not import/admit assembly, run solc or an engine,
or prove source/target adequacy. Negative mutated shapes exercise wrong store
order/word/type/reference/callee/argument/handler. Independent finder identified
an initial whole-file-hash-membership weakness; corrected per-field checks also
reject swapped fields/pipeline blocks/tags/source marker. Initial checker/logs
are retained as pre-correction evidence, not final checker adequacy.

## Constructed-call control is deliberately separate

The constructed constant-size body sets its own scalar temporary to36 and calls
the computed producer. It is expressly NOT original f(uint), which accepts all
uint sizes. Existing TRun.call evaluates the actual36 argument, enters the
parameter/default-return frame, and runs that body. Existing catchBytes transports
its actual raw data, while tryCall binds Panic code67, writes the caller return
slot and pops the catch scope. The exact normal result retains original caller
heap/globals—callee ghost allocation is rolled back. No oracle is installed.
Self=false plus empty oracle still fails; zero/wrong receiver fails. This proves
component integration against CURRENT deterministic semantics, not Valid/ValidT/
ValidC/holdsC or original native-source completion. Legacy universal callback
counterexamples remain unchanged and are not discharged by these witnesses.

Controls additionally cover empty snapshot at largest uint offset, natural
out-of-capacity range refusal, actual byte35/code ordering, true order-sensitive
synthetic overlap, wrong init/source/target/pipeline/invocation/size/type/result,
short/wrong selector/empty decoder refusal and preserved trailing decode. The
original two stores happen to commute observationally on their zero overlap;
reversed source order is still rejected by plan identity. No false same-bytes
counterexample is invented. Producer-only256-byte controls prove length, retained
initialized byte95 and zero-filled suffix; they are not target gas/REVERT proofs
or new original fixture observations. Original d() remains blocked with c().

## Unfinished design and original assignment

| Layer | M1 claim | Still required |
|---|---|---|
| P0 source identity | Exact literal/bundle/typed plan and external whole-AST integrity controls | Kernel source/compiler adequacy not inferred from hashes |
| P1/P2/P3 | Scalar side image, explicit fresh/prologue/stores and36 snapshot | General typed object layouts, full byte ISA/resources and arbitrary source-entry proof not supplied |
| P5 | Computed ghost capture/heap/frame and raw halt | Not an actual physical allocation or original hcall |
| P6/P7 bounded control | Constructed-call deterministic catch/code/return-slot transport | Original carried-body/source automation remains absent |
| P4/P5b/P8 | Explicit stop points, no implementation | Actual byte target simulation; exact original carried-body/import closure; separately reviewed native admission |

The full [proof plan](diamond-try-physical-design/proof-plan.md) and total outcome
ledger remain intact. This is not full five-row producer/assembly/ABI coverage.
Generic f(size) normal/failure/resource/divergence/host-stop meanings are unchanged;
M1 refusal at non36 is not a modeled revert for those executions. Original native
family12working/8blocked strictEXIT1 and reference18/2 with66/140prior ordered
comparisons remain open, pending actual final validation accounting. Approved
Panic decoder and217earlier audits/receipts/failures/exports are preserved.

## Verification and checking cost

No original speed-motivated representation is undone: current GateG0 recursor/
match-twin/heap rules and2f41a68a/77c6e047/cbecb7aa/2fbada13 history remain in force.
Byte operations use ordinary bounded leaf functions; no global physical indices
or context labels added. Initial nested-image whnf reached existing200000
heartbeats; repair factors per-byte snapshot and high-water projection proofs.
A maximum-word closed decide hit unchanged recursion depth; repair uses existing
range/subtraction lemmas. No heartbeat/recursion/fuel/node/test/gas/step/process
budget was raised. All failures and read-only goal/attempt logs are retained.

Actual focused diagnostics are required per changed Lean file, and final full/
TestSuite/Corpus/structural/strict/trust/frozen/source/script/original native
checks and new theorem axiom audits are recorded separately in the checkpoint
validation data. Documentation debt retains real exit1 with exact baseline/new
comparison. Runtime-only Lake config supplies Lean-j1; LEAN_NUM_THREADS1,
writer lock, disk caches, hard group12GiB/swap0 and measured disk/OS headroom are
required. Neither a connected VM nor an active job is passing evidence.


## Actual checkpoint results and open execution gates

`./run-lean.sh` exited0 (warm cached717 library jobs and259 SolkeyTestSuite
jobs); Corpus, complete frozen pins, check-orphans, check-layers,
check-automatic --strict, check-trust, inventory and staged whitespace exited0.
Five changed Lean files (four modules plus root) have structured nonpartial MCP
success, empty diagnostics and no failed dependencies, including warnings.
290 current transitive axiom audits printed exactly:73new M1 theorems and all217
retained task theorems reaudited, each using only propext/Classical.choice/
Quot.sound. No new axiom/sorry/native-decision trust was introduced.

The actual doc-paths exit is1, identical20baseline findings and zero new findings
against parent32c900fb's recorded gate. It is NOT called passing. Original native
12/8 strictEXIT1 and reference18/2,66/140ordered comparisons are retained prior
results, not new runs. The M1 source-link checks are static provenance tests,
not passing native/reference replay. No original fixture status improved.

Automatic approval review rejected launching the planned combined gate driver
because it included native/reference fixture execution under the historical
execution prohibition. The driver did NOT launch. Native family, reference
malformed_panic replay, source-admission/script-fixture and EVM-vector groups
were deferred rather than run indirectly; no new compiler or EVM fixture
execution occurred. These required original-assignment gates remain open and
are not waived or covered by the passing proof/static groups. Exact rejection,
deferred list, commands, timings, peaks, diagnostics and actual axiom sets are
in [validation](diamond-try-m1/validation.json),
[rejection](diamond-try-m1/approval-rejection.txt),
[deferred gates](diamond-try-m1/blocked-execution-gates.json),
[axioms](diamond-try-m1/axiom-account.json), and
[read-only reviews](diamond-try-m1/reviews.txt). This is a locally committed
kernel checkpoint with explicitly incomplete execution validation, not a
complete original assignment or an integration delivery.

Across actual bounded commands, maximum sampled aggregate RSS was4962772KiB and maximum cgroup peak1331539968bytes, with memory.max12884901888/swap.max0 and no max/OOM events. Resource figures include failed proof/diagnostic attempts; they do not establish a cold-build or target-execution bound. Source collection/check scripts use disk files, no backend binary/load. Full logs live at /workspace/next10-diamond-try-evidence/m1-producer.
