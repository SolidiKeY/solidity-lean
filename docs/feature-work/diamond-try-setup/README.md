# Try fixture setup compatibility: code derivation, not execution

Evidence-only child of71e77d870a22b209258b5acce7d2828a95b6bff9, same retained
VM/branch. The human permits investigation only. No historical engine is
instantiated; no fixture, instruction evaluator, symbolic execution, backend,
runner or profile is implemented/enabled. No source, compiler option, target,
admission, callback judgment, Lean definition or frozen observation changes.
No32compilations/20maps/full build are repeated. All original Panic proofs,
217standard-only audits and earlier receipts/failures/checksums are retained.
Original assignment remains native12/8strictEXIT1,reference18/2,66/140 ordered
comparisons; these are old results, not fresh source passes.

## Complete caller-entry chains and setup state

The actual current runFixture admission rejects `<byzantium` before machine/
replayBytecode is reached. The following engine chain describes the existing
caller API for admitted fixtures and a conditional setup comparison only; no
historical guard was bypassed and no historical deployment message was sent.

**Current reference, exact existing path:** replay.mjs main→runFixture→
replayBytecode→machine→createEVM→new SimpleStateManager→new EVM. Factory
constructors.js and SimpleStateManager constructor show empty account/code/
storage maps, not a loaded Mainnet genesis. Mainnet Common selects rules;
it does not populate genesis state. machine explicitly installs only sender
S=`0x1212121212121212121212121212121212121212`,nonce0,balance10^30.
Active precompile handlers and journal warm addresses are not proof of funded
precompile accounts. machine.call cleans journal/originalStorage caches and
adds warm entries, then raw evm.runCall(caller=S,origin=S,gasLimit=100M).
No `to` means default zero-value CREATE. Next calls supply actual createdAddress
and selector+bool words for f(true), then f(false), zero value each.

runCall constructs Message(depth default0,value default0) and increments sender
nonce **before** beforeMessage and journal.checkpoint. _executeCreate reduces
sender value0, changes message.data→code and clears calldata, then
_generateAddress loads incremented nonce and uses **nonce−1**. Thus first
address=last20(keccak(RLP([S,0]))), not RLP([S,1]). Collision tests inspect
nonce/codeHash/storageRoot; fresh destination account is checkpointed, storage
cleared, nonce becomes1 only from SpuriousDragon(EIP161), otherwise0. Constructor
runs with address/self=created address, caller=S,value0, empty calldata and code
=exact initcode. It must return installed runtime, not ABI values. Successful
code deposit writes stateManager.putCode, success commits journal. On message
exception the journal reverts accounts/code/storage, but the top-level sender
nonce increment preceded the checkpoint and remains. Return createdAddress by
itself is not success; caller requires no exception and actual installation.

Raw subsequent f calls increment S nonce1→2→3, including failed top-level
messages; inner g depth1 does not increment the contract sender nonce here.
Outer recipient/self/code address is actual deployed C; inner CALL (pre-Byzantium; STATICCALL in the retained Byzantium/Osaka controls) recipient/
self/code address C, caller C,value0, input g's selector+same canonical bool.
Historical createdAddresses(EIP6780) tracking is inactive: the result property
may exist empty but _executeCreate does not mark it for these forks. Current
Osaka does mark it. These are source branches, not observed historical flags.

**Pinned upstream, exact caller chain:** SemanticTest::runTest selects VM and
reset per pipeline, deploys once before first f row. deploy→
SolidityExecutionFramework::compileAndRunWithoutCheck(inline header)→
multiSourceCompileContract→ExecutionFramework::sendMessage(initcode,args,CREATE,0)
→EVMHost::call→selected EVMC VM.execute. Subsequent ordered rows call
callContractFunctionWithValueNoEncoding→sendMessage(selector,bool,CALL,0)→host.
newBlock increments block number/time15s, clears logs and newTransactionFrame
resets accesses/original storage/transient/selfdestruct flags. No transaction
validation/signature/block-gas-limit check surrounds the direct host call.

Host reset clears accounts and seeds precompile addresses1..8 with balance1;
ExecutionFramework reset funds account(i)=h160(0x1212121212121212121212121212120000000012+i*0x1000)
for i0..9 with2^100. MockedAccount nonce defaults0. Sender U=account(0), not S.
Host tx.origin=`0x9292929292929292929292929292929292929292`,gasPrice3Gwei,
blockGasLimit20M are constructor constants. reset does not replace those with
sender-derived values. Neither fixture reads these extra fields; they must not
be silently equated for a general equivalence theorem.

Host call saves **accounts backup first**, charges depth0 intrinsic gas, and
for CREATE increments U nonce0→1 then hashes RLP([U,1]) directly. Destination
must not exist. It marks m_newlyCreatedAccounts for every CREATE, leaves the
created MockedAccount nonce at its default0 (no engine EIP161 counterpart in this
wrapper), executes initcode with empty calldata, subtracts200*returned-code-size
from result.gas_left and stores code/hash if affordable. Non-SUCCESS restores
accounts backup, including sender nonce0; newlyCreatedAccounts is outside that
backup (explicit source TODO), and gas counters/recorded calls are not accounts.
Successful first create leaves U nonce1. Ordinary top-level CALLs do not
increment U nonce, so ordered f rows leave it1. Source TODOs about EOA preincrement
are actual harness behavior, not an instruction to normalize it away.

Pure pinned-util RLP/Keccak arithmetic (no EVM) gives raw first address
`0x501f373d5541129778e4195692f7fff4dd01ebc9` and host first address
`0xc06afe3a8444fc0004668591e8306bfb9968e79e`. A same-S control with nonce1 gives
`0x8f047056608fdb1be4725341c345326702096cb2`, isolating nonce from sender.
See address-formulas.json. No number here is a newly observed deployment receipt.

A narrower API incompatibility is now concrete: for this constructor with no
additional nonce-changing operation, successful ordinary unsalted raw CREATE has
`stored sender nonce = address-generation nonce + 1`, while successful upstream
host unsalted CREATE has `stored sender nonce = address-generation nonce`. Default initial
nonce0 yields raw(final1,address nonce0) versus host(final1,address nonce1).
runCall exposes `skipNonceIncrement`, but skipping at0 makes its subtraction
attempt nonce−1; preloading another nonce does not remove this one-step relation.
There is no ordinary-CREATE address override in this raw API. The separate salt option selects CREATE2, changes the address convention and is not an equivalent replacement for these original unsalted deployments. Supplying `to` turns
it into CALL, not equivalent deployment. Therefore exact address+sender-nonce
state equality cannot be obtained just by choosing these raw parameters; no
nonce/state patch is applied. A future comparison must explicitly permit an
observational address/nonce correspondence (these fixtures read only self
identity, not nonce) or pin a reviewed host-compatible creation interface. It
must not claim identical genesis/transaction states. This is static code
reasoning under normal constructor completion, not a receipt or global theorem.

**Transaction boundary audit:** pinned @ethereumjs/evm10.1.3 exports createEVM/
EVM.runCall, not runTx; @ethereumjs/vm is absent from the pinned dependency lock/
installed package set. Therefore there is no pinned runTx implementation to
trace, and selecting one requires an explicit dependency/API decision, not an
assumed published transaction wrapper. Raw runCall performs message checkpoint/
execution and nonce handling, but no transaction envelope intrinsic subtraction,
upfront gas-fee purchase, miner payment, block inclusion, receipt construction,
signature validation or full transaction finalization. postMessageCleanup clears
transient storage; machine.call resets caches, not a runTx finalizer. Upstream
host also executes messages directly, adding its explicit intrinsic subtraction/
code deposit/refund calculation rather than a full transaction backend.
100M>20M declared upstream block gas limit is accepted by this host path; a real
runTx wrapper could reject it. No new wrapper or gas normalization is installed.

## Gas reconciliation from exact byte counts and pinned constants

Supplemental GasMeter.h was fetched read-only over HTTPS at exact upstream
1835d247de183f23e7b0e2bc4a50732af525b77c; test-only archive lacks libevmasm.
provenance.json records URL and SHA256, separately from snapshot-verified test
files. Header constants: txCreate53000,txCall21000,zero byte4,nonzero byte68
before Istanbul/16after,code deposit200/byte. Installed pinned engine params.js
agrees on deposit200 and CALL40(Homestead)/700(TangerineWhistle+), memory
3*w+floor(w*w/512), copy3/word. Code facts do not prove costs of an untaken or
unresolved execution path.

For exact initcode bytes B, Z=zeros,N=nonzeros, installed runtime length L:
upstream constructor entry=100M−53000−4Z−68N before Byzantium; raw constructor
entry=100M. Deposit=200L in both code paths if actual successful output equals
retained runtime and gas suffices. Upstream final consumed gas includes intrinsic
and code deposit via InitialGas−gas_left (then bounded refund); raw executionGasUsed
includes interpreter/deposit but excludes envelope intrinsic. Failed constructor
output is not installed code; upstream code-deposit block still touches the
output/status before non-success accounts restoration, while engine success
checks gate deposit/installation. Do not equate all failure counters.

Canonical f true payload=36bytes,4nonzero selector bytes+1nonzero bool byte,
31zero bytes: intrinsic21464. False=4nonzero+32zero:21400. Thus upstream entries
99978536/99978600 versus raw100000000. No intrinsic charge for inner g; CALL/STATICCALL
opcode overhead and memory expansion belong to parent prefix. Exact per-source/
pipeline/fork initcode counts/constructor budgets/deposit values are tabulated
in gas-arithmetic.json, including distinct bytecode controls for Byzantium/Osaka.
Osaka rows describe the host's **explicit formula**, not a complete modern runTx
intrinsic/EIP7623/EIP3860 transaction model. Neither path is changed to the other.

| Retained original / pipeline (SpuriousDragon) | Init bytes / Z / N | Host constructor intrinsic | Host entry budget | Deposit if runtime installed |
|---|---|---:|---:|---:|
| assert_pre_byzantium-spuriousDragon-legacy | 616 / 120 / 496 | 87208 | 99912792 | 117000 |
| assert_pre_byzantium-spuriousDragon-viaIR | 996 / 168 / 828 | 109976 | 99890024 | 190400 |
| require_pre_byzantium-spuriousDragon-legacy | 565 / 91 / 474 | 85596 | 99914404 | 106800 |
| require_pre_byzantium-spuriousDragon-viaIR | 949 / 139 / 810 | 108636 | 99891364 | 181000 |

Let A be gas remaining after parent CALL base/dynamic/memory overhead.
Homestead forwards exactly8000 if A≥8000, else fails caller before child.
TangerineWhistle+ forwards min(8000,A−floor(A/64)); it equals8000 iff A≥8126.
Value0 adds no2300stipend or9000transfer cost. Existing self code is not a new
account; the source extcodesize guard itself costs gas. For g(false), reached
unsupported fd is an exceptional child halt charging all forwarded gas and
empty return buffer; g(true) must actually reach normal return with its own
cost below allowance. Parent consumes childUsed≤forwarded, retains its remainder,
then executes catch/success tail and uint encoding. P(prefix),memory high-water,
child normal path cost,T(tail) remain unmeasured/unproved. No guessed total path
bound, host5Mstep bound or assertion of parent positivity is supplied. Static
allowance formulas and exact intrinsic/deposit arithmetic alone cannot pass the
historical gate. Host5M instructions/120s and literal8000 remain unchanged.

## Compiler return-label correspondences without symbolic execution

frame-edges.json reads **existing** instruction/assembly/functionDebugData maps;
it neither rebuilds them nor simulates stack/instructions.456 same-block sites
across20artifacts explicitly PUSH a continuation tag equal to next JUMPDEST,
PUSH named callee entry and JUMP[in]. Record caller occurrence, continuation
PUSH PC, callee parameter/return slots, named region and its possible JUMP[out]
PCs. These establish compiler normal-return calling convention for that
occurrence **conditional on normal completion**, not a unique target for every
execution of a shared return. Original indirect outs remain listed. Other
call sites with no same-block explicit pair are conservative unresolved entries.

Concrete SpuriousDragon viaIR assert examples: call828→674 pushes return829 at820;
helper region out701 normally resumes829. call843→643 pushes return844 at835;
helper out670 normally resumes844. g call949→929 pushes950 at942, helper normal
out935 resumes950; false branch934→937→940→882 never completes that normal
return. Thus g's own out951 inherits its caller frame label, not universally950.

One additional nested-label correspondence can be read directly, beyond the
same-block extractor: external_fun_f at221 PUSHes265 at227(final encoder return),
248 at230(f return),243 at233(bool decoder return), then calls decoder152 at242.
Decoder metadata2parameter/1return preserves pending outer labels under its
normal calling convention. At243 it calls fun_f702 at247 using the already
arranged248; normal f exits831/846 return248, then allocation255→95 resumes256,
encoding264→199 resumes265 before RETURN268. This is occurrence/frame-sensitive
compiler structure, not general CFG reachability or a bytecode correctness proof.
The extractor deliberately leaves247 unresolved because its continuation push
crosses the nested decoder block; this manual chain states the extra convention
assumption/provenance explicitly. Assert/require metadata controls remain
separate; no global return-PC substitution or symbolic executor is introduced.

## Physical layout prerequisite tied to actual original code

For the original Panic-family f(uint size), retained legacy assembly initializes
`mstore(0x40,0x80)` and viaIR deployed object initializes `mstore(64,128)` before
dispatch. This is the **runtime**, not constructor memory carried across calls.
The pinned Interpreter constructs `new Memory()` per frame; Memory allocates a fresh zero-initialized Uint8Array. Thus the concrete engine design starts a callee with zero byte memory; this is a code fact, not yet a typed-model adequacy theorem. g/f's calldata uint
validation uses the stack/calldata. Original assembly writes selector word at0,
then code67 at4, then revert(0,size). The word writes overlap: second covers4..35,
leaving selector bytes0..3 and32-byte code at4..35. Under a proved fresh-frame/
prologue/no-intervening-writes relation,36..63 are zero,64..94 zero,95=0x80,
96..255 zero. Sizes3/6truncate;36is complete;256includes initialized free-memory
word. Those are conditional byte-layout consequences, not a new kernel/source
execution theorem. Actual earlier receipts supply separate concrete evidence.

malformed_error uses four stores:0selector,4offset32,36length7,68string word.
They overwrite the free-memory word64..95; the Panic byte95 reasoning must NOT
be copied to this source. Slice sizes3,6,67,74truncate encoding;75contains7reason
bytes,256includes padding/tail. No producer witnesses or physical bytes are
inserted into Lean from these arithmetic descriptions.

Refined counterexample/design obligation: identical typed Heap/env can abstract
physical memories differing at word64, so heap-only selection of revert(0,256)
is underdetermined; this does not say both satisfy the pinned prologue. The
actual prologue excludes the0xa0 candidate **if** its execution and frame-layout
adequacy are proved. Missing local relation shape (proposal only):
`FrameRel C Γ σ μ initcodeIdentity runtimeIdentity declarationId`, carrying
fresh frame, initialized word64, typed-object placement/alias/length/padding,
calldata/capture correspondence and permitted write footprint. Required theorem
shapes: entry establishes relation; uint-argument evaluation/ABI checks preserve
it before try; exact source store sequence refines big-endian overlapping byte
updates; revert slice yields actual THalt.ofData d for each admitted size;
caller frame/heap rollback retains d; existing catchData/code binding and typed
return transports complete caller tails and scope pop. Include nonnormal
exhausted/diverged separation and wrong init/callee/size/alias/order/type controls.
No global relation, new physical primitive, axiom or changed target is installed.
Physical D3 and the separately pending reference/ABI producer remain outside
implementation scope; this is an exact prerequisite, not a generic host refusal.

## Minimal future experiment DESIGN (not implemented or approved)

1. Pin exact supported historical fork/API and engine+state-manager versions;
   no unpinned runTx substitution. Decide explicit host-message comparison versus
   transaction comparison: existing raw runCall supports caller/origin/value/to/
   gasLimit/code and journal state, but does not reproduce upstream intrinsic/
   nonce/genesis conventions automatically. A historical constructor helper or
   wrapper is not authorized here. Existing machine hardcodes Osaka; it cannot
   select historical forks via its public signature. Those are concrete API
   blockers, not an invitation to change settings now.
2. Isolate a fresh state per source/pipeline/fork. Record exact sender, balance,
   nonce,precompile accounts,origin,block fields and codehash/state flags. For
   comparison to upstream choose an explicit observational correspondence or a separately reviewed host-compatible creation API: the raw nonce/address invariant prevents exact setup-state equality by parameter selection alone. Do
   not force a shared expected deployment address or discard nonce differences.
3. Deploy exact retained initcode with value0,100M original allowance. Record
   pre/post sender nonce, address hash nonce, initcode/calldata, entry gas,
   intrinsic convention, child frames, code-deposit charge, installed runtime
   hash/bytes,created flags and all account/journal restorations on failure.
4. Using actual successful created address, f(true) then f(false), both pipelines.
   Record outer caller/to/self/code/origin,36-byte inputs, parent pre/post-CALL
   gas,actual forwarded gas≤8000,child caller/self/value/code/selector/bool,
   g's halt origin PC/status,gas consumed/returned,raw bytes and parent catch/
   success continuation PCs,32-byte output1/2. No expected bytes supplied to model.
5. Pass ONLY if both ordered full outputs/failure flags and setup identities,
   code hashes, gas and rollback semantics match the explicitly chosen comparison
   convention. A g ABI/setup trap cannot be credited as intended g(false) even
   if catch returns2. A constructor/top-level trap is failure, not caught success.
   Unknown engine errors/API incompatibility, profile/code mismatch, missing
   receipts or unresolved setup difference STOP as blocked;5Mstep/120s stop stays
   a host stop, never Solidity FAILURE. No budget changes, gas-free proof,
   decoder helper or static report satisfies this experiment's runtime gate.

No approval question is repeated. Implementation/execution remains paused by the
human's investigation-only choice. Next review can assess a specific setup/API
proposal from these concrete differences; no whole-assignment completion follows.

## Evidence and validation

Exact entry sources, supplemental pinned gas header, data/script hashes, raw
commands/resource footers and independent reviews are retained under
`/workspace/next10-diamond-try-evidence/setup-frontier`. This increment uses only
static reads, byte counts, arithmetic and pure address hashes. Proportionate
integrity/inventory/doc checks and reviews are recorded after completion; prior
full/MCP/axiom/source-fixture results remain retained, not freshly run.


### Actual proportionate results and reviews

validation.json records actual bounded exits/timings/aggregate RSS/cgroup peaks.
Static setup analysis, pure address arithmetic, setup integrity controls, generated
inventory, node syntax and staged whitespace all pass. No compilations/maps or
Lean/MCP/full/fixture runs occurred. Doc paths retains actual exit1 with the same
20findings as71e77d87/new0. New controls reject wrong true-input intrinsic cost
and wrong occurrence return label; same-sender nonce hashes differ as expected.
These are static artifact controls, not execution or kernel proofs.

All bounded jobs verify MemoryMax12884901888/MemorySwapMax0,max/OOM0 and writer
locking; invocation checks LEAN_NUM_THREADS1 plus disk/OS headroom. No Lake
configuration, budget or tracked/user setup change. Exact supplemental header
URL/hash is separate from archive-verified test code. Missing machine.mjs probe,
missing snapshot library header and unavailable runTx are recorded explicitly;
no unsupported API was installed or claimed exercised.

Finder and skeptic reviewed read-only, with no Lean/server/checks/builds/writes/
EVM use. No substantive finding; fork-qualified CALL/STATICCALL and ordinary
unsalted CREATE wording corrections applied. They confirmed the narrow nonce
invariant and conditional scope; no pending runtime/full-assignment gate was
certified. Full review scope is in external reviews.txt. All original blocked
rows and native strictEXIT1 remain; only the new setup uncertainty/accounting
and local compiler-label evidence are refined.
