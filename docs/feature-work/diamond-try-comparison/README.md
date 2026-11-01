# Fixture-local comparison design: decision boundary, not approved equivalence

Evidence/design child of eef9fc8a28d09c8a24b1e45c7b2ceba59409c99a on the same
retained VM/branch. This increment does not repeat setup tracing, compiler runs,
map generation or gas arithmetic. It reads their retained artifacts to identify
possible **observation dependencies** and specify a bounded next choice. No
engine, historical instruction, runner, wrapper, evaluator, symbolic execution,
model relation, profile or transaction backend is instantiated/implemented.
All original source/bytecode hashes, ordered full-byte observations, gas8000,
100M/5M/120s, targets/gap certificates/callback meanings/budgets remain unchanged.
Native12working/8blocked strictEXIT1,reference18/2,66/140 comparisons and217audits
are retained evidence, not new passes. Physical D3/reference ABI lanes stay paused.

## 1. Concrete dependency evidence for exactly these fixtures

Both original files declare only g(bool)(assert or require) and f(bool)(try
this.g{gas:8000}(x), return1 or catch return2); there are no explicit constructors,
state variables, modifiers, other contracts, nonce reads or new expressions.
Retained compiler AST identifies g#10 and f#33, exact `this.g` declaration and
bool argument. Both required pipelines are inspected, with Homestead,
TangerineWhistle and SpuriousDragon as the admitted pre-Byzantium target set;
Byzantium/Osaka artifacts remain separate controls, not historical passes.

`dependency-census.json` is a NEW classification of occurrences in existing
assembly-coded instruction records, not another disassembler/map/CFG. It keeps
source span, function region, assembly node, PC, literal widths, copied-runtime
offset and unmapped suffix. A missing operation means only no occurrence in
that enumerated compiler assembly, not complete reachability/noninterference.
Source maps that cover whole contracts are not treated as local source facts.
Constructor copied runtime bytes are data in that frame; no metadata byte is
credited as executed code. appendCBOR=false does not license interpreting an
unmapped suffix as a reached instruction. Reached-path claims remain conditional.

| Dependency | Exact compiler/source evidence | Consequence / remaining obligation |
|---|---|---|
| self/target identity | Pre-Byzantium legacy runtime ADDRESS167, PUSH20mask168=(2^160−1), EXTCODESIZE268, CALL283, both files/all3forks. Spurious viaIR ADDRESS716, EXTCODESIZE743,CALL793. Other per-fork PCs in JSON. Generated Yul passes cleaned address() as `expr_20_address`, g selector0xd48092f7 and same cleaned bool. | Not arbitrary external call. Must show reached target equals actual executing C and contains exact installed code; address renaming must commute with this use. Opcode inventory alone does not prove target stack provenance or reached dispatch. |
| sender/origin | No CALLER/ORIGIN occurrences in selected constructor/runtime assembly; source no msg.sender/tx.origin. Inner caller is C by CALL protocol; zero call value explicit. | Record outer S/U and inner C anyway. Differences are only proposed unobserved for these sources; no blanket erasure or complete noninterference proof. |
| value/balances | CALLVALUE constructorPC5; legacy runtimePC5; Spurious viaIR f222/g281. No BALANCE/SELFBALANCE occurrences. Generated outer nonpayable guards and child value0. | Zero value required at every entry. Funding/affordability and deployment success still prerequisites, not ignored merely because balance opcode absent. Fee/transaction conventions remain separate. |
| sender/contract nonce, CREATE | No CREATE/CREATE2/SELFDESTRUCT or storage op in selected compiler assembly; source no creation. Initial deployment is a host operation, not CREATE inside runtime. | Nonce affects creation address/collision and checkpoint restoration outside source bytecode. Can only be proposed irrelevant AFTER actual successful installation for this fixed call sequence. It cannot be ignored in a creation theorem. |
| exact code, code size/hash | Constructor CODECOPY legacy26 / Spurious viaIR22 installs embedded runtime on normal constructor RETURN. Runtime EXTCODESIZE checks self. No EXTCODEHASH/EXTCODECOPY occurrence; address-width PUSH20 is mask, not hardcoded account address. PUSH32 literals are retained for inspection, not reclassified as addresses. | Keep runtime bytes/length/actual codehash and installed role exact. Equal nonzero size alone is insufficient; wrong code may still return1/2. Hash field is an integrity obligation even where source does not read it. |
| hidden CODESIZE | Spurious viaIR CODESIZE872, PUSH target800 at873, JUMP876, JUMPDEST800, POP801. Thus on this local edge the pushed size is discarded before ISZERO802. Tangerine/Byzantium occurrence PCs retained separately; no CODESIZE in listed legacy artifacts. | Cannot claim the compiler never reads code size. Exact identical runtime bytes already give equal size. Local discard is not a proof of all paths or compiler refinement. |
| calldata/return/private memory | CALLDATALOAD/SIZE and constructor CODECOPY, viaIR memory allocation/ABI helper frames. f selector98c3a6c1; child g selectord48092f7, bool word0/1, no child ABI outputs. Top-level uint output32bytes. | Both interpreters need exact own code/data and ABI/frame behavior. No shared memory between frames/runs; do not identify HRef/object addresses with physical offsets or recycle caller memory as callee memory. |
| precompiles/block/external state | No BLOCKHASH,COINBASE,TIMESTAMP,NUMBER,PREVRANDAO,GASLIMIT,CHAINID,BASEFEE,BLOB*,GASPRICE,SLOAD/SSTORE/TLOAD/TSTORE occurrences. No source reads of these fields. | Still require actual self target outside zero/precompile/sender collisions. Other genesis fields only proposed unobserved for these source hashes; installation/account existence and opcode activation remain observable prerequisites. |
| gas | No GAS opcode in enumerated assembly, but explicit gas8000 forwarded by CALL. Child exceptional halt, memory/ABI/prefix/tail costs and OOG remain execution-dependent. | GAS absence does NOT mean gas-insensitive. Both full outer normal results and intended child halt must be established separately under unchanged allowances. No projection of gas/host stops. |

Byzantium/Osaka controls use STATICCALL, not CALL. They have no value stack
operand; their caller/self identities and zero call value are still recorded.
Control success cannot validate old-fork opcode/gas behavior. The compiler has
no hardcoded raw/host deployment address in its ADDRESS→mask→self-call source
construction; observed address-width literals and original source hashes are
retained rather than inferred from textual search alone. Exact emitted-code
coverage and unobserved-component adequacy remain proof/receipt obligations.

## 2. Proposed relation R_fixture (prose only, neither approved nor proved)

Scope parameters: one exact original source hash, one pipeline, one chosen
pre-Byzantium fork and its exact creation/runtime bytes; ordered sequence
zero-value deploy, f(true), f(false). No general source profile or global
equivalence is defined. This is a comparison design, NOT a trusted predicate,
Lean theorem, admission criterion or source verification result.

**Names:** let S_R/S_H be actual raw/upstream outer senders, C_R/C_H actual
successfully installed contracts. A partial injective map phi sends S_R→S_H
and C_R→C_H, fixes selectors and non-address ABI words (bool and returned uint1/2), and keeps both roles distinct from zero and
precompile addresses1..8 (and from each other). Define phi using actual receipts,
not expected address bytes injected into either state. Setup addresses/nonces
remain printed literally in evidence. Do not rename bytes inside a required
return/revert observation. No address-valued original expected output exists;
if one appeared, this proposed scope would stop for review rather than rewrite it.

**Installation boundary:** R can start at post-deploy only if BOTH constructors
actually complete normally, exact init/runtime hashes and code bytes/lengths/
codehash fields agree for C_R/C_H, collisions are absent, and exact constructor
self/caller/value0 and empty calldata semantics hold. Record the established
unsalted nonce discrepancy: raw final sender nonce1/hashnonce0 versus upstream
final1/hashnonce1 at initial0; contract nonce differs at SpuriousDragon too.
These facts are NOT equalized or hidden. Balances, creation flags and checkpoint
side records remain separately recorded. R is not a relation between identical
genesis states or a proof deployment always succeeds.

**Reached-call boundary:** f calldata exact selector+canonical bool, outer
caller/to/self/code roles mapped; g input exact selector+same bool, reached target
C_R/C_H respectively, same code/entry declaration, inner caller C_R/C_H,value0.
Only the intended self-call is related. A different installed callee with same
return values is insufficient provenance. Installed code and size checks must
agree, no fallback/precompile/no-code path is substituted. Keep actual caller,
callee and return-frame occurrences, including helper continuations; earlier
normal-return label evidence remains conditional and does not prove these paths.

**Memory/state:** each frame has private initialized memory, own calldata and
return buffer; typed model heap/capture interfaces are not assumed equivalent
to EVM memory. Proposed comparison requires byte-exact ABI/panic/error behavior
on reached operations, no alias leakage across callee/caller/run, and correct
rollback of failed child state. The selected assembly has no storage mutation,
but whole-path account/storage-effect absence is still an obligation, not a
linear-scan theorem. Carry source storage equal (empty roots for these contracts),
record all account/code/storage deltas, sender nonce progression(raw1→2→3 versus
host1→1→1) and created flags independently. Relating observations does not erase
these setup-state differences or turn them into equal full-state transitions.

**Gas and failure:** keep two actual gas streams with their existing different
entry conventions, not an equality of gas_left. Forwarded child allowance must
match8000 on both reached calls, or record a failed prerequisite, not change
literal/budgets. Both outer paths must complete with enough gas for their tails.
For true require actual g normal completion, not accidental child failure; for
false require actual intended assert/require failure PC/status, not ABI/no-code/
wrong-target trap. Record full child return data/gas/halt origin and caller catch
continuation. Constructor failure cannot establish R; top-level failure cannot
be credited as caught failure; exhaustion/host stop is not Solidity FAILURE.
Different rollback of sender nonce on failed deployment is an explicit
counterexample to global setup equivalence, even if no f call then occurs.

**Observations:** compare original f(true) then f(false), every original full
return byte and failure flag with frozen expectations, same order, both pipelines.
No source/verdict/observation projection. Keep constructor/code/account/gas/step/
receipt evidence as additional requirements; they may differ under an explicitly
reviewed correspondence, but raw records are never normalized. Ignoring nonce,
origin or funded unrelated accounts is a proposed fixture-local abstraction only
because no direct source/compiler dependency has been found; resource/account
lookup effects, constructor success and alias/target fidelity still need proof
or exact evidence. No universal noninterference, bisimulation or decision theorem
follows from the census or finite replay.

### Proposed negative/ordered controls (DESIGN, not executed fixtures)

| Control | Required result of the proposed comparison, not a runtime prediction |
|---|---|
| Same address+code, different account nonce, no nested creation | Distinguish same-address/different-nonce from current renamed-address setup. Nonce alone is not a source read in these bodies; retain it as unequal metadata and require unchanged observed outputs via evidence, not assumption. |
| `return address(new D())` or nested ordinary CREATE, even with same parent address but different parent nonce | Reject R_fixture scope; new address depends on nonce. Existing pinned-util same-sender nonce0/nonce1 hashes in setup-frontier/address-formulas.json differ (pure arithmetic already done). Returning that address requires literal original bytes; phi must not rewrite them. No source fixture added, compiled or run. |
| Wrong self/target, wrong declaration or same-size wrong code | Reject provenance obligation even if returned uint happens to match. No claim these mutations necessarily change f output. |
| Correct bytes but wrong stored codehash | Reject installation-integrity requirement; since EXTCODEHASH absent, this alone is not asserted observable by source. Keep integrity stronger than output match explicitly. |
| Zero value changed, missing installation, target at precompile | Reject setup/frame preconditions; do not silently use another role/account/address. |
| Constructor fails / top-level fails / child ABI trap masquerades as g(false) | Relation unestablished / original observation fails / wrong halt provenance, respectively. Preserve actual accounts/nonce restoration and all data. |
| Swap f input order, reuse state from other pipeline/fork, suppress one observation | Reject even if result multiset is1,2. Require original order and distinct evidence records; no gate pass from cached or other-profile execution. |
| Different gas or resource stop | Retain actual gas/stop. No equation from GAS-opcode absence; no running2outcomes by altering8000/100M/5M/120s. |

## 3. Smallest host-compatible API alternative versus fixture-local relation

Published interfaces inspected read-only: repository origin/master
fb379ae20f10e2c92113453ddd9d40d8f2efbe09 exact blobs in
interface-provenance.json; pinned npm @ethereumjs/evm10.1.3 public runCall,
protected _executeCreate/_generateAddress in evm.d.ts; upstream Solidity snapshot
1835d247de183f23e7b0e2bc4a50732af525b77c EVMHost/ExecutionFramework and EVMC
ABI13headers. No checkout integration or new backend was performed.

| Alternative | Exact interface and compatibility | Required later implementation/proof and risks |
|---|---|---|
| A: fixture-local observation design over existing raw-message engine | Public EVM.runCall(opts), pinned10.1.3; current machine hardcodes Osaka and rejects old fixtures before entry. No public ordinary-CREATE address strategy hook. Existing unsalted hashnonce=storednonce−1 invariant prevents exact host address+nonce state by parameter choice. R_fixture could describe different actual addresses/nonces while keeping all original output bytes. | Would need explicit approval of this comparison scope, historical invocation and isolated bounded receipt capture, plus sufficient reached-path/provenance/resource evidence. Prove/justify dependence restriction and frame/gas obligations; no automatic source correctness from replay. Highest risk is hiding gas/setup observability or broadening relation beyond2source hashes. It remains unapproved/unproved. |
| B: use exact upstream host path as reference | EVMHost(EVMVersion,evmc::VM&)→EVMHost.call→evmc_vm.execute(host interface,context,revision,message,code,size), EVMC ABI13. ExecutionFramework supplies genesis, intrinsic/code-deposit/backup/address ordering unchanged. This naturally preserves its direct postincrement hash and whole account restoration, without a nonce patch. | Requires actual complete upstream host/build closure or suitable existing binary plus exact binary/hash pin, VM capability/revision support and bounded step hook. Common.h suggests evmone0.22.0 release, but that URL is NOT a verified binary pin or loaded backend. No such backend/build has been validated here. Preserve recorded host side-flag TODOs rather than silently repair them. Verify5Minstruction stop can be enforced by supported interface (base EVMC execute has no instruction callback argument); timeout alone is insufficient. No installing/building/running is authorized now. |
| C: custom host-compatible creation inside EthereumJS | Protected _generateAddress/_executeCreate internals exist, not a public host plug-in strategy. Subclass/patch/state edit would have to change nonce/hash, checkpoint, intrinsic, deposit/failure and flag order, not just pass skipNonceIncrement. | NOT a zero-change API option. Requires new reviewed adapter/backend meaning and proofs; no wrapper, override or account normalization is written. More duplicated operational behavior than B; cannot be called already host-compatible. |
| D: transaction runTx wrapper | Not exported by pinned evm, @ethereumjs/vm absent from lock/install. Transaction validation/finalization differs from both direct-message hosts;100M allowance versus20M declared block limit can reject before source execution. | New dependency/version/hash and explicit envelope comparison decision required. Not the minimal host-message alternative; no unpinned wrapper installed, no gas-limit adjustment or transaction-finalization assumption. CREATE2 is not a substitute for any ordinary-CREATE option. |

A and B are viable **design directions**, not available validated runners. B retains the existing host semantics directly, but has concrete
binary/build/instruction-bound support blockers. No
alternative changes the original reference/native admission or claims compatibility
before actual authorized execution. Source/compiler facts versus dependency
availability versus runtime results are three distinct columns, not a pass tally.

## 4. Bounded next milestone / exact choice boundary

| Established now | Checkable with current approved read-only APIs | Requires later explicit authorization |
|---|---|---|
| Original sources/AST/opcode occurrences/bytes and exact nonce/address mismatch; no direct nonce/origin/storage/block reads in enumerated assembly | Artifact hashes, source/compiler occurrence provenance, public/protected API signatures, old pure nonce hashes, decision/design consistency | A's fixture-local comparison scope and bounded historical API invocation, OR B's exact-host backend/build pin and host-limit implementation. Neither authorized by this report. |
| Intended self target and value0 in source/Yul; code-size check and conditional local CODESIZE discard | Inspect exact assembly frames and retained decoder/capture laws without executing instructions | Reached target/entry and rollback/ABI/frame adequacy; both outer normal completions, both gas paths, actual historical receipts |
| Original ordered f outputs are full32byte1,2 and failure=false; raw native family remains12/8EXIT1 | Preserve expected observations/old receipts; check no source/budget/profile drift | Any new historical replay result, admission/support classification or full-assignment gate closure |

The next productive step is now a **specific comparison/API choice**, not another
inventory: select A's explicitly limited, reviewed observational correspondence
(with required proof/evidence obligations) versus B's exact-host path and pinned
backend/host-limit feasibility. C/D require broader changes and are not silent
fallbacks. This report stops at that boundary without asking the generic runner
question again or treating a design direction as approval. Physical producer
and pending reference ABI decisions are unchanged and not rephrased as this work.

Future bounded milestone, if specifically authorized:2exactsource hashes×2required
pipelines×one explicitly chosen supported pre-Byzantium fork per run. If claiming
all3forks, require12separate source/pipeline/fork records, not one representative.
Each record requires zero-value constructor receipt plus actual ordered f(true)
and f(false) receipts, exact init/runtime/installed-code identities, literal full
outputs/failure flags, outer/inner addresses/caller/value/code/selector/bool,
nonce/checkpoint/account/storage/created-flag changes, CALL gas before/after and
forwarded8000, child intended halt origin PC/data, caller normal catch/success
continuation and gas/steps. Original budgets100M/5M/120s apply to every run; no
profile change or engine substitution gets a pass.

PASS only if complete required observations and chosen comparison obligations
hold for every declared record. FAIL a literal output/failure/order/code/frame
mismatch; STOP blocked on unknown API/engine error, missing setup/provenance,
unsupported fork/opcode producer, unresolved gas/rollback, missing step bound or
host timeout/exhaustion. A child ABI trap yielding the right2still fails intended
halt provenance. Incomplete records, old Osaka controls, pure hashes/static code
and conditional kernel witnesses are never historical execution passes.

## Validation and independent review

Proportionate new integrity checks and actual doc-baseline/resource results are
recorded below after completion. Prior full/TestSuite/Corpus/strict/trust/MCP/
217audit evidence remains retained, not repeated. This increment implements no
trusted relation, compiler pass, semantic rule, engine or source bridge.


### Actual evidence/design checks and review

validation.json records command exits/timings/sampled aggregate RSS/cgroup peaks.
New dependency/API artifact checks pass, including3corrupt-artifact negatives
(source hash, retained map hash and opcode occurrence) and local CODESIZE
continuation metadata. These validate evidence integrity, not R_fixture or an
execution. Generated inventory, staged whitespace and lock/resource invocation
checks pass. Doc paths retains actual exit1, identical20baseline findings at
eef9fc8a/new0. No old compilations/maps/gas arithmetic, full Lean/MCP/axiom,
original fixture runs or historical engine operations were repeated.

Bounded commands retain12GiB/swap0,max/OOM0, writer lock and LEAN_NUM_THREADS1;
disk/OS headroom is logged. No Lake/configuration/cache/budget change. Exact
published and snapshot API hashes remain in interface-provenance.json; full
old artifacts are external evidence, not generated anew.

Independent finder/skeptic reviews are read-only with no Lean/server/checks/
builds/writes/EVM. No substantive finding. Replaced an unsupported comparative
implementation-cost phrase with direct host-semantics wording. Clarified address
role renaming versus fixed non-address ABI words. Neither relation, backend,
compatibility, fresh source/kernel result nor assignment completion is certified.
Review scope and actual commands remain under
`/workspace/next10-diamond-try-evidence/comparison-design`.
