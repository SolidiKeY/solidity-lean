# Post-M1 readiness: published bytes, exact source body and call frame

Evidence/design only, based on clean M1 commit3ee3855c21f62b7454d629b824be281d66384bae.
This supersedes status/dependency claims in the historical
[physical design](diamond-try-physical-design/proof-plan.md), preserving its full
obligations and every original gap/target certificate. M1 remains a component,
not original source coverage: native12working/8blocked strictEXIT1. No Lean edit,
proof execution, P4/P5b/P8 implementation, source admission, D3/target/default/
callback/profile/budget change, published-code import or sibling work is made.
No rejected/deferred native/reference/EVM/script-fixture group is run by any
route. The listener owns the pending compatible-execution question; this work
neither repeats it nor infers permission. No historical B engine acquisition,
build/load/run/instrumentation or new relation is undertaken.

## New published evidence, pinned once

Read-only `git fetch --no-tags origin master` and matching `ls-remote` at
2026-10-30T12:52:20Z resolve published master to
8445c3fc203144251b9d1fc9181f7f61a8189522. Local HEAD remains M1; cached old origin
wasfb379ae20f10e2c92113453ddd9d40d8f2efbe09. No switch, merge or cherry-pick.
Exact fetched/ref response, source blobs, SHA256, Git blob IDs, local/published
comparisons and type headers live in
/workspace/next10-diamond-try-evidence/post-m1-design and the JSON alongside.
Source inspection is not a fresh build, axiom audit or execution receipt.

The old blanket “no byte primitive is published” is outdated. Newly published
G38 failure emission provides a real independent byte-addressed slice:
[Slice](https://github.com/SolidiKeY/solidity-lean/blob/8445c3fc203144251b9d1fc9181f7f61a8189522/Solidity/Backend/Failure/Slice.lean),
[Correct](https://github.com/SolidiKeY/solidity-lean/blob/8445c3fc203144251b9d1fc9181f7f61a8189522/Solidity/Backend/Failure/Correct.lean),
[Composition](https://github.com/SolidiKeY/solidity-lean/blob/8445c3fc203144251b9d1fc9181f7f61a8189522/Solidity/Backend/Failure/Composition.lean),
and [Unwind](https://github.com/SolidiKeY/solidity-lean/blob/8445c3fc203144251b9d1fc9181f7f61a8189522/Solidity/Backend/Failure/Unwind.lean).
Slice/Correct's last published change is4cb5d0aff8b4e71e2de0726869bb408a69b4719b,
proved reachable from this master. Later composition/unwind hashes are recorded.
These modules are not installed in this M1 branch.

| Published item and actual interface | Exact assumptions/conclusion | What it does NOT discharge |
|---|---|---|
| Slice.Memory = Nat→UInt8; Machine.stack = List Roadmap.Word (Fin2^256) | Independent target byte memory; step : Instr→Machine→Option(Machine×Option Outcome) | Not intrinsic State C Γ, not a source-term IR, not full EVM |
| Slice.step | PUSH, MSTORE8, RETURN, REVERT only; top word=offset, next=value/length; unsupported/underflow→none | No MLOAD or MSTORE arm, calldata access, gas or memory-expansion charges |
| getBytes_putBytes(m,a,bs) | getBytes(putBytes m a bs) a bs.length = bs; no premises | Range read/write law, not same-bundle bytecode execution |
| putBytes_frame(m,a,x,bs,h) | h:x<a∨a+bs.length≤x; byte x unchanged | No overlapping-word semantics or initialization proof |
| getBytes_congr(m,n,a,len,h) | Pointwise agreement on[a,a+len) implies equal slice | No executable producer or caller ownership relation |
| run_writes(a,bs,p,s,h) | h:a+bs.length≤2^256; runs actual emitted MSTORE8 write blocks then p, preserving stack | Does not run original solc MSTORE instructions |
| checkedRun_emit_suffix(a,i,p,s,h,hs) | Fits a i.bytes = a<2^256 ∧ len<2^256 ∧ a+len≤2^256; hs:s.stack.length+2≤1024; exact final memory=putBytes, stack tail retained, outcome=i.observation; suffix unreachable | No gas5M/120s contract, original compiled body/code placement/dispatch, source or full target simulation |
| Local.execute_failure(c,a,d,live,hf,hs) | Same Fits/stack conditions; execute local emitter returns some(restore c,revert d) | Checkpoint P T is explicit local snapshot, not ContractWorld/TTx/legacy catch/callback semantics |

Exact copied declaration TYPE headers and qualified names/file/line are in
actual-types.json; the complete retained module blobs preserve surrounding
sections and implicit variable binders. These were read, not re-elaborated.
This table abbreviates them. Slice.run uses
Option.none for unsupported/underflow, not THalt.revert/exhausted/diverge. Its
Outcome has success/revert only. Never turn absent execution into completed failure.

The published G03 map STILL has /dependencies/modules/G46.02/modules=[] with
71owned cells,0lines, ownerV15. G04 R31 still requires a byte-memory bridge for
the final target. The module count is a ledger fact, not proof that no adjacent
byte code exists: G38 above is a newly available adjacent component. G46.02's
remaining split is MLOAD/MSTORE/MSTORE8 representation, calldata, memory expansion/
resources, RETURN/REVERT ranges against the real target. Source module text and
owner docs—not the empty list alone—establish the limited scope.

The unchanged Evm.Machine is word-addressed. mloadAt/mstoreAt are not a proof for
MSTORE at byte4 overlapping byte0's word; ×32 scaling cannot simply identify
those original offsets. The optional EvmYul bridge's old projected word agreement
is not a new MSTORE/gas/source bridge. No other owner's implementation is taken.

### Exact reuse and P4 stop point

A future pure view lemma may relate an M1 FrameMem's Fin cells on a bounded
ByteSpan to Slice.getBytes on a Nat-addressed memory agreeing on that interval.
Convert M1's uint subtype of Int to Roadmap.Word Fin2^256 with an explicit range
proof; they are not definitional aliases. Reuse getBytes_congr/putBytes_frame
for range framing. Source-side fresh/init/key/heap facts remain M1's, not implied
by arbitrary target Memory. A partial-range view says nothing about gas/frames.

Do NOT replace the original producer by `emit 0 (.custom computed36)` and call
P4 done. It executes36 MSTORE8 writes (111 emitted instructions including PUSHes
and terminal), while original source has two word stores and pinned solc has
its own exact code/stack/control path. The theorem is about `emit`, not that
code. For short slices the emitter also leaves bytes after its payload untouched,
while original stores write through35 regardless of returned length. A final
slice equality is separate from program identity, final memory, attempted steps,
expansion and gas. M1's mstore64=128 prologue also needs the actual runtime entry
proof. No opcode/gas evaluator or erasing observational relation is introduced.

P4 still needs: (a) exact runtime code/path/stack/selector/arguments from EACH
retained pipeline; (b) correct big-endian unaligned MSTORE32/load semantics and
prefix initialization; (c) no-wrap/expansion/gas/host outcomes; (d) actual terminal
range/frame observation. G46.02/V15 owns byte representation/resources; G38 owns
its emitter/slice; compiler/source integration and this lane's same-bundle proof
must connect them. G38 local rollback is not permission to adopt a callback
judgment or new global source semantics. No such import or proof happens here.

## Existing P5b machinery: exact types and missing construction

M1 certifiedProducer returns `TRes (Out C σ.H (.mem bytesR :: Input))` with an
explicit actual size=36 premise. Its constructedBody is a TStep and explicitly
sets a scalar temporary to36. But Stmt.tryCall.sbody is `Prog C (ρ++ps) Γf`, not
a TStep and not a record with a freely assignable run field. A function run
cannot be cast into that inductive syntax. Metadata SourceFunction or f#7 alone
cannot construct or prove the source body's identity.

Already present, and byte-identical locally/published where recorded:
- litBytes(x,bs,k) : Prog C Γ Γ₁ constructs existing declMem/newArr, typed
  litWrite/assignMem sequence, then k. No new statement is necessary merely to
  reify an immutable computed snapshot as ghost syntax.
- Prog.run_litBytes(x,bs,k,σ) states full Prog.run = TRun.litBytesT bs k.runR σ.
- TRun.litBytesT_alloc(σ,bs,hn,k) equates the two runs AFTER map(·.st), where k
  starts at actual σ.allocPush(bytesObj σ.H bs hn). It is NOT already a full Out
  equality. If k is proved to halt, constructor inversion on map yields that
  exact halt; do not silently discard normal Out/extension information.
- TRun.revertData_mem and M1 readback/bytesHalt_exact supply the actual raw halt.
- Args.evalT : Args C Γ ps→TRes(TEnv C σ.H ps); CallRet.enterT takes the actual
  parameter state and produces Out C τ.H (rs++ps); TRun.call evaluates Args,
  enters this frame, runs body, then only on normal completion composes heap
  extensions and restores caller locals. Error bypasses leaveT.

The exact FIRST mechanical missing law is a closed-`Prog` reification of M1's
ghost halt (via these existing helpers), followed by a frame-entry transport law
for that constructed Prog. No duplicate byte foundation is needed for that law.
The FIRST original-SOURCE missing law is different: a checked source/callsite
construction relation associating original f#7 at c#105's actual36 entry with
that carrier. M1 StoreShapeCert only equates its typed plan with originalPlan;
its external AST checker is not a kernel lowering-correctness proof. Neither
G38 emission nor carrier reification supplies the missing association.

The source obstruction is concrete: local memoryRethrow? accepts exactly ONE
canonical revert(add(data,32),mload(data)) assembly statement. Original f's block
has THREE statements, two stores and revert(0,size). It returns none there;
Frontend.stmt reports unsupported. Published master retains the same refusal
at its updated line2447. Also directSelfTryContext(referenceOnly=false) rejects
InlineAssembly in this branch. That JS adapter is LOCAL to this retained task:
it does not exist at published8445c3fc (exact git absence recorded). Do not call
it a published foundation, import another branch, or force referenceOnly=true.

Existing SourceFunction retains exact source declaration/signature/mutability/
ABI role; FunDecl.sourceDecl and SolcFun.sourceDecl retain this metadata. Reuse
those, not another name-based resolution model. Original identity is C, source
original.sol/source-index0 (AST SourceUnit node141), contract C#140,
f#7/parameter#2 at17:216:0, c#105 at656:231:0, try#103/call#79/member#77/
receiver-this#76/argument#78/Panic-binder#87, signature
f(uint256)/selector0xb3de648b, c()/0xc3da42b8. Source hashes, compiler0.8.38+
1835d247/SHA6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390,
Osaka/optimizerfalse/runs200/appendCBORfalse and distinct legacy/viaIR input/output/
runtime/creation keys remain the [original identities](diamond-try-physical-design/fixture-identities.json).
No source, compiler input, expected bytes or verdict is modified.

## Concrete typed DESIGN pseudocode — NOT Lean declarations/proofs

All new capitalized certificate names below are PROPOSED, not imported types,
axioms or inhabited theorem premises. Existing types/operations are identified
above; actual headers are separately retained. `b` binds complete source/artifact
identity, not just a collision-prone hash equality. No untyped runtime IR.

```text
ps := [.val .uint]                 -- M1 Input; actual parameter #2
rho := []                         -- f returns void
kRaw : Prog C (.mem bytesR :: ps) (.mem bytesR :: ps) :=
  .cons (.revertData [.mem .raw .here]) .nil
inner36 : Prog C ps (.mem bytesR :: ps) :=
  litBytes (.user freshGhostName) M1.computed36 kRaw
carrier36 : Prog C ps ps :=
  .cons (.block inner36) .nil       -- ghost local does not escape

carrier36_halt (tau : State C ps) :
  (Prog.run tau carrier36).halt? = some (THalt.ofData M1.computed36)
  -- TO PROVE, not a certificate field:
  -- run_litBytes; litBytesT_alloc.map(st); existing raw-memory halt;
  -- invert map/error, then block/error laws. No normal Out equality inferred.
```

This carrier has no source meaning by itself. Its ghost heap object is NOT a
new physical allocation or charged opcode sequence, and must not be compiled
as new bytes(n) and substituted for pinned solc code. P4 relates the original
word stores directly. An unconditionally exported f(size)=carrier36 is WRONG:
M1 snapshot_length at a size3 span gives3 bytes, while computed36_length gives36.
This is a typed length countermodel/design control, not a fresh EVM receipt.

```text
args36 : Args C Gamma ps :=
  .snoc .nil .uint (.user "size") (.simple (.lit 36 checkedRange))
retF : CallRet Gamma [] Gamma := .rets .nil
sourceCall : ExtCall C Gamma :=
  <.env .selfAddress rfl, resolvedNativeAlias(f#7), [<.uint,.lit 36 checkedRange>]>
selfFlag := true                    -- original this.f, no oracle substitution

structure CapturedEntry (sigma : State C Gamma) where
  evaluated : TEnv C sigma.H ps
  argsEq : Args.evalT sigma args36 = .ok evaluated
  entered : Out C sigma.H ps
  enterEq : entered = CallRet.enterT retF (sigma.withEnv evaluated)
  sizeEq : TEnv.get M1.sizeSlot entered.st.env = M1.size36
  -- no run result/hcall/desired bytes field

literal36Entry(sigma) : CapturedEntry sigma
  -- TO CONSTRUCT from existing equations, no semantic assumptions:
  -- evaluated=(36,()); entered=(sigma.withEnv evaluated,refl)
```

At this inner f call no return-default object is allocated: rho=[] and
enterT(.rets nil) is identity over that parameter state. Arbitrary live caller
heap and alias objects remain in H with the SAME IDs; caller env roots do not
become physical callee roots because entered.env contains only size. Preserve
all storage/net/balance/TTx fields. Physical byte frame is fresh; do not assert
logical heap empty. M1 scalar-frame proof and inhabited aliasCaller illustrate
this distinction. The caller c has a SEPARATE hidden uint return slot; do not
mistake it for f's empty return context.

For original this.f, the receiver reads actual self, NOT the synthetic literal7
used by M1 controls and NOT a fixed global address/profile. Nonzero self is an
explicit local success condition. Current selfFrame lowering rewrites msg.sender
reads to selfAddress and msg.value reads to0; it does not mutate TTx to arbitrary
callee context. f's body reads neither, but its source association must preserve
that rewrite and withPanics/inlining construction. Published lowering differs
from local bytewise, so exact respective blobs are recorded; no API equality
beyond inspected definitions is assumed. Existing body-order/decl-resolution
rules still require source f before c, established by source spans/dependency
closure, not merely numeric7<105.

```text
structure CallsiteBodyConstructionAt36 (b, C, Gamma, sourceC, sourceF) where
  identity : existing SourceFunction for original f#7, public/selected/pure,
             signature/selector + bundle/source/member/reference identities
  args : existing Args C Gamma ps
  argsConstruction : args = args36
  occurrence : exact checked THIS c#105/try#103/call#79/#77->f#7 linkage
  body : Prog C ps ps
  bodyConstruction : body = carrier36
  origin : carrier36 was generated from M1's computed typed plan, NOT expected bytes
  originalAtCall : CheckedSourceConstructionAt b c#105 f#7 parameter#2 36 body
  -- MISSING relation/constructor, must be proved by a verified scoped source
  -- recognizer/reifier, not accepted as hcall or source-run/bytecode adequacy

call_halt_from_construction
  (binding : CallsiteBodyConstructionAt36 ...)
  (entry : CapturedEntry sigma) :
  TRun.call binding.args retF .refl binding.body.runR sigma =
    .error (THalt.ofData M1.computed36)
  -- TO PROVE: unfold actual call/args/enter; carrier36_halt.
  -- Mechanical proof still does not CONSTRUCT binding.originalAtCall.
```

The body/Args equalities make the mechanical transport precise; they are not
original-source association proofs. C must be the contract produced for owner
C#140 in the same bundle, rather than any arbitrary contract sharing a name.
Current TTx has no runtime code-installation registry: do not invent a body/code
lookup or claim nonzero address proves installed EVM code. Logical self dispatch
uses the explicitly carried body; actual installed runtime identity belongs to
P4's target context/source linkage.

The new relation must have inspectable, nonvacuous constructors for EXACT whole
resolved source nodes and typed operands/positions, plus a replay/normalization
correctness proof. It may not contain an arbitrary desired outcome as a field,
or merely a Python guard/oracle/hcall assumption. Existing imported SourceFunction
metadata alone is insufficient. Current definitions CANNOT construct
originalAtCall: f body lowering is unsupported. A proposal that leaves this as
an abstract always-assumed premise does not close P5b. Full original FuncDecl
must be retained; the scoped specialization is attached only to this exact
inlined call occurrence, never rewriting global f's semantics/domain.

### Continuation, heap, failure and nonvacuity obligations

On the derived raw halt, existing TRun.catchBytes_self_data transports actual
immutable bytes without reading ext. Existing tryCall decodes Error first then
Panic; approved decodePanic binds67 at36 bytes. Panic handler receives
TEnv.append([uint],CodeBinder.some("c").decodeT(67),sigma.env), updates c's
actual return slot, then ends that return path and drops its own scope. Reuse
existing catchData_self_data for later data handlers rather than duplicating it.
On error no callee Out/ghost heap reaches the caller; handler starts from the
ORIGINAL sigma. Normal Out transport must keep exact Ext composition, TEnv.wk,
CallRet.leaveT and contexts, never equality across different Out-context types.

Positive nonvacuity gate: for BOTH bundle keys, actual args36/enter witnesses
and a sigma with nonzero self + preexisting object/two alias locals must construct
carrier and return witness. Preserve M1's concrete both_constructed_returns/
aliasCaller controls as component controls, not evidence of original binding.
The new source constructor must then be inhabited from the actual source closure;
without that, P5b remains open regardless of carrier success.

Negative/refusal gates: wrong file/bundle/pipeline/whole source/callee/parameter/
selector/caller/member/reference/order/shape/arg value, wrong body with identical
bytes, wrong self/call code identity, escaping ghost local, wrong heap/Ext/alias/
return slot/catch bytes/normal outcome. A source36 certificate must refuse other
actual parameter values; refusal is NOT a revert or a global target restriction.
Zero receiver fails before callee/catch. Any argument-evaluation error occurs
before enter/body and is not caught by constructor/callee handlers. Selected
handler failure and its tail are not recaught. Source early return must suppress
the actual later assert(false) in _2/_3; setting a return slot alone is not that
control-flow theorem. Existing try-scope normalization ownership stays untouched.
Gas exhaustion/invalid/host stop/divergence are never completed reverts by Option
none, fuel mismatch or a pure image theorem. Callback universal counterexamples
remain negative; no ordinary witness implies ValidT/holdsC under current meanings.

## Updated P0–P8 readiness and smallest future implementation

| Layer | After actual M1 and current published evidence | Remaining exact obligation |
|---|---|---|
| P0 | M1 exact two keys, source/AST external controls and source literal | Verified source construction of the callsite certificate, not hash injectivity |
| P1 | M1 scalar spans/zero/overlap/snapshot; published G38 byte range helpers | Full object layouts/copy/load/ISA/physical resources remain full-design work |
| P2 | Constructed fresh/prologue image and nonvacuity | Actual same-pipeline dispatch/entry/resource correspondence, not assumed prefix |
| P3 | Two-store36 source-linked component | Source parametric sizes and remaining five-row producer/continuation account |
| P4 | Newly published MSTORE8/range/RETURN/REVERT/emitter subset | Original MSTORE32 + real code/stack/expansion/gas/call simulation, G46.02/G38/interfaces |
| P5 | M1 exact ghost capture/IDs/heap/frame/raw halt | Prog reification law above; never extra physical allocation/cost |
| P5b | Existing actual Args/CallRet/call APIs; exact mismatch/proposal above | First mechanical carrier reification, then genuinely source-linked construction at c#105; no assumed hcall |
| P6/P7 | M1 constructed deterministic raw/code/return controls + preserved decoder | Original source handler/return/tail proof; other sizes and Error interior payload/sentinel logic |
| P8 | Current native host and body lowering still refuse the assembly | Separately approved checked source-certificate consumer/admission policy and full ordered dual-pipeline replay; no force-reference, D3 removal or global target change |

Smallest future scope FOR REVIEW ONLY: one task-owned proof module reifying
M1 computed36 into closed existing Prog and proving actual literal Args/enter/
call halt transport, with precise SourceFunction/whole-node descriptor and
negative mismatch controls. It closes the real TStep→Prog mechanical gap needed
by original Stmt.tryCall, using existing litBytes laws; it is not another byte
interpreter or proof of original f. Next scoped source-construction implementation
must make originalAtCall inhabitable from the whole original declaration/callsite,
without unconditional fixed36 global f replacement. Both require later approval;
NO implementation is made now. P4, P5b and P8 stay independently reviewable gates,
not an implied all-or-nothing new global profile choice.

The tradeoff is explicit: reify a scoped carrier first (small, no admission or
new statement, but original source association still open), or seek later approval
for the combined scoped source-construction proof/consumer (larger and must resolve
current excluded-body type boundary, with P4 still external). Do not choose a
fallback ordinary revert for all n≠36 or narrow source admissibility to make it
pass. A full parametric f producer/lowering is the eventual general alternative,
requiring the remaining design's feasible/outcome/layout cases, not authorized
here. No fresh generic foundation or historical-runner question is asked.

## Remaining original ledger and validation limits

Retained current family ledger is20original rows:12nativeworking/8blocked,
18referenceworking/2historicalblocked,66/140old ordered comparisons; fresh0.
Five malformed files retain21observations/pipeline=42, with _4.d declared but
NOT an original observation. malformed_panic.sol has M1 n36 only; a3/b6/d256 and
original whole source are unclosed. _2/_3 need short actual raw rethrow, caught
36/256 and early-return tail; _4 adds ordered Error refusal but no invented d
receipt. malformed_error needs four stores, overwritten free-word/zero-slot,
actual interior Error copy/uint64/length guards, default sentinel and exact
string capture/return for3/6/67/74/75/256. Reuse the full design, not G38 `.reason`
encoding as a malformed source producer. invalid_error_encoding remains the
policy-blocked external-reference/ABI owner lane, not a task moved here. Both
pre-Byzantium rows remain unexecuted and historical choices unchanged. The12old
working rows are not re-run or newly passed. Exact frozen metadata/receipt hashes
and per-row boundaries are retained in family-ledger.json/original-identities.json.

No new historical B capability follows from a pure target slice. Official
v0.22.0/ABI13/source/build-edge/tracer limitations stay as in the preserved
[official feasibility report](diamond-try-official-evmone.md); no redundant
backend inventory or official-source fetch was repeated. No engine ABI or
abortable shared-step contract was supplied by these published kernel modules.

Evidence-only proportionate checks are hash/type-header/provenance/ancestry,
full retained-checksum integrity, generated inventory unchanged and document/
whitespace checks. No cold/full Lean build, MCP, fresh axiom, compiler or fixture
run is claimed. Retained M1 5cleanMCP/290standard-only audits and full/code gates
are unchanged historical inputs. Document checker retains its actual exit1
with exact current/base comparison and zero new findings only if checked.
Read-only finder/skeptic reviews record actual scope; no server/build use.

GateG0/history constraints remain: do not reindex State/Fml/Stmt with physical
layout or use indexed matches in hot folds; preserve linked recursor twins.
Future small carrier/entry proofs are estimated seconds–minutes/low single-digit
GiB using warm imports, not measured guarantees; actual source proof and target
composition costs unknown. Hard12GiB/swap0, serial Lean-j1/threads1, disk caches,
writer lease and OS/disk headroom stay binding; no fuel/node/heartbeat/test or
100M/5M/120s/literal8000 increase. Current source-only checks need no Lean config.

## Actual checks and independent review for this increment

The static integrity command passed (exit 0, 1 s): 28 published blobs, five M1
blobs, 19 exact source headers and all 2,386 retained evidence checksums matched.
The original baseline is an ancestor of both retained HEAD and the fetched
published commit. Existing Lean hash-manifest contents are unchanged. These
are source/hash checks, not newly elaborated theorem or execution evidence.

Generated feature inventory check passed (exit 0, 1 s; 212 features, 783 symbols).
Strict documentation paths retained exit 1 (3 s): its complete pre-footer output
is byte-identical to the M1 baseline, including 20 missing references and all
ambiguity notices; zero new findings. Both read-only reviewers found no concrete
defect, checking actual source headers, frame APIs and the typed/source boundary;
the final tightening review checked occurrence identities and explicit Args/body
equalities. They ran no Lean, build, compiler, fixture or EVM commands.

All three static check groups verified memory.max=12,884,901,888 bytes and
memory.swap.max=0, with no max/OOM events. Largest measured cgroup peak was
24,494,080 bytes; largest sampled aggregate RSS was 24,428 KiB. Disk had 22 GiB
available and host MemAvailable exceeded 16 GiB before checking. Each group
held the writer lock, ran serially and inherited LEAN_NUM_THREADS=1; no Lean
invocation or temporary Lake configuration was needed. Full mandatory original
assignment gates remain retained historical evidence, not rerun or newly passed.

The next scoped implementation would prove the mechanical closed carrier/entry
laws, with explicit limits, or additionally implement the constructive checked
source association under a separate reviewed approval. Neither is implemented
here. P4 and P8 stay independently gated. This is a design checkpoint, not an
original-assignment completion or an integration delivery.

Callsite-specific static c()->this.f(36) refinement: [exact PCs, frame/source obligations and held Cancun plan](diamond-try-c36-path-design.md). No P4/P5b/P8 implementation or status improvement.

Post-carrier source-construction frontier (design only): [generic original f and local36 derivation](diamond-try-source-construction-design.md). Carrier/Args/call/catch proofs are now completed; original P4/P5b/P8 remain open.
