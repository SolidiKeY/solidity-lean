# Original c()->this.f(36): conditional compiler path and source construction

Evidence/design increment from clean af34584f93b36286ec063fa948bc1685923411a4.
The accepted M1/design/Osaka turns are not replayed. Native12/8 strictEXIT1,
P4/P5b/P8 and both historical rows stay open. No Lean, compiler, backend or
fixture is invoked here. No new interpreter, relation implementation, checked
source admission, D3/default/callback/target/expectation/budget change.
This extends [post-M1 readiness](diamond-try-post-m1-design.md); original full
[physical proof obligations](diamond-try-physical-design/proof-plan.md) remain.

## Exact artifacts and epistemic boundary

Only retained static-frontier malformed_panic-osaka-{legacy,viaIR}-input/output,
assembly, optimized Yul and source maps were decoded. Exact complete source is
M1 originalSource: SHA256522bfa3512517476f4f06cef823b176afe52978eb52393b25783e30d10ccc311,
original.sol/source-index0; compiler0.8.38+1835d247 SHA256
6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390.
Osaka, optimizerfalse/runs200/appendCBORfalse and both distinct input/output keys
are preserved in [bundle identities](diamond-try-c36-path/bundle-identities.json).

| Pipeline | Creation length / runtime offset / runtime length | Runtime SHA256 |
|---|---|---|
| legacy | 1701 / 28 / 1673 | e335ea9f2867baaaf40c876fa250ffd2bece75a4b833be111d97f9d2c1b799cc |
| viaIR | 2008 / 43 / 1965 | faf0d96218acbf1285125e35959e2ab4babebd7f6e64446c25445aa203c90d52 |

The full creation hashes are respectively
988857e8e73099fe3e0b04beb535cf254d303aa88db9a5bd25550126fe7fe2ad and
0a86ca6323640d3728309fe5b57961ef2c15c634714fd2959d6853855ca5d470.
These byte hashes equal the *retained*, accepted Osaka reference report's two
artifacts. Its compiler input hashes differ (preamble/unit/output-selection),
so this equality does not identify AST/source occurrences across invocations or
prove compiler correctness; exact [comparison](diamond-try-c36-path/reference-byte-identity-comparison.json).
No fresh runtime receipt or reproduction of its passing tests is claimed.

Each decoded instruction retains byte PC, operand, compressed source-map fields
and exact source substring. Static byte splitting has NO state/stack/PC-transition
evaluator. A source map is compiler attribution, not a proof that a branch runs.
Legacy generated helper sourceID1 is retained; viaIR often attributes helpers
to the entire source contract or -1. Helper identity there comes from THAT
bundle's assembly/Yul/debug entry, never an invented narrow statement map.

The [complete callsite ledger](diamond-try-c36-path/path-ledger.json) lists every
relevant constructor/dispatch/caller/callee/helper/terminal range and all its
instruction PCs, including alternative failures. [Call frames](diamond-try-c36-path/call-frames.json)
name explicit callee/continuation labels occurrence by occurrence. Their JUMPDEST
and opcode facts are checked statically; frame integrity and reachability are
NOT proved. No shared indirect JUMP is assigned a universal destination.

## Conditional compiled path (PCs decimal, per section/frame)

The following is a *conditional path design*: exact instruction locations and
Yul structure are facts; traversing them assumes correct installed artifact,
entry arguments/context, intact stack/return labels, normal execution of each
prefix instruction and sufficient resources. No guessed path/gas bound is proved.

| Stage | legacy runtime PCs | viaIR runtime PCs | Guard/transport obligation |
|---|---|---|---|
| Fresh runtime prefix | MSTORE4 writes64=128; callvalue11->15; size24 avoids85 | MSTORE4 writes64=128; size12->18; selector helper107 returns28 | Separate fresh caller/callee memories; outer callvalue0; calldata at least4; code/init/resource claims still conditional |
| c selector | c3da42b8 PUSH75/EQ80/JUMPI84->207 | c3da42b8 PUSH73/SUB78; false82; JUMP86->429 | Earlier a/b/d/f selector comparisons fail; no selector match goes to fallback, not f |
| c body | JUMP214->879, continuation215 | wrapper429: value434 avoids477; voiddecode127 returns445; JUMP455->1732, continuation456 | Original c#105 hiddenreturn#74 initialized0; c has no args |
| Receiver/selector/argument | ADDRESS881/mask903; selector904; literal36 at909 | ADDRESS1745; cast544/532/504/490; selector1751; literal36 at1756 | Actual this/current code identity, not synthetic address7; size literal AST#78 |
| Code check timing | EXTCODESIZE949 after argument stores; nonempty956->960; empty REVERT959 | EXTCODESIZE1759 before allocation/encoding; empty1764->1960->556/REVERT559 | Code guard failure is outside child catch; never reinterpret missing code as f's generated Panic |
| Calldata construction | MLOAD913=128; selector MSTORE925; encoder1648/1633 MSTORE1644 at132; return938 | allocate113 returns1781; shift631 returns1793; selector MSTORE1795; encoder1711/1698 MSTORE1709 at132; return1804 | Actual input memory[128,164): selectorb3de648b + uintword36, length36; no extra incoming calldata/lazy ABI lane |
| Child operation | GAS962/STATICCALL963 | GAS1807/STATICCALL1808 | top-first operands conditionally gas,self,128,36,128,0; STATICCALL, no CALL/value transfer and no output copy; actual child failure required for catch branch |
| Child f dispatch | same fresh prefix then fselector69/73->179 | same fresh prefix; fselector68/72->87; JUMP91->403 | Installed exact f(uint256) selector b3de648b; child value0; calldata36; same self/code address |
| Actual uint parameter | wrapper199->1175->1155 CALLDATALOAD1158; validator1133/cleanup1080; return200; JUMP204->835 | wrapper418->373->358 CALLDATALOAD361; validator338/cleanup142; return419; JUMP423->1649 | Calldata offset4 word36, end-start32 passes bound; formal#2 externalReference212:4:0, not caller returnslot#74 |
| Actual f stores | PUSH32 selector836; MSTORE870 offset0; MSTORE875 offset4 value67; DUP876 actual size | PUSH4+SHL1657; MSTORE1659 offset0; MSTORE1664 offset4 value67; size already carried | Actual big-endian stores overlap[4,32); prefix64=128 remains; no allocation occurs in this f prefix; this is not yet target simulation |
| Child terminal | REVERT878 offset0/size36 | REVERT1666 offset0/size36 | Actual raw slice[0,36) computed from operations, no expected/reference byte injection; gas/resource failures are separate |
| Failure branch | 973->977; no981->1061 | no1814->1916; no1823->1902 | STATICCALL successbit0, returndata36. Success-only result handling remains distinct |
| Selector check | 988->1321 return989; COPY1336[ret0,4)->caller[0,4); shift1309; SUB995 zero | 1832->749 return1833; size>3 branch759->762; COPY769; shift107 return779; EQ1839->1866 | Check actual length/selector before Panic payload; no source Error catch here |
| Panic data check | 1006->1352 return1007; size>35; COPY1369[ret4,36)->caller[0,32); MLOAD1375 | 1873->785 return1874; size>35 branch796->799; COPY808; MLOAD813 | Approved prefix decoder yields actual uint67; trailing accepted by decoder, short/wrongselector not eligible |
| Selected Panic tail | decoderflag1012->1018; asserttrue1024->1033; return c94 at1041->1077; exit1079->215 | decoderflag1879->1885; assert_helper737 returns1899 for true; return1901->456 | Binder#87 at769:6:0, returnidentifier#93 resolves87; earlyreturn#94 sets original cslot#74 and terminates this function branch |
| c ABI result | tuple1104/word1089 MSTORE1100 at128; return228; RETURN236 offset128,length32 | allocate113 returns464; tuple158/word145 MSTORE156 at128; return473; RETURN476 offset128,length32 | Code67 word, actual heap/frame/output context; no success/catchall tail after this return |

Creation is separate from both runtime frames. Legacy constructorPC4 writes
64=128, zero value takes10->14, CODECOPY24 copies creation[28,1701) to memory0,
RETURN26 length1673. INVALID27 is delimiter; the rest is copied runtime, not
constructor instruction flow. ViaIR constructorPC4 writes64=128; zero value
JUMP13->32 reads freepointer and returns14; CODECOPY22 copies[43,2008) to
memory128, RETURN27 length1965. Nonzero value goes8->28->38/REVERT41. INVALID42
is delimiter. No metadata suffix (appendCBORfalse). Constructor memory is not
reused as runtime memory. Installation/rollback/address/context/resource laws
remain existing runner/World obligations, not facts established by byte splitting.

### Failure and resource alternatives are not erased

Legacy missing/short selector REVERT88; nonpayable runtime rejection REVERT14.
ABI short uint goes1175 bound branch to1129/REVERT1132; invalid typed word
validator failureREVERT1151 (uint256 cleanup is identity, but no free shape
cast). ViaIR fallback482/REVERT485, external nonpayable guard477->119/REVERT122,
ABI short uint398->123/REVERT126, validatorREVERT357. Missingcode is the
pre-child guard above, with its pipeline-specific timing.

If child unexpectedly returns normally: legacy981->1061 assertfalse; viaIR
1814->1916 performs normal empty-return ABI/allocation handling then1902
assertfalse. ViaIR finalize_allocation590 has its real uint64/wrap guard and
Panic0x41 alternative; do not classify it as source f's code67. Wrong selector
or short Panic payload reaches legacy1042 or viaIR1852 catchall assertfalse.
Assertion false produces Panic1 helper (legacy1382, viaIR717); it does not
rethrow f's raw bytes. Assertiontrue goes directly to selected return as shown.

Every opcode can fail from resource/context constraints not supplied by this
static map. In particular child OOG/empty returndata/call-depth or invalid code
cannot be replaced by completed raw Panic67. EIP150 GAS forwarding, memory
expansion, shared5M attempted steps, parent remaining gas and120s host stops are
unproved here; no target evaluator or guessed gas path bound is introduced.
Exhaustion/divergence/host interruption stays a stop/inconclusive outcome.

## Typed source construction refined around these occurrences

All capitalized new names/signatures below are DESIGN PSEUDOCODE only; none is
a new Lean declaration, axiom, inhabited premise or installed simulation relation.
Existing intrinsic syntax/state/value types are reused; raw source/assembly
records are external provenance, not a second untyped operational language.

Whole-source identity: sourceUnit AST141, owner C#140; f#7 at17:216:0 has scalar
parameter#2 at28:9:0, assembly#5 at61:166:0, stores84:77:0/174:15:0 and terminal
202:15:0. Its Yul size externalReference at212:4:0 resolves exactly#2, valueSize1,
not slot/offset. c#105 at656:231:0 has hidden return#74, Try#103, Call#79 at
705:12:0, Member#77->f#7, receiver-this#76, literal#78=0x24. Success#85,
Panic-clause#96/binder#87, Return#94/Identifier#93->87, catchall#102 are ordered.
Names/types alone cannot resolve these occurrences or owner/whole-body identity.

```text
psF := [.val .uint]; rhoF := []; GammaC := actual elaborated c-body context
-- GammaC contains the hidden uint slot associated to source declaration74.
-- psF can have the same Ctx shape, but parameter2 and return74 are NOT one local.

carrier36 : Prog C psF psF :=
  .cons (.block (litBytes ghostName M1.computed36
    (.cons (.revertData [.mem .raw .here]) .nil))) .nil

carrier36_halt (tau : State C psF) :
  Prog.run tau carrier36 = .error (THalt.ofData M1.computed36)
  -- FUTURE mechanical proof from existing run_litBytes + litBytesT_alloc.map(st)
  -- + actual immutable byte readback/raw halt + block error inversion.
  -- Never infer full normal Out equality merely from map(st).

EntryAtC36 (sigma : State C GammaC) := proposed typed record with
  evaluated : TEnv C sigma.H psF
  args : Args C GammaC psF
  argsConstruction : args = actual resolved literal36 argument program
  argsEq : Args.evalT sigma args = .ok evaluated
  entered : Out C sigma.H psF
  enterEq : entered = CallRet.enterT (.rets .nil) (sigma.withEnv evaluated)
  sizeEq : TEnv.get M1.sizeSlot entered.st.env = M1.size36
  occurrence : source bundle/owner140/c105/try103/call79/f7/parameter2 linkage
  -- no desired run outcome, final byte sequence, hcall or target adequacy field

CheckedOriginalAt36 b (C140 : exact owner) (entry : EntryAtC36 sigma) :=
  proposed CONSTRUCTIVE checked source-occurrence/body-construction derivation
  over the full original f declaration and that one actual inlined callsite.
  -- Must check all stores/externalReference2/actual size expression and preserve
  -- selfFrame/withPanics lowering and complete c clauses/earlyreturn.
  -- Existing metadata/hash/source parser equality is NOT this derivation.

call36_halt_from_constructed_prog (entry : EntryAtC36 sigma) :
  TRun.call entry.args (.rets .nil) .refl carrier36.runR sigma =
    .error (THalt.ofData M1.computed36)
  -- derive actual args/enter/body; this alone is STILL a constructed-call fact.

source_callsite_halt (construction : CheckedOriginalAt36 b C140 entry) :
  actual source-carried call at c105/call79 reduces to the preceding derivation
  -- MISSING source correspondence law, not assumed hcall/desired bytes.
```

A local n=36 equality must be DERIVED from the actual literal Args, not added
as a new source/specification assumption. Nonzero actual self is an explicit
conditional model success condition; no global admissibility/target restriction
is introduced. Physical outer CALLVALUE0/installed code and normal-prefix
conditions for this static path are separate target obligations, not silently
strengthened source specs or established by that nonzero condition.

Arbitrary live caller H is retained when sigma.withEnv evaluated discards
caller locals for scalar f parameters; `enterT(.rets nil)` has empty f return
context and preserves H/fields. It allocates no f return object. A fresh ghost
bytes object in carrier is typed at the extended H, distinct from all retained
objects and preserving their identities/aliases/order; on error the Out does
not leak to caller. Immutable raw bytes survive and handler starts from the
ORIGINAL sigma. This allocation is not EVM physical allocation, expansion or
cost. The callee physical frame is fresh even though the logical H is not empty.

Context warning: M1.frameKey records the logical entered.st.tx fields unchanged.
Current selfFrame lowering rewrites sender/value *reads*, not TTx. Physical
STATICCALL child sender is the parent self, value0, self/code address unchanged;
those need NOT equal every logical frameKey.sender/value field. Do not equate
them or normalize the state. f here observes size/memory only; an eventual
context-abstraction/frame law must prove the relevant projection/identity facts
without changing default judgment or treating nonobservation as an axiom.

After derived actual hcall, reuse existing catchBytes_self_data with actual
receiver .env.selfAddress, hnz, hself and self=true; no oracle lookup replacement.
Decoder code67 uses the approved semantics and actual produced bytes. Handler
context is `[val uint binder87] ++ GammaC`; its return accesses the distinct
cslot74 through the correct shifted index, then drops handler scope and returns
from c. Existing return normalization stays with its owner. Slot assignment
alone is not earlyreturn/tail control. Normal Out branches must preserve exact
Ext composition, TEnv.wk and CallRet.leaveT; error branches restore original H
and caller locals/storage/frame. Handler failure is not recaught, and argument
failure precedes child/catch. Empty oracle is irrelevant to this self=true
constructed call; it cannot justify arbitrary external-call source coverage.
Existing universal callback counterexamples remain negative.

n=3/6/256 are NOT specializations to this carrier. Their Args/literal/bundle
occurrences differ (a#39/b#71/d#139), and physical terminal length changes. n3/6
fail the Panic length guard and take catchall, returning0; n256 returns a longer
raw payload including initialized freeword and zero tail, though approved
decoder still yields67. Returning67 at n256 does NOT equate raw256 with raw36.
Capacity96 is M1's witness, not an admissibility bound; original f(uint) remains
parametric over all uints, with resource/overflow/large-range alternatives open.

## First missing laws, precise ownership and a bounded next milestone

No general foundation inventory is repeated. We reuse the already inspected
reachable published master8445c3fc203144251b9d1fc9181f7f61a8189522, with exact
[API blobs](diamond-try-c36-path/api-provenance.json); no new fetch/import/build.

* Existing Semantics.Run Args.evalT(sigma):Args C Gamma ps -> TRes(TEnv C sigma.H ps),
  CallRet.enterT(ret)(tau):Out C tau.H (rs++ps), and Prog.run_litBytes provide
  mechanical inputs. AllocBytes.litBytesT_alloc equates only `.map(.st)`.
  RevertMemory.catchBytes_self_data explicitly requires the actual derived hcall.
  M1 certifiedProducer_exact is LOCAL checkpoint3ee3855c, not a published import.
* FIRST mechanical law still missing is `carrier36_halt` and actual literal-entry/
  call transport above; it is independent proof work, not authorized here.
* FIRST original SOURCE law is constructing CheckedOriginalAt36 (whole resolved
  declaration/body/callsite, with a sound scoped construction/reduction theorem).
  Current published Frontend.SolcJson.Body.memoryRethrow?(declarations:List Json)
  (j:Json):Option Json accepts exactly one canonical rethrow; actual f has three
  assembly statements and cannot inhabit that consumer. Source integration owner
  is the frontend compiler lane plus this task's narrowly scoped try source
  composition; P8 consumer/admission remains separately gated. There is NO
  published signature/theorem for this missing relation to cite as if available.
* FIRST original TARGET law is the byte-level actual MSTORE32/load/dispatch/
  STATICCALL frame/resource correspondence over the specified original code PCs.
  G46.02/V15 owns byte representation/expansion/resources; R31 needs the final
  bridge. Published G38 Failure.Slice.step:Instr->Machine->Option(Machine x
  Option Roadmap.Outcome) supports MSTORE8/RETURN/REVERT, not original MSTORE32,
  MLOAD or host CALL/STATICCALL/gas. Its emitter correctness requires Fits and
  stack bounds and concerns different emitted code. Slice/Correct published
  change4cb5d0aff8b4e71e2de0726869bb408a69b4719b supplies reusable interval facts,
  not this first target law. Missing full target API is a precise owner boundary,
  not an abstract assumed bytecode-adequacy premise or permission to implement it.

Smallest future implementation choice is proof-only carrier36_halt + literal
Args/empty-CallRet entry/call transport, over existing constructors. Acceptance:
explicit all live-H states, a nonzero-self/oldobject+twoalias positive control
per pipeline key, actual args36 witness and actual raw halt; old refs/Ext/frame/
scope preserved; reject wrong Args/parameter/body/owner/selector/bundle/frame,
wrong bytes, non36 length controls, empty/malformed payload, zero receiver and
callback misuse. No globalf replacement or source improvement claimed. Expected
warm checking cost seconds–minutes/low GiB is an ESTIMATE, not measured proof
budget approval. G0 recursor conventions/no hot indexed matches and all current
heartbeats/fuel/nodes/tests/hard12GiB/swap0/serial-j1 stay unchanged.

A milestone claiming P5b additionally MUST construct the whole-source derivation
from the exact original source and prove the scoped normalization/return/frame
law, nonvacuously for both bundle keys; stop if current Prog/source representation
cannot support it without new admission/profile semantics. A milestone claiming
P4 additionally needs the owner-produced actual byte-memory/resource relation,
including each failure boundary, not this static path. P8 requires separately
reviewed consumer/admission and full original ordered dualpipeline replay.
These broader implementations are unapproved; no opaque hcall/final-byte field
is an acceptable fallback. No source row or original-family status improves here.

## Held validation plan and unchanged ledger

[Concrete Cancun plan ONLY](diamond-try-c36-path/held-cancun-plan.md) identifies
exact source-admission/vectors88 commands, three actual source files and every
transitive selection route, both legacy/viaIR and existing Cancun settings.
Source-admission performs22 calls; vectors88 performs88; all existing expected
observations and30Mgas stay unchanged. Neither imports the upstream corpus or
selects a historical file. Crucially, these existing scripts do NOT enforce the
reference machine's5M attempted-step hook. Gas30M/timeout120s are not that
guarantee. That unchanged host limit remains mandatory; its missing hook/envelope is a
further concrete tooling prerequisite, not permission to instrument/raise bounds.
Listener input is pending; neither command/group nor an indirect route runs.

Native12working/8blocked strictEXIT1, old66native/reference+140reference/frozen
account, accepted freshOsaka146tests/66native/8single-reference observations and
retained full library/TestSuite/Corpus/strict/trust/MCP/standard-only axiom audits
remain separate historical inputs. No new passing validation or kernel theorem
is claimed. Six physical/reference source rows and two historical rows remain
unfinished; policy-blocked ABI is outside this scope. No historical inventory
or backend/runner/action A/B is repeated or implemented.

## Actual source-only validation and review

Static decoder exit0 (1s) expanded retained byte/source-map records only. Static
integrity/control check exit0 (1s) checked2,309 runtime instruction records, exact
selected opcode/operand/AST/externalReference identities, constructor boundaries,
manual frame-label destinations and six negative static controls (wrong CALL,
argument, selectorword, MLOAD opcode, non-JUMPDEST return labels). It did not
evaluate their stack/control meaning. All2,386M1/2,454post-M1/2,510Osaka prior
evidence checksums matched; no prior file/export/rejection/failure was discarded.
Both static groups verified memory.max12884901888/swap.max0/max-OOMevents0;
largest cgrouppeak31,014,912bytes, sampledRSS18,140KiB. Disk22GiB available and
host MemAvailable17,095MiB observed, diskcache/writerlock/threads1 kept; no Lean
command/config or MCP, compiler, fixture, backend or held-group run occurred.

Independent finder checked principal PC/guard/helper/store/decode/return claims
against retained TSV/constructor/callframe and actual Yul; skeptic checked typed
source/frame/owner/fixed36 limits and held scripts' actual imports/settings/call
paths. Neither certified every PC, reachability/resources, later gates or source
adequacy. No concrete defect found; no scripts/checks/Lean/server/compiler/EVM
were run by reviewers. [Actual scope](diamond-try-c36-path/reviews.txt).
Documentation paths keep actual historical exit1 and zero new findings only
after exact output comparison; subsequent check details are retained below.

Final documentation check retained exit1 (4s): complete pre-resource-footer
output byte-identical to accepted Osaka baseline,20missing and unchanged
ambiguities,new0. [Exact comparison](diamond-try-c36-path/documentation-comparison.json).
Generated inventory --check exit0 (1s),212features/783symbols,current; no manual
generated edits. All source-only checks remain distinct from retained full
Lean/strict/trust/runtime gates. Accepted prior receipts are acknowledged in
[delivery](diamond-try-c36-path/delivery.json), not cleared or replayed.

[Exact check/resource results](diamond-try-c36-path/validation.json) include all five
source-only groups: largest cgrouppeak31,014,912bytes and sampled aggregate
RSS28,600KiB; writerlease/hard12GiB/swap0 verified with no max/OOM event.

Post-carrier source-construction frontier (design only): [generic original f and local36 derivation](diamond-try-source-construction-design.md). Carrier/Args/call/catch proofs are now completed; original P4/P5b/P8 remain open.
