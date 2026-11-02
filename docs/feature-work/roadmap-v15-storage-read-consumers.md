# V15 charged storage-read consumers

This G46.03/Backfill A-B checkpoint follows helperfcb013963f7e577093f2b07160802a030cf30c15.
Helper published base remains e7cc378c275eafe7a047c63f672bedbed2fec6ff; original
frozen base2fe1f8932f96be15b00df03ba2cde46f64a87758. Required fresh fetches before
P10 and this next storage item both succeeded at febf70a6ba99df908a69499aca026381c3993102.
Its Backend/Storage/Bridge producers are byte-identical to the helper base;
no foreign branch or unrelated entrypoint changes were adopted. Original main/
private work, goal, sealed exports and failed receipts stay preserved.

P10's G45.03 execution meaning is not supplied by that publication: Backend
Control still proves expansion/layout/jump positions, not its execution meaning.
QG45 requests the exact committed module/signature packet, including code,
frame, stack, scanner and resource premises, from its owner revert-outcome-specs.
This specific dependent composition stays open while independent storage work
proceeds. G45.03 and hash G46.05 remain read only with that owner. Next assigned
items are memory/storage, environment G46.04, then decoder G45.05-BR.

Owned `Bridge/SolidityBridge/RoadmapV15/P10/StorageReadConsumer.lean` has twelve
public facts. Backend emitted SLOAD/TLOAD decode is derived at arbitrary typed
Site; native key/tail is installed without a desired execution or frame premise.
Actual driverGate memory/gas/arity/capacity/static checks and EVM.step derive
whole charged State and X continuation. Input tail.length+1≤1024 and adequate
actual gas remain explicit. SLOAD costs100 for the actual owner/key warm pair,
otherwise2100 (universally bounded2100). TLOAD costs100. The returned values and
state are the EXISTING State.sload/tload pairs: persistent reads add an accessed
storage key; transient reads retain substate. No new account/storage semantics.

slotWord observes actual UInt256 reads as intrinsic Semantics.Word. Existing
G27 ValueRep, Transport and source_word_observation connect actual persistent
reads to Scalar.encodeValue of the intrinsic SVal/path observation. found,
ValueRep, finite numeric Transport and coverage are explicit undischarged
GENERAL representation premises, not desired decoder/gate/run certificates.
Read transport needs no added hash injectivity; it does not produce compiled
path origin, hash interpretation, alias-safe writes, packing or contract-world
representation. SourceCode/profile/refusal/invariants remain unchanged. The
actual UInt256/typed word clause is discharged; full source compilation is not.
Abstract read-shape facts expose only changed fields and preserve every other
actual field; they avoid expanding populated account maps during fixture proof.

Owned `Bridge/SolidityBridge/RoadmapV15/P10/StorageReadControls.lean` has23 named
controls. Nonzero owner7 and context11 have distinct persistent/transient stores;
actual sourceUInt513/int-1/booltrue clients construct ALL four representation
premises and derive execution. Wrong covered root rejects Transport. Neighbor/
unset/absent-account reads, word wrapping, full1024 input, static/writable reads,
wrong owner/key warmth, permission-refusal negatives and precise gas/arity/fuel
ordering are checked. Raw wrapped UInt input does not expand compiler root bounds.
Memory aa,bb; returnData cc,dd; H_return ee,ff; calldata11,22,33; caller/context,
nonzero nonce/balance accounts, code and spill258,513 remain in whole-State
outputs. Cold→warm and warm→warm fetched SLOAD/PUSH1(13)/SLOAD sequences yield
[513,513,258,513], gas2203/203→0,PC3→7,execLength41→44.

Two review/proof corrections are retained explicitly. The initial new fuel
control wrongly expected low gas to precede fuel1; actual driverSteps returns
OutOfFuel before decoding/gate at fuel0/1. Both cases now preserve that result;
fuel2 tests gas-before-arity independently. The initial NEW cold sequence
expected only one access-set insertion. Actual execution inserts twice, and
native RBSet representation can change on duplicate insertion. Final expected
State keeps BOTH actual insertions; it never quotients or weakens observations.
The wrong original draft and failed equality remain in raw evidence.

First full-control check failed137/66.44s at enforced12GiB; it remains failed.
The unchanged failed operation was not repeated. Abstract state-shape factoring,
modular first-step composition and pointwise typed-word proofs replaced broad
whole-State normalization. Foundation/basic bounded diagnostics passed; final
consumer05 PASS8.88s/12 standard-only reports and finalcontrols01 PASS12.57s/23
standard-only reports, warning-free, aggregate RSS about1.64GB. A signed cast
recursion failure was fixed with bounded arithmetic, never a recursion increase.
All original source snapshots, memory peaks, raw exits and review corrections
remain in /workspace/v15-evm-agreement-evidence/storage-reads-20261102.

MCP diagnostics tools are unavailable; actual checks use the supported bounded
serial route.12GiB/no swap,4GiB H1 reserve,-j1,300s file/5400s full, heartbeat/
recursion/fuel budgets remain unchanged. Exact receipt-bound exited own containers
were released under H1; no cache/source/commit/prior seal was deleted. Final
registered/structural/docs checks and finder/skeptic reviews are in the exact-head
handoff. Unchanged Source.Horizon300s full-core failure is not rerun or waived;
raw docs1/helper-baseline and frozen-baseline comparisons remain separate.
Historical5400s124/CONNECT403/monitor failures and disclosed lost early unsealed
retry raw/timing evidence remain failed/missing evidence, not reconstructed.

Memory G46.02 still needs actual allocator/padding/read-value/compiler/driver
facts. In the pin, both readBytes and readWithPadding append opaque zeroes even
at zero padding; Memory.PaddingCorrect has no supplied witness. Pure encoding
laws and preallocated capacity do not establish those facts. No native fixture
or new axiom supplies them. Work1/2/3/5 and Backfill A/B remain partial; Work4/
G47 requires production source/ABI/V13/V14/G45.03/world/frame/Osaka/resource/
transaction/finite/infinite trace facts. All150 full opcode rows stay OPEN.
Proposed G03: G46.03 partial charged persistent/transient read clauses, finite
source representation consumer, Backfill A/B; no generated ledger edit. No new
axiom/sorry/native shortcut/global hash premise, changed profile/refusal/pin or
fresh external compiler/EVM test. Goal remains unchanged and blocked.

Registered01 PASS36.27s/2178Bridgejobs and KeySort2jobs, actual Lean4.24.0/
Lake5.0.0-src+797c613; guardnull. Layers/orphans/trust/whitespace01 PASS.
Raw docs01 exit1/48missing retained; complete helper-base finding equality
PASS0, frozen-base equality FAIL1 with the same three inherited findings.
Finder/skeptic independently cleared source, controls, exact passing snapshot
identity, representation non-vacuity and this handoff, without Lean/server/build/tests.
Low-fuel controls refer to driverSteps; X continuation is proved at fuel+2.
No equality of the two drivers at every insufficient fuel is asserted. Original
frozen fixtures/expected pipelines are untouched; corrections above concern
only the new, previously uncompiled storage-control draft.
