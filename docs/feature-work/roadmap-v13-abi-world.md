# V13 ABI compilation and external-call world transport

Base: `2fe1f8932f96be15b00df03ba2cde46f64a87758`.
Branch: `codex/solidity-v12-v17-20261031/v13-abi-world`.
Checkout: `/workspace/solidity-lean`. Parent lane remains **blocked**, not complete.
Only the new ABI-world namespace, this document, lane controls and append-only
registration are changed. No reserved implementation, manifest, generated ledger,
profile, refusal, Fml.inTarget, verdict, SolKey name or proof budget is changed.

## Published interfaces and missing premises

The binding decisions are [solidity-scope.md](../solidity-scope.md), the
[G01 contracts](roadmap-g01-interfaces.md), [G03 ledger](roadmap-g03-ledger.md),
[G04 restrictions](roadmap-g04-restrictions.md), and [G06 pin](roadmap-g06-evm.md).
The two solc pipelines, full exact bytes, arbitrary history-dependent permitted
callees, unbounded reentrancy, transient sharing, static restrictions and rollback
remain required. No no-callback assumption is substituted for the world interface.

Published Failure bytes/emission are consumed read-only, as required by
[backend-failure-emission.md](backend-failure-emission.md). Creation, assembler,
hash and precompile boundaries remain those of
[backend-creation-artifacts.md](backend-creation-artifacts.md),
[backend-assembler.md](backend-assembler.md),
[hash-collision-bound.md](hash-collision-bound.md), and [precompiles.md](precompiles.md).

At this exact base, `Source/Eval.lean` encodeOne explicitly halts with
"not ABI-encodable" for unsupported values. decodeElemWord explicitly halts with
"dynamic ABI decoding is not modelled"; decodeArg permits memory dynamic arrays
of value types but explicitly refuses other dynamic element types and routes
fixed arrays, structs and tuples to unsupported static decoding. Val.word in
`Source/Observe.lean` returns none for references/function values. These are
missing aggregate encoder/decoder premises, **not approved exclusions**. Full
nested arrays, fixed arrays, structs, tuples and function-value signatures remain
obligations. Lazy/noncanonical calldata semantics stays with its existing owner.
This lane adds controls only for published Error-returndata behavior.

`Semantics/ContractWorld.lean` Entry carries an explicit result decoder and
World.call performs it after callFrame. emptyBody refuses nonempty static bodies.
Source.World supplies typed accounts, transient stores and journal laws, but not
a compiler/world relation. These published components do not discharge V12's
full statement/memory call-frame compilation or the missing aggregate codecs.
No unmerged worker branch was fetched, imported or cherry-picked.

## Queue and backfill accounting

| Item | Actual status and remaining obligations |
|---|---|
| G40 | Blocked: all-signature ABI decoder emitters, validation/failure agreement and runtime selector/receive/fallback dispatch remain unproved. Published aggregate decoding premises above are absent; no signatures were dropped. |
| G41 | Partial preparation: actual Error/Panic packet adapters, independent source-byte agreement, execution, byte observations, typed roundtrips and reason/raw catch laws below. Aggregate result/custom-error encoders and cross-call decoding, full catch dispatch and actual CALL/RETURNDATA transport remain open. |
| G42.01 | Blocked: typed self-call ABI execution and persistent/transient world-sharing compiler proof need V12 and complete codecs. |
| G42.02 | Blocked: arbitrary permitted callee return/exception world transport and history-dependent environment realization need published world/call compilation interfaces. Reserved readonly/source-world implementations remain untouched. |
| G42.03 | Partial independent journal preparation only: heterogeneous marks restore published source worlds. Actual compiled callback execution, caller frame restoration and invariant preservation remain open. |
| G42.04 | Blocked: aggregate caller-storage library execution and linked ABI/world transport remain open; existing library semantics are read-only. |
| G42.05 | Blocked: external function address/selector dispatch for every signature and static restriction simulation remain open; old function-ref-args/restricted tasks remain untouched. |
| G42.06 | Partial independent prefix transport only. Actual call-mode/ABI/world/rollback composition and resource-indexed full-constructor coverage remain open. |
| Backfill A | Published Error codec and Source.abiLayout have arbitrary-list lengths/cursors, tail alignment, concatenation and tail noninterference; the Error codec has arbitrary-length padding/offset/length/noninterference and representable encode/decode laws, plus empty/31/32/33, nested-packet and malformed controls. General nested aggregate codec laws and aggregate malformed witnesses await the unavailable published aggregate codec. |
| Backfill B | Independent typed world separation, heterogeneous rollback and prefix concatenation proved, with actual persistent/transient writes and negative controls. Published static/self/library signature and explicit callee-refusal controls are proved in PublishedCallControls; intrinsic-to-compiled call-frame/world transport and full ABI signature combinations remain open with V12/codecs. |

## Theorems and exact boundaries

All names below have prefix `Solidity.Backend.AbiWorld.`.

- padded_length/alignment/bounds/payload/suffix have no size premises. error_offset,
  error_length_word and error_payload observe bytes 4, 36 and 68 of the existing
  Semantics.encodeError. error_body_alignment includes the four-byte selector.
- packet_prefix/packet_byte preserve every byte under suffix concatenation;
  packet_byte needs i < packet.length. padded_injective retains equal original
  lengths; the negative control proves that deleting that premise is false.
- numeral_byte covers every width and valid index. word_eq_numeral relates two
  **existing** definitions, not a new ABI semantics. read_word needs n < 256^32.
  error_roundtrip needs reason.length < 256^32 (the ABI length-word bound).
- emitError reuses Failure.emit (.reason reason). execute_error needs exactly
  Failure.Fits a (encodeError reason) and stack.length + 2 <= 1024, and proves the
  actual checked slice execution with arbitrary suffix, exact REVERT bytes,
  stack and exact byte writes. Gas/expansion and whole pinned EVM are excluded
  from this component theorem, not excluded from the required parent proof.
- catch_error uses the intrinsic CatchKind.reason.decode, with the same length
  representability bound; catch_raw needs packet.length < 2^256. No decoder is
  independently redefined here. Controls preserve the published decoder's missing
  padding and head-overlapping offset acceptance.
- unrelated_world_frame preserves typed account/transient observations for
  arbitrary update functions at owner-separated addresses. Separation is explicit.
  heterogeneous_callback_rollback requires outer/inner marks equal to the actual
  pre-call journal lengths; metadata can differ. This is source journal transport,
  not a theorem that arbitrary compiled callbacks preserve an invariant.
- prependEvents_monotone preserves Roadmap.Prefix.Le, including its finality
  condition. prependEvents_assoc preserves observation order. Neither proves
  resource adequacy or discharges missing call-mode simulations.

All headline axiom sets are pinned by #guard_msgs: standard propext/Quot.sound,
plus Classical.choice through existing execution, world and source layout/word definitions. Exact sets are guarded in each headline theorem. Finite codec controls use
kernel decision proofs, no native_decide, new axioms, sorry or budget overrides.

## Runtime and validation

Actual Lean 4.24.0 (797c613eb9b6d4ec95db23e3e00af9ac6657f24b),
Lake 5.0.0-src+797c613. Clean initial branch work was exactly at the assigned base;
the authorized lane branch was created without resetting anything. The outer VM
has memory.max 17179869184, no active swap and about 30 GiB free disk initially.
Systemd user scope failed because no user bus is present (raw output retained).
The task-owned offline Debian runner enforces memory.max 12884901888 and
memory.swap.max 0, one CPU, LEAN_NUM_THREADS=1. A toolchain wrapper serializes
actual Lean processes with flock and passes -j1. It changes no proof budgets.

Runtime `lake build Solidity.KeySort`: pass, "Build completed successfully
(2 jobs)." This was a cached target; it does not imply whole-lane validation.
Actual cgroup peak for that gate: 25436160 bytes. RUNTIME_GATE_PASS.
Per-file Lean MCP and get_goal are not exposed in this session's tool inventory.
Early per-file direct diagnostics used -j1 --tstack=131072. The installed repository
stdio MCP helper was subsequently discovered and validated in a separate capped
runner: interactive=false, severity=error, max one open file, explicit -j1 and
--tstack=131072. Final per-file MCP checks cover the owned files and registration
root; no reviewer used a Lean server. The helper's existing event-loop cleanup
warning is retained separately from successful complete diagnostic responses.
The existing persistent goal is preserved; no competing goal is created.

Raw failed proof iterations are retained in the external evidence directory.
The initial finite controls exceeded evaluator recursion depth; kernel decision
proofs fixed them without increasing any budget. No failed iteration is a pass.
Focused Error emission dependency closure passed (38 jobs). Final validation,
independent review outcomes and the committed artifact handoff are recorded below. No external compiler/EVM tests have been run for this preparation.

## Reviews and handoff

Independent finder and skeptic reviews used no Lean server/builds. Neither found
an incorrect theorem, duplicated semantics, ownership violation or hidden
preservation premise. Confirmed findings were fixed: the docs entry now remains
in its table; the import checker requires all nine module names and resolves
actual imports; a genuinely mutating other-owner control applies the separation
law; largest-word and next-word wrap controls exercise the ABI representability
boundary. The same-owner mutation negative refutes framing without separation.
The skeptic correctly identified independently available static/self/library
controls. PublishedCallControls now proves signature-polymorphic static refusal
and missing-callee refusal, with inhabited self-address/aggregate-result/library
and role-negative witnesses. These consume the published implementation without
adding a readonly implementation or pretending to prove compiled calls.
The first focused combined gate passed (49 jobs). Additional published-layout backfill and isolated installed static/nonstatic controls were then added after follow-up review. Follow-up review is recorded in the
external review evidence when returned. Full-lane completion is blocked by the named prerequisites;
no parameterized composition certificate is counted as discharge.

Proposed coordinator ledger IDs: G40, G41, G42.01-.06; features abiEntryValidation,
abiEncode, abiDecode, revertPayloads, catchClauses, tryStatement, functionCalls,
libraries, externalLibraryCalls, externalFunctionTypes, staticCallRestriction,
worldAssumptions, calldataLocation, fallbackFunction and receiveFunction.
No global ledger or feature status was rewritten. No push, merge or PR.

## Preparation checkpoint validation and remaining handoff

Owned per-file diagnostics and guarded axioms, focused import closure, layer,
orphan, trust, lane imports, exact-base doc comparison and ownership checks are
recorded in `/workspace/scratch/v13-abi-world-evidence`. Raw failed iterations
remain there. Standard warning debt in unchanged AST/ContractWorld is retained.
The final repository `./run-lean.sh` and root MCP gates passed as recorded below.
This preparation checkpoint is partial against the entire assignment, not a
whole-lane completion claim. The failed cold/root attempts remain separate failures.

The original patch, Git bundle, checksum manifest and exact base/head handoff
are exported under `/workspace/scratch/v13-abi-world-artifacts`. The external
HANDOFF.md records the actual committed head after commit, avoiding self-reference.
Parent G40/G41/G42 remains blocked by missing published aggregate-codec
semantics/results and V12/full call/world compilation interfaces. The assigned
backfill completed here is useful independent preparation only; general nested
aggregate and actual cross-layer transports remain open. Existing owners must
publish/integrate those prerequisites before final applications and whole-lane
checks. No scope exclusion or weakened premise is requested.

## Follow-up independent backfill

The skeptic identified Source.abiLayout as additional available preparation.
PublishedLayout now measures that actual encoder with headSize/tailSize and
proves layout_go_lengths, layout_length, dynamic_head, dynamic_offset (the exact
modulo-2^256 cursor), dynamic_payload, tail_alignment, go_append,
tail_noninterference and later_head for arbitrary part lists/cursors. These
measurements construct no bytes and do not redefine ABI semantics.
canonical_head_size explicitly requires each static part to occupy 32 bytes;
the raw-fragment negative shows why that premise cannot disappear.
Controls cover empty lists/tails, static+31/33-byte tails, nested already-encoded
packets, exact offsets and cursor wrap. This does not supply the missing typed
nested aggregate codec or its decoder correctness.

The finder found that the original static examples could fail for absent code
or library roles. Their replacement installs distinct caller/library identities
with valid roles, and installed_nonstatic_success proves both ordinary and
library nonstatic calls succeed with the same nonempty body and result. The
static witnesses now discriminate removal of either static guard. Explicit
missing-code and wrong-role negatives remain separate.

The initial RSS sampling format omitted Docker's required PID field and returned
no usable samples. Its zero values are invalid, not memory evidence. The final
sweep uses pid/command/RSS columns, retains the raw sampling error and records
measured aggregate RSS separately from the actual cgroup peak.

## Final codec consumer additions

ErrorRoundtrip.numeral_mod proves arbitrary-width wrap behavior of the existing
machine numerals. ErrorEmission.panic_roundtrip covers **every intrinsic uint256**
code, not only the source's ten named panic codes. Panic controls cover zero,
maximum uint256 and strict rejection of a trailing byte. No decoder is redefined.

PublishedLayout.dynamic_length observes the exact length word modulo 2^256 for
all lists. canonical_layout_alignment keeps the explicit static-width premise.
source_digits and source_word_bytes relate existing encoders for every width and
all natural-number inputs, including overflow. source_error_bytes/source_panic_bytes
prove equality to the actual independent Source.errorData/Source.panicData.
execute_source_error and execute_source_panic compose those byte agreements with
actual Failure instruction-slice execution. They require only the published Fits
address/length conditions and two free stack cells. sourcePanicInput selects all
Source.PanicCode constructors into the existing typed emitter. These are NEW G41
consumer proofs, not changes to Source or its reserved decoder agreement task.

The programs are **packet-specialized**: their input bytes/reason values have
already been evaluated. They do not constitute a uniform runtime encoder or body
compiler for dynamic arguments/results. Those all-signature obligations remain
open, along with all whole-call/world/resource composition. Paired result types
in the published-world controls are not a proof of aggregate ABI signatures.
The existing emptyBody static restriction is preserved as a published interface
behavior, not approved as a final-profile exclusion; effect-certified nonempty
view/pure execution remains a reserved prerequisite.

## Cold full-gate failure retained

`timeout 5400 bash ./run-lean.sh` in the serial capped runner returned **124**
after 5400.579 seconds at 977/990 default jobs. No Lean error was reported, but
the command did not complete and did not reach the required TestSuite/sort stages.
It is a failed gate, not historical debt waived against the base. Raw log:
full-run-lean.log; result: full-run-lean.json. Peak sampled aggregate RSS was
9623596 KiB; actual cgroup peak 12884901888 bytes, swap.max 0, OOM/OOM-kill counts
both zero. Source/toolchain-keyed materialized artifacts stay in the single .lake
build tree for the required final check of the changed source. No failed proof,
process or TestSuite budget was increased. The final full gate was pending at that checkpoint; the separate later passing
command is recorded below. The cold timeout itself remains a failure.

## Reserved prerequisite requests (not applied)

- Source/Eval encodeOne/encodeParts and decodeElemWord/decodeArg: publish typed
  fixed/nested array, struct, tuple and function-value codecs and agreement for
  every admitted signature, retaining accepted noncanonical/lazy calldata cases
  and exact malformed/failure behavior. No new refusal is an approved exclusion.
- V12/compiler body and call-frame interfaces: publish the actual complete typed
  statement/memory lowering simulations and world representation/transport needed
  by self/external/library/function-value calls, including callbacks and rollback.
- Semantics/ContractWorld emptyBody/callFrame/libraryCall and the reserved readonly
  owner: publish effect-certified static entries covering admitted nonempty
  view/pure bodies and attempted-write restrictions, plus aggregate caller-storage
  library interfaces. The preparation controls cannot discharge these premises.
- Coordinator registration reconciliation: the owned import checker covers all
  nine modules; global CORE could register /^Solidity\.Backend\.AbiWorld\./.
  No shared checker or generated ledger was edited by this worker.

## MCP root import setup attempt retained

All nine owned files returned complete success, no errors, no failed dependencies
in mcp-final-all.log. The root diagnostic returned partial/timed_out and caused
lake setup-file to auto-build the still-missing DecisionHashes import from the
cold timeout. That automatic build used LEAN_NUM_THREADS=1 but omitted explicit
-j1; the task-owned MCP container was stopped and the attempt is **not** counted
as a passing gate. No DecisionHashes .olean/trace was produced. The process
snapshot and failed MCP response are retained. The corrected MCP toolchain wrapper
adds -j1 to every process and serializes import builds, while allowing the server
and its single file worker to run without an advisory-lock deadlock. The root
was subsequently checked after the explicit serial full import closure passed;
mcp-root-final.log records complete success with the corrected wrapper.

## Final source review

Independent finder and skeptic cleared the final source-wire/Panic preparation
candidate. They verified its staged patch and append-only registrations; no
soundness, hidden-premise, ownership, duplicated-semantics or non-vacuity defect
remained. The skeptic's final wording correction is applied: source_word_bytes
quantifies Nat, so its description says natural-number inputs, not signed Int
values. Source-byte agreements were explicitly reviewed as owned G41 consumers
of unchanged published encoders, not a reserved Source decoder implementation.
Their clearance is for partial preparation; it does not discharge pending gates
or G40/G41/G42 parent obligations.

## Final preparation validation and committed handoff

| Gate | Outcome and decisive evidence |
|---|---|
| `lake build Solidity.KeySort` | Pass, 2 jobs; actual Lean 4.24.0 / Lake 5.0.0-src+797c613. runtime-gate.log and runtime-gate-final.log. |
| Per-file MCP for nine owned modules, then `Solidity.lean` | Complete success, interactive=false/severity=error, no items/failed dependencies. mcp-final-all.log holds nine clean owned responses plus the retained failed first root attempt; the two wording-edited files were checked again in mcp-wording-final.log; mcp-root-final.log is the separate complete root pass. |
| `lake build Solidity.Backend.AbiWorld.Controls Solidity.Backend.AbiWorld.PublishedCallControls Solidity.Backend.AbiWorld.PublishedLayoutControls` | Pass, 62 jobs, ready-focused.log; guarded headline axiom pins pass with only standard propext/Classical.choice/Quot.sound dependencies. |
| Final `timeout 5400 bash ./run-lean.sh` in capped serial runner | Pass, exit 0, 1382.752 s. Default 990 jobs; SolkeyTestSuite 262 jobs; parsed 377 taclets, 131 read-bearing, table covers 131; annotations match the explicit frozen rule file. final-run-lean.log/json. |
| `node scripts/check-layers.mjs` | Pass, ready-layers.log. |
| `node scripts/check-orphans.mjs` | Pass, ready-orphans.log. |
| `bash scripts/check-trust.sh` | Pass, ready-trust.log. |
| `node tests/v13-abi-world/check-imports.mjs` | Pass, exact nine modules, no unresolved/direct or forbidden transitive imports; ready-imports.log. |
| `git diff --cached --check`, owned paths, base-prefix registration, proof-budget/trust-construct scan | Pass, ready-static.json; no foreign changed paths, all three registrations append-only, no forbidden proof construct. |
| `bash scripts/check-doc-paths.sh --strict`, current and exact base | Raw checker fails on the same 46 inherited missing references. No-new-findings and owned relative-link checks pass; ready-static.json and raw current/base logs retain the distinction. |

The final full check used the same 5400-second bound and 12 GiB/no-swap cap,
not a larger budget. Sampled peak aggregate RSS was 11535200 KiB; actual cgroup
peak 11586351104 bytes, memory.max 12884901888, swap.max 0; OOM and OOM-kill counts
zero. RSS is a summed sample and can double-count shared mappings. The passing
final source includes the final source-wire/Panic additions. The initial cold
5400-second timeout and partial/aborted root MCP attempt remain failed evidence,
not relabeled passes. All checks were serial; no reviewer ran Lean or an LSP.

No new external compiler/EVM test is claimed. Existing Failure Osaka evidence
was reused read-only; its vectors/runner/lock hashes match the published report
(published-failure-hashes.log). Kernel/source-byte and instruction-slice proofs,
finite controls, prior external component evidence and whole-call coverage are
distinct. Gas/expansion, uniform runtime codecs/dispatch and all missing typed
world/call simulations remain parent obligations.

The owning document, all nine modules and append-only registrations are committed
as a reviewable preparation checkpoint. Exact committed head, original patch,
Git bundle, evidence archive and SHA256 manifest are recorded in the external
HANDOFF.md under /workspace/scratch/v13-abi-world-artifacts after committing this
section. No empty result-marker commit, push, merge or PR is performed. The full
persistent assignment remains blocked by the reserved prerequisites listed above;
G40/G41/G42 and unavailable aggregate/call backfill are not declared complete.


## Recovery catch consumer checkpoint

Audit run: `63a82c65-2eae-4212-9f05-f84978fc7695`. Continued the same VM,
branch and blocked original goal from clean committed preparation head
`53fedb6574fc26694e268aad96d728744f854b9e`; the frozen base above is unchanged.
The five original artifact checksums verified from their artifact directory.
Original artifacts/manifests and all raw failed gates remain untouched.

The new CatchTransport module consumes the published intrinsic tryCall,
catchBytes and catchData interfaces, RevertMemory self-call byte extraction,
and AllocBytes literal allocation, all read-only. try_revertWith retains the
nonzero/self receiver and actual executed-callee premises, Error-before-Panic
branch order, named code environment and exact clause drops. catch_allocated
retains the executed-callee and actual CatchKind.decode premises and derives
clause execution from the fresh bytesObj, followed by popping the data binder
and every clause local. It removes only the Out heap-extension certificate
from its observation, not state fields. Neither theorem assumes desired frame
preservation, supplies a new evaluator, or concludes whole-world rollback.

CatchControls.actual_reverting_call and extracted_actual discharge execution
for arbitrary literal byte packets using actual Prog.runR/TRun.call and the
published THalt.ofData behavior, including bare reverts. The inhabited caller
has four locals: a result slot, marker 77, and two aliases of an older object
at identity 0 with bytes [161,178]. source_error_clause and source_panic_clause
instantiate the generic dispatch law and explicitly consume source_error_bytes,
source_panic_bytes, error_roundtrip and panic_roundtrip. allocated_source_error
uses catch_allocated with the actual callee premise discharged; it reads byte
66 in the clause, pops both the fresh data binder and a further bool local,
and observes heap length 2, marker 77 and both original aliases/ordered bytes.
allocated_other_packets and empty_allocation cover raw/custom, unpadded Error
and accepted empty allocation. observed_payloads reads and rethrows the exact
reason [66,0,254], custom [222,173,190,239,0,255] and full Panic packet from actual
catch memory. emitted_and_consumed connects the same Source Error bytes to the
existing checked REVERT instruction emitter and this executed catch consumer;
it is a byte boundary, not a proof of CALL/RETURNDATA simulation.

The controls distinguish Error reason (result 20), encoded allocation Panic
(code/result 65), intrinsic assertion Panic (default code 1), raw/custom/bare
(catch-all result 30), and success (result 10). They preserve accepted unpadded
Error data, reject a truncated declared payload through the actual reason
consumer, and exercise wrong-kind, zero-address, absent-callee and successful
call extraction refusals. Empty indexed reads retain the published revert
behavior, while a clause that does not index accepts the same empty raw data.
The exhaustion witness uses intrinsic assumeFalse, which has no Solidity source
syntax: it proves propagation, not realistic resource exhaustion/adequacy.
The divergence witness is a real typed while(true) empty loop with a mathematical
unbounded-run proof; it is not a finite-fuel timeout or completed revert.

Finder and skeptic independently inspected actual sources without running Lean
or a server. Both found the initial certificate-erasure wording imprecise and
requested explicit source_panic_bytes reuse; both corrections were made. The
raw bounded proof attempt exceeding 200000 heartbeats was preserved; the final
control reuses catch_allocated instead of increasing any proof budget.
Final reviewed gate results and committed handoff are recorded below after the
bounded checks. All new evidence is separate from the original sealed archive.

Queue accounting remains: G40 blocked; G41 partial intrinsic packet preparation,
with uniform aggregate result/error encoding and cross-call decoding open;
G42.01-.02 blocked; G42.03 partial journal preparation with compiled callbacks
open; G42.04-.05 blocked; G42.06 partial independent prefix preparation with full
call-mode/world/rollback composition open. Backfill A remains partial for the
published Error/layout codecs, now with executed malformed/noncanonical catch
controls; general aggregate codecs remain unavailable. Backfill B gains actual
intrinsic catch allocation/frame controls, but V12, arbitrary external-world
execution, compiled frames, caller-storage libraries and resource-indexed
composition remain unresolved. No missing prerequisite is an approved exclusion
or new premise counted as discharged. The full persistent goal stays blocked.


### Recovery gates and committed handoff

Final sources received independent read-only finder and skeptic approval after
the corrections above. Their reports are finder-source-review.md and
skeptic-source-review.md in the NEW evidence directory
/workspace/scratch/v13-abi-world-recovery-63a82c65-evidence. Neither ran Lean.
Both final source hashes are recorded there; final artifact reviews are saved
separately after the checkpoint commit, without rewriting the old manifest.

| Command/gate | Actual outcome and decisive evidence |
|---|---|
| Lean/Lake versions | Lean 4.24.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake 5.0.0-src+797c613. lean-version.log, lake-version.log. |
| Serial capped `lake build Solidity.KeySort` | Pass, exit 0: Build completed successfully (2 jobs). keysort.log. RUNTIME_GATE_PASS follows this output. |
| Per-file MCP, each new module, interactive=false, severity=error | Pass: success=true, partial=false, timed_out=false, items=[], failed_dependencies=[]; transport-mcp-final.log and controls-mcp-final.log. |
| `lake build Solidity.KeySort Solidity.Backend.AbiWorld.CatchControls` | Pass, exit 0, 84 jobs; runtime-focused.log. All scoped headline axiom pins accept only propext, Classical.choice and Quot.sound. |
| `timeout 5400 bash ./run-lean.sh` | Pass, exit 0, 3.144 seconds using the existing cache: 992 default jobs, 262 TestSuite jobs, 377 taclets/131 read-bearing/table covers131 and frozen annotations match. final-run-lean.log/json. |
| Root MCP after full build | Pass with complete empty error diagnostics; root-mcp.log. The earlier failed root attempt remains in original evidence. |
| `node scripts/check-layers.mjs`, `node scripts/check-orphans.mjs`, `bash scripts/check-trust.sh`, `node tests/v13-abi-world/check-imports.mjs` | All pass; layers.log, orphans.log, trust.log, imports.log. Exact 11 owned modules, zero forbidden imports. |
| `git diff --cached --check`, owned paths, append-only registrations, proof-construct scan and owned links | Pass, static.json and diff.log. No foreign path, new trust construct or budget increase. |
| `bash scripts/check-doc-paths.sh --strict`, current and verified exact-base snapshot | Both raw exits 1; same 46 missing references and 37 strict ambiguity findings, no new findings. docs-current.log, docs-base.log, base-snapshot-verify.log and static.json. Raw failure is not green. |
| Original five sealed artifact checksums | All pass again; original-checksums.log. Original SHA256SUMS and archive are unchanged. |

The full gate sampled peak aggregate RSS 1131076 KiB (shared mappings may be
counted multiple times); cgroup peak 997322752 bytes, max 12884901888, swap.max 0,
OOM/OOM-kill 0. Runtime/MCP cgroup and host resource logs are retained; checks
were serial and no swap was available. No unchanged failed heavy gate was
repeated: changed sources received the required new bounded confirmation.
The original cold 5400-second exit124, failed root attempt and raw doc exit1
remain preserved in the old evidence/artifacts; local failed proof diagnostics
and the unchanged-heartbeat failure are in the new evidence.

Checkpoint handoff: commit only this reviewed intrinsic catch-consumer addition,
then seal a NEW original patch (frozen base to committed head), recovery-only
patch, Git bundle, owning document, HANDOFF.md, raw evidence archive, committed
state record and SHA256SUMS under
/workspace/scratch/v13-abi-world-recovery-63a82c65-artifacts. HANDOFF.md records
the full committed head/base/branch/repository, every Work/Backfill disposition,
exact theorem premises and external-test boundaries. No new external EVM/solc
test is claimed. The existing blocked persistent goal is retained; no getter
is exposed in this tool surface, and no goal creation, reset, reactivation,
continuation scheduling or completion was attempted. Parent status is BLOCKED.


## Published memory-call consumption

The human notified this original VM/thread that ordinary memory internal calls
were actually published on origin/master at
91e94ab57305ca055127934fd9e68fe9ea5e6be3. Clean task head
 d6df81f66466c9641fff1f5497a134b31e27a6ea was preserved, and that exact published
revision was merged into the isolated task branch as
1578f42505c5edf6c1cdd72d6b13348cd2e89b3e. No master branch, unmerged worker branch
or reserved producer was edited. Both independent read-only integration reviews
verified exact published producer bytes and every prior owned file/suffix.
The publication itself updates the existing Compiler module-map row; the task's
own additions remain append-only relative to this integration baseline.
All earlier sealed manifests, artifacts, raw failures and the single cache remain.

The new owned CompiledMemoryCalls module consumes the actual public
Compiler.Compilation.memoryCalls_input/correct branch and its StateRepr,
requiredFrame, allocationCost, BaseExtends and GrowsAllocator relations.
memory_calls_rep exposes that exact output relation. completed_transport
requires actual Input, isMemoryCalls, no payment and a successful intrinsic run;
it concludes actual target success, stack equality, full state representation,
old-base relation and reached allocator growth. shared_completed discharges all
of these premises for a compiled typed program; five public input/agreement
endpoints are inhabited for shared, escaping, failing, empty and wide returns.
No desired frame/alias preservation is inserted as a hypothesis.

The actual call's caller contains an older three-word buffer, another alias,
marker77 and stored9, with nonempty machine stack77 and sentinel memory127=99.
The shared-return callee mutates the old buffer's second word to127, exports its
reference, then rebinds the private parameter to a separate allocation and
writes238 there. Caller writes67 through the returned alias. Actual source
references are [heap3,result0,alias0,original0,marker77]; target pointer locals all
hold256, old payload is [67,127,254], the independent parameter object has238,
and allocator cursor263. The escaping callee returns its own two-word object:
resultid2/address261, both older aliases remain id0/address256 with [66,0,254],
returned contents [67,136], cursor264. Source/target store9, marker77, stack77
and sentinel99 are explicitly observed. Private LOCAL BINDERS are dropped;
physical target memory cells need not be cleared.

The exact expanded requiredFrame is6 for every control, exceeding four surviving
caller locals. Reached costs are7(shared),8(escape),5(require failure). Frame1 and
cursor W-7 refuse the shared Input. A default empty return causes the caller's
indexed write to revert (cost5), while the actual intrinsic uint word300 is
compiled successfully but rejected by this partial byte observation. Recursive
and external-call constructors retain actual compiler refusals.

returned_error_observation follows the actual returned target pointer, checks
the buffer header equals3 and each observed word is below256, and binds the
result into existing Source.errorData/CatchKind.reason.decode using the existing
source_error_bytes/catch_error proofs. No second codec is defined. The observer
rejects a two-word result and word300; those are observer boundaries, not new
compiler/source-profile exclusions. It is a fixed three-cell observation, not a
uniform aggregate decoder or a compiled byte encoder.

Whole-program entry has an EMPTY heap: its BaseExtends witness is consequently
vacuous at entry. The actual call's older aliases and return identity controls
are nontrivial, but this endpoint must not be promoted to a nonempty-entry
arbitrary-world theorem. The missing packet composition interface is precise:
Evm.Machine.mem is word-cell memory; Failure.Slice.Machine.memory is
byte-addressed. No published adapter here maps the returned word-array header,
pointer and contents into a compiled byte-addressed Error/Panic REVERT packet.
Existing packet emitters remain usable independently. No external CALL/
RETURNDATA, arbitrary recursion, bytecode/gas adequacy, callback/world rollback,
aggregate ABI codec or complete source-lowering theorem follows.

The lane import checker now permits Evm dependencies ONLY for this new consumer
and ONLY within the published Compiler dependency closure. The prior 11 modules
retain their Evm exclusion; every module still rejects Frontend, elaborators,
printers and Tools. No producer/example/front-end file is copied or imported as
an owned implementation; programs are built with existing intrinsic constructors.

Queue status: G40 blocked; G41 partial preparation now includes the actual
compiled returned-word/ABI-helper observation; G42.01-.02 blocked for typed
external/self ABI/world compilation; G42.03 partial journal preparation with
compiled callbacks open; G42.04-.05 blocked; G42.06 partial prefix preparation
with full call-mode/ABI/world/rollback/resource composition open. Backfill A
remains partial for published codecs. Backfill B gains actual compiled direct
memory-call frame/alias/escape/resource controls; full V12/source lowering,
nonempty-entry world transport and external-mode combinations remain open.
The persistent original goal stays blocked. Publication discharges this direct
memory-call prerequisite only; remaining premises are not counted as discharged.


### Published-component validation and handoff

Both independent read-only source reviews passed after the binder wording,
source-store and returned-reference/byte-observer negative improvements.
Reviewed source SHA256 is
914c13c5bdbd5de5ad346cfda515f0f13a1a592eb15d089514d243deed77e6c6.
Neither reviewer ran Lean/server/builds. NEW evidence is stored at
/workspace/scratch/v13-memory-calls-91e94ab5-evidence; earlier evidence and sealed
manifests remain unchanged. The raw numbered diagnostic failures include the
200000-heartbeat and recursion-depth failures; both were fixed by proved halt
certificates and explicit Option rewrites, with no budget increase.

| Gate command | Actual outcome and decisive evidence |
|---|---|
| `lean --version`, `lake --version`, `lake build Solidity.KeySort` | Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake5.0.0-src+797c613. KeySort exit0,2jobs; versions/keysort logs. RUNTIME_GATE_PASS followed this output and cap verification. |
| Focused `lake build Solidity.KeySort Solidity.Evm.Compiler` after publication integration | Pass exit0,156jobs; published-focused.log. |
| Per-file MCP on new consumer, interactive=false/severity=error/timeout_s=45 | Pass, complete empty errors/dependencies; consumer-mcp-final.log/exit. |
| `lake build Solidity.Backend.AbiWorld.CompiledMemoryCalls` | Pass exit0,185jobs before/after scoped pins; consumer-focused-01/final logs. Pins accept only propext/Classical.choice/Quot.sound. |
| `timeout 5400 bash ./run-lean.sh` | Pass exit0,111.986seconds;995 default jobs,262 TestSuite jobs,frozen377taclets/131read-bearing match. Published MemoryCallExamples built in26seconds. final-run-lean.log/json. |
| Root MCP after the full gate | Pass, complete empty diagnostics; root-mcp.log/exit. |
| `node scripts/check-layers.mjs`, `node scripts/check-orphans.mjs`, `bash scripts/check-trust.sh`, owned import test | Pass:172core/0meta,1010reachable/0orphans,1025sources/0trust findings,12owned modules/0forbidden imports. |
| Owned paths, append-only registrations vs integration baseline, exact published producer bytes, forbidden construct/budget scan and owned relative links | Pass; static.json. Published module-map row update remains attributed to publication. |
| `bash scripts/check-doc-paths.sh --strict` on current, frozen base and published revision | All raw exits1. Current/published have85findings (48missing,37ambiguities); frozen has83 (46missing,37ambiguities). Raw failures retained. |
| No-new-doc-findings vs frozen exact base | FAIL:two references inherited unchanged from the newly published inline-assembly document. static.json lists exact findings. This gate is not green. |
| Separate no-new-doc-findings vs exact published revision | PASS:zero new findings from this lane. A temporary task-owned source-only snapshot verified exact publication, then was removed; no cache/build tree was duplicated or deleted. |
| Prior sealed artifact manifests | All original5 and recovery8 entries pass; original-checksums/recovery-checksums logs. |

Full-gate sampled peak aggregate RSS2745936KiB (shared mappings can count more
than once), actual cgroup peak2197045248bytes, max12884901888, swap.max0 and
OOM/OOM-kill0. LEAN_NUM_THREADS=1 and explicit lean-j1 wrappers, serial heavy
work and one cached build tree were retained; disk/RAM snapshots are saved.
No unchanged failed heavy command was repeated or budget enlarged.

The two frozen-base doc regressions are in the byte-identical published
 docs/feature-work/inline-assembly.md: references to
Solidity/Frontend/SolcJson/Yul.lean and Solidity/Yul/Syntax.lean, whose modules
are not published here. This lane must not edit another owner's feature doc or
create placeholder semantic files. Requested owner/coordinator patch: mark
these two path mentions explicitly as planned locations using plain text rather
than the checker's existing-file citation syntax, OR publish the genuinely
implemented referenced modules through their owners. This is a documentation
prerequisite request, not authorization to weaken a theorem/profile or a reason
to reclassify the frozen-base no-new-findings gate as passing.

The published MemoryCallExamples payloadCall_source/payloadCall_observed controls
also confirm the remaining packet boundary: the intrinsic payload is observed,
but Compiler.compile refuses that revertData-containing call. No general
aggregate or byte-emission premise is silently inferred from the new component.

Commit this reviewed consumer and handoff section on the same task branch;
seal NEW artifacts at /workspace/scratch/v13-memory-calls-91e94ab5-artifacts.
HANDOFF.md will record frozen base, exact publication, integration commit and
final full head; original/full patch, consumer-only patch, bundle, owning doc,
command logs, independent artifact reviews, checksums and every queue/backfill
status. The compiled consumer's kernel obligations pass, but the checkpoint
retains the inherited frozen-base documentation failure and the entire original
assignment/goal remains BLOCKED on the still-open prerequisites above.


## Uniform returned-array observation

Investigated recovery d8d43e28-abba-48a8-aa41-6ad1f87c6bc5 resumes this same
VM/thread/branch at clean73b8070a0319f6103c7a9cfb2442d9b71c8397d7, preserving
all earlier commits, one cache, sealed manifests and raw failures. No prerequisite
was fetched/merged, no producer/semantic/global-pin/profile file changed, and no
goal write, reset, recreation or failed-context retry occurred. The user reports
published master93920309f5c800c9ce4809bc74700ed4fde65fb2; the local tracking ref
still points to the already integrated91e94ab5 and that newer object is absent.
No new publication is needed for the actual ArrayRepr/StateRepr consumed here.

ReturnedBytes is a partial observation of ACTUAL word-cell memory: byteCell
rejects symbolic slots and values at least256; cells reads every cell in order;
arrayBytes uses the observed header; localBytes follows the actual local pointer.
These definitions are not an ABI decoder, a new EVM evaluator or byte-addressed
memory semantics. ArrayRepr supplies exact header/length/every element/no-wrap;
StateRepr supplies actual pointer, full heap/struct representation and frame.
ByteRange is only a premise for converting this actual uint-array to bytes,
NEVER compiler/source admission. The total helper payload would modulo-convert
outside ByteRange, so it is not a successful observation there; payload_values
proves every natural value exact under ByteRange, and payload_length proves no
dropped elements. Empty arrays observe some[] rather than none.

array_complete and local_complete have no fixed length/base. independent_addresses
and interval_noninterference cover arbitrary represented bases and changes outside
the complete header/element interval. error_observations reuses the actual
Source.errorData/source_error_bytes, existing encodeError/catch_error and owned
layout laws for exact offset4 word32, length at36, complete payload at68 and ALL
zero padding. error_not_panic retains actual packet class. compiled_return
consumes public Compilation.correct/memoryCalls_input through completed_transport;
it retains actual source success, target execution, stack, FULL StateRepr,
BaseExtends and exact GrowsAllocator. Its explicit no-payment and ByteRange/get
premises are discharged below, not counted as compiler/world assumptions.
memory_call_pushes_zero uses the actual public certificate pushFree field to
normalize the stack index without forcing a symbolic program.

ReturnedBytesPrefix executes a real compiled setup: saved=9, marker42, distinct
older object0 containing[161,178], nonempty machine stack77 and sentinel cell127=99.
prefix_ready/nonempty_entry derive the caller StateRepr and allocator from actual
Calls.Program.sound/source execution. Entry heap length is1; oldRef0 is genuinely
inhabited. prefixCursor retains the EXACT producer-cost expression in its type;
prefix_resources separately proves cost3/cursor259. This is not empty-entry
BaseExtends passed off as nonempty world evidence.

ReturnedBytesControls instantiates six actual public compiler certificates and
successful source runs: lengths0,3,31,32,33(alias return), and33(private escape).
nonempty_applications supplies all six from that executed prefix, preserving
EVERY old typed address and specifically the inhabited object0 address. Every
Application includes final StructAllocatorRepr and complete ErrorFacts in addition
to actual target run/stack/state/base/growth/bytes/catch. The argument and returned
reference alias in the first five; private escaping object3 is distinct from
argument1 and old object0. A post-call first-byte write changes both argument
and return in alias cases, but only the return in the escape case. Original
argument/returned bytes include all intervening zeros and last255; expected
return is[7,zeros...,255] when nonempty. Logical private binders are popped;
physical private cells need not be cleared.

Public complete_payloads, finite_source_observations, finite_packet_facts,
finite_resources, finite_packet_sizes and observed_error_packets expose full
ordered payloads, every Error offset/length/padding/catch observation, old data,
alias/escape identities, scalar42/store9 and actual stack/sentinel observations.
Expanded need is6 for each stage. Reached costs are2,5,33,34,35,69 and final
cursors261,264,292,293,294,328 after prefix259. Packet lengths are68,100,100,100,
132,132, with padding0,29,1,0,31,31. Uniform theorems remain distinct from these
finite inhabited controls; no uniform compiler admission for aggregate signatures
is claimed from selecting these fixtures.

Positive target_baseline precedes wrong_length_pointer_order, invalid_cell_observations
and wrong_catch_and_offset_claims. Wrong numeric headers can yield shorter valid
bytes, and a pointer to old object0 legitimately yields[161,178]; the controls
reject WRONG complete-payload claims rather than pretend every malformed header
or pointer returns none. Reordered cells change ordered data; invalid range or
symbolic cells refuse observation. Error/Panic class, raw-vs-reason and encoded
offset64-vs32 claims remain distinct. The actual compiled_word300_observation
starts from the same nonempty prefix, has successful public compiler Input/run/
StateRepr/old-address/allocator evidence, returns raw words[7,300,0], proves
ByteRange false and the NEW uniform observer none. The older fixed3 accepted300
controls remain unchanged and checked too. No silent UInt8 truncation is used.

Resource failures are retained, not waived. Three combined/fixture worker OOM
kills occurred at the enforced12GiB cap; raw MCP worker errors and cgroup events
are saved. A later automatic11GiB guard stop and a manual task-owned stop after
10.63GB avoided further OOMs. No other session was killed. The expensive steps
were dependent allocator-cost rewriting and fully unfolding SAME-reference
state equality. Keeping the producer-cost cursor expression, splitting the new
prefix module and proving finite reference IDs then applying PUBLIC HRef.heq_of_id
preserve the SAME allocator/ref claims. All six cases then passed near1.10GB and
final controls incl actual300 near1.48GB, under unchanged memory/time/heartbeat/
depth/fuel/node budgets. Raw earlier failures and intermediate drafts stay evidence,
not committed proof substitutes. No old source/helper was refactored or deleted.

Scope remains G41/BackfillA/B preparation: a logical observation-to-existing-Error
codec theorem is NOT emitted byte encoding, a word-memory-to-byte-machine execution
relation, aggregate ABI signature compilation, external CALL/RETURNDATA or callback/
world transport. All missing producers/signatures/refusals remain. G40 blocked;
G41 partial; G42.01-.02 blocked; G42.03 partial journal preparation; G42.04-.05
blocked; G42.06 partial prefix preparation; BackfillA/B partial with this new
uniform/inhabited consumer. Full source lowering, arbitrary permitted external
callees/recursion, transient/world sharing and resource-indexed composition stay
open. The exact-base documentation no-new gate still fails by the two inherited
inline-assembly path references; its raw exit1 and reserved-owner repair request
remain binding. Goal remains blocked and untouched, questions=[].


### Uniform consumer final gates and handoff

Final source/premise/nonvacuity/ownership/doc/pin finder and skeptic reviews both
PASS; literal actual300-to-NEW-observer linkage was added after review and passed.
Reports are finder-source-review.md and skeptic-source-review.md in NEW evidence
/workspace/scratch/v13-returned-bytes-d8d43e28-evidence. Neither reviewer edited or
ran Lean/server/builds. Actual final guarded source hashes are in those reports.
Final staged gate/handoff and committed sealed-artifact reviews follow separately.

| Command/gate | Actual outcome and evidence |
|---|---|
| `lean --version`, `lake --version`, explicit `lake build Solidity.KeySort` | Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Lake5.0.0-src+797c613; KeySort exit0/2jobs. Actual versions/keysort logs precede RUNTIME_GATE_PASS. |
| Each new file MCP, interactive=false/severity=error/timeout_s45, outer120 | PASS complete empty errors/dependencies; uniform-mcp-final, prefix-mcp-final, controls-mcp-final logs/exits; sampled cgroup-current peaks825282560/1076367360/1388744704bytes. |
| `lake build Solidity.Backend.AbiWorld.ReturnedBytesControls`, timeout180 | PASS188jobs before/after guarded pins; controls-build-02 and focused-final logs. Actual axiom output/sets retained; pure array laws only propext/Quot.sound, compiler/source facts add Classical.choice. |
| `timeout 5400 bash ./run-lean.sh` | PASSexit0/3.135seconds cached,998default jobs/262TestSuite jobs/frozen377taclets131read-bearing/table covers131 and annotations match exact rulefile. final-run-lean.log/json/exit. |
| Root MCP after full gate | PASS complete empty errors/dependencies; root-mcp log/exit/resource. |
| `node scripts/check-layers.mjs`, `node scripts/check-orphans.mjs`, `bash scripts/check-trust.sh`, owned import checker | PASS172core/0meta;1013reachable/0orphans;1028sources/246inventory/0findings;15ownedmodules/0forbidden imports. |
| Diff whitespace, owned8paths/append-only registrations, all old12modules+reserved producers unchanged, trust/budget scan and owned relative links | PASS; static.json/diff.log. No semantics/pins/profile/global ledger changed. |
| `bash scripts/check-doc-paths.sh --strict`, current/exact verified frozen snapshot | Both RAW FAILexit1. Current85findings(48missing/37ambiguous), frozen83(46missing/37ambiguous). FROZEN no-new gate remains FAIL2, never green. |
| Separate own-change no-new comparison to accepted73b8070a checkpoint | PASSzero new findings. Exact inherited inline-assembly references remain unchanged; static.json retains separate statuses. |
| Three prior sealed manifests | PASS5original+8recovery+9memory-call entries. All old manifests/artifacts remain untouched; separate checksum logs. |

Final full gate sampled aggregate peakRSS583024KiB across3samples; brief peaks
may be missed and shared mappings may count more than once. Actual full cgroup
peak1425731584bytes/max12884901888/swap.max0/OOM0. Final successful MCP/runtime
resource observations are distinct from the THREE earlier worker OOM kills and
two preemptive stops described above; none is relabeled green. Existing serial
LEAN_NUM_THREADS=1/explicit lean-j1/12GiB hard cap/no swap/OS headroom and one
source-toolchain cache were retained. Raw initial/current diagnostics, failed
focused attempt, exact budget failures and successful changed-source gates all
remain in evidence. No unchanged failing heavy gate was repeated or bound raised.

All ready original-scope work in this checkpoint is the uniform represented
return observation and actual nonempty compiled applications/controls. The source
word-to-byte-addressed Failure-machine/emitted encoder, general aggregate codec,
external CALL/RETURNDATA, arbitrary permitted world/callback/library transport,
complete source lowering and full resource-indexed call composition remain absent
prerequisites, not hypotheses counted as discharged. The protected inline-assembly
doc repair request remains as recorded earlier. This checkpoint/full original
assignment remains PARTIAL/BLOCKED because original obligations and exact-base
doc gate remain open. No new semantic choice is requested, questions=[].

Commit the reviewed owned consumer/handoff section on the existing task branch;
seal a NEW artifact set under
/workspace/scratch/v13-returned-bytes-d8d43e28-artifacts. Its HANDOFF.md records
full final head/frozen base/accepted prior73/published interface91/repository,
original/full patch, consumer-only patch, Git bundle, exact theorem premises and
all Work/Backfill dispositions, raw evidence/reviews/checksums. No old manifest
is rewritten. No push, merge, PR or goal write/retry/reset/reactivation is made.
The original blocked goal is preserved under the explicit recovery instruction.

### Published library boundary integration (audit dff2fe2b)

Integrated exact published `9b24b57311b8daf0d4cd01b52bf420fd024c1d3a`
into the isolated lane, preserving all prior owned files. LibraryTryFrame SHA256
is `4ac1544e54f9cd52628283fac73c64cf4d8dd799a75e158f35f4819b0a67cb85`.
The attempted older introducing-revision merge conflicted in reserved files;
its raw conflict evidence was saved and that task-owned attempt aborted.
The exact supplied publication includes the existing memory-call prerequisite
and merged without conflicts. No reserved producer was repaired by this lane.
Independent read-only library_integration_finder and library_integration_skeptic
reviews found no ownership, preservation or closure issues; neither ran Lean.
This is source integration only: consumer proofs and changed-source gates remain
pending. The original goal stays blocked; G40–G42 and Backfill A/B remain partial
or blocked as documented above, never closed by this integration.


### Library continuation consumer (audit dff2fe2b)

`LibraryFrameTransport.resume_live` preserves the complete dependent live
snapshot (heap typing, heap, typed environment and transaction). Storage and
balance come from the actual selected world; the already-settled ledger becomes
empty. `tail_refresh`, `execute_success` and `execute_caught` consume actual
prefix execution, argument evaluation, prefix settlement, installed operation,
return decoding and catchability. They do not assume the desired simulation.
Preservation is uniform at continuation entry; arbitrary tails may mutate old
objects. The concrete supplied tails preserve their old aliases after execution.
`failed_tail_checkpoint` concerns the actual ContractWorld atomic checkpoint.
There is no published map relating ContractWorld worlds to Source.ExecState
journal states while preserving libraryCall/finish: the separate WorldFrames
journal rollback theorem is not silently applied to this representation.

`LibraryFrameControls` discharges the premises with actual intrinsic programs:
a prefix writes caller saved=9, pays 3 to address10, allocates [161,0,178],
binds two aliases of ID0 and keeps scalar77. A real installed library writes
caller saved=12 on success; its own saved remains0. A completed revert keeps
the actual prefix saved=9. The selected typed tail updates marker12/18 and pays2.
Both paths finish with caller95/recipient5, demonstrating settled prefix3 plus
tail2, not a repeated prefix payment. `live_actual` instantiates the uniform
snapshot result at this populated caller. `caught_application` uses the actual
operation reduction through published library_frame. RawLibrary.total is
explicitly discharged by a total raw extractor; the actual Binders.decodeT
returns primitive12 and the complete ordered unconsumed [0,254].

`packet_actual`, `observe_packet` and `reason_execution` transport arbitrary
complete failure bytes through the real library operation and actual typed tail,
then consume the existing Source/Error agreement and CatchKind decoder. Controls
cover custom bytes [222,173,0,255], canonical Error, accepted unpadded Error and
truncated Error; no packet is reconstructed after catching. Real failing typed
programs distinguish argument failure, successful-call decoding failure, caller
tail failure and catch-tail failure. Wrong role/address/static operations remain
refused. `failed_tail_atomic` restores the actual original world after a failed
caller tail, distinctly from a caught callee preserving the settled prefix.
`packet_prefix_associative` consumes the existing owned observation-prefix law
on actual caught bytes and explicitly supplied caller observations; it supplies
no resource-indexed execution trace or journal/world simulation.

Independent read-only finder/skeptic reviews inspected actual source, premises,
non-vacuity and ownership without Lean/server/builds. Confirmed findings were
fixed: Error decoding now directly observes transported packets, constant-error
tail fixtures became real Prog.run bodies, and observation composition actually
uses WorldFrames while the absent journal relation remains explicit. Both final
source re-reviews found no blocking issue. Actual headline axiom sets are pinned
locally with guard_msgs: only propext or propext/Classical.choice/Quot.sound.
No global trust pin, semantic producer, expected verdict or proof budget was
edited by this consumer checkpoint.

Local-control reconciliation blocker: the user relayed the prior human decision
`call_ce385a5125ae4d06b1e976f6c1561935` (question1, coordinator chat
`01a18291-8b61-7ce2-914f-36d4242e0b88`) approving the narrow decoder correction
published as `aca22c9396011005a528bb39b29a57ecc5520770`. Decoder approval is not
requested again. Git blame identifies the exact-length-negative at
`Controls.panic_boundary_controls` as introduced locally by V13 in `53fedb657`,
not an original Solidity fixture requirement. Published producer documentation
records both original pipelines/native receipts, and its kernel controls prove
suffix independence, unsigned bounds and genuine malformed refusals. Raw producer
receipts are not present on this VM; no new local native replay is claimed.

The relay itself did not authorize changing the retained V13 control. A concrete,
independently reviewed local-only patch was prepared, and the human then explicitly
answered `Q-PANIC-CONTROL`: “Authorize only this local V13 control reconciliation
and added malformed negatives, followed by required validation.” Exactly that patch
was applied. The obsolete suffix rejection now observes exact code1 acceptance;
zero/max and all existing genuine negatives remain, with truncated35-byte,
missing-word and wrong-selector negatives added. Decoder, original fixtures,
expectations/verdicts, source/default profiles and pins remain unchanged. This is
not a historical-runner authorization or broader semantic/ABI coverage decision.
The local question is resolved; missing original producers and failed gates remain.

Two existing owned proofs were adapted without changing statements or premises:
`ErrorEmission.panic_roundtrip` now takes the complete32-byte word explicitly;
`ReturnedBytes.error_not_panic` uses distinct selectors instead of obsolete length
reasoning. Both retain their scoped allowed axiom sets. The initial bounded full
`./run-lean.sh` ended exit1 after5038.87 seconds, reporting Controls and ReturnedBytes.
Its raw failure and resource data remain separate from subsequent successful repair
checks: ReturnedBytes MCP strict success and focused closure199 jobs PASS. The
full run reached its hard12GiB cap (253 max events), swap0, no OOM/kill; sampled
aggregate peak RSS9097008KiB. No time/proof/resource budget was increased.
After explicit authorization, Controls MCP and focused46-job build pass. The
whole default/import closure passes1034 jobs (2.126s cached), and fresh whole-root
MCP is strict success/nonpartial/no errors or failed dependencies. Both authorized
control theorem axiom sets are guarded in a separate scoped audit: only propext.
The earlier full/root failures remain raw failures, not retroactively relabeled.
The unchanged timed-out TestSuite is not retried or granted a larger bound; the
composite full gate remains unresolved for that independent validation obligation.

| Original obligation | Current status and remaining producer |
|---|---|
| Work1 G40 | Partial preparation only; every in-profile aggregate decoder/entry dispatch and noncanonical/refusal compilation remain open. |
| Work2 G41 | Partial: actual catch consumers, Error/Panic/layout laws and represented returned-byte observer exist; uniform aggregate result/error emission and cross-call target decoding remain open. |
| Work3 G42.01 self calls | Blocked final application: no complete V12 target/world plus ABI transport chain. Intrinsic self-call consumers remain preparation. |
| Work3 G42.02 external calls | Blocked: arbitrary permitted target callees, CALL/RETURNDATA, exact target exceptions and world transport are unavailable. |
| Work4 G42.03 callbacks | Blocked: arbitrary target reentrancy/callback frame relation unavailable; source journal/frame preparation is not that theorem. |
| Work4 G42.04 libraries | Partial: actual published caller-storage continuation consumed with uniform live entry snapshot and inhabited execution; aggregate ABI and compiled library-world endpoint unavailable. |
| Work4 G42.05 external function values | Blocked: address/selector target dispatch and all-signature/static composition missing; reserved owners unchanged. |
| Work5 G42.06 composition | Partial preparation: actual library selection/atomic checkpoint and observation concatenation; no full constructor/resource-indexed target call-mode/ABI/world/rollback composition. |
| Backfill A | Partial: arbitrary layout/offset/length/noninterference and returned-array packet observers plus malformed/noncanonical controls; no uniform aggregate codec/emitter closure. |
| Backfill B | Partial: typed library live frame/world selection, actual prefix and exactly-once settlement controls, checkpoint/observation laws; journal-world relation, arbitrary target callee/callback and final composition remain open. |

Changed-source final gates and artifact reviews are recorded in the new external
handoff/evidence seal; the original persistent goal remains blocked and untouched.


Final source finder/skeptic re-review also inspected the unchanged-statement
ReturnedBytes proof repair and found no weakened theorem, hidden premise or
ownership breach. The skeptic's confirmed stale documentation finding was fixed:
the local-control question now replaces the obsolete decoder-compatible-closure
request. All initial full failures, intermediate diagnostics and historical seals
remain retained; no failed gate is relabeled green.


Terminal validation account: Lean4.24.0/Lake5.0.0-src+797c613 and KeySort2 jobs
passed. Earlier root MCP returned nonpartial failure/diagnostics_unavailable with failed
dependencies (including retained Controls); root is not certified clean. Independent
SolkeyTestSuite build retained timeout124 at180.12 seconds under its unchanged
180-second bound; it was not retried. The pinned sort gate passed:377 taclets,
131 read-bearing, table covers131. Initial full gate remains exit1/5038.87 seconds;
after the unchanged-statement ReturnedBytes repair, focused import closure passed
199 jobs. The later post-authorization default/import gate and root MCP pass separately;
the full composite TestSuite obligation remains failed/unresolved, not waived. The original goal stays blocked and untouched.

Static evidence:17 owned modules/0 forbidden imports;180 core modules/0 layer
violations;1049 reachable/0 orphans;trust1064 sources/248 inventoried sites/0 findings;
49 published Node source/IR adapter fixture tests pass, not native EVM tests.
Original pinned TestSuite static parity passes564=552derived+11refuted+1excluded,
0pending/0divergent,2skip. All30 prior seal entries verify. Doc raw exits remain1:
current/published85 findings (48missing37ambiguous), frozen83 (46missing37ambiguous).
Complete finding-line/multiplicity comparison isolates the two published inline-
assembly missing paths, no removals; frozen no-new FAIL and publication equality
PASS remain separate. All17 owned registrations and10 relative doc links resolve.

Proposed coordinator G03 reconciliation only: attach the new local evidence to
G41, G42.04 and G42.06/BackfillB; retain every original parent as incomplete and
all original signatures/refusals/observations. No generated ledger/coverage status
or global TrustAudit pin was edited. No native_decide/sorry/new axiom, proof-budget
increase, new profile, historical runner, push/default-branch merge or PR.


Post-authorization checkpoint review covers the actual applied local-control diff,
explicit human scope, genuine malformed negatives and guarded propext-only audits.
Earlier pre-authorization exports are preserved separately and were not sealed;
the final authorized export uses a new directory/head and never rewrites prior seals.
No original fixture observation or global semantic/profile default changed.

### Published ABI-entry prerequisite (099bfbe1)

Integrated exact published `099bfbe185731c354b12a40f28ccf5d98534c779`, including
CF1 `64bc48673aeab48ea79143947104c975e1eba757`, into the isolated assigned lane.
Both independent read-only integration reviewers verified published source hashes,
ancestry, preservation of all17 owned modules and approved Panic controls, and
append-only registration resolution; neither ran Lean/server/builds. Only the
module-map append conflict needed resolution, retaining both complete sides.
Three inherited publisher EOF-blank-line diff-check findings remain raw failures;
reserved documents were not repaired. This is source integration, not lane closure.
The new Shape/Val/Entries and entry/verdict facts remain owned/read-only upstream.
Owned G40 consumers and bounded validation follow; all original queues stay open.


### G40/BackfillA published entry consumer (099bfbe1)

EntryTransport consumes existing indexed AbiEntry.Shape/Val/Entries and exported
verdict_revert_iff, verdict_run_entry and eager_cref without changing upstream.
rejection selects the actual Failure.emit.empty only for certified entry.revert;
runRejection executes that selected real program in the existing checked Slice.
entry_revert_exec/verdict_revert_exec retain real Fits and two-stack-cell bounds,
exact empty bytes, unchanged full memory/stack and unreachable suffix. Accepted
and named-blocked cases produce no rejection program. This is NOT emitted decoder
code or a proof of entry/native/bytecode equivalence.

body_from_entry/body_witness preserve actual entry and bodyValues witnesses;
calldata_handoff couples the real reference/eager result with actual cval, keeping
I.size<=lim and the published one-step fuel difference. Controls compute actual
aggregate values from the decoder, not arbitrary expected typed fixtures. Complete
ordered diagnostic values cover nested arrays, shared overlapping tails, a signed
negative-offset lazy-only layout, and unpadded bytes with embedded zero/padding.
encodeArgs is only a diagnostic encoding, not a source operation on readsOnly
parameters. G0 generalized recursors add a length-only typed-value projection
with concrete1/2 results. bodyObservation still calls published bodyValues; this
is neither a Source Prog execution witness nor general native x.length admission
for malformed unaccessed elements. Copying lazy-only layouts, access-time failures,
possible allocation Panic(0x41), and fuel exhaustion retain exact named blocked
verdicts and never become certified empty reverts. Dirty uint8 aggregate and a
truncated head actually drive the real emitter; a1023-cell stack fails closed.

Independent read-only finder/skeptic reviews found no soundness/ownership issue.
Their confirmed diagnostic-versus-source-body concern was fixed with explicit
labels, G0 recursor length observations and retained admission limits. Both used
no Lean/server/builds. Actual scoped axiom guards use only standard axioms; the
length observer control is axiom-free. Native0.8.38/reference dependencies are
absent locally; no new native pipeline is exercised or claimed, no0.8.34 substitute.

All original Work1/G40 remains PARTIAL: no all-profile emitted decoder, selector/
receive/fallback target dispatch, source/native theorem or bytecode simulation.
G41 remains PARTIAL; G42.01/.02/.03/.05 final target/world applications BLOCKED;
G42.04/.06 and BackfillA/B remain PARTIAL with the prior exact residual producers.
Arbitrary callee/callback/world/journal/persistent-transient/resource and CALL/
RETURNDATA prerequisites stay open. Allocation/access-time/lazy/fuel refusals and
original profile/fixtures/verdicts/pins/Fml.inTarget/Panic controls stay unchanged.
Proposed coordinator G03 update: attach local G40/BackfillA evidence only, close
no parent, edit no generated ledger/global trust pin. Final gates/handoff below
are bounded evidence, never whole-lane completion.


Final entry-checkpoint validation: Lean4.24.0 commit797c613 / Lake5.0.0-src+797c613;
KeySort passes2 jobs; pinned sort377 taclets/131 read-bearing/table covers131.
Both new per-file MCP diagnostics pass, focused entry build16 jobs passes, final
root MCP passes with no failed dependencies/errors. The initial changed-publication
default gate FAILED1/5386.152s: ReturnedBytes.memory_call_pushes_zero lacked the
new memoryLoops/memoryLoopScopes constructor alternatives; the scoped axiom guard
correctly rejected the incomplete elaboration. Only those two false=isMemoryCalls
branches were added as contradictions; statement/premises/guards unchanged. Both
independent source reviewers approved that exact2-line fix. Per-file MCP and
ReturnedBytes controls/prefix closure pass200 jobs/15.343s; repaired full default
passes1059 jobs/2.110s using the one existing cache. Initial raw failure stays failed.
Final scoped actual #print axioms passes, including compiled_return with no sorryAx.

One TestSuite attempt was justified by actual published Derived17/MemoryLoopReplay
proof/dependency changes, documented before running. Under its unchanged180s bound
it FAILED124/181.125s (Derived8 and Derived7 completed); not retried. The full
./run-lean.sh composite remains unresolved, with prior1/5038.87s and prior
Suite124/180.12s preserved. No larger TestSuite bound, bypass or green composite.
All heavy work serial LEAN_NUM_THREADS=1/Lean-j1, hard12884901888 bytes memory,
swap.max0, one cache. Initial default sampled peak aggregate RSS9086968KiB,
cgroup peak hit12GiB with613 max events but0OOM/0OOM-kill; repaired default peak
1095716864 bytes/0max events, Suite peak6336241664 bytes/0max/0OOM. Root MCP sampled
peak3441491968 bytes. Disk headroom initially20GiB/final19GiB; prior39 checksum entries all verify.

Static passes:19 owned modules/0 forbidden imports;184 core/0layer violations;
1096 reachable/0orphans;1111sources/258trust sites/0findings;25 Node adapter tests
and pinned TestSuite static564=552derived+11refuted+1excluded/0pending/0divergent/2skip.
Raw docs FAIL1 for current/frozen/publication: complete finding multiplicities
current86(48missing38ambiguous), frozen83(46missing37ambiguous), publication86.
Frozen no-new FAIL: two inline-assembly missingpaths plus finite-dispatch Arms.lean
ambiguity; publication equality PASS separately. Reserved-owner repair requested;
no reserved doc edited/placeholders added. Owned relative links and diff check pass.
Three inherited publisher EOF diff-check findings remain failed historical evidence.

Final finder/skeptic source reviews pass actual diff/premises/nonvacuity/ownership,
with approved local Panic controls byte-unchanged. Both ran no Lean/server/builds.
New exact-head artifacts and their independent review/seal are outside the source
checkout; prior seals/raw failures remain intact. Every original Work/Backfill
status above remains open: this checkpoint only advances G40/BackfillA preparation.
Missing admitted source/native-to-entry correspondence, all-profile emitted decoder/
dispatch/aggregate result codecs, target CALL/RETURNDATA, V12 target frames/world,
arbitrary callees/callbacks, linked library target world and resource prefixes stay
explicit. The existing blocked goal was not mutated or reactivated.


### Published enum prerequisite and parallel interface (457130f3)
Exact published457130f3da4bc474825bc8f3df6bf65e1c33f813 incorporates CF1enum6816ca49
and CF2 round2. Fetch onlyorigin/master; frozenbase/099bfbe1/6816ca49 ancestry verified.
Independent read-only finder/skeptic PASS combined diff/ownership before checks:
all19 priorownedmodules and approvedPanic controls byte-unchanged; producer bytes
exact publication, only prior append-only root/map/README registrations differ.
No conflicts, unmergedpeerinputs or reserved edits. Source integration alone is
not consumer/runtime validation. Next owned enum/packet proofs retain actual
Kind.enumBelow cardinality, typed signatures and all Fits/stack/fuel/size/refusals.
Human parallel scheduling authorization does not change semantics or completion.
An exact66c08fde committed interface package is exported separately (not a dirty
combined-tree snapshot) for peer development; final concrete combined gates remain
required. All original Work/Backfill queues and blocked goal are preserved.


### G40/G41/BackfillA enum and typed packet consumers
Published Kind.enumBelow n is used directly; no uint8-cardinality equivalence is
assumed. EnumEntry.invalid_entry proves whole-loaded-word n<=w causes actual entry
revert before ANY tail parameters at fuel+2. invalid_revert and truncated_revert
select the existing checked empty REVERT with real Fits/stack conditions. No enum
comparison/decoder machine code is emitted, no source/native entry theorem added.
PacketEmission.emitResult/emitCustom consume actual indexed Vals and existing
encodeArgs/selectorBytes, then actual Failure.emit.returned/custom; execute_result/
execute_custom retain exact bytes, memory interval, entire old stack and unreachable
suffix. accepted_packet and EnumControls.accepted_emission discharge actual entry/
bodyValues witnesses on real decoded tuples. This is value-specialized packet
emission, NOT a runtime encoder of symbolic word memory or all-profile ABI compiler.

Inhabited memory/calldata signatures put enum3 value2 BEFORE a dynamic uint8-array
[7,0,255]. Full192bytes, relative offset64, length3, zero/last255 and selector11223344
are observed; custom selector does not change the argument-relative offset to68.
Noncanonical tail offset96 (32-byte gap) layout and empty array accepted, exact original inputs
retained. Missing/truncated word load as0 yet reject by head size; one-past3 and
highword2^248+2 reject without low-byte cleanup. Invalid leading enum preempts an
eager memory allocation Panic; calldata retains its own tail behavior. Dirty array
memory entry reverts, lazy calldata element failure remains named blocked; allocation
Panic/fuel remain blocked, never certified empty revert. Actual reference after enum
is100/3; eager64 and cval63 agree via published eager_cref with size<=lim. Old stack
77/88 and exterior byte observations retained;1023-cell stack rejects. All controls
are kernel codec/byte-slice facts, not source admission or arbitrary target calls.

Independent read-only source finder/skeptic found no soundness/G0/ownership issue.
Confirmed clarifications applied: selected-existing-emitter wording, memory-only
Panic preemption, and one inhabited combined accepted_packet endpoint. Preliminary
MCP recursion failures were repaired through actual projection witnesses without
raising limits; raw failures retained. Actual scoped axiom outputs use only the
standard axioms; exact guards are pinned locally, not in global TrustAudit.
All prior19ownedmodules/approvedPanic controls remain unchanged. Every original
Work/Backfill remains partial/blocked. Top-level v2 enum publication does not close
nested enums, constructor/v1, selector/receive/fallback compiler, runtime aggregate
encoder, arbitrary external/callback/world/rollback or resource-prefix composition.


PARALLEL source checkpoint gates: all22ownedmodules focused closure PASS219jobs;
new3per-fileMCP PASS and13actual scoped axiom outputs/guards use standardsets only
(selector_split propext). No oldownedKind match repair needed. Staticimports22/0,
layers184/0,orphans1100/0,trust1115sources258sites/0; Node25PASS, pinnedTestSuite
static564rows/0pending/0divergentPASS. ActualLean4.24.0/Lake5.0.0-src+797c613 and
KeySort2jobsPASS. MCP-container sort script SKIPPED because reference mount absent;
not a passing sort gate; actual pinned full-container check remains required.
RawdocsFAIL1: current/published86(48missing38ambiguous), frozen83(46missing37ambiguous).
Complete finding classes/multiplicities retain exactly3published new findings:
finite-dispatch Arms.lean ambiguity and2inline-assembly missingpaths. Frozen no-new
FAIL, publication equalityPASS separately; no reserved doc repair/placeholders.
Prior51sealed entries verify, oldfirstinterface seal preserved; correctedR2 exact
66c08fde source interface sealed separately with reviewed no-payment/reference/
live-at-entry clarifications. Current newenum/packet interface is exported from this
exact focused-checked commit with full import/default/root/composite gates PENDING;
peer staging cannot count as final integration. Every original Work/Backfill remains
partial/blocked; original goal unchanged. Broad checks follow this early committed
handoff so peer development need not wait for the whole preceding lane/gate.


### G41/BackfillA/B full-word array observation and packet transport
Continued ready owned work after the early f103b7c6 parallel checkpoint. That
exact immutable delta/source package remains unchanged for peer staging; default
1063jobs PASS3989.158s and rootMCP PASS at that head are separate later evidence.
New once-only changed-publication Suite180 attempt FAILED124/181.061s; no retry
for the following owned observers, which do not affect TestSuite. Composite remains
unresolved, all earlier raw failures remain failures. Pinned full-container sort
PASS377/131 separately repairs the MCP-container reference-mount skip, not its log.

WordArrayPacket reuses published Scalar.encode_uint_toNat and ArrayRepr/StateRepr,
constructs existing indexed AbiEntry.Word/Seq/Vals, and observes EVERY actual numeric
word. No ByteRange premise, silent uint8 truncation or new decoder/machine semantics.
compiled_observation consumes actual Compilation.correct, isMemoryCalls/Input/
noPay/hrun/hget and retains full StateRepr/BaseExtends/GrowsAllocator. Values are
explicitly modeled as uint256[]; Core normalized types alone do NOT establish an
admitted Source declaration/result signature. encoded_values is an unconditional
raw-codec formula (offset32, encoded length, complete32-byte words); exact length
needs length<W, supplied for real Core arrays by heap_length. Source ABI64-bit lim/
allocation/admission conditions stay separate and unchanged. observedPacket reads
an ALREADY EXECUTED symbolic word-machine result, then emits a value-specialized
literal through the real Failure byte-slice. This is not a static runtime encoder,
not one machine identifying word and byte addresses, and not Source/world simulation.

Two actual compiler applications start from the published real nonempty setup:
old object0 [161,178], caller marker42, saved9, stack77 and sentinel99. Callee aliases
or privately allocates a3-word return, writes300, drops a private bool local; caller
writes11. Actual fields show result pointer259/264, argument pointer259, header3,
complete old object header2/contents161/178; frame6, reached cost5/9 retained. The
complete160-byte ABI packets encode [11,300,255] or [11,300,0], including01,2c for300;
the old BYTE observer still refuses300. Wrong pointer yields a different well-typed
empty observer value, wrong header/order/offset claims fail, symbolic slots are outside the
numeric observer. Successful target_run comes from actual compiler completion;
target is only a finite diagnostic projection, never a fallback execution oracle.
The raw200k heartbeat failures in symbolic interpreter rewriting are preserved;
using an abstract result projection/kernel finite diagnostics repairs them without
raising limits or changing theorem premises. Singleton enum controls additionally
isolate complete36-byte acceptance from4/35-byte missing/truncated-word rejection,
with actual entry/body values and emitted RETURN/empty REVERT endpoints.

Independent read-only finder/skeptic initial reviews found no soundness/G0/ownership
issue. Confirmed clarifications/strengthening applied: raw-list versus Core/source
length bounds, explicit successful target, complete older-object/argument-pointer
observations, separate post-execution packet scope. New guarded17axiom outputs use
standard sets; prior13guards/Panic controls remain unchanged. Every original Work/
Backfill stays partial/blocked; runtime ABI memory reading/emission, Source-native/
declaration agreement, arbitrary external CALL/RETURNDATA/world/callback/library/
function-value/resource chains remain genuine unresolved producers. No source-only
interface or conditional theorem closes those premises; no generated ledger/pins.


Word-array checkpoint validation: newfiles and amended singleton controls per-file
MCP PASS, all24ownedmodules225jobs focused PASS. Actual17additional scoped axioms/
guards standardsets only; combined30headlineguards. Raw HB200000/recursion failures
remain archived; no budget change. Finalstatic:24imports/0forbidden,184core/0layer,
1102reachable/0orphan,1117sources/258trustsites/0findings. Complete rawdoc finding
comparison remains86current/86publication/83frozen, rawFAIL1 and frozenno-newFAIL;
publication equalityPASS is separate. No reserved document edit or placeholder.
Both independent read-only final staged reviews PASS actual7path diff, premises,
nonvacuity and G0. Minor empty-observer wording clarified without allocated-object
admission claim. Old19pre-enum ownedmodules/approvedPanic remain unchanged; early
f103parallelpackage seal unchanged. New cached import/default and rootconfirmation
follow this exact committed source. Suite/composite prior failures are not retried
for these observers; they do not reach the Suite dependency graph. Originalfullgoal
unchanged/blocked; no push,defaultmerge,PR,peerunmergedinput or globalpin/ledger edit.


## Recovery8229a81e: selected compiled caller alias to current packet

Checkpoint parent `6ca8356729861c0d34b14a12abef9e9ef406b678`; frozen base remains
`2fe1f8932f96be15b00df03ba2cde46f64a87758`. This is G41/BackfillB preparation,
not full G40–G42 delivery. The existing persistent goal remains blocked and untouched.

The human-authorized private dependency input is exact V12 commit
`7881cb3aa87b7b01ae557d12de19b8eeeed7ba3b`, with published prerequisite099bfbe1.
All90 archive sources were matched against both original SHA256 manifest and
actual committed Git blobs. Only the six required InternalFlow modules and
three producer fixture modules are overlaid read-only in the private dependency
tree. The other81 task-owned copies and original sealed package remain intact.
No producer was merged into this branch or represented as published. Reconstruct
this checkpoint with that exact nine-source overlay to validate the combined tree;
the assigned checkout alone does not contain those unmerged producer imports.

[`CallerPacket.lean`](../../Solidity/Backend/AbiWorld/CallerPacket.lean) proves
`captured` and `selected`: actual CallerTail.selected_target yields the reached
dropped StateRepr, actual target run, stack, BaseExtends, GrowsAllocator and typed
caller capture. CallerView.reference/represented then connect the old alias to
WordArrayPacket.local_complete/encoded_values. The complete CURRENT array is
observed, including mutation. Exact header/space and independent base addresses
remain; no byte-range restriction or unchanged-heap premise is introduced.
All producer miss/hit, Disjoint, withinM, writesAt exclusion, actual source run,
representation, frame and reached capacity premises remain explicit.

[`CallerPacketControls.lean`](../../tests/v13-abi-world/CallerPacketControls.lean)
reuses the exact producer fixture rather than defining another evaluator.
`selected_client` literally applies the new selected theorem; `prefix_client`
discharges input through actual compiled nonempty setup. `application` observes
the captured old array after mutation `[7,11]` to `[12,11]`; the same actual result
has entry-address identity and complete128byte codec packet: words32,2,12,11.
`resource_client` proves prefix/selected word-cell costs7/4, total11 and cursor
135→139 with stack77. `scalar_fields`/`scalar_packet` retain marker42 and actual
callee storage mutation9→11. `alias_negatives` excludes distinct older, private
and default objects through reached representation separation. `ordered_bytes`
rejects stale, reversed, other `[23,29]` and private `[99,101]` payload claims.
The prefix heap has3objects and reached heap5; the whole caller environment is
correctly not framed because the tail writes its unprotected destination.

Both new files have per-file strict MCP diagnostics PASS; all13 headline axiom
guards PASS (standard propext/Classical.choice/Quot.sound only; ordered_bytes
axiom-free). Source preparation of the three exact producer fixtures PASS within
120seconds. Final explicit-j1 serial-wrapper import gate PASS1062jobs; root MCP
PASS; focused closure, complete ordered byte/signature export, owned-import25,
layer184, orphan1109 and trust1124/258 checks PASS. Hard12GiB/no-swap/CPU1 and a
single shared keyed cache were enforced. Early preliminary Lake checks selected
the direct sysroot; final Lake checks corrected that with the existing wrapper
and task-only -j1 weak arguments. No tracked build configuration or budget changed.

Finder and skeptic independently reviewed actual source/premises/non-vacuity and
ownership without Lean/server/builds. Finder's confirmed core-to-elaborator issue
was fixed by moving the inhabited client into lane tests. Proof decomposition
fixed the raw200000-heartbeat failure without raising the budget. All failures,
including the initial signature-export path failure, are retained in NEW evidence.

Raw docs remain FAIL1:86findings (48missing/38ambiguous), frozen83; three inherited
published regressions remain. Exact complete finding-class/multiplicity equality
to publication457130f3 and prior6ca is a separate PASS, not a frozen-gate waiver.
No reserved document was repaired. Original Suite124/181.061seconds, oldfull5400,
fullcomposite1/5038.87seconds, OOM/heartbeat and other sealed failures stay unchanged;
no unchanged failed Suite/composite command was rerun.

Every original queue remains accounted for: G40partial, G41partial;
G42.01/.02/.03/.05blocked; G42.04/.06partial; BackfillsA/Bpartial.
This discharges a narrow selected INTERNAL call-plus-tail caller-array observation,
not general ABI admission/decoding/emission or external/self/library/callback/world
compilation. Missing Source-type/entry agreement, uniform runtime aggregate codec,
CALL/RETURNDATA, arbitrary callee/callback world relations, physical resource
composition and required whole-lane gates remain explicit. No byte-slice machine
is identified with word cells; no post-execution literal packet is claimed here.
No new semantic choice or producer repair is requested. G03 reconciliation proposal
only: attach these named G41/BackfillB local facts; close no parent feature ID.

NEW evidence: `/workspace/scratch/v13-caller-tail-8229a81e-evidence`.
NEW exact-head artifacts: `/workspace/scratch/v13-caller-tail-8229a81e-artifacts`.
Original sealed exports/manifests are preserved and referenced by the new handoff.


## Mixed scalar and current-array packet increment after88111a7b

This original G41/BackfillA/B checkpoint adds
[`Solidity/Backend/AbiWorld/MixedPacket.lean`](../../Solidity/Backend/AbiWorld/MixedPacket.lean).
Its intrinsically typed tuple is `[dynamic uint256 array,uint256 scalar]`;
`snocWord` uses generalized Vals.casesOn, not an untyped representation or a
second codec. `scalar_complete` derives the actual numeric local from reached
StateRepr.core.vals. `array_encoding`, `head_size`, `encoded_values` and
`encoded_length` use the published codec: head64, scalar, length, every ordered
full uint word, exact96+32*n bytes. There is no ByteRange restriction.

`captured` proves the captured primitive is unchanged while the OLD alias denotes
the CURRENT reached array. `selected` composes actual CallerPacket.selected with
typed capture, preserving actual target run, stack, StateRepr, BaseExtends,
GrowsAllocator, miss/hit, Disjoint, tail withinM/write exclusion, actual source
success, frame and reached capacity premises. Reached arrays provide length<W;
raw typed-list codec equations have no admission assumption. Source ABI64-bit
allocation/fuel/reference/profile admission and byte Fits are separate obligations,
not consequences of a word-cell heap bound. No source admission theorem is claimed.
`execute_observed` composes existing literal result emission AFTER observation,
with a SEPARATE byte-slice machine, actual Fits and two-cell stack bound.

New controls live outside core in
[`tests/v13-abi-world/MixedCodecControls.lean`](../../tests/v13-abi-world/MixedCodecControls.lean),
[`tests/v13-abi-world/MixedCallerValues.lean`](../../tests/v13-abi-world/MixedCallerValues.lean), and
[`tests/v13-abi-world/MixedPacketControls.lean`](../../tests/v13-abi-world/MixedPacketControls.lean).
The inhabited endpoint reuses the checked selected target and applies new captured
transport to that SAME reached representation. This differs from literally
instantiating the generic selected theorem on the large fixture; those attempted
elaboration routes failed and remain failed evidence. No desired execution or
capture is assumed, and the generic selected theorem is independently proved.

The real nonempty compiled prefix/call/tail yields complete160bytes with words
64,42,2,12,11 AND the previous128byte standalone array on one machine. Marker42
is retained, storage changes9→11, current array is12,11 rather than stale7,11,
old-address identity and stack77 survive. Resource controls retain costs7+4=11 and
word-cell cursors135→139. Other/private pointers are excluded by reached heap
separation. Pure codec fixtures cover empty96bytes, array element300, and max uint256
in both scalar and element positions, with complete ordered vectors. Negatives retain
positive baselines for offset32, swapped typed fields, stale/private arrays and
marker11; marker42 is explicitly distinguished from storage11 in the actual
compiled result. A separately checked literal160byte result discharges Fits/stack;
it is not unknown-runtime-memory encoder code or a word/byte simulation.

Strict per-file MCP checks for all4new files, all22headline scoped axiom guards,
focused/import closure and source fixture checks pass under original bounds.
The raw45second partial diagnostic,200000-heartbeat normalization failure,
two11GiB preemptive memory-guard stops and the syntax/focused failure are retained.
Proof decomposition and reuse of actual checked frame facts repaired the checking
path; no proof/time/fuel/node/stack/resource budget changed and no guard was lowered.
No unchanged failed Suite180/composite5400 gate was rerun.

Independent read-only finder/skeptic source reviews pass: actual premises,
non-vacuity, source ownership, scalar/current-array distinction, concrete endpoint
versus generic proof route and separate literal machine were checked without Lean.
All prior25owned modules and prior caller controls remain byte-identical to88111a7b;
the nine exact read-only private V12 sources at7881cb3a are unchanged. Assigned
checkout alone still lacks those imports; all passing Lean gates are private
combined-tree checks. Persistent goal remains blocked and untouched.

Every original queue remains open at its existing status: G40partial, G41partial;
G42.01/.02/.03/.05blocked; G42.04/.06partial; BackfillsA/Bpartial. Full source/native
entry/decoder/dispatch agreement, emitted runtime aggregate codec, CALL/RETURNDATA,
arbitrary callees/callback/library/world and physical resource composition remain
unresolved. Global coverage/TrustAudit/G03/profile/verdict/pins are unchanged.
Proposed coordinator ledger attachment: these named G41/BackfillA/B local facts,
not parent closure. No new human semantic question.

NEW evidence: `/workspace/scratch/v13-mixed-caller-88111a7b-evidence`.
NEW exact-head artifacts: `/workspace/scratch/v13-mixed-caller-88111a7b-artifacts`.
Raw docs1/frozen no-new failure remain separate from complete publication/prior
finding equality; reserved doc repairs and prior mandatory failures stay open.


## Audit87fc9907: two current dynamic-array packets

Original G41/BackfillA/B increment afterb7b64c76; full V13 remains partial.
[`Solidity/Backend/AbiWorld/ArrayPairPacket.lean`](../../Solidity/Backend/AbiWorld/ArrayPairPacket.lean)
concatenates existing intrinsic Vals with generalized casesOn, reads both arrays
from ONE actual StateRepr using WordArrayPacket.local_complete, and uses the
published AbiEntry.Val/Seq/Vals codec unchanged. There is no replacement encoder,
new source/heap/target semantics, emitted runtime memory reader or new literal
packet pipeline. Equal references and equal indices are allowed generically.

The actual first encoded payload determines secondOffset:64+payload.length,
proved96+32*n. Exact total length is128+32*(n+m). Generic encoded_values/words,
head_slices, first_tail/second_tail/first_prefix and prefix_noninterference retain
complete order. Changing second contents OR length preserves the first prefix;
this is a codec fact, NOT a heap-write frame for aliased objects. Empty arrays
still encode a length word, so empty-first secondOffset is96, not64.

Both current arrays and both entry-address identities follow actual captured
caller references. selected consumes CallerPacket.selected, retaining original
compilation/miss/hit/Disjoint/tail withinM/write exclusion/source execution/
representation/frame/capacity, stack/BaseExtends/GrowsAllocator premises. The
original Disjoint guard concerns return destination versus captured view; no
array-separation hypothesis was added. Both typed heap lengths are<W. This does
NOT imply the byte offset96+32*n<W; generic wordBytes formulas are raw codec,
not an unwrapped-decoder or Source ABI64 allocation/fuel/profile theorem.
Concrete offset160 bound and actual published second-head loads at byte32
returning96/160 pass; the96/128/160 arithmetic cases are proved separately.

New tests
[`tests/v13-abi-world/ArrayPairCodecControls.lean`](../../tests/v13-abi-world/ArrayPairCodecControls.lean),
[`tests/v13-abi-world/ArrayPairValues.lean`](../../tests/v13-abi-world/ArrayPairValues.lean), and
[`tests/v13-abi-world/ArrayPairControls.lean`](../../tests/v13-abi-world/ArrayPairControls.lean)
reuse the existing populated compiled prefix and selected call/tail. ONE reached
machine provides BOTH256byte packets: shared old object[64,160,2,12,11,2,12,11]
and distinct older object[64,160,2,12,11,2,23,29], alongside original160byte mixed
and128byte standalone observations. The shared-object witness uses distinct
retained locals pointing to the same reference; no narrower equal-index-only
fixture. Both headers2, old-address identities, marker42/store11, stack77 and
actual base/growth relations remain. Alias controls prove shared cell equality,
other-cell inequality and private-object refusal from reached representation.
Resources retain actual prefix7+call4=11wordcells and cursors135→139.

Codec-only empty/full-word controls include both-empty128, one-empty192 and
full-word224byte packets with300 and maximum uint elements in the two arrays.
Wrong second offsets, swapped tails, stale[7,11], private[99,101], deduplication,
missing empty length words and byte truncation claims have positive baselines.
Changing the second array length to zero still preserves the full first prefix.
All19complete ordered vectors, including all9prior mixed/standalone vectors
reexported byte-identical, are retained. No altered expected vector or ByteRange
restriction. Pure codec fixtures are distinct from compiled/source admission.

All4new files have strict per-file MCP PASS, focused/import and three source
fixture checks PASS, and34headline scoped axiom guards with only standard
propext/Classical.choice/Quot.sound dependencies. Raw syntax, redundant-tactic,
length-equation and recursion-depth constructor-search failures remain in NEW
evidence. Constructor search for the huge numeric bound was replaced by kernel
decision checking; no proof/recursion/time/fuel/node/stack budget changed. An
initial intended heap-length edit missed its exact target; the retained repeat
failure was followed by verified replacement using published Heap.len/MObj laws.
No unchanged failed Suite180/composite5400 retry or guard weakening.

Independent read-only finder/skeptic source reviews pass without Lean/server/
builds. They checked actual premises/non-vacuity, same-machine observations,
equal aliases, nonwrap/admission distinctions and ownership. All prior26owned
modules and old test fixtures remain unchanged; nine exact read-only privateV12
sources at7881cb3a are unchanged. Mainalone still lacks those imports; all passing
Lean gates are private combined-tree validation. Persistent goal remains blocked
and untouched; this recovery does not reactivate automatic continuation.

Every original queue: G40partial/G41partial; G42.01/.02/.03/.05blocked;
G42.04/.06partial; BackfillsA/Bpartial. General source/native decoder/dispatch,
unknown-runtime aggregate encoding, CALL/RETURNDATA, arbitrary callee/callback/
library/world/physical resource composition and mandatory whole-lane gates remain
open. Raw docs1/frozen regressions stay failed, separate from complete publication/
prior finding equality. Old Suite124/181.061s, full1/5038.87s, cold5400exit124 and
all original sealed failures remain. No reserved edit/pin/profile/verdict/semantic
change, new axiom, goal mutation or publication. G03 proposal only: attach these
named G41/BackfillA/B facts; close no parent feature.

NEW evidence: `/workspace/scratch/v13-array-pair-87fc9907-evidence`.
NEW exact-head artifacts: `/workspace/scratch/v13-array-pair-87fc9907-artifacts`.
Prior21-entry mixed seal and all94earlier entries remain immutable.


## Nested uint-array codec checkpoint (parent 784ac610, 2026-11-01)

Owned `Solidity/Backend/AbiWorld/NestedUintPacket.lean` constructs indexed outer
Seq values from arbitrary lists of full uint values, reusing WordArrayPacket.sequence
and the real AbiEntry Val/Seq/Vals/encodeArgs/assemble definitions. Generic proofs
provide all ordered words/bytes, top offset32, outer length, inner head offsets
relative to the element-head base AFTER the outer length, exact inner payloads,
and total bytes64+64*outerLength+32*totalElements. No ByteRange or disjointness
premise. Raw natural offsets, modulo word serialization and actual source
lim/allocation/fuel admission remain distinct; heap-length bounds imply no
unconditional total-size/nonwrap theorem here.

Earlier heads and payload prefixes are preserved only in the stated scoped
forms. Middle payload growth changes later heads; last payload changes preserve
the complete earlier prefix. Pure two-array regrouping is also proved, without
creating a nested runtime heap reference. Generic accepted_layout explicitly
requires an actual exact typed verdict; finite entry controls instead extract
actual eager/lazy body values and prove complete encoded-byte agreement. They
do NOT prove typed-value identity or instantiate that exact premise. Fuel0 is
blocked, never recast as revert. No universal nested admission/native agreement.

New lane tests `tests/v13-abi-world/NestedCodecControls.lean` and
`tests/v13-abi-world/NestedEntryControls.lean` cover mixed/empty arrays,
300/max uint/embedded zero, middle/last growth and wrong-base/relative-offset,
missing length/swapped/truncated-word byte claims after positive baselines.
All prior19complete observations are retained unchanged alongside new vectors.
Malformed byte inequalities are not new decoder-rejection theorems.

Strict per-file diagnostics and registered import build PASS;45scoped axiom
outputs use only standard propext/Classical.choice/Quot.sound (two are empty).
Initial direct typed-verdict reduction hit maxRecDepth and lacked Decidable;
actual Option extraction was factored through an abstract lemma, preserving
all proof/fuel/node/time limits. Raw failures remain in new evidence. Separate
independent read-only finder/skeptic source reviews found no semantic issue and
required the typed-identity reporting boundary above. Neither ran Lean/builds.

Original G40/G41partial; G42.01/.02/.03/.05blocked; G42.04/.06partial;
BackfillA/Bpartial. Native runtime decoder/dispatch, unknown-memory encoder,
CALL/RETURNDATA, arbitrary callee/callback/world/library/resource composition
remain open. This codec increment is not an emitted encoder or nested machine
representation. Mainalone lacks9private V12 inputs7881cb3a; combined validation
uses exactly the prior immutable overlay. Goal remains blocked and untouched.
No reserved producer/profile/pin/fixture/Panic control or prior seal changed.
Raw docs1/frozen comparison1 and Suite124/181.061s, composite1/5038.87s,
cold5400exit124 remain failures; no unchanged failed heavy retry. Publication/
prior complete finding equality is separate. G03 proposal: attach these named
G41/BackfillA facts, close no parent. Exact new gates/reviews/artifacts are in
`/workspace/scratch/v13-nested-784ac610-evidence` and
`/workspace/scratch/v13-nested-784ac610-artifacts`.


## Canonical readback checkpoint (parent cc281c12, 2026-11-01)

Owned `Solidity/Backend/AbiWorld/CanonicalReadback.lean` proves the EXISTING
AbiEntry.load reads a full word n<W embedded after arbitrary bytes and before
arbitrary bytes. It reuses ErrorRoundtrip.read_word and proves the actual
bytesAt/fold relation; no second loader, codec or machine. Values300/max/zero
remain whole uint256 words. Natural offsets, modulo serialization and actual
source admission are distinct; no ByteRange restriction.

Generic mseq_words/mdec_array consume real canonical bytes and construct the
actual indexed WordArrayPacket.sequence. Sufficient original fuel relations
are length+2 for the static-word sequence, length+3 for array mdec, and length+4
for top-level melem/eager/entry. These are sufficient lemma hypotheses, not new
decoder budgets or a necessary admission predicate. mdec_array uses the ORIGINAL
alloc check free+(cursor+(32*length+32))≤lim and returns that exact cursor.
Word length representability is derived from this bound, not assumed to follow
from heap length. Canonical input_size measures actual selector+codec+suffix.

roundtrip proves actual canonical memory/calldata verdicts with exact typed
WordArrayPacket.values xs, both complete encoded body observations and the
published cval read with the original one-step fuel difference. Arbitrary
four-byte selectors/trailing bytes are preserved; selector dispatch is NOT
proved. Its real input-size≤lim premise supports published eager_cref/lazy
agreement. Helpers without that size premise are scoped facts about the existing
intrinsic decoder/reference checks, not universal Source admission. The allocation premise on canonical calldata helpers
is sufficient for their eager-copy/body route, never a necessary restriction
on all calldata/lazy/readsOnly inputs. Original noncanonical cases are unchanged.

mdec_tail/nested_tail/nested_inner additionally derive actual selected-inner
array decoding from the real nested layout and its POST-length base. The
inhabited selectorless fragment decodes byte160 at cursor128→224. This is NOT
whole nested outer-sequence/entry readback. The generic dynamic mseq allocation
composition and full nested indexed entry identity remain unproved owned work;
no absent producer or assumed desired verdict is substituted for that proof.
Prior NestedEntryControls.actualValues still establishes its original encoded
byte equality; no new identity for those old witnesses is claimed.

New `tests/v13-abi-world/CanonicalControls.lean` instantiates generic results
for[300,max,0], empty arrays, arbitrary selector/trailing bytes and exact lim
allocation. Swapped/stale arrays are positively accepted with changed values.
Actual wrong-offset/missing-length/truncated entries revert; truncation consumes
the checked existing empty REVERT emitter with real Fits/stack conditions.
One-byte over-allocation and insufficient fuel stay BLOCKED, and a truncated
packet with over-allocation preserves panic-before-region order. Wrong-load
position/low-byte/truncated/swapped/stale byte inequalities are distinct from
actual classified decoder failures. No native/compiler/EVM agreement is added.

34headline scoped axiom guards and per-file diagnostics PASS; focused and
registered import closure PASS1066jobs. Raw dependent-match, syntax/name,
recursion-depth and unavailable equality-instance failures are retained. The
proof repair exposed the existing mdec dependent recursor and factored actual
error observation into a proof lemma; no decoder edits, raised proof/fuel/node/
time limits, axioms or trust shortcuts. Separate independent finder/skeptic
source reviews found no proof defect. Skeptic wording fix labels allocation
Panic as possible/blocked rather than a completed panic. Neither ran Lean.

Every original queue remains G40/G41partial; G42.01/.02/.03/.05blocked;
G42.04/.06partial; BackfillA/Bpartial. Full native/runtime decoding/dispatch,
unknown-memory encoding, CALL/RETURNDATA, arbitrary callee/callback/library/
world/resource composition and mandatory whole-lane validation remain open.
Private validation retains the exact9V12 inputs7881cb3a; mainalone still lacks
those imports. Goal blocked and untouched, no automatic reactivation. All
prior157entries/14seals remain immutable. Raw docs1/frozen86versus83 comparison1,
Suite124/181.061s, full1/5038.87s, cold124/5400.579s remain failures, not retried.
Complete publication/prior finding equality is separate. No reserved edit,
profile/pin/fixture/Panic-control change or push/merge/PR. G03 proposal only:
attach the named canonical G40/G41/BackfillA consequences; close no parent.

NEW evidence: `/workspace/scratch/v13-canonical-cc281c12-evidence`.
NEW artifacts: `/workspace/scratch/v13-canonical-cc281c12-artifacts`.


## Full canonical nested readback checkpoint (parent64e37675, 2026-11-01)

Owned `Solidity/Backend/AbiWorld/NestedReadback.lean` discharges the preceding
checkpoint's unproved generic uint[][] outer-sequence/allocation and indexed
entry/body identity obligation. It consumes the REAL codec, byte loader and
mdec/melem/mseq, not an assumed successful decoder or new allocator. All old
modules, semantics, observations, controls and9private producer inputs stay
unchanged; no profile/admission/default change.

outer_sequence keeps one actual I, processed-prefix head index and remaining
indexed Seq. Each step reads the actual relative offset from the real head table,
decodes one inner array, advances the head index and threads its exact resulting
allocation cursor. Offset≤lim/<W follows from actual canonical bytes and
I.size≤lim, not len<W. innerBytes measures actual inner payload lengths and
allocationBytes includes outer32*N+32 plus every inner allocation. The exact
sum is32+64*N+32*totalUInts; codec length is that sum+32. Every original rounded
alloc check is discharged by the global free+cursor+sum≤lim bound.

Original sufficient fuel is remainingN+remainingUInts+4 for mseq, N+UInts+5 for
outer mdec and N+UInts+6 for top-level melem/eager/entry. These are auxiliary
sufficient bounds, not raised budgets or necessary admission predicates.
roundtrip proves full actual indexed values in memory/calldata verdicts, complete
body observations and published cval with its original one-step decrement.
Selector/trailing bytes, actual input-size≤lim and allocator bounds remain explicit.
Calldata allocation conditions suffice for this canonical eager/body route;
other noncanonical/lazy/readsOnly behavior is unchanged, not excluded.

canonical_layout consumes NestedUintPacket.accepted_layout GENERICALLY from
these proven actual verdicts. New `tests/v13-abi-world/NestedOuterControls.lean`
also preserves the old mixedInput/free/fuel64/locations before proving its
canonical verdict, original actualValues typed identity by Verdict.run injection
and the old exact entry/body layout premise. No codec injectivity or expected
simulation is assumed. This strengthens the old witness with new proofs;
its previous observations and source remain untouched.

Nontrivial mixed/full300maxzero/emptyouter/emptyinner/multipleempty/repeated equal
values and accepted swapped/stale inputs instantiate the generic proof. Equal
values are not runtime nested-reference alias evidence. One actual input carries
allocation128→224→288→320 through processed heads. Exact lim allocation accepts;
one-byte over-limit remains blocked possible Panic. Truncated inner length checks
precede allocation, while allocation precedes a later payload-region failure.
Memory wrong-base reverts and real checked empty REVERT emission stay distinct
from calldata access-time blocking and fuel refusals. Wrong-base/order/truncation
byte inequalities follow positive baselines, never new admission restrictions.

36headline axiom guards and strict per-file/core/control/root diagnostics PASS;
focused and registered import closure PASS1067jobs.70complete ordered vectors
retain all43prior vectors byte-identical. Actual cursor and failure-kind exports
are retained separately; remaining-sequence reencodings are observations of actual
values, not raw input slices or an unknown-memory runtime encoder. No external
native/compiler/EVM agreement added. Initial control syntax/definitional-depth
failure remains raw; repair uses proved cursor measurements, not depth/heartbeat/
fuel/node/time increases. Independent source finder/skeptic found no proof defect;
final artifact reviews/checksums are recorded with the export.

Every original queue remains G40/G41partial; G42.01/.02/.03/.05blocked;
G42.04/.06partial; BackfillA/Bpartial. Canonical uint[][] readback is proved;
all-profile native/runtime ABI emission/decoding/dispatch, CALL/RETURNDATA,
arbitrary callee/callback/library/world/physical resource composition and mandatory
whole-lane validation remain open. No full source-lowering/native/byte-memory
relation, runtime nested heap or parent closure follows. Mainalone lacks9private
V12 inputs7881cb3a; checks use the exact combined tree. Original goal blocked and
untouched, not reactivated/completed. Prior178entries/15seals remain immutable.
Raw docs1/frozen86versus83 comparison1 and Suite124/181.061s, full1/5038.87s,
cold124/5400.579s stay failed; no unchanged failed heavy retry. Complete prior/
publication finding equality is separate. No reserved producer/pin/profile/
fixture/Panic-control change, push/merge/PR or new peer transfer. G03 proposal:
attach these named canonical nested G40/G41/BackfillA consequences, close no parent.

NEW evidence: `/workspace/scratch/v13-outer-64e37675-evidence`.
NEW artifacts: `/workspace/scratch/v13-outer-64e37675-artifacts`.


## Canonical byte-string readback checkpoint (parentd8523c15, 2026-11-01)

NEW owned `Solidity/Backend/AbiWorld/BytesReadback.lean` proves generic actual
Shape.bytes/Val.bytes readback, not another uint-array codec. Existing
ErrorRoundtrip/CanonicalReadback word readback and ErrorLayout padding length/
payload laws are reused. New bytes_prefix generalizes actual bytesAt extraction
under arbitrary prefix/suffix; rounded_formula links the original roundUp to
existing pad32. Val.enc/encodeArgs remain the only codec; no new loader or allocator.

mdec_bytes consumes actual length-word/payload bytes, arbitrary following bytes,
ORIGINAL free+(cursor+(roundUp(length)+32))≤lim and positive decoder fuel. It
proves exact Val.bytes and the rounded allocation cursor. The second allocation
roundUp is discharged using existing roundUp_words. Length/W/lim bounds follow
from the actual rounded allocation, not len<W alone. Generic canonical input
retains arbitrary four-byte selector/trailing bytes; encoded length64+roundUp(n),
exact payload and all padded zeros are proved. Fuel2 suffices for original top
melem/eager/entry recursion, fuel1 for mdec. This is NOT a size-independent CPU/
gas/resource bound; bytesAt still traverses bytes and no proof budget changes.

roundtrip derives actual typed memory/calldata verdicts, both full body byte
observations and published lazy cval with its one-step fuel difference. Actual
input-size≤lim supports eager_cref/cval agreement. Helpers without that size
premise concern the existing intrinsic natural-address decoder/reference checks,
not universal Source admission. Canonical allocation conditions suffice for the
eager/body route, not necessary conditions for all noncanonical/lazy/readsOnly
inputs. No accepted-input predicate, profile, decoder/default or refusal changed.

NEW `tests/v13-abi-world/BytesEntryControls.lean` instantiates the generic proof
for empty/zero/255/mixed and31/32/33bytes. Actual rounded cursors32/64/64/96 and
exact padded payloads/zeros are retained. Exact lim allocation accepts; one-byte
over-limit remains possible Panic BLOCKED. The strengthened incomplete-header
control hasfree=lim-31: even minimum32byteallocation would fail, but actual entry
reverts first. Valid header plus truncated payload distinguishes allocation-before-
region failure. Actual wrong-offset/missing-header/payload entry reverts are proved; the
certified short-payload failure consumes the real checked empty REVERT adapter
with Fits/stack conditions.

Dirty padding and unpadded inputs remain accepted; body normalization uses the
existing canonical codec and does NOT preserve dirty raw padding. Full255payload
bytes need no per-byte cleanup. Bytes' reference-region checks happen at calldata
entry, so truncation is entry revert, not an invented element access-time failure.
Insufficient allocation on full calldata keeps the original lazy-only refusal;
readsOnly=true run is only intrinsic classification, not permission to encode an
admitted Source body. Fuel remains blocked, not revert. Unchecked zero-extension
is explicitly distinct from valid entry. Equal padded tails[17]/[17,0] have distinct
length words and actual typed values, not assumed padding injectivity.

35headline scoped axiom guards, strict per-file core/control/root diagnostics and
focused/registered import validation PASS1068jobs.117FULL ordered vectors retain
ALL70prior vectors byte-identical;22actual cursor/kind outputs retain10old scalar
observations unchanged. No new external compiler/EVM/native agreement. Raw initial
namespace/simp, finite membership and length-normalization failures remain in NEW
evidence; source repairs changed no heartbeat/depth/fuel/node/time/resource limit.
Independent read-only finder/skeptic source review found no proof defect and checked
the discriminating header control; final artifact reviews are recorded in export.

Every original queue remains G40/G41partial; G42.01/.02/.03/.05blocked;
G42.04/.06partial; BackfillA/Bpartial. Canonical bytes progress is not unknown-
memory encoding or all-profile/runtime/native decoding/dispatch, CALL/RETURNDATA,
arbitrary callee/callback/library/world/physical-resource composition. Mainalone
still lacks9private V12 inputs7881cb3a; exact combined validation remains explicit.
No O1 declared-return/same-invocation/static-frame law is supplied or assumed;
its sealed proposal remains untouched and with its original owners. Original goal
blocked and unchanged, no automatic reactivation/completion. All prior seals
including O1triage are preserved. Raw docs1/frozen86versus83 comparison1 and
Suite124/181.061s,full1/5038.87s,cold124/5400.579s stay failed; no unchanged failed
heavy retry. Complete publication/prior finding equality is separate. No reserved
producer/pin/profile/fixture/Panic-control change, push/merge/PR or peer transfer.
G03 proposal only attaches named canonical bytes G40/G41/BackfillA facts, closes
no parent/global ledger. NEW evidence/artifacts:
`/workspace/scratch/v13-bytes-d8523c15-evidence` and
`/workspace/scratch/v13-bytes-d8523c15-artifacts`.


## 2026-11-01 canonical heterogeneous and two-array entry recovery (c498a0f6)

NEW `Solidity/Backend/AbiWorld/TupleReadback.lean` consumes the EXISTING indexed
AbiEntry codec, array mdec_tail, full-word loader and actual enter/bodyValues.
array_window/scalar_window/reference_window have real byte/load/range premises;
mixed_reads/pair_reads discharge these from actual encodeArgs, never a desired
decoder/verdict premise. mixed_entry and mixed_locations prove actual [uint[],uint]
entry/body identity; reverse_entry proves actual [uint,uint[]] identity. pair_entry
proves actual [uint[],uint[]] entry/body identity for all FOUR memory/calldata
combinations. Dependent Vals and Entries preserve exact order/full unsigned words.

The complete second offset is the real first payload length plus64, not a fixed
constant. pair_reads bounds it from full input size≤lim, not len<W. Selector is
arbitrary with length4; suffix is arbitrary. Allocation is explicitly original
free+cost(xs)+cost(ys)≤lim, cost=32+32*length. Exact entry cursor is spent(left,xs)+
spent(right,ys), with calldata spending0. Original fuel max(lengths)+4 suffices:
enter REUSES that fuel for each parameter, not a new sum or CPU/gas bound. Mixed
fuel length+4 suffices. Scalar consumes no allocation. Neither theorem changes
admission, defaults, noncanonical/lazy behavior, decoder semantics or budgets.

IMPORTANT: actual bodyValues copies each calldata parameter eagerly from cursor0;
this is NOT a new sequential body allocator. The summed allocation premise is
sufficient, not necessary for all lazy combinations. A real calldata-only run at
free=lim-96 for two length2 arrays discriminates this from memory entry needing192.
Actual entry cursors MM192,MC96,CM96,CC0 are retained. Body identity is actual indexed
value identity, not merely encoded equality. No assertion that decoder allocations
alias; equal-value inputs need no disjointness premise. Existing compiled shared/
distinct-reference observations and all prior packets remain intact in the exports.

NEW `tests/v13-abi-world/TupleEntryControls.lean` applies the generic proofs to
empty, distinct/equal, reversed,300/max/zero full-word values, different selectors/
suffixes and exact-limit cases. Stale/swapped packets have positive accepted
baselines for THEIR values before negative byte equalities. One-over allocation
is Panic blocked, insufficient fuel is fuel blocked, malformed second offset/head/
tail reverts. Actual first allocation precedes the invalid second offset; actual
second allocation precedes its truncated payload. No wrong-byte equality is
misreported as a decoder failure. Complete ordered observations are exported.

Independent preliminary read-only finder and skeptic source reviews found no
mathematical issue and highlighted the entry-versus-body allocation distinction;
it is documented here and checked by lazy_capacity. Final source/artifact reviews,
actual command exits, axiom sets and exact dependency bindings are in the NEW seal.
No source/native/compiler/EVM agreement or runtime memory-reading byte encoder is
claimed by this canonical intrinsic roundtrip. Mainalone still lacks the exact9
private V12 sources7881cb3a; combined-tree validation is development evidence only.

ALL original queues remain: G40partial,G41partial,G42.01/.02/.03/.05blocked,
G42.04/.06partial,BackfillA/Bpartial. Unknown-memory encoding, full native/runtime
ABI decoding/dispatch, CALL/RETURNDATA, O1 declared-demand/raw same-invocation/static
Frame, arbitrary callees/callback/library/world/physical resources and final
mandatory whole-lane gates remain OPEN. O1 sealed proposal is not adopted or a
passing premise. Goal remains blocked unchanged; this recovery does not reactivate
it. All earlier seals,117ordered vectors and22scalar observations are preserved.
Raw docs1/frozen86vs83,Suite124/181.061s,full1/5038.87s,cold124/5400.579s remain
FAILURES, not retried unchanged. Complete prior/publication finding equality is
separate. No reserved edits, pushes/merges/PRs, new peer inputs, profile/pin/fixture/
Panic-control changes, axioms or budget increases. G03 feature reconciliation is
proposed only: G40/G41 canonical multi-parameter readback preparation, not closure.

Final recovery evidence: strict core/control/root per-file diagnostics PASS;
registered import closure PASS1069jobs; scoped26standard-only axiom guards PASS;
134FULL ordered byte vectors preserve all117prior,29scalar observations preserve
all22prior. Lean4.24.0/Lake5.0.0-src+797c613; actual KeySort output “Build completed
successfully (2 jobs).” RUNTIME_GATE_PASS applies to this measured runtime only.
Hard12GiB/swap0, cgroup peak1973567488bytes, no OOM events. Independent final
finder/skeptic SOURCE reviews PASS/no findings; final committed-artifact reviews
remain separately recorded in the export. Early proof/parser errors and a writer-
lock refusal are retained, with corrected final diagnostics; no budgets changed.


## 2026-11-02 compositional entry and bytes/uint-array readback

NEW `Solidity/Backend/AbiWorld/EntryComposition.lean` defines typed appendEntries
using the existing indexed Entries recursor. heads_append and UNCONDITIONAL
enter_append prove arbitrary parameter-list concatenation with exact pos+headsOf
prefix and actual reached allocation cursor. The SAME original fuel argument is
used on prefix and tail, just as enter reuses it for every parameter; no remaining-
fuel consumption relation or CPU/gas bound is claimed. prefix_failure/tail_failure
preserve actual ordered failures. This law composes enter, NOT entry's global head
check or arbitrary body validation. encoded_dynamic_pair/layout_reads derive the
actual dynamic head64, second offset64+first real payload length and exact byte
windows through the EXISTING assemble/Val.enc/encodeArgs codec. No second codec.

NEW `Solidity/Backend/AbiWorld/BytesArrayReadback.lean` proves actual [bytes,uint[]]
and [uint[],bytes] entry/body indexed identity for all FOUR memory/calldata
combinations in EACH order. Both clients CONSUME enter_append and discharge the
actual byte/window/mdec/cref facts, not a desired successful decoder/verdict premise.
bytes_window reuses BytesReadback.mdec_bytes and the real rounded allocation;
array_window/reference_window reuse TupleReadback/CanonicalReadback unchanged.

Selectors are arbitrary length4, suffix arbitrary. Complete actual input size≤lim
bounds natural offsets below W; len<W alone is never used as an offset bound.
Original free+costBytes+costArray≤lim is an explicit SUFFICIENT allocation condition,
not an admission restriction. costBytes=roundUp(bytes.length)+32, costArray=32+32*n.
Fuel n+4 suffices for the actual recursion, dominating bytes' two steps, unchanged
across params. No ByteRange premise on uint elements;300/max/zero remain full words.
Exact entry cursor follows argument order, spentBytes+spentArray or reverse;
calldata spends0 at entry. Published bodyValues separately copies each calldata
argument eagerly from cursor0; this does not define a sequential body allocator.

NEW `tests/v13-abi-world/BytesArrayControls.lean` instantiates both generic theorems
for empty,31/32/33bytes, unequal96byte/64array costs and full-word arrays. Actual
second heads160 versus128 and refs100/196 versus100/164 discriminate order. Actual
entry cursors160/96/64/0, exact lim success/one-over Panic, malformed second offsets,
missing/short heads/tails, first allocation before invalid second offset and second
allocation before short byte payload are checked. Short header reverts BEFORE even
minimum allocation would fail. Calldata entry at zero fuel can pass while body
classification remains fuel blocked. Weaker calldata capacity remains a run while
one-byte-tighter eager copy keeps the original lazy-only refusal. Complete padded
zeros are retained. Wrong-byte claims have positive canonical/reverse baselines;
byte equality is not typed alias identity or a classified failure.

triple_observed is a FINITE actual three-parameter body-byte observation and head
loads96/192/42 through existing decoder/codec, not generic typed triple identity or
compiler coverage. Generic arbitrary-list composition remains the enter equality.
All160FULL ordered vectors preserve ALL134prior (including prior117) byte-identical;
47scalar observations preserve ALL29prior (including prior22). Scoped29 actual
standard-only axiom guards pass. No new external compiler/EVM/native pipelines.

Independent read-only source finder/skeptic PASS; fuel-comment precision finding
closed without proof/budget changes. Final command/axiom/observation/resource and
committed-artifact review evidence is in the NEW checkpoint export. Failed local
syntax/namespace/proof/depth attempts are retained; explicit codec rewriting fixes
the depth failure with NO raised heartbeat/depth/fuel/node/time/resource limit.

Parallel ownership: O1 owns its primitive declared-demand consumer; V15/V16/V17
keep their distinct leaves. This canonical input work supplies NO raw-return byte/
declared-return metadata/same-invocation/static-frame law. The prior sealed O1
proposal stays intact and unadopted. A small current local-availability handoff
records real source types/hashes and the precise missing producer contract; it
must not substitute selector-bearing entry decoding for raw RETURNDATA validation.
The existing human model-repair approval is acknowledged, not requested again.

ALL original queues remain G40partial,G41partial,G42.01/.02/.03/.05blocked,
G42.04/.06partial,BackfillA/Bpartial. Unknown-memory runtime encoder, all-profile
source/native/runtime decoding/selector/receive/fallback compilation, CALL/RETURNDATA,
arbitrary callees/callback/library/world/physical resources and mandatory final
whole-lane checks remain OPEN. Mainalone lacks the exact9 private V12 inputs7881cb3a;
passing combined-tree development checks do not establish publication/standalone
closure. No claim that all independently ready backfill is exhausted. Goal remains
blocked unchanged; recovery is not reactivation/completion. All earlier seals,
Panic approval/controls, profiles/pins/verdicts/refusals/fixtures/budgets preserved.
Raw docs1/frozen86vs83,Suite124/181.061s,full1/5038.87s,cold124/5400.579s remain
FAILURES, not unchanged heavy retries. Complete prior/publication finding equality
is separate. Only proposed G03 reconciliation: G40/G41 compositional canonical
readback preparation, never parent closure; generated ledgers remain untouched.

Final recovery checks: strict per-file composition/bytes-array/control/root MCP
PASS; focused guarded modules and registered import closure PASS1071jobs; final
controls and full signatures/observations/29scoped standard axioms PASS. Static
import/layer/orphan/trust/whitespace PASS. Lean4.24.0/Lake5.0.0-src+797c613 and
actual KeySort “Build completed successfully (2 jobs).” RUNTIME_GATE_PASS only for
this runtime check. Hard12GiB/no swap, peak2103234560bytes and no OOM. Independent
source/owning-roadmap finder and skeptic PASS; comment precision finding CLOSED.
All245prior checksum entries/19manifests verify, untouched. Final committed-artifact
reviews/seals and the narrow caller-phase availability packet are in the export.


## 2026-11-02 actual body composition and generic typed triple readback

NEW `Solidity/Backend/AbiWorld/BodyComposition.lean` proves UNCONDITIONAL
body_append over actual bodyValues and arbitrary indexed Param/Entries lists.
appendValues reuses existing ArrayPairPacket.append, transporting ONLY the index
along List.map_append; no new value representation, decoder or evaluator. The
transport_cons/appendValues_cons facts preserve actual value order and contents.
Tail body starts at pos+headsOf prefix, with SAME input/original fuel. All actual
.val/.ref/eager fuel/nonfuel/cvalRef/readsOnly success/refusal String branches are
preserved in order. body_success/body_prefix_failure/body_tail_failure are direct
consequences. This is recursion equality, not proof of arbitrary body admission,
entry-origin, source/native/target simulation, physical allocation or remaining-
fuel consumption. Existing body copies each calldata parameter from cursor0.

NEW `Solidity/Backend/AbiWorld/TripleReadback.lean` CONSUMES enter_append and
body_success to prove generic actual [bytes,uint[],uint256] typed entry/body/
verdict identity for all FOUR bytes/array memory/calldata combinations; scalar
is the original value location. No successful entry/body is an assumed premise.
Existing byte/array/scalar windows discharge actual prefix and tail successes.
The REAL three-word codec head96, second offset96+actual bytes payload length
and full scalar word are derived through existing Vals.parts/assemble/encodeArgs,
not reused from the old two-head64 layout or supplied as desired bytes.

Explicit auxiliary sufficient bounds: arbitrary selector length4/suffix; actual
complete input.size≤lim; original free+costBytes+costArray≤lim; array.length+4≤f.
Natural offsets/ranges follow complete encoded input/allocation bounds, not len<W.
Full uint300/max/zero values retain all32bytes with no ByteRange restriction.
Entry cursor is spentBytes+spentArray, scalar allocates0; each calldata body eager
copy separately starts0 as the existing definition specifies. These sufficient
canonical bounds do NOT redefine admission/profile/default fuel or change lazy/
noncanonical refusals. calldata_entry proves actual all-calldata entry with only
original fuel≥2 (for scalar) and size/selector bounds, WITHOUT memory-copy capacity
or array body fuel. bytes_prefix derives actual typed prefix success independently
of a later array fuel failure. Neither weaker lemma assumes whole-body acceptance.

NEW `tests/v13-abi-world/BodyTripleControls.lean` strengthens EXACT retained
BytesArrayControls.triple input/values to typed entry/body identity via old_input,
old_values and generic roundtrip; old finite observation and all old sources stay
unchanged. Empty,31/32/33/full-word/different selector/suffix/all4location clients
have actual typed witnesses. Unequal96/64costs give refs132/228, heads96/192/42,
entrycursors160/96/64/0. Exact allocation limit accepts; one-byte-over and an actual
wrong second cursor96→97 Panic are distinguished. Positive correct cursor/head
baselines precede wrong-cursor/head/offset and malformed/globalhead/header/tail
negatives. Prefix allocation precedes invalid later offset; short header reverts
before even minimum allocation could succeed. No wrong byte equality is called
a classified decoder failure, and no symbolic word-cell/physical-byte equivalence.

Most critically, calldata_origins supplies actual typed entries at fuel2 for
BOTH body failure controls. With adequate bytes capacity the actual bytes prefix
succeeds and independently failing array tail fuel propagates via body_tail_failure.
With tight capacity, first bytes' eager Panic followed by original lazy-only refusal
precedes that independently failing tail fuel via body_prefix_failure. Same input,
fuel and actual entered references retained. These are body String classifications,
not callee catch/revert or world rollback. Wrong tail head position64 versus correct32
is checked on the same retained references. No invented well-typed frame is counted
as an entry witness. The generic body law is arbitrary-list; successful typed triple
admission covers this declared family, not all aggregates or native code.

All176FULL ordered vectors preserve ALL160prior byte-identical;64scalar observations
preserve ALL47prior. Scoped29actual standard-only axiom guards. No new external
compiler/EVM/native pipelines. Failed early simplifier depth and codec heartbeat
attempts are retained; shallow equations/explicit codec parts repair them without
ANY budget increase. Initial export failed only for three UInt8 binder annotations;
raw exit/source retained separately, corrected changed export passes. Independent
read-only source finder/skeptic PASS; byte-unit comment finding CLOSED, proof unchanged.

Original queues remain G40partial,G41partial,G42.01/.02/.03/.05blocked,G42.04/.06partial,
BackfillA/Bpartial. Arbitrary signature admission/emitted unknown-memory encoder,
source/native/runtime selector/receive/fallback, CALL/RETURNDATA, arbitrary callee/
callback/library/world/physical-resource and mandatory final closure remain OPEN.
O1 retains its primitive declared-demand consumer; Source/raw same-invocation/static
Frame producer remains missing locally. Prior caller packet is missing-contract
triage with old proposal UNADOPTED, untouched; no new semantic choice or approval
request. Approved local Panic controls/profile/pins/fixtures/verdicts/fuel/proof/node/
process budgets unchanged. Mainalone still lacks exact9private V12 inputs7881cb3a;
combined checks are development evidence, not standalone/publication. Goal blocked
unchanged, no administration/reactivation/completion. Ready work is not declared
exhausted. Raw docs1/frozen86vs83 and Suite124/181.061s/full1/5038.87s/cold124/5400.579s
remain FAILURES, not repeated unchanged; prior/publication complete finding equality
is separate. Only G03 reconciliation proposal: G40/G41/BackfillA compositional typed
readback preparation, not parent closure. No reserved edits, push/merge/PR/new peer.

Final recovery evidence: strict per-file body/triple/control/root diagnostics PASS;
focused guarded modules/controls and registered changed closure PASS1073jobs;
176FULL vectors/64scalars preserve160/47prior;29standard-only actual scoped axiom
guards PASS. Static import/layer/orphan/trust/whitespace PASS; raw docs1 and frozen
comparison1 remain failed, complete prior/publication finding equality0 separately.
Lean4.24.0/Lake5.0.0-src+797c613; actual KeySort “Build completed successfully (2 jobs).”
RUNTIME_GATE_PASS only for runtime. Hard12GiB/swap0, peak2077908992bytes/no OOM.
All270prior entries/21immutable manifests verify, including unchanged caller packet.
Independent source and owning-roadmap finder/skeptic PASS, byte-unit comment finding
CLOSED with proof unchanged. Final committed-artifact/seal reviews are in the NEW
immutable export. No whole-lane, native/runtime/world or automatic-goal completion.


## 2026-11-02 uniform canonical word-list and actual aggregate constructors

The exact initial/current inventory and dependent remaining signatures are in the
NEW export's constructor-inventory.json. Existing canonical readback covered uint
words, bytes, uint[] and uint[][] plus isolated mixed families; unconditional
enter_append/body_append alone did not prove successful arbitrary list admission.
Actual Shape constructors remain word/bytes/array/fixed/tuple, with Param value/
memory/calldata and readsOnly behavior unchanged. No scope/exclusion is changed.

NEW `Solidity/Backend/AbiWorld/WordListReadback.lean` proves uniform canonical
successful readback by typed induction over ARBITRARY existing Param/Vals lists
whose shapes are validated words. WordShapes is an auxiliary SUFFICIENT constructor
condition, NOT an admitted source/profile predicate or rejection of other shapes.
All existing Kind.valid cases/Word.lt/Word.valid are used, including nominal enum
cardinality, signed and fixed-byte cleanup; no uint8proxy, ByteRange or new AST.
go_static/assemble_static/parts_static/encoded_cons derive actual encodeArgs heads
from the existing assemble.go/parts recursion, not a supplied desired packet.
encoded_length/heads_words derive exact32*N extent. window constructs ACTUAL Entries
from canonical arbitrary prefix/suffix bytes, exact head position, original fuel2
and unchanged incoming allocation cursor, consuming enter_append/body_success.
roundtrip then proves actual entry/body/verdict typed identity, no assumed success.
Complete input-size≤lim yields actual4+headsOf≤lim, not a len<W shortcut. Each parameter
reuses the SAME original fuel; this is not constant CPU/gas/resource cost. Existing
intrinsic locations/readsOnly covered; no new Source location profile is admitted.

NEW `Solidity/Backend/AbiWorld/StaticAggregateReadback.lean` then continues ready
constructor work. members proves ACTUAL mmembers for arbitrary heterogeneous
validated-word Vals: original consumed member fuelN+2 and cursor unchanged.
mdec_tuple proves actual Shape.tuple decoding, region check, allocationN*32 and
original fuelN+3; tuple_roundtrip adds memory/calldata entry/body typed tuple identity
at top fuelN+4 and published eager_cref lazy agreement at fuel-1 under actual size
bound. Flat parameter bytes equal these tuple bytes, but typed shapes/costs differ:
flatwordlist allocates0; tuple allocates32*N. No type/heap/alias equivalence inferred.

sequence proves ACTUAL mseq for arbitrary indexed Seq(.word k)n. mdec_fixed uses
real fixed codec/header/count/region/allocatorN*32 and original fuelN+3, with explicit
pre.length+31<input.size EVENn=0, preserving the published guard. mdec_word_array
uses actual count header, count/word bounds derived from allocatorN*32+32, exact
sequence/cursor and original fuelN+3, for ANY existing validated word kind rather
than uint256 only. Fixed/dynamic-word-array results are mdec FRAGMENTS, not generic
entry/body/lazy admission for all these constructors. Source nested-enum/aggregate
type mapping is NOT proved. No reserved decoder/slice/source semantics changed.

NEW `tests/v13-abi-world/UniformWordControls.lean` supplies an inhabited arbitrary-
length repeat client over actual Param/Vals and full max words, heterogeneous
uint8/bool/enumBelow3/int8/fixedBytes32/uint256 values, all intrinsic locations and
mixed-location/readsOnly controls. Actual typed tuple entry/body/cval, fixed and
word-array mdec consume the generic theorems. All condition premises are discharged
in nonempty finite applications. Signed/max/full300 values retain ALL32bytes.
Nominal enum3 rejection is distinguished from uint8 validity of3. Wrong highword,
truncation, wrong-offset and wrong-cursor cases have positive baselines. Tuple
allocation before invalid member and fixed allocation before short payload preserve
actual failure priority. Exact lim succeeds; one-byte-over Panic stays distinct.
Calldata invalid cleanup remains access-time BLOCKED versus eager entry REVERT.

Intrinsic empty controls do NOT admit empty Source aggregates: empty flat enter
allocates nothing even above memorylim; empty tuple executes real alloc0 and can
Panic; empty fixed still needs its original32byteheader lookahead. Positive fixed0
with suffix32 and short-header negative preserve that exact guard. No new human
semantic choice, default or premise weakening. Generic constructor conditions are
sufficient; remaining shapes and lazy/noncanonical cases retain original behavior.

All203FULL ordered vectors preserve ALL176prior byte-identical;87scalar observations
preserve ALL64prior.43actual scoped standard-only axiom guards. No new external
compiler/EVM/native agreement. Source finder/skeptic PASS/no findings. Actual raw
iteration failures retained; no heartbeat/depth/node/fuel/test/resource increases.
Finite invalid-kind fixtures are representative, not exhaustive per-kind testing.

Remaining OWNED proofs are explicit: uniform mixed dynamic parameter lists require
actual assemble.go head/tail offset induction plus recursively DERIVED allocation/
fuel; arbitrary recursive array/fixed/tuple elements require mseq/mmembers/mdec
canonical proofs over existing Seq/Vals. Definitions exist: not a whole-lane excuse,
not discharged by an assumed decoder-success certificate. Current static-word case
is progress toward uniform consumer coverage, not full all-profile closure.

G41 runtime encoding gap stays OPEN: PacketEmission.emitResult specializes bytes
from already supplied Vals; ReturnedBytes observes represented cells; Failure.Slice
only supports fixed literal PUSH/MSTORE8/RETURN/REVERT. None reads unknown runtime
memory or proves arbitrary CALL/RETURNDATA. Do not widen that reserved slice or
rename host codec/observer equality as emitted execution. Actual Source type/value/
codec lowering, raw declared-demand/same-invocation/static Frame, arbitrary callee/
callback/library/world/physical-resource and mandatory final closure remain with
real producers/owners. Prior O1 caller packet/proposal untouched and UNADOPTED.

ALL original queues remain G40partial,G41partial,G42.01/.02/.03/.05blocked,
G42.04/.06partial,BackfillA/Bpartial. No Source/native/compiler/EVM/profile/target
predicate/observation/pin/fixture/Panic-control change. Mainalone lacks exact9private
V12 inputs7881cb3a; combined checks remain development evidence, not publication.
Goal blocked unchanged; no administration/reactivation/completion. More ready owned
cases remain, not declared exhausted. Raw docs1/frozen86vs83,Suite124/181.061s,
full1/5038.87s,cold124/5400.579s remain FAILURES, no unchanged heavy retries. Complete
prior/publication finding equality is separate. Only proposed G03 reconciliation:
G40/G41/BackfillA uniform constructor readback preparation, not parent closure.

Final recovery checks: strict per-file uniformword/aggregate/control/root MCP PASS;
focused guarded modules/controls and registered changed closure PASS1075jobs;
203FULL vectors/87scalars preserve176/64prior;43actual standard-only scoped axioms.
Static import/layer/orphan/trust/whitespace PASS. Lean4.24.0/Lake5.0.0-src+797c613,
actual KeySort “Build completed successfully (2 jobs).” RUNTIME_GATE_PASS only for
runtime; hard12GiB/swap0, peak1470836736bytes/no OOM. All292prior entries/22immutable
manifests verify, untouched. Independent source and owning-roadmap finder/skeptic
PASS/no findings; final committed-artifact/seal reviews recorded in NEW export.
No original queue, mandatory failed gate or blocked goal is declared complete.


## Mixed dynamic list and tuple recovery (parent 69f142bf)

`DynamicListReadback` extends canonical readback beyond WordShapes by actual
indexed Param/Vals induction for arbitrary lists of validated words and byte
strings. LeafShapes is an auxiliary sufficient constructor case, not a new
admitted profile or exclusion. `go_word`, `go_bytes`, `head_fold`, `head_length`,
`encoded` and `encoded_length` derive the actual assemble.go heads/tails.
`go_append` advances the suffix offset by the actual ordered prefix tail byte
length; `prefix_noninterference` fixes the starting offset and therefore does
not cover a change to the total number/extent of heads. `tail_aligned` proves
alignment of the actual byte extent, without identifying natural offsets with
modulo word arithmetic. Size bounds, not list length alone, justify loads.

`window` and `roundtrip` derive actual enter/entry/bodyValues/verdict results
from those real byte windows, with arbitrary selector of length four, suffix,
free pointer, existing locations/readsOnly and validated full-word kinds. The
actual location-dependent `spent` cursor omits calldata entry allocations; the
sufficient allocation bound includes all dynamic bytes for eager body copies.
Original parameter recursion reuses fuel f with sufficient f>=2, not constant
CPU/gas. No desired decoder result, body-success oracle or simulation premise
is assumed. Existing enter_append/body composition are reused unchanged.

`DynamicAggregateReadback.members_window` and `mdec_tuple` consume the actual
recursive Shape.tuple constructor on arbitrary word/bytes members. The outer
allocation is members.length*32 in addition to the real byte-object tails;
mmembers consumes original fuel N+2, mdec N+3 and top entry N+4. Tuple-relative
offsets use the real tuple base. `tuple_roundtrip` proves actual memory/calldata
entry and typed body/verdict identity for a genuinely dynamic tuple, using
published eager_cref. Static tuples retain the earlier consumer. This advances
a recursive constructor, not arbitrary recursive nesting or fixed/array bytes.

New controls include an inhabited arbitrary-length byte/word client, full max
uint values, nominal enum, two distinct byte strings and actual dynamic tuple;
empty/zero/255 and31/32/33 boundaries; exact/one-over allocation and nonzero
incoming cursor; wrong offsets/relative base/typed shape, truncation, fuel
before validation, allocation before short payload, and accepted unpadded bytes.
An initial control normalization exceeded the original recursion limit; the
repair rewrites only a proved numeric cost instead of unfolding typed values.
No limit was raised; raw diagnostics/build errors are retained.

Remaining ready owned proofs: extend LeafShapes to genuine recursive aggregate
values with derived per-shape cost/fuel, actual Seq mseq and nested mmembers
canonical readback; fixed/array dynamic bytes remain unproved. The actual
definitions exist. A whole upstream lane is not the blocker for these leaves.
G40/G41/BackfillA progress is intrinsic canonical preparation only. Existing
noncanonical/lazy/refusal/failure order and all profiles remain unchanged.
Unknown-memory runtime encoding, all-profile Source/native/compiler dispatch,
CALL/RETURNDATA, O1 declared-demand/raw same-invocation/static-frame and arbitrary
callee/callback/library/world/physical-resource producers remain open/reserved.
PacketEmission, ReturnedBytes and Failure.Slice are not widened or counted as
runtime memory reading. Every original Work/Backfill item remains partial or
blocked as in the preceding handoff; persistent goal unchanged/blocked.

Validation, complete old/new observations, scoped axioms, exact private-nine
input hashes, independent source/artifact reviews and real failed gates are
recorded in the new immutable recovery export. Historical docs/frozen, Suite,
full/cold and initial body export failures remain failures; complete prior and
publication documentation multiset equality is a separate check. No push,
merge, PR, new peer input or goal administration. Proposed G03 reconciliation
only: G40/G41/BackfillA mixed canonical constructor progress, no parent closure.

Independent source finder/skeptic found no proof defect. Their two precision
findings were fixed: spent is explicitly allocation-correct only for LeafShapes;
take210 is accurately a second length-header truncation. A new take240 payload
truncation and free=lim-100 control distinguish successful first allocation,
second allocation Panic before short payload, and second header REVERT before
that second allocation. Original expectations and budgets are unchanged.

Final recovery validation: strict per-file new list/aggregate/control/root MCP
PASS; focused modules/controls and registered changed import closure PASS1077
jobs.242complete ordered vectors/103scalars preserve all203/87prior unchanged;
76actual scoped standard-only axiom sets. No new owned proof/control warnings.
Static imports/layers/orphans/trust/whitespace PASS; docs raw1/current86 versus
frozen83comparison1 remain FAIL. Complete prior/publication finding-multiset
equality separately PASS. Historical Suite124/181.061s,full1/5038.87s,
cold124/5400.579s and initialbodyexport1 retained; no unchangedfailed heavy retry.
Lean4.24.0/Lake5.0.0-src+797c613; actual KeySort2jobs PASS before
RUNTIME_GATE_PASS(runtime only). Hard12GiB/swap0, observed peak3325009920bytes,
OOM0, original serial-j1/thread1/cache.316prior entries/23seals verified
immutable. Independent finder/skeptic source/roadmap review PASS after the two
precision fixes; final committed artifact/seal reviews recorded separately.
No whole-lane/goal closure, source/native/EVM/runtime encoding claim or
ready-work-exhaustion claim. All original queues remain explicitly open.


## Byte sequence and fixed/array constructor recovery (parent 388ea85d)

`ByteSequenceReadback.sequence_window` proves actual mseq for arbitrary existing
Seq.bytes count, base, nonzero original index and incoming allocation cursor.
The byte windows come from Seq.parts/assemble.go; head offsets, ordered tails
and padded lengths are the existing codec, never desired successful execution.
`go_cons`, `tail_cons`, `head_fold`, `head_length`, `fixed_encoded` and
`fixed_length` derive the actual layout and byte-object extent. The proof
reuses DynamicListReadback.tails_independent and the actual byte decoder window
consumer. Size-derived offset bounds retain natural/modulo distinctions.

`mdec_fixed` and `mdec_array` consume the real fixed/array constructors.
Fixed outer allocation is n*32, dynamic array n*32+32, each plus all actual
rounded byte-object allocations. The dynamic element-head/offset base is AFTER
the count word. Original sufficient fuel is n+2 for mseq, n+3 for mdec and n+4
for top entry; no CPU/gas/default-budget claim. `zero` separately proves n=0
mseq uses no fuel/allocation. Fixed retains its ORIGINAL p+31<size guard even
for n=0, before allocation; empty encoding alone cannot discharge it.

`array_roundtrip` and `fixed_roundtrip` derive actual indexed memory/calldata
enter, entry, bodyValues and verdict.run identity for arbitrary Seq.bytes,
selector length4/suffix/free, exact actual input-size/allocation bounds and
original fuel. Fixed top also retains the zero-count header bound67<inputsize.
A private reusable dynamic-single composition premise is discharged by both
actual constructor proofs; it is not a generic decoder-success certificate.
Published eager_cref is reused unchanged. These are sufficient canonical
consequences, never a new admitted profile, Source constructor mapping or
coverage of arbitrary recursive Shape.

Controls use existing intrinsic Seq constructors: arbitrary list-of-bytes
client; empty and multiple strings including zero/255/31/32/33 bytes; real
array/fixed typed body identity, separate outer allocations320vs288, actual
array count3 and post-length-relative offsets96/128/192; exact free limits and
one-over; nonzero incoming cursor17 and actual sequence fragment base68/index1/
cursor13 yielding173. A shared noncanonical offset is accepted with the exact
different ordered result, not rejected or silently equated to canonical bytes.
Truncated count/head/element-header/payload, invalid offsets/count, allocation
before last short payload versus last header before allocation, and fuel-before-
validation controls retain original order. Empty fixed memory REVERT versus
calldata reference entry, named lazy-only body refusal and readsOnly body
acceptance remain distinct. Intrinsic zero-fixed controls do not extend Source.

Remaining ready owned proofs: actual recursive array/fixed/tuple element
correctness beyond bytes/validated-word leaves, plus arbitrary mixed Param/Vals
containing those recursive shapes with derived cost/fuel/head/tail relations.
No success/simulation premise discharges them. General Source/native/runtime
decoding/dispatch, unknown-memory encoder, CALL/RETURNDATA, declared-demand/raw
same-invocation/static-frame and arbitrary callee/world/physical-resource
producers remain reserved/open. PacketEmission, ReturnedBytes and fixed
Failure.Slice are not widened or relabeled. All original Work/Backfill items
remain partial/blocked; original goal blocked unchanged/no administration.

Actual diagnostics/closure/controls/complete old observations/axioms, raw failed
attempts, full gate outcomes and independent read-only source/artifact reviews
are recorded in the new immutable recovery export. Historical Suite/full/cold/
initialbodyexport/docs/frozen failures remain failures; complete prior and
publication finding equality is a separate gate. No new native/EVM claim,
profile/Panic-control/fixture/pin/budget change, peer input, push/merge/PR or
ready-work-exhaustion claim. G03 reconciliation proposal only: original
G40/G41/BackfillA byte sequence constructor preparation, not parent closure.

Source finder found one documentation coverage mismatch: invalid count was
initially described as truncated count. Added actual take50 count-header
truncation controls, distinguishing header-before-outer-allocation from fuel0;
take20 top-head truncation separately REVERTs before fuel. Full-input fuel6
exhausts while sufficient7 succeeds; calldata reference entry ignores that
fuel but body validation blocks at fuel0. Empty fixed typed identity is proved
with its real extra32-byte suffix/header. No original guard or budget changed.

Final byte-sequence recovery checks: strict per-file sequence/control/root MCP
PASS, focused and registered changed closure PASS1078jobs; raw final controls
and final complete export PASS.300FULLvectors/120scalars preserve all242/103
prior unchanged;108actual scoped standard-only axiom sets. New module/control
has no warnings. Static imports/layers/orphans/trust/whitespace PASS. Raw docs1
and frozen86versus83comparison1 remain FAIL; complete prior/publication finding
multiset equality separatelyPASS. Historical Suite124/181.061s,full1/5038.87s,
cold124/5400.579s, initialbodyexport1 and all prior local failures retained. No
unchanged failed heavy retry. Lean4.24.0/Lake5.0.0-src+797c613; actual KeySort
2jobs before RUNTIME_GATE_PASS(runtime only); hard12GiB/swap0/thread1/-j1, peak
3197374464bytes/OOM0, one original cache.340prior entries/24seals verify
immutable. Independent finder/skeptic source/roadmap PASS after the count-header
coverage fix; committed artifact/first-seal reviews recorded separately. Original
full assignment remains partial and goal blocked unchanged; all ready recursive
Shape/Param proofs and real reserved producer/final gate obligations stay open.


## Recursive nested byte-array and heterogeneous recovery (parent 03029891)

`NestedByteReadback` consumes actual Seq(.array .bytes)n, preserving each
inner Val.array's own dependent count and byte values. `inner_length` derives
that an inner canonical bytes[] encoding has the SAME byte extent as its real
decoder allocation (count+element pointers+rounded byte objects). go_cons,
tail_cons/head_fold/head_length/fixed_encoded/fixed_length derive actual
Seq.parts/assemble.go heads, ordered dynamic tails and exact tailCost.
`element_at` applies the published owned byte-array decoder, whose own inner
head offsets are relative to AFTER its count word. No decoder-success oracle
or second codec/allocator/evaluator is introduced.

`sequence_window` is typed induction over arbitrary actual outer/inner counts,
base/index/cursor and byte windows. Recursively derived sufficient fuelNeed
(nil=0, cons=max(innerCount+4,remainingNeed)+1) matches ORIGINAL mseq fuel
decrements and sufficient inner decoder fuel. It is NOT a raised default,
minimality or CPU/gas assertion. Actual input/prefix extents and allocation
bounds justify offsets/counts/nonwrap; array length<W alone does not.
`mdec_array` and `mdec_fixed` add the actual outer n*32+32 or n*32 allocation;
both need fuelNeed+1. Outer dynamic offsets use the true post-count head base,
each inner array uses its OWN post-count base. Fixed retains p+31<inputsize
even n0, before allocation. `array_roundtrip`/`fixed_roundtrip` derive real
enter/entry/body/verdict for memory and calldata, selectorlen4/arbitrary suffix/
free/actual input+allocator bounds/fuelNeed+2; fixed also retains67<inputsize.
Private conditional single-parameter composition is discharged by the actual
constructor proofs, never counted as general recursive coverage.

`NestedByteListReadback.roundtrip` additionally proves a generic heterogeneous
[nested byte array, validated Word k] client beyond LeafShapes, not another
fixed evaluated fixture. Arbitrary actual nested Seq and full Word.valid/lt
are retained; scalar comes from the SAME actual codec input, no ByteRange
restriction. Real assemble head offset64/marker word, reached allocation and
same original parameter fuel derive through enter_append/body composition.
This does NOT prove arbitrary recursive heterogeneous parameter lists.

Inhabited controls include empty/multiple nested arrays/empty byte strings,
zero/255/31/32/33 payloads; actual typed nested-array512 versus nested-fixed480
allocation and full-word mixed marker; outer/inner offsets96/128/320 and64/96
and32 at distinct post-count bases; exact-limit/oneover, incomingcursor17→529,
actual fragment base68/index1/cursor13→365, and typed empty-fixed with real
32-byte suffix/header. Shared offsets at outer and inner levels are ACCEPTED
with exact DIFFERENT ordered values/cursors672/544, not rejected or silently
equated. Wrong relative base/offset/count, truncated top/count/inner-count/
element-head/byte-header/payload, outer/inner allocation before head-region
validation, last-byte allocation before short payload versus header first,
fuel9 failure versus sufficient10, and lazy-entry/body/readsOnly refusal
controls retain the actual semantics. Intrinsic zero-fixed controls do not
extend admitted Source signatures. None supplies machine/caller-frame origin.

Raw initial failures are retained: wrapper namespace ambiguity produced a
failed focused build before repair; narrower opened names fixed it without
changing limits. The initial combined new-control file timed out at the
UNCHANGED45-second MCP bound (partial=true, not a pass). New uncommitted tests
were partitioned into typed fixtures and focused layout/failure/boundary/alias/
head/fixture modules, preserving ALL expected statements and constants. This
repair adds imports but no budget/trust/semantic shortcut; test speed history
was inspected. Every module gets strict per-file diagnostics, and ONE serial
raw driver checks the ENTIRE set under the original180-second aggregate bound.

Remaining READY owned proofs: arbitrary recursive Shape element/tuple/fixed/
array mseq/mmembers/mdec/melem with derived canonical extents/cost/fuel, and
uniform recursive heterogeneous Param/Vals composition beyond the new generic
two-parameter client. Actual definitions exist, no whole-lane wait excuse and
no future success premise counted discharged. Full Source/native/runtime ABI
decoding/dispatch, unknown-memory read/loop/encoder representation, raw return
demand/same-invocation/static-frame/O1, CALL/RETURNDATA and arbitrary callee/
callback/library/world/physical-resource producers remain reserved/open.
PacketEmission/ReturnedBytes/fixed Failure.Slice are not widened or runtime
encoding. All original Work/Backfill items partial/blocked, persistent goal
blocked unchanged/no administration. Old caller proposal remains unadopted.

Exact complete old/new vectors, actual axiom guards, raw failures, original
resource caps/budgets/cache, import/static/docs gates and independent read-only
source/committed-artifact/seal reviews are recorded in the new immutable export.
Raw docs/frozen comparisons and historical Suite/full/cold/bodyexport failures
remain FAIL; complete prior/publication doc finding equality is separate. No
new native/EVM agreement/profile/Panic-control/fixture/pin/budget change, new
peer input/VM/thread, push/merge/PR or ready-work-exhaustion claim. Proposed G03
reconciliation only: original G40/G41/BackfillA recursive canonical progress.

Final nested-byte recovery validation: strict per-file core/fixture/layout/
failure/boundary/alias/head/case/root/aggregate MCP PASS, focused and registered
changed closure PASS1080jobs. Entire final guarded control set passes ONE
original180-second serial gate in75.325s; final367FULLvectors/141scalars
preserve all300/120prior and initial export unchanged,143actual scoped
standard-only axiom records. New core/control warnings0. Initialcombined
45sMCPpartialtimeout and initial focusedbuild1 remain FAIL with raw source/logs;
partition repair preserves expectations and all limits. Static imports/layers/
orphans/trust/whitespace PASS. Rawdocs1/frozen86vs83comparison1 FAILretained;
complete prior/publication finding-multiset equality separatelyPASS. Historical
Suite124/181.061s,full1/5038.87s,cold124/5400.579s and initialbodyexport1 remain
FAIL; no unchanged failed heavy retry. Actual Lean4.24.0/Lake5.0.0-src+797c613
and KeySort2jobs before RUNTIME_GATE_PASS(runtimeonly). Hard12GiB/swap0/
thread1/-j1/cache unchanged, cgrouppeak6522720256bytes/OOM0.364prior entries/
25seals reverified immutable. Independent source/roadmap finder/skeptic PASS;
committed artifact/firstseal reviews recorded separately. Whole original
assignment partial/goalblocked unchanged; ready arbitrary recursive and
heterogeneous-list proofs plus real Source/runtime/world/final gates remain.


## Recursive canonical constructor composition (da17b201)

`RecursiveLayout`, `RecursiveReadback` and `RecursiveEntry` derive allocation and sufficient original fuel from actual intrinsic values, separately from encoded extent. The mutual value/element/sequence/members laws prove actual mdec/melem/mseq/mmembers readback for every existing constructor, arbitrary sequence index and member position. Static tuple/fixed heads retain their true variable widths. RecursiveEntry.roundtrip derives actual indexed enter, entry, bodyValues and verdict for arbitrary parameter lists without an assumed successful decoder.

These are sufficient canonical-window facts: at least 32 trailing bytes, actual input size at most lim, free plus full recursive copy allocation at most lim, and value-derived original fuel. The lookahead retains fixed-zero header guards. Full-copy room is conservative for calldata; returned entry cursor uses location-dependent spent. No admission/profile or accepted noncanonical behavior changes. The populated client has array(tuple[uint256,fixed uint256[2],bytes]), differing byte lengths0/33, another nested static fixed array, bytes and bool, and covers every intrinsic Loc. Its array encoded extent480 differs from allocation544; whole packet allocation800, memory cursor800 and calldata cursor192. Negative controls retain truncation, aggregate-allocation-before-missing-header panic, plus separate byte-allocation-before-truncated-payload priority, fuel0 and fixed-zero guards. A draft truncation fixture still contained its required word and was corrected; original fixtures were untouched. Draft proof-depth/export errors are retained without raised limits. A changed top offset64 is actually accepted in this intrinsic representation; its raw observation is not relabeled a refusal.

Independent read-only finder/skeptic reviews found no circular decoder-success premise. Final source/artifact results are recorded in the fresh handoff. Every G40/G41/G42 and Backfill remains partial/blocked: canonical kernel readback does not prove runtime unknown-memory encoding, Source/native agreement, CALL/RETURNDATA, arbitrary world/callback or physical-resource simulation. Private combined evidence still uses exact9 read-only V12 inputs7881cb3a; standalone closure is pending. Historical Suite124/full1/cold124/docs1/frozen86vs83 remain failures; complete prior/publication finding equality is separate.

Validation: per-file recursive sources and controls PASS; one bounded control aggregate6.174s PASS; registered PRIVATE closure1083jobs PASS; complete379vectors/156scalars preserve all367/141; scoped162standard-only axiom records preserve all143. Actual nonzero-index recursive sequence cursor544/561 and shared-offset cursor608 are finite intrinsic evaluation controls. Runtime Lean4.24.0/Lake5.0.0-src+797c613 and KeySort2jobs PASS under12GiB/no-swap. Raw documentation and frozen comparison remain FAIL; complete prior/publication finding equality PASS separately. All original queues and the blocked persistent goal remain unresolved in their full scope.


## Location-sensitive sufficient allocation bound (420fbcc5 recovery)

New owned LocationPeak preserves RecursiveEntry unchanged. Its recurrence is max(allocation v, retained(p,v)+peak tail), with retained0 for calldata and allocation v otherwise. The actual indexed window/roundtrip proofs derive head decoding, eager body readback at zero, original same-f recursion, exact spent cursor, Entries/body/verdict identity and all guards from existing codec windows. peak_le_sum and room_of_sum prove every original full-copy sufficient condition implies the new one; spent_le_peak relates exact retained cost. This is a sufficient bound, not a minimal physical-memory cost or new admission predicate: the proof also budgets an auxiliary head copy above incoming cursor for calldata. Actual enter uses cref without allocating; body eager copies start at zero. A switched-order actual success outside the new bound explicitly prevents treating it as necessary.

Inhabited repeated-calldata and mixed calldata/memory/value clients have peak96 versus copy sum192, retained cursors0/96, and typed entry/body/run at free=lim−96; old room is provably false. One byte over distinguishes successful calldata entry from eager/body allocation failure, versus actual mixed entry allocation failure. Nonzero initial cursor17 reaches113. The recursive nested client has peak544 versus oldsum800 and retains192 with actual typed identity. Actual intrinsic Loc has only value/memory/calldata, no storage constructor; no storage or Source-valid mapping is invented. Trailing32, actual size/nonwrap, original sufficient fuel, lazy/noncanonical/fixed0 behavior and all old observations remain unchanged.

Finder and skeptic source/control reviews PASS, no Lean/server/builds by reviewers. An observation-only joined-driver ambiguity was repaired by fully qualifying old selector/suffix names; original exit1 retained without raised limits. Full source/native/unknown-memory encoder/CALL/RETURNDATA/O1/static-frame/world/resource and mandatory whole-lane gates remain unresolved. All Work1–5 and BackfillsA–B stay partial/blocked; persistent goal remains blocked unchanged. Private exact9V12inputs7881cb3a remain read only; canonical kernel progress is not standalone integration or lane closure. Historical Suite124/full1/cold124/docs1/frozen86vs83 remain failed, publication/prior complete multiset equality separate.


## Indexed recursive sibling-prefix readback (65237160 recovery)

New owned SiblingReadback consumes actual indexed Vals/Param concatenation and existing builder laws; it adds genuine actual recursive decoder and entry/body consequences rather than re-exporting byte assembly identities. Total head extent derives from actual shapes and parts. Exact earlier head/tail windows remain unchanged when later values at those same shapes change; later tail starts at total heads plus actual ordered prefix-tail length. Separate actual mmembers and enter/body readback proofs carry original member/parameter fuel, actual input-size/nonwrap/trailing32 guards and either full prefix allocation or LocationPeak's sufficient bound. Only the earlier prefix is decoded; no later successful admission/execution is assumed. Actual prefix entry's head guard is proved. Generic windows also carry nonzero head position, preceding tail bytes, original allocation cursor and derived offset.

The paired entry statement observes actual entered body values and exact cursor, retaining separate real Entries witnesses; generic raw Entries identity is not claimed. Finite actual entry-reference controls observe the same byte-address/length under later replacement. These are intrinsic calldata positions, not word-memory/world alias preservation. Changing later shape/head extent, prefix values/order or prefix locations is outside the corresponding fixed-index equality, not a new source exclusion. Byte-builder natural offsets alone are not nonwrapping decoded words; decoder applications retain actual input/allocation bounds.

Inhabited earlier tuple/static-fixed/bytes and array-of-tuples/fixed/bytes clients discharge all actual decoder/entry/body premises. Incoming cursor17 yields entered241 versus copy-decoder305, and array-prefix273. Nonzero head position32/offset160/leading bytes32 is discharged; later payloads include empty/31/32/33 cases. Earlier refs remain324/31 or shifted388/31 in finite observations; memory-location change instead retains305 and removes that calldata ref. Changing total head extent changes first offset96→128. Finite malformed/over-allocation later tails preserve prefix readability while full entry fails, without any rollback/world claim. Head-before-fuel priority remains original. A draft fixture size calculation confused encoded192 with allocation224; staged codec extent proofs corrected only new draft expectations to422/614 and retained normalization failures without raising budgets. No original observation changed.

Independent read-only finder/skeptic source and populated-control reviews PASS; actual axiom guards, exact final artifact/seal review and gate evidence accompany the handoff. Original RecursiveEntry and LocationPeak remain unchanged. All original Work1–5/BackfillsA–B remain partial/blocked; canonical kernel facts do not prove Source/native/runtime dispatch, unknown-memory encoding, O1/raw-demand/same-invocation/static-frame, CALL/RETURNDATA/arbitrary world/resources or mandatory full gates. Exact9private V12inputs7881cb3a remain read only; all passes are private combined development evidence. Historical Suite124/full1/cold124/docs1/frozen86vs83 remain failed; prior/publication complete finding equality is separate. Persistent goal remains BLOCKED unchanged, no goal administration or publication.
