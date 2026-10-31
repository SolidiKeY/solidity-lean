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
