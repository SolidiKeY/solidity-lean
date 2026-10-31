# V14 executable consumers and open lane obligations

Batch `solidity-v12-v17-20261031`, lane `v14-payments-bytecode`.
Assigned base: `2fe1f8932f96be15b00df03ba2cde46f64a87758`.
Branch: `codex/solidity-v12-v17-20261031/v14-payments-bytecode`.
Checkout: `/workspace/solidity-lean`.

This checkpoint is independent preparation from backfill A/B. It does not close
G43, G36.03, G44, G45 or the V14 lane. The required serial V11–V13 compiler
prerequisites are not integrated at the assigned base. No worker branch was
fetched, imported or cherry-picked. The checkpoint has no source/machine
simulation premise which is counted as discharged.

The [G01 contracts](roadmap-g01-interfaces.md), [G03 ledger](roadmap-g03-ledger.md),
[G04 restrictions](roadmap-g04-restrictions.md), [G06 boundary](roadmap-g06-evm.md)
and [human decisions](../solidity-scope.md) remain authoritative. The intrinsic
representations, source profile, observations, verdicts, target predicate and
proof budgets are unchanged. All reserved implementations remain read only.

## Published components consumed

The [creation component](backend-creation-artifacts.md) supplies the intrinsic
instruction type, independent byte `fetch`/`effect`/`Exec`, `Prefix`,
`Prefix.exec`, `Placement.exit`, and deterministic exact return/revert bytes.
The [assembler component](backend-assembler.md) supplies `assemble_pushTag`,
`tagIndex`, `asmWidths`, `offset`, `decode_encode` and checked jump destinations.
The new code does not repeat either algorithm or its semantics.

The [world component](contract-world.md) and existing payment world API supply
`World.create`, `World.receiveRun`, `World.stipend`, `sendResult`, `atomic`,
`World.create_ok`, `World.create_installs`, `World.stipend_transfer_failure` and
`payment_atomic_failure`. These are existing unmetered APIs, distinct from the
independent source and pinned EVM semantics. The [stipend rule](stipend-cost-rule.md)
remains unchanged; its `Stipend.Obligation` is not proved here. The
[failure component](backend-failure-emission.md), [hash premises](hash-collision-bound.md)
and [precompile component](precompiles.md) are read-only prerequisites, not
reimplemented or silently treated as parent completion.

## Backfill A: byte-prefix and assembly consumers

[Prefix](../../Solidity/Backend/Executable/Prefix.lean) adds continuation-prefix
transitivity and stack-suffix transport over actual independent byte steps.
`effect_stack_tail` excludes halt steps and requires all CODECOPY operands on
the unextended stack: a protected suffix cannot supply missing operands.
`constructor_segments` composes two actual finite segments with the existing
exact-byte exit wrapper. `returned_excludes_reverted` distinguishes outcomes
even for identical bytes; `reverted_bytes_unique` retains exact failure bytes.

[Assembly](../../Solidity/Backend/Executable/Assembly.lean) composes those
constructor segments with actual base-zero assembly, decoder roundtrip and a
resolved target in the returned runtime bytes. The creation-image offset is
never added to runtime jump addresses. A finite proof about returned bytes
is not account installation, execution of runtime jumps, decoder agreement
with the pinned EVM, or a source constructor correctness proof.

[Prefix controls](../../Solidity/Backend/Executable/PrefixChecks.lean) use the
published nonempty CODECOPY fixture, split into two nonempty segments. They
cover protected one/two-word suffixes, empty/nonempty runtime, nonempty
arguments, return/revert separation, argument-byte contamination rejection
and stack-underflow refusal. [Assembly controls](../../Solidity/Backend/Executable/AssemblyChecks.lean)
prove actual successful assembly of JUMPDEST/PUSH0/JUMP and compose both
constructor segments. A negative distinguishes runtime target 0 from creation
image offset 16. It is a real backward target, not proof of executing a loop.

The prefix preserves the suffix at every continuing step. The terminal runner
observes bytes and exposes no final stack. Arbitrary suffixes carry no
1024-word stack/headroom proof, gas certificate or caller-frame correctness.

## Backfill B: payment checkpoint consumers

[PaymentCheckpoint](../../Solidity/Backend/Executable/PaymentCheckpoint.lean)
proves exact false/error characterizations of the existing send result,
uncaught rollback of a successful effectful prefix, creation-failure-before-send
ordering, retention of a successful create when a subsequent receive failure
is caught, and distinct handles from two actual successful creations at
distinct checked addresses. The first three laws are generic result algebra;
the final three consume actual existing world runs.

[Controls](../../Solidity/Backend/Executable/PaymentCheckpointChecks.lean)
construct an actual empty typed contract, create it, execute a receive with
nonempty literal revert bytes, and create a second distinct instance.
Caught send retains the first account, while uncaught transfer restores the
original outer world with exact recipient bytes. Further controls distinguish
the created account from the input, preserve divergence/exhaustion as errors,
separate nonempty failure bytes from empty revert and reject a colliding create
before the receive. These fixtures do not prove declaration/source lowering,
source inheritance order, stipend adequacy or nonce-derived CREATE addresses.

## Exact theorem premises

All names below are under `Solidity.Backend.Executable`. Headline axiom reports
are guarded in the owned modules and use only standard Lean axioms.

| Theorem | Explicit evidence required |
|---|---|
| `prefix_trans` | Two actual `Creation.Prefix` derivations over the same code, joined at identical stream/stack/memory. |
| `effect_stack_tail` | An actual continuing `Creation.effect` equation on the original operand stack. |
| `prefix_stack_tail` | An actual finite `Creation.Prefix` derivation; no stack-limit claim. |
| `constructor_segments` | Existing arithmetic `Placement`, two actual joined prefixes ending at its wrapper, arbitrary stack suffix. |
| `returned_excludes_reverted` | An actual successful byte `Exec` from the exact same code/stream/stack/memory. |
| `reverted_bytes_unique` | Two actual reverted `Exec` derivations from identical initial inputs. |
| `assembled_constructor_segments` | Actual base-zero successful assembly, `Placement` of its encoded runtime, two actual prefixes and a resolved pushTag item. |
| `send_false_iff` | No simulation premise; exact characterization of an existing supplied result. |
| `send_error_iff` | No simulation premise; exact characterization of an existing supplied result and halt. |
| `prefix_atomic_failure` | Actual supplied prefix success equation and supplied continuation failure equation; outer checkpoint world. |
| `create_send_creation_failure` | Actual failed `World.create` equation, with exact halt. |
| `create_send_caught_prefix` | Actual successful create, installed-recipient admission, failed receive and catchability. |
| `creation_handles_distinct` | Two actual successful creates and distinct checked addresses; no hash/address injectivity assumption. |

## Queue and remaining integration obligations

| Assignment item | Status and exact remaining obligation |
|---|---|
| 1: G43 | Blocked/open. No joint compiled payment/world relation, sender-funds/stipend gas proof, history-dependent strategy agreement, or source-success/machine-revert asymmetry discharge is claimed. The base legacy `Sim.oracle` uses a per-transaction table; the world API is unmetered. `Stipend.Obligation` still requires actual compiled worst-path gas and enforced rejection, not supplied parameters counted as proofs. |
| 2: G36.03 | Deferred by assignment until independent G43 and integrated V12/G37. Prefix algebra here does not prove payment/call-loop finite-prefix or divergence simulation. |
| 3: G44.01 | Open: independent source initializer/inheritance order, argument evaluation/ABI and constructor failure transport through the integrated lowering/compiler chain. |
| 3: G44.02 | Published installation/linking/immutable component reused read only; consumer proofs above return exact runtime bytes. Source/runtime interface, immutable declaration/value identity and full artifact-table composition remain open. |
| 3: G44.03 | Open: source new/try-new, nonce-derived address, account/state/payment installation and failed-creation rollback composition. Existing world controls are preparation, not that proof. |
| 4: G45.01–.02 | Partial independent consumer now includes selected multi-operation scalar execution over an encoded typed caller frame and derived exact headroom. General source/local/frame producer and fetched-runtime adapters remain open; no Scalar/Evm implementation was duplicated. |
| 4: G45.03 | Published structured label proofs remain read only; execution transport of structured branch/LOOP and actual backedge execution are open. |
| 5: G45.04–.05 | Reused assembler/byte proofs named above; offset/link layout, PUSH-data handling and `decode_encode` do not prove pinned decoder/step agreement. Reserved Bridge adapter remains untouched. |
| 5: G45.06 | Open: selection/stack/control/assembly/encoding composition against actual executable runtime-byte behavior; resources, decoder agreement and integration premises are undischarged. |
| Backfill A | Partial useful preparation now also includes selected scalar sequence/capacity composition over populated typed caller frames. Actual finite prefixes, suffix transport and assembled-runtime constructor consequences are retained. General runtime frame/layout and relocation/creation composition still need their actual producers; no parent closure. |
| Backfill B | Partial useful preparation: checkpoint/prefix algebra, actual create/send/transfer rollback and byte/fresh-handle controls. Full effectful loop-prefix and source constructor/payment observations remain open. |
| Reserved lanes V11–V17 | V11–V13 are blocking predecessors; V15–V17 are successors, not V14 prerequisites. No reserved work was reassigned and no unmerged branch imported. Coordinator integration of published predecessor interfaces is required before serial lane closure. |

No reserved edit is proposed as an unauthorized repair. The needed integration
is publication of the V11–V13 lowering/compiler/frame interfaces, then payment
and source/runtime producer composition in this owned namespace. Global G03
ledger/status reconciliation stays with the coordinator. Relevant feature IDs
are `sendTransfer`, `emptyDataValueCall`, `valueOption`, `constructors`,
`inheritance`, `newContract`, `creationTry`, `constructorLifetime`, `creationCode`, `runtimeCode`,
`immutables` and `libraries`; no manifest verdict changed.

## Runtime, diagnostics, checks and evidence

The clean initial branch `work` was exactly at the assigned base. The assigned
codex branch was created from that commit; ancestry is verified. Lean is
4.24.0 (`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`); Lake reports
5.0.0-src+797c613 (Lean 4.24.0). No Lean MCP tools are available in this session.
Focused file/import-closure CLI checks replace per-file MCP diagnostics.

The VM cgroup limit is 16 GiB, with no configured OS swap. Systemd user scopes
are unavailable; a local Docker scope using existing binaries verifies
`memory.max = 12884901888`, `memory.swap.max = 0`. Builds run with
`LEAN_NUM_THREADS=1`, explicit Lean `-j1` via an untracked alternate lakefile,
the repository writer lock and no Lean server. No network/cache download or
budget increase was used. The source/toolchain-keyed Lake cache is reused.

`lake -f v14-runtime.lakefile.toml build Solidity.KeySort` passed (2 jobs),
with 47,156 KiB maximum child RSS and 31,059,968-byte cgroup peak:
RUNTIME_GATE_PASS. The first timing probe could not run because `/usr/bin/time`
was absent; its raw log is retained and is not a passing build.

Both owned import closures pass: assembly/constructor controls (13 jobs) and
payment controls (33 jobs). Cold payment dependency checking took 88.51s,
906,204 KiB maximum child RSS, 598,798,336-byte cgroup peak, with zero OOM events;
that run failed on new proof syntax/cases, which were repaired. Raw failed
attempts, including bounded recursion/heartbeat diagnostic failures, remain in
`/workspace/v14-evidence`; no proof budget was raised. Final fresh per-file,
structural, trust, layer, orphan and exact-base docs comparison outcomes are
recorded in the external handoff and checkpoint follow-up below.

The repository full `./run-lean.sh`, whole-lane source/EVM composition controls
and final integrated gates remain pending. Focused kernel proofs and finite
controls are not external EVM/compiler tests; no new external EVM tests or
whole-lane agreement evidence are claimed. A partial checkpoint is not lane
completion.

## Independent reviews

Read-only finder `/root/backfill_a_finder` and independent skeptic
`/root/backfill_a_skeptic` reviewed the actual owned proofs without Lean servers
or builds. Both found no soundness defect. Their confirmed completeness/scope
findings were fixed: an actual assembler/backedge constructor witness, a
wrong-coordinate negative, guarded headline axiom pins, explicit account/runtime
and stack/headroom limits, and distinction between generic result algebra and
actual world-run consumers. Both accepted the backfill A source fixes.

Backfill B review required actual create/failed-receive/two-create witnesses,
resource/byte negatives and guarded axiom pins. These are now implemented;
final independent follow-up and actual diff/handoff review are recorded with
the checkpoint gates below and in the external review evidence. No reviewer
used a Lean server or build. The original raw failures are not relabeled green.


## Checkpoint validation and committed handoff

| Gate | Actual result |
|---|---|
| Focused assembly/constructor import closure | PASS, 13 jobs; actual assembled backedge and constructor controls. |
| Focused payment import closure | PASS, 33 jobs; actual world creation/receive/rollback controls. |
| Fresh CLI file diagnostics | PASS, all six owned files, explicit `-j1 --tstack=131072`, no MCP available. |
| Scoped headline axiom reports | PASS, thirteen guarded reports; only standard Lean axiom subsets. |
| Lane structural scope/import/registration guard | PASS, six owned modules, zero findings. |
| Layer / orphan / trust checks | PASS: 172 core modules with no elaborator reach; 1002 reachable and zero orphans; 1017 sources, 246 inventoried sites, zero trust findings. |
| Whitespace / owned relative links | PASS, exact-base diff whitespace; relative links checked in the owning document and test README. |
| Whole-repository doc paths | FAIL, 46 missing historical references; raw failure retained. |
| Exact-base no-new-doc-findings | PASS, complete raw base/head outputs identical. |
| Full repository `./run-lean.sh` | PENDING; not run and not claimed passing. |
| Full V14 source/payment/creation/runtime composition | BLOCKED/open on the obligations above, not discharged by this checkpoint. |

Final fresh diagnostics sampled one Lean worker at a time: peak aggregate Lean
RSS 643 MiB, minimum host MemAvailable 17,026 MiB, child cgroup peak
172,097,536 bytes, zero OOM events. The sampler can miss sub-0.5s workers;
all six explicit per-file command exits are independently retained. The local
VM disk still has about 30 GiB available; no cache or unrelated work was deleted.

The commit carrying this section is a reviewable partial backfill checkpoint.
The external handoff `/workspace/v14-artifacts/HANDOFF.md` records the full
committed head and base, exact commands/exits, all unfinished obligations and
absolute patch/bundle/evidence/checksum paths. Its evidence directory is
`/workspace/v14-evidence`. Neither this checkpoint nor a green focused check
marks the lane or persistent goal complete.


Final finder/skeptic diff review found no soundness or ownership defect. Its
small confirmed findings were fixed: the second actual creation now explicitly
preserves the first installed-account observation; `creationTry` is included
in the feature-ID reconciliation list; and V15–V17 are correctly identified
as successors rather than V14 prerequisites. Both reviews also require actual
committed head/artifact/checksum values in the external handoff before export.


## Recovery checkpoint: scalar sequences and guard

This continues the original frozen assignment on the same VM/branch from
`bb10f6f6e2a304479b9885ea1ebd4683fc436b2e`; the earlier checkpoint and original
artifacts are preserved. Available owned independent work was not exhausted
at that checkpoint. Predecessor absence does not waive any implementation,
proof, backfill or validation obligation and does not authorize weaker scope.

[ScalarSequence](../../Solidity/Backend/Executable/ScalarSequence.lean) consumes
actual published `selectBinary`, `selectUnary`, `ClosedCertificate.binary` and
operator certificates. It does not implement or rename their instruction
selection. The real sequence emits right literal, left literal, SUB, a
word-preserving selected uint-to-int cast, DUP1, signed-zero literal, SWAP1,
selected SLT and selected Boolean ISZERO. Binary LEFT is on top; casting emits
no opcode. The saved signed result and protected caller tail survive the later
comparison. Both original `shortT = none` source premises are explicit in
`source_result`/`typed_result`; operand definedness witnesses are equations
of existing intrinsic operations, not assumed simulations.

The caller frame encodes two actual `State C [.val .int, .val .uint]` locals
via existing `TEnv.get` and `encodeValue`, followed by a word spill. The exact
source/target result is composed for this sequence with those two protected
cells. The OPEN producer obligation is to show a real general runtime calling
convention supplies precisely this representation, and to cover arbitrary
intrinsic local/reference frames; that is not a premise silently discharged
by constructing an encoded frame. This fragment does not restrict the final
admitted profile. It changes no intrinsic AST, state, formula or semantics.

`stages` exposes exact operand/result words at the eight named boundaries;
`first_boundary` exposes the first physical PUSH separately. `heights` proves
the complete physical instruction-height trace. The exact peak is entry+3,
so `frame_capacity_iff` derives that the two frame cells leave at most 1019
spill words, not merely a safe exit height. `typed_result` combines actual
source evaluation, full numeric execution and that derived capacity.
`emitted_bytes` gives every PUSH32 payload and opcode in order, `bytes_length`
gives 104, and `decode_bytes` is the total encoder roundtrip.

[ScalarSequenceResources](../../Solidity/Backend/Executable/ScalarSequenceResources.lean)
consumes existing `ClosedInvocation.prefix_safe`, `BinaryInvocation.prefix_safe`
and `CheckedInvocation.testPrefix_safe`, with their invocation capacities
proved here from the actual instructions/typed frame lengths. Their
implementations are not duplicated. Its concrete continuation pushes right
then left operands above the earlier Boolean/signed results, then executes
the selected existing checked-add overflow test. `followup_boundaries` exposes
both intervening materialization stacks; `test_boundaries` exposes the entry
and exact words after each of the five actual test instructions. The two DUP2
operations create entry+6 peaks while exit is only entry+5. The exact spill
bound is therefore 1016 with this caller frame. Complete emitted payload/test
bytes and encoder roundtrip cover all 175 bytes, not only the last opcode.
This test returns a real failure flag; no compiled panic branch is claimed.

[Controls](../../Solidity/Backend/Executable/ScalarSequenceChecks.lean) inhabit
an actual typed state with caller words -7 and 99. SUB 3-5 wraps, the selected
cast reads -2, SLT with zero is true, and ISZERO is false, retaining -2 and
both caller words. Reversed operand emission produces a different Boolean
and saved value. Controls expose actual first/operand/DUP boundaries, full
concrete bytes and the eight-word checked DUP peak. Populated caller frames
with 1020/1017 spill words violate the exact intermediate bounds even though
the respective final heights fit 1024. A separate impossible closed invocation
confirms a successful unbounded numeric run cannot justify physical capacity.

These are numeric-slice/encoding consequences. `Scalar.run` is gasless;
`decode_encode` is not a pinned EVM decoder theorem; the creation runner does
not execute these scalar opcodes or jumps. No relation between those runners
is defined by fiat. Fetched runtime/Osaka, source/frame producer, full payment/
world asymmetry, effectful loops, source constructors and executable-byte
correspondence all remain open as recorded in the work queue above.

### Guard repair and regression evidence

The [lane guard](../../scripts/check-v14-executable.mjs) now uses a nonempty
recursive filesystem census including untracked/nested owned Lean sources,
requires exact noncommented root registration, and inspects both raw reachable
imports and the published graph. Missing raw dependencies and unsupported
lexical forms fail closed. Raw `meta`/`public`/`all` header forms are read even
when the shared graph filters them. The inherited plain-Lean bootstrap is
permitted only through the frozen AST/Eqns edges; new owned Lean/meta imports
are rejected. Git scope combines tracked changes with untracked files and
uses `--no-renames` so a reserved deletion cannot disappear behind an owned
rename destination. Registrations remain append-only.

The scanner is a conservative structural guard, not a complete Lean parser
or compiler admission checker. Owned brace-bearing/interpolated strings and
quoted identifiers require a future explicit term/token-aware trust scanner
and currently fail closed; this does not alter Solidity's admitted profile.
Reserved imported source is not rewritten. Normal/raw/character literals and
nested comments are masked independently to avoid hiding actual declarations.
Axiom tokens are rejected regardless of declaration modifiers/attributes.

[Fourteen Node regressions](../../tests/v14-executable/guard.test.mjs) cover
zero census; empty/commented/duplicate registration; raw forbidden edges hidden
by filtered/missing graph nodes; raw transitive and published edges; nested
untracked owned trust escapes; private/attributed/inline axioms; meta headers;
zero-hash raw backslashes; ordinary harmless strings; embedded interpolation
terms including comment-separated/non-bang forms; quoted-identifier comment
markers; and a real temporary Git rename/untracked-file census. No regression
passes via a skipped scan. Identifier-only import continuation refusal is a
conservative defense: Lean 4.24 imports one identifier per command.

### Recovery theorem premises and gates

| Result | Exact premises / boundary |
|---|---|
| `ScalarSequence.stages`, `first_boundary` | Existing typed numeric operands, source operation result/refusal equations for staged SUB/cast/comparison; first boundary needs no source-result premise. Actual numeric execution is derived. |
| `source_result`, `typed_result` | Both exact short-circuit refusal equations, existing operator result equations and actual typed state/frame. Spill room is derived from exact instructions; no desired target run is assumed. |
| `heights`, `capacity_iff`, `frame_capacity_iff` | Unconditional exact trace and arithmetic equivalences for this actual program. |
| `stage_prefixes` | Derived Closed/Binary invocation capacities, actual successful prefix equation, existing published prefix laws. |
| `checked_stages`, `followup_boundaries` | Earlier source-result witnesses and real published checked test, with exact earlier-result protected tail. |
| `test_boundaries` | Arbitrary existing typed uint operands and tail; each actual test-prefix run is proved. |
| `checked_heights`, `checked_capacity_iff`, `checked_frame_capacity_iff` | Exact selected test opcodes and frame lengths; no supplied capacity oracle. |
| `checked_prefix_safe` | Derived invocation capacity and actual successful checked-test prefix; existing law consumed. |
| `emitted_bytes`, `checked_emitted_bytes`, `bytes_length`, `decode_bytes`, `checked_bytes_length`, `checked_decode_bytes` | Actual total encodings; no fetched-byte semantics or pinned decoder agreement. |

The resumed KeySort gate passes under memory.max=12884901888,
memory.swap.max=0, `LEAN_NUM_THREADS=1` and explicit `-j1`; actual versions
remain Lean 4.24.0 and Lake 5.0.0-src+797c613. The cold scalar closure used one
Lean worker, peak aggregate RSS 7903 MiB, cgroup sampled peak 8434 MiB, minimum
host MemAvailable 8708 MiB and zero OOM events. Its initial owned height proof
failed; the raw failure is retained. Later focused checks pass with unchanged
budgets. A symbolic-byte `rfl` attempt exhausted the existing 200000 heartbeat
budget and was replaced with explicit encoder equations, not a higher budget.
Axiom pins retain exactly standard Lean axiom subsets; long printed messages
use whitespace-lax guards without weakening the axiom lists.

Fresh per-file diagnostics, focused import closure, final real guard and
regression outcomes, static/docs gates, independent proof-versus-guard reviews
and the actual checkpoint head are recorded in the recovery handoff/evidence.
The 46 historical docs findings stay raw exit 1, compared with the exact base;
no unchanged failed full gate is repeated. The full assignment is not complete
merely because this independent checkpoint or export exists. Further concrete
assigned constructor/payload consumer work follows this checkpoint.


Recovery checkpoint validation: fresh CLI checks pass on all three new Lean
files; scalar import closure passes 71 jobs; all headline pins pass; Node
regressions pass 14/14 with zero skipped; real guard passes 9 owned modules,
zero findings; layer/orphan/trust/whitespace/owned-link gates pass. Raw docs
checker is exit 1 with the same 46 findings and byte-identical exact-base
output; the separate no-new gate passes. Full repository and lane completion
gates remain open. Recovery evidence is `/workspace/v14-recovery-evidence`;
checkpoint handoff/export is under `/workspace/v14-recovery-artifacts/checkpoint2`.


Other public recovery facts: `instructions` fixes the selected physical program;
`frame_length` fixes the two actual frame cells; `frame_capacity` needs only the
explicit spill-length bound proved sufficient by `frame_capacity_iff`;
`frame_prefix_safe` additionally consumes a real prefix split/run equation.
`subtractionInvocation`, `comparisonInvocation` and `followupInvocation` are
constructed existing invocation objects with those derived capacities, not
new invocation semantics. `typed_combination`, `reverse_order` and
`checked_combination` are closed kernel controls, not new hypotheses.
The final independent guard review's stale six-module README count was changed
to the count-independent "owned modules" before commit.


## Recovery checkpoint: scalar payload and constructor composition

[ScalarArtifact](../../Solidity/Backend/Executable/ScalarArtifact.lean) continues
backfill A after the scalar/guard checkpoint, rather than stopping at that
commit/export. It consumes the exact 104/175-byte scalar encodings and existing
creation prefix/wrapper proofs read only. `runtimeCode` merely chooses those
two already proved actual programs; it is not a new AST or instruction selector.
`runtime_length` derives both payload lengths, `placement` derives PUSH1 lengths
and offset16 from the six-byte existing copy prefix and ten-byte wrapper.
No caller-provided layout or success oracle supplies these equalities.

`constructor_exec` executes both actual nonempty prefix segments and the exit
wrapper, returning or reverting the complete selected payload while protecting
a separate `List Creation.StackWord`. It does not coerce that tail into
`Scalar.Stack`, identify runners, or execute the returned runtime instructions.
`front_length`, `image_length`, `runtime_slice` and `arguments_slice` fix all
byte intervals. `decode_runtime` is exactly the existing encoder roundtrip.
`typed_payload`, for the base 104-byte variant only, retains the source, numeric execution, derived scalar capacity,
actual constructor-return and same-byte roundtrip facts as separate conjuncts;
it explicitly does not turn their conjunction into fetched-runtime agreement.

`excludes_argument_bytes` and `excludes_revert_arguments` consume deterministic
actual executions to exclude contamination by any nonempty argument suffix on
both result paths. `excludes_wrong_tag` distinguishes return and revert even
for the same complete payload. [Controls](../../Solidity/Backend/Executable/ScalarArtifactChecks.lean)
inhabit both payload sizes, success/revert with nonempty arguments, protected
creation words11/22 and separate typed scalar caller words-7/99, exact total
image length193 for the checked payload plus two arguments, argument start191,
and the retained scalar-capacity conjunction. These are constructor byte-slice
observations, not account installation or source constructor lowering.

Exact premises: `constructor_exec` needs only its actual checked/base choice,
typed operands, success/revert flag, argument bytes and creation tail;
`placement` is constructed, never assumed. Interval/length/decoding theorems
are unconditional on those inputs. `typed_payload` additionally retains the
previous two source short-circuit refusals and operation result equations,
actual typed caller state/spill and the exact1019 spill bound. The two argument
negatives require positive argument length only for the impossible-contamination
claim. No source profile, failure observation, Fml target or budget changed.

Focused import closure passes80jobs with seven guarded artifact/control axiom
reports using only standard Lean axioms. A first concrete drop191 control hit
the unchanged recursion-depth limit when reducing the whole payload length;
rewriting with `runtime_length` fixed it and its raw failure is retained.
Independent read-only finder and skeptic found no soundness/layout/ownership
defect. Their refinements were implemented: preserve the capacity conjunct and
add a failed-constructor argument-contamination control. Fresh diagnostics,
static/docs gates, final reviews and actual commit head are recorded in the
checkpoint handoff. Full original Work/Backfill and fetched/pinned/source/world
obligations remain open. Concrete world-operation prefix/iteration backfill
continues after this checkpoint; it will reuse existing operations/fold laws,
not introduce a new loop semantics.


Checkpoint3 final reviews accepted the source/layout/model/ownership fixes.
The handoff now states that `excludes_wrong_tag` has no external run premise
(it uses the internally derived `constructor_exec` proof), and both document
and handoff qualify `typed_payload` as the base104-byte variant only. Actual
constructor/layout facts still cover both104/175-byte payloads. Focused80jobs,
fresh two-file diagnostics, seven pins and static gates pass; real guard11/0;
raw docs exit1/46 is unchanged and separate no-new comparison passes.


## Recovery checkpoint: actual world finite prefixes

[WorldPrefixes](../../Solidity/Backend/Executable/WorldPrefixes.lean) continues
backfill B using existing `List.foldlM` and `ContractWorld.Operation.run` directly.
It adds no operation syntax, payment semantics, execution function or loop
interpreter. `success_iff` proves both directions of actual prefix/suffix world
factorization; `cut_success_iff` handles every take/drop position, including
empty/whole cuts. `prefix_failure` blocks later operations after the exact first
halt; `suffix_failure` transports the exact suffix halt after a real successful
prefix. `iteration_split` uses published list replication/folding laws to
factor any finite n+m repetitions. It does not claim divergence correspondence.

`atomic_suffix_failure` restores the original complete world after any actual
failed suffix, retaining the exact halt. `atomic_prefix_success` separately
commits the genuine prefix world. These are existing atomic result algebra;
for arbitrary THalt they do not assert a completed chain Step or that model
exhaustion/divergence becomes a caught revert. G36.03 still requires independent
G43 and the actual V12/G37 simulation producers, with no circular G43 premise.

[Controls](../../Solidity/Backend/Executable/WorldPrefixChecks.lean) reuse the
existing empty typed contract/receive fixture and install a real account from
a sender funded with3units. Three actual1-unit payable empty calls settle
sender3→0 and recipient0→3. The explicit1+2 iteration cut consumes the general
split theorem and identifies its real middle as `paidOne`; two-sided prefix
extraction identifies that same world. A funded failing receive exposes actual
nonempty bytes de/ad, while an unfunded call fails empty before executing the
same recipient. A failed real prefix blocks a tail call proved successful
from that input world. Outer rollback restores creation and every earlier
settled payment, while a separately committed prefix retains the installed
account and actual balances. These are unmetered paid-call controls, not
compiled send/transfer/stipend adequacy or approved environment simulation.

Exact premises: `success_iff`, `cut_success_iff` and `iteration_split` are
unconditional algebra of existing actual operation executions. `prefix_failure`
requires its exact actual prefix failure equation; `suffix_failure` and
`atomic_suffix_failure` require actual prefix success and suffix failure;
`atomic_prefix_success` requires actual prefix success. These equations are
discharged by the inhabited controls, not counted as whole compiler/world
preservation. Source effects, receiver bytes and funding are read through
existing APIs. Private value/error result projections merely recover closed
kernel-checked observations and do not supply execution semantics or oracles.

The first whole-world `rfl` controls exceeded the unchanged recursion-depth
limit. Shared result projection, kernel-only Boolean/error observations and
published fold/bind equations fixed them without raising recursion, heartbeats,
fuel, nodes or test limits. Original failures are retained. Focused closure
passes35jobs; eight scoped headline/control axiom pins retain only standard
Lean subsets. Separate read-only finder/skeptic reviews found no semantic or
ownership defect; their actual-middle, stopped-successful-tail and nonempty
iteration-cut refinements are implemented. Fresh diagnostics/static/docs/final
review results and actual checkpoint head appear in the recovery handoff.

All original Work/Backfill/reserved obligations remain binding. This completes
additional independent prefix/iteration preparation, not G43/G36.03/payment
asymmetry or a source constructor/runtime/executable-byte proof. Next final
validation runs the required unchanged full repository gate under the same
serial resource controls, without relabeling historical docs failure green.
