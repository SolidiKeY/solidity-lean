# V14 executable consumers and open lane obligations

Batch `solidity-v12-v17-20261031`, lane `v14-payments-bytecode`.
Assigned base: `2fe1f8932f96be15b00df03ba2cde46f64a87758`.
Branch: `codex/solidity-v12-v17-20261031/v14-payments-bytecode`.
Checkout: `/workspace/solidity-lean`.

This document consolidates the original checkpoint and eight recovery checkpoints.
Milestone-specific gate tables below are historical; the final validation table
at the end records the current source result.

This work is independent preparation from backfill A/B. It does not close
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
| 3: G44.01 | Partial: actual source initializer/base-argument prefix and failure-state transport plus successful legacy/viaIR source-deployment controls are proved. Argument controls are standalone metadata; source lowering/ABI and compiler constructor relation remain open. |
| 3: G44.02 | Published installation/linking/immutable component reused read only; consumer proofs above return exact runtime bytes. Source/runtime interface, immutable declaration/value identity and full artifact-table composition remain open. |
| 3: G44.03 | Open: source new/try-new, nonce-derived address, account/state/payment installation and failed-creation rollback composition. Existing world controls are preparation, not that proof. |
| 4: G45.01–.02 | Partial independent consumer now includes selected multi-operation scalar execution over an encoded typed caller frame and derived exact headroom. General source/local/frame producer and fetched-runtime adapters remain open; no Scalar/Evm implementation was duplicated. |
| 4: G45.03 | Published structured label proofs remain read only; execution transport of structured branch/LOOP and actual backedge execution are open. |
| 5: G45.04–.05 | Reused assembler/byte proofs named above; offset/link layout, PUSH-data handling and `decode_encode` do not prove pinned decoder/step agreement. Reserved Bridge adapter remains untouched. |
| 5: G45.06 | Open: selection/stack/control/assembly/encoding composition against actual executable runtime-byte behavior; resources, decoder agreement and integration premises are undischarged. |
| Backfill A | Partial: actual selected scalar/local reads and capacity over populated typed caller frames, constructor payload assembly, and library/immutable patch equality to selected bytes are proved. General runtime frames, assembler/session link provenance and executable decoder/control/resource producers remain open. |
| Backfill B | Partial: actual world finite prefixes/iterations, paid-prefix tryCreate catch boundaries, source-journal nested/committed rollback, and source-initializer/argument failure controls are proved. Full effectful compiler-loop/divergence and source-to-runtime payment/constructor relations remain open. |
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


## Recovery checkpoint: actual typed local reads

Completeness review found that protected populated cells were not yet read by
emitted code. [LocalFrame](../../Solidity/Backend/Executable/LocalFrame.lean)
now proves uniform intrinsic `.local .here` int and `.local (.there .here)` uint
lookup against actual DUP1/DUP2 over the existing two-cell `frameTail`. No local
is evaluated into a literal in generated code. Exact source/target read values
are `TEnv.get` of the arbitrary typed state, with arbitrary protected spill.

The noncommutative local subtraction emits the right literal first, shifts the
uint local access to DUP3, then consumes the published selected SUB certificate.
`stages` proves each physical boundary and result/tail order. `source` requires
only the actual intrinsic operation result and exact short-circuit refusal.
Actual heights are h,h+1,h+2,h+1; `capacity` derives spill≤1020, while each plain
read derives spill≤1021. `prefix_safe` consumes the resulting complete-code
capacity for any actual prefix. All35 emitted bytes are pinned, including the
PUSH32 payload, DUP3/SUB and same-encoder roundtrip.

[Controls](../../Solidity/Backend/Executable/LocalFrameChecks.lean) read real
locals-7/99 with spill123/456, compute99-3=96, and reject a wrong caller index,
a forgotten PUSH-induced index shift and reversed SUB operands. Spill1021
admits the final output height but refuses the intermediate1025-word peak.
Five scoped guarded headline/control axiom outputs contain standard Lean
subsets only. Initial source literal normalization and symbolic encoder `rfl`
failures are retained; explicit source reduction and published encoder equations
fix them without changing budgets. Focused73jobs passes; fresh/static/final
separate read-only finder/skeptic results and head are in checkpoint5 handoff.
General local/reference/runtime-frame production and fetched Osaka execution
remain OPEN; these are real reads in an independently specified typed frame.

The first full-gate attempt failed before Lean (container Node missing,
exit127); exposing the existing host binary fixed that setup. The next full
build was deliberately interrupted (exit137, NOT a pass) after completeness
reviews identified the local-read, tryCreate, linking/immutable and permitted
source-journal gaps. Its original raw log/cache remain. Final full gate follows
those changes; no inherited Lean failure has been waived and no proof/test
budget raised. Blanket absence claims are replaced with exact boundaries:
Source.construct/deploy and old Bridge loop transport already exist; required
relations from NEW Backend outputs/frames to those published interfaces do not.


Checkpoint5 exact API premises: `int_source`, `uint_source`, `reads`,
`read_capacity`, `heights`, `capacity`, `bytes`, `decode` are unconditional
component consequences for their arbitrary typed state/spill/operand inputs.
`stages` additionally requires the actual intrinsic SUB result equation;
`source` also requires exact short-circuit refusal. `prefix_safe` requires
spill≤1020, an actual whole-code split and a successful actual prefix run.
No local-value or simulation oracle occurs. Five guarded axiom pins pass.

| Checkpoint5 command | Actual result and absolute evidence |
|---|---|
| `lake -f v14-runtime.lakefile.toml build Solidity.Backend.Executable.LocalFrameChecks` | PASS73jobs; `/workspace/v14-recovery-evidence/local-frame-pins.log` |
| `lake -f v14-runtime.lakefile.toml env lean -j1 --tstack=131072` on LocalFrame and LocalFrameChecks, each180second limit | Fresh2files PASS,1worker675MiB; `/workspace/v14-recovery-evidence/local-frame-fresh.log` |
| Lane/layer/orphan/trust/whitespace/docs static commands | `/workspace/v14-recovery-evidence/checkpoint5-checks.json`; raw docs46/1 separate from no-new PASS |

Final separate finder/skeptic found no proof defect. Their actual log mapping,
real module-path extensions and external handoff link-base corrections are
applied before checkpoint commit/export.


## Recovery checkpoint: actual constructor attempts after a paid prefix

Completeness review correctly identified usable published `World.tryCreate`
and `ContractWorldCertificates` interfaces. [CreationAttempt](../../Solidity/Backend/Executable/CreationAttempt.lean)
consumes them without adding source/target semantics. `prefix_caught` requires
an actual prefix success, mutable context and actual constructor failure with
specified bytes; it proves the outer atomic result retains the genuine paid
world and exact constructor data through an arbitrary observation function.
`prefix_argument_failure` requires actual prefix success only: argument failure
never enters constructor catch, so outer atomic returns the earlier checkpoint.
For arbitrary THalt this is result algebra, not a completed Step for divergence
or model exhaustion; the inhabited controls use completed reverts.

Actual one-unit payment takes sender3→2 and installed recipient0→1. A new closed
constructor at a different checked address executes `revertData ca/fe`; its
catch retains both funded balances and the earlier account, with no failed
account installed. Constructor context value is zero (ordinary default), not
a proof of constructor value-payment lowering. The actual empty constructor
also succeeds and supplies `World.create_installs` and exact fresh address.
A subsequent success continuation returns77failure unchanged, distinct from
constructorca/fe and argumentab. The latter stays outside catch even when
catchable; an actual paid-prefix argument failure restores the outer world.
`operation_consistency` consumes the published **world-result erasure**
certificate and actual `Operation.tryCreate_caught`; exact bytes are proved
independently, not recovered from erased results. Six guarded headline/control
axiom outputs contain standard Lean subsets only.

Initial syntax/namespace and whole-world product-eta recursion failures are
retained; explicit existing run witnesses and product case analysis fix them
without raising budgets. Source/new/try-new lowering, nonce/address production,
constructor source/runtime identity and pinned EVM rollback remain OPEN.
Separate read-only finder/skeptic found no proof defect; their erasure-wording,
axiom-pin and arbitrary-THalt caveat refinements are implemented.

| Checkpoint6 command | Actual result and evidence |
|---|---|
| `lake -f v14-runtime.lakefile.toml build Solidity.Backend.Executable.CreationAttempt` | PASS36jobs; `/workspace/v14-recovery-evidence/creation-attempt-pins.log` |
| Fresh `lake -f v14-runtime.lakefile.toml env lean -j1 --tstack=131072 Solidity/Backend/Executable/CreationAttempt.lean`,180second limit | PASS,1worker662MiB/noOOM; `/workspace/v14-recovery-evidence/creation-attempt-fresh.log` |
| Lane/layer/orphan/trust/whitespace/docs static commands | `/workspace/v14-recovery-evidence/checkpoint6-checks.json`; raw docs46/exit1 and separate exact-base no-new gate |

The next independent preparation consumes actual linking/immutable patch
locations within owned selected runtime payloads; no reserved implementation
or global ledger is changed. The full original queue remains binding.


## Recovery checkpoint: linking and immutable selected payloads

Completeness review identified unused published linking/immutable interfaces.
[PatchedPayload](../../Solidity/Backend/Executable/PatchedPayload.lean) constructs
actual bounded20-byte library data at offset46 inside the second PUSH32 and
32-byte immutable data at offset1 inside the first. `compatible_regions`
derives the actual disjoint intervals1..32 and46..65. `linked_runtime` proves
the resolver's42 changes exactly the selected left literal; `immutable_runtime`
proves arbitrary typed b changes exactly the selected right literal. The full
patched104-byte runtime equals `encode (ScalarSequence.code libraryWord b)`;
this is not arbitrary patched bytes or only a length/wrapper consequence.

`installs_selected` consumes `combined_installs` with that exact equality;
`decode_selected` is the same-encoder roundtrip. `immutable_read` consumes
`ImmutableTable.read` for the actual full32-byte immediate. `args_unchanged`
retains constructor arguments, while `excludes_arguments` derives the stronger
actual return-contamination negative from deterministic execution and nonempty
argument length. No source/machine simulation premise is assumed. These facts
are unconditional for arbitrary typed b/argument bytes, except the explicit
nonempty-argument premise on that negative.

LinkTable origin here is **lane-authored template metadata inside PUSH32**,
not `tableOfAssembly` or assembler-generated PUSH20/reference provenance.
The fixed42 fixture resolver is not a proved deployed-library/session identity.
Source immutable declaration/value agreement, actual linked-instance identity,
general artifact-table production and fetched execution remain OPEN.

[Controls](../../Solidity/Backend/Executable/PatchedPayloadChecks.lean) combine
actual42-5=37 signed comparison/negation over populated caller words, exact
constructor return, opcode bytes at0/33/66, nonempty args and contamination
refusal, cross-kind commutation, individually bounded but overlapping regions,
missing address, unresolved-template refusal and out-of-bounds immutable refusal.
Six scoped guarded headline/control axiom outputs use standard Lean subsets.
Initial missing import cache and whole-table conversion timeout are retained;
published interval compatibility avoids the timeout without raising budgets.
Separate read-only finder/skeptic found no proof defect; their precise link
provenance caveat and stronger argument-return negative are implemented.

| Checkpoint7 command | Evidence |
|---|---|
| `lake -f v14-runtime.lakefile.toml build Solidity.Backend.Executable.PatchedPayloadChecks` | PASS84jobs; `/workspace/v14-recovery-evidence/patched-payload-pins.log` |
| Fresh `lake -f v14-runtime.lakefile.toml env lean -j1 --tstack=131072` on PatchedPayload and PatchedPayloadChecks, each180second limit | Fresh2files PASS,1worker681MiB/noOOM; `/workspace/v14-recovery-evidence/patched-payload-fresh.log` |
| Static lane/layer/orphan/trust/whitespace/docs commands | `/workspace/v14-recovery-evidence/checkpoint7-checks.json`; raw docs46/1 kept separate from exact-base no-new |

Next preparation repairs the overbroad Source import guard boundary to admit
published pure independent source semantics and consumes actual source journal
and initializer prefix laws read only; it does not change reserved source code.


## Recovery checkpoint: independent source journal and permitted read-only imports

The completeness review found the guard's blanket Source ban broader than the
assignment, which permits consumers of published independent source semantics.
The guard now allows the exact pure `Source.World` dependency closure (World,
State, Types, Const, Syntax). Source implementations remain reserved/read only;
the writable-path guard still rejects any Source edit. Every allowed module's
raw recursive imports and independent published graph are checked. New tests
accept pure Source reads, reject reserved writes, and detect forbidden raw or
graph edges hidden behind an allowed Source module. This is an import audit,
not a new source admission/exclusion.17/17 regressions pass, zero skipped.
A mistaken read-only-shell test invocation failed EROFS creating its temporary
fixtures; original output is retained in source-guard-readonly-failure.log.
The authorized write-enabled fixture run passes source-guard-tests.log.

[SourceJournal](../../Solidity/Backend/Executable/SourceJournal.lean) consumes
the actual independent source `ExecState.transfer/apply/run/enter`,
`rollback_transfer`, `rollback_run` and `rollback_outer_after_commit`.
`transfer_operations` requires an actual successful transfer and distinct
addresses and extracts its two existing journal operations. `paid_inner_outer`
uses that actual transfer after an existing installation-operation list: inner
rollback keeps the paid world; payment-frame rollback keeps the preceding
installation; outer rollback removes it too. `paid_commit_outer` derives the
joined installation/payment operation prefix and proves an inner commit plus
later writes is still undone by the outer frame. All execution/operations/types
are the existing source definitions, not a new AST or payment runner.

Exact generic premises: arbitrary intrinsic source layout/state, existing
installation/inner/tail operation lists, two distinct checked addresses and
an actual paid-transfer equation. No world preservation or source/EVM relation
is assumed. Six guarded headline/control axiom pins contain only propext and
Quot.sound. `checkpoints_distinct` witnesses the worlds actually differ.

Controls journal an actual code0/nonce1 account update (explicitly **not**
Source.deploy/CREATE or a constructor run), settle sender3→2/recipient0→1,
then perform real storage+transient Boolean writes. Journal lengths3/5 and
exact typed before/after reads are kernel checked. Nested/committed rollback,
wrong-checkpoint refusal, unaffordable and self-transfer funding checks, and
recipient overflow despite sufficient sender funds are inhabited. Projection
helpers only recover kernel-checked observations; reference alternatives are
eliminated by their existing impossible location proofs. Source execution
failure-byte, initializer/constructor and compiler/EVM relations remain OPEN.

| Checkpoint8 command | Evidence |
|---|---|
| `lake -f v14-runtime.lakefile.toml build Solidity.Backend.Executable.SourceJournal` | PASS11jobs; `/workspace/v14-recovery-evidence/source-journal-final.log` |
| Fresh `lake -f v14-runtime.lakefile.toml env lean -j1 --tstack=131072 Solidity/Backend/Executable/SourceJournal.lean`,180second limit | Fresh PASS,1worker243MiB/noOOM; `/workspace/v14-recovery-evidence/source-journal-final-fresh.log` |
| `node --test tests/v14-executable/guard.test.mjs` | PASS17/17; `/workspace/v14-recovery-evidence/source-guard-tests.log` |
| Static lane/layer/orphan/trust/whitespace/docs commands | `/workspace/v14-recovery-evidence/checkpoint8-checks.json`; raw docs46/1 separate from exact-base no-new |

Initial transfer witness inference and dependent-Val equality controls failed;
explicit original operations and typed Boolean observation recovery fix them
without changing budgets. Independent separate proof and guard finder/skeptic
review results are retained at checkpoint export. Next source initializer and
base-argument prefix transport consumes published source semantics read only;
full lowering/runtime/payment prerequisites remain undischarged.


Checkpoint8 independent proof finder/skeptic found no correctness defect.
Their exact-self-transfer identity and committed-inner-plus-tail observations
are added: the funded self-transfer returns precisely `some paid`, while the
pre-rollback committed state has source nonce9 and six journal entries. This
makes the later-write leg nontrivial; rollback still restores the earlier
complete source state. Guard finder/skeptic accepted the exact pure closure,
read-only ownership boundary and17/17 meaningful no-skip regressions.


## Recovery checkpoint: actual source initializer and argument prefixes

[SourceInitializers](../../Solidity/Backend/Executable/SourceInitializers.lean)
consumes existing `runInits`, `giveArgs`, `collectArgs` and the existing EM
monad. `inits_append`, `arguments_append`, `collect_append` are unconditional
finite-prefix equalities over the original intrinsic resolved lists. They
preserve all actual source-state effects; no second evaluator is introduced.
`inits_success` consumes the exact actual successful prefix equation and feeds
its complete Locals×St to the suffix. `inits_failure` and `arguments_failure`
consume an exact actual failure equation and retain both complete state and
Halt without executing the suffix. Rollback, completion and compiler
simulation are separate obligations; arbitrary Halt includes source timeout.

[Controls](../../Solidity/Backend/Executable/SourceInitializerChecks.lean)
reuse the published A/B inheritance fixture read only. Both initializer lists
are nonempty; A then B stores1/1 while B then A stores1/0. The actual successful
intermediate source state discharges the general cut law. A static first
initializer actually reverts empty, blocks the nonempty suffix and leaves both
values zero. Successful source deployment result tags are now proved for BOTH
legacy and viaIR at the existing20horizon, and actual code/nonce installation
is observed. The reused storage observations distinguish legacy1 from viaIR2;
they are no longer described as success witnesses without checking result tags.

Positive standalone base-argument metadata is zero-parameter, records baseA
once and skips the duplicate. It is explicitly not asserted equal to
GAB.prog.baseArgs nor evidence of Program.Derived/source argument lowering.
A deliberately bad-arity typed standalone negative evaluates division-zero
arguments before the later parameter-shape refusal; its exact panic bytes and
full source state block the suffix. These are component negatives, not admitted
constructor witnesses or new profile exclusions. The nonempty base-collection
prefix also consumes its published-program list law. Existing source fixtures
use toyFixed: no Keccak, library/session or EVM deployment agreement is claimed.

Ten guarded headline/control axiom outputs retain standard Lean subsets.
Initial missing cache, redundant split steps, ExceptT representation and
Except-equality decision failures remain in raw logs. Actual bind-continuation
state transport and kernel-checked status projections fix them without raising
recursion, heartbeats, horizons, fuel, search or test budgets. Cold published
source closures stayed serial under the cap (605MiB and1264MiB sampled peaks,
zero OOM), with original raw failures retained.

The guard allowlist now exactly matches the pure published Source.SemanticsExamples
closure:22 Source modules,26 total including the four existing pure Hash/Keccak/
Roadmap dependencies. Source.Elaborated is a typed pure representation;
Source.Elaborate, Frontend, Lean.Elab and unknown Source remain forbidden.
Every raw and published edge and reserved-write fence still runs. Regression
cases now cover World, Semantics and SemanticsExamples reads and hidden bad
edges behind both World and Semantics; no scan/test is skipped. This is import
audit, not compiler source admission. Independent separate proof and guard
finder/skeptic reviews found no defect; their successful-deployment-tag and
standalone/toy-fixture caveats are implemented.

| Checkpoint9 command | Evidence |
|---|---|
| `lake -f v14-runtime.lakefile.toml build Solidity.Backend.Executable.SourceInitializerChecks` | PASS29jobs; `/workspace/v14-recovery-evidence/source-initializer-pins.log` |
| Fresh `lake -f v14-runtime.lakefile.toml env lean -j1 --tstack=131072` on SourceInitializers and SourceInitializerChecks, each180second limit | Fresh2files PASS,1worker392MiB/noOOM; `/workspace/v14-recovery-evidence/source-initializer-fresh.log` |
| `node --test tests/v14-executable/guard.test.mjs` | PASS17/17,0skips; `/workspace/v14-recovery-evidence/initializer-guard-tests.log` |
| Static lane/layer/orphan/trust/whitespace/docs commands | `/workspace/v14-recovery-evidence/checkpoint9-checks.json`; raw docs46/1 distinct from exact-base no-new |

All Work/Backfill obligations remain as in the queue. Existing Source.construct/
deploy and old Bridge loop transport are published; missing relations are the
actual compiler/frame/world and NEW Backend-output decoder/layout/state
producers, not absent source semantics or permission to replace reserved code.
The final unchanged repository gate follows this checkpoint after the identified
independent recovery work; missing parent proofs are never counted discharged.


Checkpoint9 raw closure/allowlist equality is separately checked in
`/workspace/v14-recovery-evidence/initializer-source-closure.json` (PASS26/22,
no forbidden closure modules). Actual focused29jobs and fresh2file checks pass;
source-init/deployment and base-argument boundaries above remain distinct.


## Final recovery validation and exact blocking interfaces

The final complete repository command ran on committed source head
`c470fb4e531a527daf14046a5bddecfb3e797413` after all identified recovery
consumers and independent reviews. It PASSED: default build1002jobs,
SolkeyTestSuite262jobs, and solkeycheck parsed377taclets/131read-bearing with
table coverage131 and exact pinned-file agreement. The following final
checkpoint changes this owning document only; Lean/scripts/tests remain the
same tested source. No unchanged failed heavy gate was retried as a waiver.

Actual runtime: Lean4.24.0 commit797c613eb9b6d4ec95db23e3e00af9ac6657f24b;
Lake5.0.0-src+797c613. `lake -f v14-runtime.lakefile.toml build Solidity.KeySort`
completed successfully (2jobs), recorded in recovery runtime.log before
RUNTIME_GATE_PASS. That runtime-availability gate does not discharge lane proofs.
No per-file Lean MCP tool was exposed; fresh explicit-j1 CLI diagnostics and
focused import closures were used. Seventy-five guarded headline/control axiom
outputs across21owned Lean modules contain only standard Lean subsets.

The unchanged `./run-lean.sh` ran through a task-owned PATH Lake wrapper which
selects the saved alternate lakefile (same package/targets, explicit-j1 flags).
LEAN_NUM_THREADS=1; writer lock held through Docker process completion;
aggregate MemoryMax12GiB/MemorySwapMax0; one sampled Lean worker throughout.
Actual full wall10533.2s; peak aggregate Lean RSS10900MiB, peak anonymous10227MiB;
child cgroup peak12884901888bytes (the12GiB cap), max-events2414 (cap-hit/allocation pressure; reclaim attempted),
OOM/oom_kill/oom_group_kill all0; minimum host MemAvailable5872MiB. The cap was
reached, not exceeded or bypassed. Before full gate about29GiB disk free;
after it24GiB. Existing single build tree/source-toolchain cache was reused;
no caches or duplicate build trees are exported.

| Gate command | Actual outcome / decisive evidence |
|---|---|
| `./run-lean.sh` with saved bounded runtime wrapper and actual SOLKEY_RULES | PASS exit0:1002+262jobs;377/131/131 exact sort agreement; `/workspace/v14-recovery-evidence/full-final.log` |
| Repository aggregate sampler | `/workspace/v14-recovery-evidence/full-final-measure/summary.json`; one worker, no OOM, cap/pressure statistics above |
| Per-checkpoint focused/fresh kernel checks | PASS as named in each milestone and exported handoff;75exact guarded standard-axiom outputs |
| `node --test tests/v14-executable/guard.test.mjs` | PASS17/17,0skips; `/workspace/v14-recovery-evidence/initializer-guard-tests.log` |
| `node scripts/check-v14-executable.mjs`, layer/orphan/trust checks, whitespace | PASS; final static evidence is in `/workspace/v14-recovery-evidence/checkpoint10-checks.json` |
| `bash scripts/check-doc-paths.sh` | Raw FAIL exit1/46 retained; final log in `/workspace/v14-recovery-evidence/checkpoint10-docs.log` |
| Separate exact-base no-new docs comparison | PASS byte-identical to `/workspace/v14-evidence/docs-base.log`; this never relabels the raw checker green |

Initial full-gate setup failure127 (Node absent inside the restricted container)
and the deliberately interrupted137 attempt before accepted recovery findings
were implemented remain raw non-passes. The host Node binary was then mounted
read-only; final full pass used the fixed runtime. All original proof/control
failures remain in evidence. Original checkpoint/artifacts at bb10f6f6 are
preserved with unchanged checksums. No new goal/reset/VM/competing continuation,
reserved implementation edit, push, merge, PR or unmerged predecessor fetch.
The exposed tools contain stop_goal but no get_goal; the launcher's original
objective is preserved, and its audited identity is not replaced.

Separate independent read-only finder/skeptic reviews accepted every checkpoint
and the actual complete base-to-c470fb4e source diff (21modules/28paths), including
hypotheses, non-vacuity, ownership and model distinctions. Neither reviewer used
Lean/server/builds. Final validation-document/handoff/export review follows;
all review refinements are implemented. Kernel proofs, guard regressions and
repository/TestSuite/sort checks are separate evidence. No external solc/EVM
execution was run or claimed by this lane; Scalar.run remains gasless, Creation
execution returns bytes without arbitrary runtime op execution, decode_encode
is an encoder roundtrip, Source fixtures use toyFixed, and authored PUSH32 link
metadata is not deployed-library identity or assembler-origin provenance.

The entire assignment remains **blocked/partial**, not complete. The exact
remaining producer requests (no unauthorized patch made) are:

* Source owner: publish the independent payment/session interfaces required by
  the frozen G01 decisions. Existing Source.Eval.pay/callAddr have no stipend
  classification input; Source.Semantics explicitly records missing stipend,
  sender-validity and failure-point modeling. Complete that reserved interface
  while preserving the admitted profile/observations; do not add an exclusion
  or desired-simulation premise. V14 still owes its own joint compiled world/
  payment relation, actual fitted/enforced gas proof and asymmetry discharge.
* V11–V13/G37 compiler/frame owners: publish/integrate the source-to-intrinsic
  constructor/argument/ABI lowering, general runtime-local/reference frame and
  call/return/world producers. Existing Source.construct/deploy are present;
  old Evm memory-frame and per-transaction Sim.oracle results are present but
  do not supply a history-dependent compiled receiver-world strategy or the
  NEW Backend scalar/control frame relation. G36.03 waits for independentG43
  and actual V12/G37 prefix/divergence producers, never vice versa.
* Reserved Evm/Bridge execution owners: publish a checked decoder/layout/state/
  resource adapter from NEW Backend.Instr, Control.expand and Assembler outputs
  to the existing pinned-step interface. Old Bridge decoded_loop_turn/prefixes/
  simulation and SafeStructured safe_simulation already exist over old macro
  Image/LoopLayout; reusing them requires this representation producer, not
  recreating their loops. Scalar/Creation/Failure slices do not jointly execute
  CALL/JUMP/account/gas behavior. Keep Bridge outside Solidity.lean/core.

Consequently G44 source-new/try-new, nonce/account/state/payment/runtime identity
and immutable/library session identity remain open, as do G45 general selection/
frame/control/fetched-byte composition and pinned resources. All exact Work/
Backfill statuses and theorem premises above remain binding. Coordinator G03
reconciliation should record independent preparation for G43/G36.03/G44.01-.03/
G45.01-.06 and the feature IDs already listed, without changing parent verdicts
or TrustAudit/manifest pins. No human semantic scope choice is requested.


## Published creation-frame recovery (audit 57995d33)

The frozen assignment base remains `2fe1f8932f96be15b00df03ba2cde46f64a87758`.
Original sealed source/export HEAD `e74b7ac80fc5bccfa6e547764097f456c8020476`
is retained as the first parent of incorporation
`e85fc5f07d52a2ed7f0a8299bab57e1b828a2d5a`. Its second parent is the exact
human-authorized published `4165de133bafd522ab18099e18cad489bb1aa7d6`.
The merge was conflict-free; separate read-only finder/skeptic reviews verified
all prior owned files unchanged, all registrations retained, and all other
merged blobs identical to publication. No unmerged worker branch was fetched.
The consumed `Semantics/CreationTryFrame.lean` has blob
`4cbd2c9b8e4d6497aca23e753efc56b27d6ad325` and SHA256
`e813b13eeb9e2ab3134de2fa8e5f3294db13ec153af383b1c8b8360f3532f95f`.
Reserved producers remain read only after incorporation.

`Backend/Executable/CreationFrame.lean` consumes actual `CreationTryFrame.run`,
`caught`, `success`, `tail_success`, `tail_body_failure`, `atomic_tail_failure`
and `errorData_refused`. Its constructor failure uses `encodeError` of boom,
proved to decode by actual `CatchKind.decode .reason`; raw ca/fe is explicitly
refused. `caught_run` and `paid_prefix_resumes` discharge creation and branch
premises constructively, using the actual existing paid-prefix witness.
The original caller has two aliases of object0 and local41. The handler
allocates object1 with decoded bytes98,111,111,109, drops its local, and retains
object0 containing7,8. `old_length_read` and `resumed_run` execute the caller
on that grown heap, reading the old alias length2, not the catch length4.
`fresh_catch_binding`, `caught_heap`, `exact_objects`, `resumed_frame` and
`wrong_tail_heap_refused` expose those intermediate/final distinctions.

`argument_bypasses` and `argument_outer_rollback` propagate exact argument ab
outside the catch. `selected_tail_failure` propagates exact tail77, not the
constructor payload, and `paid_outer_rollback` restores outer `created`, not
`paidOne`. `success_run` stores the actual supplied returned handle in the old
uint local; `success_handle_observed` distinguishes its address from `fresh`,
and `success_installs`/`returned_identity` prove actual installation/identity.
There are wrong-world, bytes, alias and malformed-payload controls.
These public headlines are closed kernel proofs, with no external simulation
premise; private helpers only recover actual evaluated results or abstract the
pair while consuming the existing proved constructor result. Scoped axiom
outputs pin either none or the existing standard propext/choice/Quot.sound set.

The pending caller explicitly identifies sender and retains balance3/netempty;
the paid world has sender2/fresh1. No `World.finish` or `CreationTryFrame.execute`
is used: execute's unpaid/local-only convention cannot reconcile this stale
paid caller. These results concern intrinsic world/typed heap semantics, not
independent Source lowering, nonce derivation, compiled constructor/new, target
CREATE, fetched byte execution or gas. G44.03/Backfill B gain this independent
composition; every remaining Work/Backfill obligation in the queue table stays
open/partial with exactly the prior scope. In particular G43 stipend/payment
asymmetry, G36.03 and G45 fetched-state/resource relations are not discharged.

The owned guard now checks local scope and append-only registrations against
the exact reviewed incorporation, while verifying frozen/incorporation/published
ancestry and the incorporation's exact ordered parents. All raw/transitive,
zero-census, untracked and trust fences remain. Behavioral controls reject each
missing ancestor and malformed/reordered parent sets, and a real Git fixture
shows unchanged inherited reserved content excluded and subsequent reserved
edits rejected. This is provenance/scope validation, not a semantic premise.

Separate read-only proof finder/skeptic reviews required the actual-handle
success observation, alias-dependent tail read and explicit payer identity;
all are implemented and re-reviewed without remaining findings. Separate guard
finder/skeptic reviews required behavioral ancestry/parent rejection tests;
those are implemented. Neither review area ran Lean/server/builds.
Post-incorporation focused/import, static, documentation-baseline and full-gate
outcomes are recorded in the new absolute VM evidence/handoff, preserving all
old seals and raw failures. Until that final gate passes, the old full pass is
only evidence for its old source. This recovery does not complete the lane or
change the unchanged persistent goal's blocked status.

Recovery focused gate passed64jobs with26 scoped axiom pins. Guard regressions
passed19/19,0skips; scope22modules/0findings, layers/orphans/trust/automatic and
whitespace passed. Fresh Lean4.24.0/Lake5.0.0-src and KeySort2jobs passed under
12GiB/no-swap (RUNTIME_GATE_PASS). Raw docs exit1 remains: frozen46missing/
37ambiguous; publication/current48missing/37ambiguous. The complete multiset
difference is exactly publication's two inline-assembly references; no lane
addition or omission relative to publication. This is a separate no-new-finding
pass, never a passing raw docs gate or zero global delta against frozen base.
Post-incorporation full gate is pending at this checkpoint. New evidence:
`/workspace/v14-creation-frame-evidence`; prior sealed exports remain untouched.


### Creation-frame checkpoint11 full validation and handoff

The post-incorporation `./run-lean.sh` gate passed exit0 on committed Lean source
`233df942f10ef4076a69a4e3e10b724ecfacd470`:1039 default jobs,262 TestSuite jobs,
377taclets/131read-bearing/131covered exact SolKey annotations. Actual wall9211.8s;
peak aggregate Lean/Lake RSS11029MiB, anonymous10299MiB, one Lean worker;
minimum host MemAvailable6062MiB. Child memory.peak12884901888bytes reached the
12GiB cap; max-events1561 records allocation/reclaim pressure. OOM/oom_kill/
oom_group_kill all0, swap.max0; no cap, proof, fuel, node or test budget changed.
Disk after build23GiB free, same build/cache tree. Full raw log and sampler:
`/workspace/v14-creation-frame-evidence/full.log` and `full-measure/summary.json`.

Checkpoint11 handoff/export:
`/workspace/v14-creation-frame-artifacts/checkpoint11/HANDOFF.md` binds frozenbase,
publication/incorporation, tested source and export HEAD. Its original.patch
includes exact published incorporation; lane.patch isolates owned changes.
The branch bundle carries the verified history required by the structural guard;
a source-only patch does not carry that incorporation ancestry. Prior sealed
exports remain unchanged. Raw docs exit1/48missing37ambiguous and inherited+2
versus frozen remain failed/debt evidence; separate no-new-versus-publication
comparison passes. This checkpoint closes the independent typed creation-frame
consumer and its checks/reviews, not any parent G43/G36/G44/G45 obligation.
The next available independent backfill consumes actual constructor arguments;
it is not included in this tested source or checkpoint's proof claims.


## Constructor argument consumer (checkpoint12)

`Backend/Executable/CreationArguments.lean` consumes published
`CreationTryFrame.constructorArg` and `argument_binding`, without modifying
constructor, source, frontend or world implementations. `actual_argument`
reads caller local41; the existing closure binds that word into a typed
constructor local and `RevPart.word` produces its exact ABI word in the actual
constructor failure. A second real constructor run at42 produces word42,
excluding a hardwired payload. `binding` at `State.init C` is explicitly a
standalone component witness; `actual_constructor_failure` separately runs the
real world-entered frame. No general source constructor/ABI lowering follows.

`argument_to_catch`, `argument_dependent_payload` and `paid_argument_catch`
compose the actual read, argument-dependent constructor failure and typed raw
catch after the real paid prefix. The catch allocates32actual bytes and drops
its local, preserving old object0bytes7/8, aliases0/0 and caller local41.
`selected_wrong_payload_refused` compares the actual heap payload with word42;
`raw_is_not_error_reason` separates these raw ABI words from decoded Error data.
The separate preceding CreationFrame fixture still exercises genuine Error
boom decoding; these are different payload/handler observations.

`arithmetic_argument_failure` evaluates actual typed41/0 after the proved
`no_short_circuit` condition. Existing intrinsic `TRes.ofOpt none` returns bare
`.revert`, not `.panic` or an EVM panic-byte payload. The initial external draft
expected panic; the first diagnostic/refusal inspection corrected that claim,
without changing semantics, refusals or budgets. Raw failed diagnostic remains.
`evaluated_argument_bypasses`/`paid_argument_rollback` propagate that exact
argument halt outside catch and restore outer `created`. The raw handler would
complete normally on that halt, making bypass observable. It would also
complete on77, whereas `argument_tail_failure` preserves exact selected-tail77
and `paid_tail_rollback` restores `created`; tail failure is not re-caught.
All public results have concrete discharged evaluation/creation/branch premises
and19 scoped standard-axiom outputs. No paid execute/finish, source lowering,
byte CREATE, gas or fetched-runtime relation is supplied. G44.01/G44.03 and
Backfill B gain independent transport; the complete original queue remains
partial/blocked as recorded above. Final gates/reviews follow below.

Checkpoint12 fresh per-file diagnostics and focused/import build passed65jobs
with19 scoped axiom pins under the unchanged180s focused limits and12GiB/no-swap
runtime. Separate independent read-only finder/skeptic reviews accepted actual
source/doc after the positive paid-prefix, selected wrong-payload and normally
completing handler controls. Neither ran Lean/server/builds. The initial draft's
panic expectation is corrected to the actual intrinsic bare revert, with raw
failed exit retained in `arguments-first.log`; final diagnostics pass. A new
incremental full gate is required for this added import; checkpoint11's full
pass alone does not validate this new source.


### Checkpoint12 final validation and whole-assignment handoff

The incremental `./run-lean.sh` gate passed exit0 on committed Lean source
`84c28d8e2ba411b0f061fe06439e0c3ce2d20256`:1040default+262TestSuite jobs,
377taclets/131read-bearing/131covered exact SolKey agreement. Warm-cache wall3.5s;
peak aggregate Lean/Lake RSS1643MiB, anonymous113MiB, one Lean worker; exact
cgrouppeak920690688bytes, max/OOM/oom_kill/groupkill all0, swap.max0. The prior
post-incorporation cold/rebuild full pass and its actual12GiB cap pressure
remain separately recorded above; neither run changes any proof/test budget.
Logs: `/workspace/v14-creation-frame-evidence/arguments-full.log` and
`arguments-full-measure/summary.json`. One keyed cache/build tree is reused.

There are23owned modules and120guarded axiom outputs (75preserved+26frame+
19argument). Final guard23/0,19/19script regressions0skips, layers180core/0elaborator,
orphan/trust/automatic and whitespace checks pass. Raw docs remains exit1:
48missing/37ambiguous, exactly publication's multiset; +2inherited missing
references versus frozen46/37. The publication-relative no-lane-new gate passes;
raw checker and frozen-global delta are not relabelled green.

Final whole-assignment handoff and exact-head artifacts:
`/workspace/v14-creation-frame-artifacts/final/HANDOFF.md`, with original.patch
from frozenbase, full owned lane.patch from exact publication, recovery.patch
from reviewed incorporation, namedbranch bundle, APIs, gate/rawfailure evidence,
independent reviews and checksum manifest. MANIFEST.json binds actual export
HEAD and both checked source commits; final documentation-only changes preserve
all checked Lean blobs. Checkpoint11 and the prior original/recovery seals remain
intact. Restore bundle history for the guard's pinned incorporation ancestry.

All original Work/Backfill rows remain binding. G43 payment/stipend/asymmetry,
G36.03 prerequisites, general source/NEWBackend constructor/runtime/reference
frames, paid caller/world reconciliation and G45 fetched-byte/state/resource/
decoder correspondence are unfinished. Published old Evm memory-call/frame
certificates and narrow unpaid constructor-source consumers do exist; they do
not supply these missing NEWBackend relations. No parent or entire lane is
complete, no human scope weakening is requested, and the original persistent
goal remains unchanged/blocked. Proposed coordinator ledger updates are only
independent G44.01/G44.03/Backfill B transport preparation; existing G43/G36/G45
partial/open verdicts and reserved implementations/pins remain untouched.


## Checkpoint 13 — concrete payment cases and parallel interfaces

The human restored the unchanged original goal ACTIVE for ready owned work.
PaymentCases consumes actual intrinsic TRun.send/transfer, World.enter/finish,
World.stipend and Stipend.rule. payment_client and settlement_agrees prove
nonzero success with full functional world equality; successful_transfer adds
the actual transfer path with protected local99 and its original false bool.
Rejected send, unfunded transfer and funded body failure retain exact halts.
no_equal_transfer_halt proves the published source bare-revert versus world
revertWith(dead) boundary, rather than erasing those bytes. overflow_enters,
overflow_frame, overflow_settles and overflow_reply_rejects check an actual
entered caller and full failed-send world preservation for the finite overflow
receipt. allocation_policy_gap distinguishes source cost refusal from actual
unmetered world success. These fixed, inhabited reply tables are not a general
history-dependent receipt producer, source compiler relation or EVM gas proof.

Independent read-only finder/skeptic reviews found no false theorem. Their
wording/signature/axiom-report requests and the skeptic's overflow entry/full
settlement request were implemented. Final follow-up reviews and raw checks
are retained in the new parallel evidence export. Scoped axiom sets contain
only propext, Classical.choice and Quot.sound (some are propext only).
Lean4.24.0/Lake5.0.0-src+797c613 and KeySort2jobs passed under12GiB/no swap.
The first import-closure gate passed1041 default+262TestSuite but explicitly
skipped SolKey; a separate pinned rules check passed377/131/131. Final checks
are recorded in the handoff. Historical raw doc failures remain failures;
there is no new claim that frozen-base global documentation debt is zero.

All original Work and Backfill A/B obligations remain binding. General G43
stipend/world/asymmetry, G36.03 finite-prefix/divergence, source constructor
lowering/general frames and G45 fetched-byte/state/resource/decoder adequacy
remain open. Previous kernel/creation/encoding consumers remain preparation.
No premise, observation or budget has changed. Exact V13 head
66c08fdefbbb53c0eee111b09d1baa6277fedff5 is a sealed development dependency,
not publication or complete-lane evidence; private concrete staging is permitted.

The small parallel interface is recorded in
[PARALLEL-INTERFACE](../../tests/v14-executable/PARALLEL-INTERFACE.md), with exact
module blobs and source commit in the adjacent JSON. Its source is committed;
the external checkpoint export supplies the immutable bundle/archive checksums.


## Checkpoint 14 — exact peer emission to typed constructor catch

The staged lane-local client in tests/v14-executable/staged/PeerFailure.lean
uses actual sealed V13 ErrorEmission.execute_error/catch_error and the existing
CreationFrame.branch/caught_run/tail. constructor_catch relates the actual
slice terminal to the actual typed catch outcome; emitted_resume composes the
heap-dependent caller tail, retaining the actual supplied paidOne world. That
world is not a state of the numeric slice. The fixture derives Fits32 and two
free cells, protects words17/29 and existing memory0x55, and halts before an
unsupported ADD suffix. Capacity1023, malformed raw ca/fe and success-terminal
negative controls are explicit. The handler allocates the existing Error reason
and drops only its catch local, preserving the old heap aliases.

The client is a staged lane test, not a registered core module requiring an
unmerged producer. Exact committed inputs are materialized privately and their
hashes, checked combined tree and gates are recorded in the new handoff. No
reserved producer implementation is modified. This is substantive G44.03 /
Backfill B packet/frame transport, not general source constructor lowering,
new/try-new compiler adequacy or pinned EVM creation. All original obligations
and proof budgets remain; the original goal stays ACTIVE for ready work.


The concrete private combined commit is
58a00e6018c82128d78ba41b93d4968f1d6c47f5 (tree
2c2bb40ad13c6ff19db444336837f6c43b4c4753). Its ./run-lean.sh gate
passed1045 default+262TestSuite and pinned377/131/131 in4.05s, under
12GiB/no swap with Lean-j1 and the writer lease. This validates that concrete
staged import closure, not master publication, whole-lane adequacy or a
world/gas theorem. Eleven new scoped axiom reports contain only standard
axioms. Finder/skeptic requested explicit fixed-world labeling, immutable
producer provenance, actual same-payload RETURN and missing/failed-slice
negative controls; these were implemented. Final independent source reviews
are retained with raw diagnostics and the new exact-head export.


## Checkpoint 15 — actual receiver-result receipt preparation

PaymentReceipt.prepare derives an intrinsic table receipt from the actual
World.receiveRun result, after the actual stipend library/storage admission
check. Successful execution yields an explicit ok receipt; completed failure
yields a rejecting other receipt with actual THalt.data; noncatchable failure
or failed admission yields None. None is adapter refusal, not an encoding of
the exact halt: retain the original actual world run for that observation.
There is no fallback to the model's accepting missing-entry behavior.

receive_funded derives sender funding through the published actual enter/body/
finish witness. world_observation proves two-sided Option Bool equality with
actual World.stipend.send, under the explicit numerical checkpoint premise
sigma.selfBalance.val = (w.funds sender).val. prepare_refused_iff characterizes
refusal exactly by an error in that actual full world send. These are actual
send observation consumers, not a desired simulation hypothesis. General
producer/declaration resolution, invariant-preserving immutable receipt tables,
pending caller ledger/world alignment, full source lowering and post-world
simulation remain OPEN. This checkpoint equality is not an admitted-profile
restriction and does not close general G43 or enable final G36.03 simulation.

Inhabited controls execute actual receiver success, body failure, entry overflow
and funding refusal. New head-first installation shadows a stale failure;
an independently populated other-key Panic17 receipt and protected uint99
survive. Missing code fails admission before raw receiver failure. An actual
assumeFalse receiver reaches the published model-exhausted halt; no ordinary
intrinsic send receipt can reproduce that halt. This is model-stop evidence,
not EVM out-of-gas. A receipt derived from actual receiver bytes still leaves
the existing source-transfer bare revert versus world revertWith(dead)
difference explicit. The arbitrary rejecting-entry transfer helper is not
misstated as proof of an actual completed receive.

Separate read-only finder/skeptic reviews requested the populated unrelated
receipt and precise halt-origin/helper wording; these were implemented. Final
reviews and all raw failures are retained in the checkpoint handoff. Twenty-three
new scoped axiom reports are guarded with standard axioms only. New bounded
jobs sample aggregate Lean/Lake RSS, all-container RSS, worker count, host
headroom and cgroup peak under the unchanged12GiB/no-swap/j1 writer lease.
Prior sealed exports remain immutable. All original queues remain binding;
the same original goal stays ACTIVE while ready owned work continues.


Checkpoint15 final focused63jobs and required ./run-lean.sh1043default+
262TestSuite passed; pinned SolKey377/131/131. Actual Lean4.24.0 commit797c613,
Lake5.0.0-src+797c613 and KeySort2jobs precede RUNTIME_GATE_PASS. Measured
aggregate Lean/Lake RSS peak1712372KiB, one Lean worker, minimum host available
17338764KiB; cgroup peak393105408bytes, noOOM/swap under unchanged12GiB cap.
The initial runtime probe exited1 before any build because the Lake wrapper
prepended its config before --version; it was repaired by probing the actual
Lake binary. That raw failure is retained separately, not relabeled green.
Independent final finder/skeptic reviews accepted all fixes and explicit limits.
Gate commands/raw logs are under /workspace/v14-receipt-evidence. Raw historical
documentation failures and exact-baseline no-new-findings remain separate.


## Checkpoint 16 — concrete same-key payment history boundary

PaymentHistory executes two actual stipend sends against the same installed,
empty payable receiver, starting one credit below uint256 capacity. The first
succeeds and settles sender3→2/receiver→maximum. second_enter_fails exposes the
actual next entry refusal; second_runs catches it and retains the exact first
paid world. two_runs preserves ordered(true,false). These are completed actual
world operations, not a conditional desired simulation certificate.

source_program_runs links the same helper states to an actual two-Stmt
intrinsic Prog with full=false ordinary-send flags and one unchanged transaction table.
source_both proves prefix(true,true), protected99, net−2 and balance1.
no_fixed_receipt constructively excludes every explicit installed ExtResult
from matching both world prefix Bools. The local is overwritten; this is not
a new trace semantics or a final-Bool-only counterexample. The absent-table
control also accepts both calls. pointwise_receipts derives the changed answer
only after the actual first world operation. It does not prove a fixed
whole-program table sufficient. deferred_settlement_fails explicitly records
that the normal intrinsic program's two-credit ledger fails World.finish;
there is no claim of successful final intrinsic world settlement.

The initial almost-full world is an inhabited intrinsic fixture. No chain
reachability, Fml.inTarget, admitted independent Source/compiler or pinned EVM
counterexample is claimed. This is Backfill B/G43 preparation that exposes a
real interface-composition boundary while preserving all full-profile source,
world, observation and resource obligations. It is not final G36.03.

Separate read-only finder/skeptic reviews found no false theorem or vacuity.
Their required prefix-versus-final/target-profile limits are explicit, and the
suggested direct second-entry/deferred-settlement observations were added.
Fourteen headline/control axiom outputs are guarded with standard axioms only.
Raw normalization failures remain retained. The same unchanged goal stays
ACTIVE; all original queues and reserved producer ownership remain binding.


Checkpoint16 focused per-file and required ./run-lean.sh1044default+
262TestSuite passed; pinned377/131/131. Full gate4.94s, aggregate Lean/Lake
RSS1709420KiB, one worker, minimum host available17298976KiB, cgroup
peak388984832bytes with noOOM and zero swap. The earlier actual Lean/Lake/
KeySort runtime gate is retained with checkpoint15. A final skeptic wording
finding was fixed: Stmt.send's final false is full=false ordinary-send mode,
not a general callback-disable flag. Final independent source reviews accept
with no remaining finding; exact logs/commands in /workspace/v14-history-evidence.


## Updated private combined validation and parallel handoff

The refreshed private combined commit is
f4932cdfa66661409d4ee24ec295f901a7e9e383, tree
51b6d954efe1753446bc856e2734da37a7263d77. Its source is committed main
04aa23d5ea4d0c396488d74f1a1f252eb1874795 plus exactly the three unchanged
V13 Error modules, the byte-identical canonical staged client and its append-only
root import. Git comparison confirms only those five dependency/registration
paths differ. The actual combined ./run-lean.sh passed1048default+262TestSuite
and pinned377/131/131 in2.34s. Aggregate Lean/LakeRSS1713008KiB, one worker,
hostminimum17287980KiB, cgrouppeak387563520bytes, noOOM/no swap under12GiB.
This is a concrete private checked tree, not master integration or lane adequacy.

The updated test-lane parallel-interface-v2.json records exact source head,
module hashes, actual private head/tree and each open producer premise. Exact
Lean #check signatures are retained in interface-types.log. Original published
Stipend.Obligation still requires both Fitted and Enforced for actual compiled
gas/resource execution; no such premise has been silently discharged. Final
documentation/interface metadata changes do not change the checked Lean blobs.
All original Work/Backfill rows remain open/partial as recorded in the handoff.
The same original goal remains ACTIVE. No get_goal or Lean MCP diagnostic tool
is exposed in this runtime; supplied goal context is preserved and bounded
per-file CLI diagnostics are used. No goal administration was attempted.


## Checkpoint 17 — actual CALL operand selection and byte emission

ValueCall emits existing Backend.Program instructions and real CALL0xf1 bytes,
with empty input/output buffers. A selected PUSH1zero and three actual DUP1s
produce four buffer operands; selected typed PUSH32s then place amount,
recipient and supplied gas in reverse push order. Literal code is105bytes.
complete_bytes exposes every PUSH payload via the existing toBytesBE encoder.
No new AST, numeric evaluator, ABI codec or CALL/world semantics is introduced.

localOperands uniformly loads the actual uint local in the existing constructed
two-cell signed/uint frame. Four buffers relocate index1 to index5, selecting
DUP6 rather than the old DUP2. local_source consumes the existing source local
read; local_amount_stage/local_recipient_stage/local_correct execute actual
instructions and preserve both typed cells and every spill word. The code is
independent of sigma; distinct runtime callers99/13 produce the respective
CALL value words with identical emitted code. Local code is73bytes and
complete_local_bytes pins DUP6 plus both actual PUSH payloads and CALL.

capacity_iff derives the literal operand-prefix+7 peak from its actual opcode
choices. local_heights transports that actual height trace; frame_length derives
the exact spill≤1015 bound from two caller cells plus seven operand words.
local_correct proves DUP6's operand exists; height-only checks do not assume
that. Existing prefix_capacity supplies each intermediate bound. Populated
signed−7/uint99/spill17/29, wrong DUP2 (reads zero), swapped gas/address,
physical1017/1018 edges and full160-bit address controls are inhabited kernel
checks. Thirty-five new axiom reports are guarded with standard axioms only.

Explicit limits: supplied gas2300 is bits, not proof of forwarded gas or an
ordinary-send policy; EIP150/value stipend behavior and Fitted/Enforced remain
OPEN. The old Evm CALL takes two symbolic operands, so it is not used to justify
this actual seven-operand opcode. Scalar.run of full code is None because CALL
is unsupported; that is neither an EVM revert nor a failed source payment.
Decoder evidence is encode/decode roundtrip. frameTail is a supplied constructed
representation, not a general runtime-frame producer. Actual CALL execution,
post-call stack/world/memory, gas and failure-byte behavior, general source
lowering and fetched-byte/pinned decoder agreement remain OPEN. No source
profile/Fml.inTarget/observations or budget is changed; no G43/G45 parent closes.

Separate read-only finder/skeptic reviews found no proof or nonvacuity defect.
Finder requested full emitted payload order and explicit open frame-producer
wording; both were added. All focused raw syntax/normalization failures remain
in evidence, including the early untracked LiteralCall prototype (not a checked
dependency or deliverable). Numeric range normalization was fixed by kernel
reduction without changing values, recursion/heartbeat limits or test budgets.
The same original full goal remains ACTIVE; all original queues stay binding.


Checkpoint17 focused76jobs and required main ./run-lean.sh1046default+
262TestSuite passed, pinned377/131/131. Actual Lean4.24.0/Lake5.0.0-src+797c613
and KeySort2jobs precede RUNTIME_GATE_PASS. Aggregate Lean/LakeRSS1712644KiB,
one worker, hostminimum17264424KiB, cgrouppeak392884224bytes, noOOM/no swap.
Independent final emitter/frame finder/skeptic reviews accept all fixes.

The existing pinned EthereumJS10.1.3 Osaka package was absent after VM recovery.
The cloud runtime skill confirmed current enforced registry allowance. Exact
existing evm-vectors package/lock were copied to a single lock-hash/Node24 cache
outside the repository; strict TLS/inherited proxy, ignore-scripts and original
pins were preserved. No shared generated engine, package pin or core dependency
was edited. Runtime modules/caches are excluded from exported artifacts.

New lane-only export-value-call.lean exports actual Backend.encode bytes.
check-value-call-evm.mjs runs seven bounded cases at the existing1M gas/180s
limits. STOP and real published Failure.emit dead REVERT callees are installed
in independent worlds. Actual fetched CALL execution preserves the entire
signed/uint/spill stack and caller memory55; value1/99/13 debit/credit and nested
failure rollback/exact dead return data pass. Full160-bit destination passes.
Wrong unshifted DUP2 transfers0 rather than desired99 and is a negative control.
Entry gas observations distinguish supplied0/nonzero-value→2300,
supplied2300/zero-value→2300 and supplied2300/nonzero-value→4600. These are
bounded external observations, not universal stipend policy/Fitted/Enforced or
kernel CALL/world/fetched-decoder correspondence. Ordinary send/transfer
compilation and general resource/failure-ordering relations remain OPEN.
Raw export/install/execution logs and exact lock SHA are in v14-call-evidence.


Independent test-harness finder/skeptic reviews required exact seven scenario
identities and six-positive/one-negative roles, canonical required metadata
(including observed entry gas), identical local99/local13 body bytes with
distinct runtime locals, and the entire seeded32-byte memory word. These were
implemented together with independent exact memory/frame preamble checks.
The strengthened unchanged seven-case suite passes; no skipped/missing scan
can succeed. This is payment-balance rollback evidence for those installed
STOP/REVERT worlds, not general world/storage rollback or a transaction-level
source/compiler proof. All raw earlier harness/kernel logs are retained.


Checkpoint17 private combined commit
b7b141270725ce5b2b8b2fae06d9834c52cc87e9 (tree
2b4367fd993adcd2f225cda0f5f515a5e2e5b333) checks committed main source
9662519387b7b37adfb41cbce9323e5ecacf56ad plus the same exact three V13
producer files, canonical peer client and root import. Only those five paths
differ at the checked source. Actual full gate1050default+262TestSuite and
pinned377/131/131 passes, aggregateRSS1725636KiB/oneworker, hostminimum
17260916KiB, cgrouppeak387874816bytes, noOOM/no swap. Final docs/interface
metadata leaves all checked Lean/code/test blobs unchanged.

parallel-interface-v3.json binds real source/test hashes, private head/tree,
actual dependent #check types, bounded EVM evidence and every open producer
boundary. Original Work/Backfill obligations remain partial/open. Strict frozen
no-new-docs still fails+2 inherited missing paths; publication-relative no-new
passes0; raw checker remains exit1 at48missing37ambiguous. No waiver or parent
completion is claimed. The same original goal remains ACTIVE for ready work.
