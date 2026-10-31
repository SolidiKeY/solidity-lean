# V14 executable consumers: independent backfill, lane blocked

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
| 4: G45.01–.02 | Open: actual scalar instruction and typed stack/frame expansion adapters using published Scalar and Evm primitives, including stack headroom. No parallel copy of reserved Scalar/Evm work was made. |
| 4: G45.03 | Published structured label proofs remain read only; execution transport of structured branch/LOOP and actual backedge execution are open. |
| 5: G45.04–.05 | Reused assembler/byte proofs named above; offset/link layout, PUSH-data handling and `decode_encode` do not prove pinned decoder/step agreement. Reserved Bridge adapter remains untouched. |
| 5: G45.06 | Open: selection/stack/control/assembly/encoding composition against actual executable runtime-byte behavior; resources, decoder agreement and integration premises are undischarged. |
| Backfill A | Partial useful preparation: actual finite prefixes, suffix transport and assembled-runtime constructor consequence. General typed frame/layout and relocation/creation composition still need integrated producers; no parent closure. |
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
