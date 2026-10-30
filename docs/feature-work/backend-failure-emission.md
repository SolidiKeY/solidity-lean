# G38: failure and return emission

Assigned base: `50658f41061b366d6e503d1e8a3a324a281e9fca`.
Branch: `codex/solidity-independent5-20261029/failure-emission`.
Checkout: `/workspace/scratch/failure-emission-assigned`.
The original clean checkout on branch `work` at
`dedb3aee5743025aeb6d8f7219c9b6b9c1e00e5d` is preserved untouched.
This lane imports no other new lane and edits no reserved implementation.

This is an exact instruction-slice component, not a source-to-bytecode,
whole pinned-EVM, full ABI-shape, catch-dispatch or whole-world rollback proof.
G37/G42/G47 and the source/backend composition obligations remain with their
owners. Gas exhaustion, memory expansion, the calling convention and code
placement still require integration. Existing observations, exclusions,
refusals, target predicates and approved profile are unchanged.

## Source and feature anchors

Manifest IDs are `assertBuiltin`, `requireBuiltin`, `revertBuiltin`,
`errorDeclarations`, `returnStatement`, `tryStatement` and `catchClauses`.
There is no `tryCatch` ID at this base. Local evidence points to
`Syntax/Elab.lean`, `Syntax/Scoped.lean` and the error-declaration frontend
files; this component does not change their partial verdicts.

The current intrinsic `RevPart` constructors are `bytes`, `sel`, `word`
and `mem`; `RevPart.evalT` and `TRun.revertData` in
`Solidity/Semantics/Run.lean` evaluate and concatenate their bytes.
`Stmt.revertData`, assert lowering in `Solidity/Syntax/Elab/Arms.lean`,
`Semantics.encodePanic`, `encodeError` and `selectorBytes` in
`Solidity/RevertBytes.lean` remain the read-only source of payload bytes.
`Roadmap.Outcome.success` and `.revert` carry exact byte observations.
G04 R04/R29 and the current payload-free `Evm.Machine` revert remain parent
composition obligations. Nothing here revisits source failure semantics.

## Queue and checkpoint 1 handoff

| Item | State |
|---|---|
| 1: typed input and opcode emission | Done: focused gates and independent reviews passed |
| 2: independent byte memory, stack tails, terminal slices | Done: kernel proofs, controls and independent reviews |
| 3: intrinsic observations and discriminating controls | Done: proofs, controls, independent reviews and focused gates |
| 4: local checkpoint/unwind and nested failure | Done: proofs, inhabited nested witness, reviews and focused gates |
| A: arbitrary payload chunking, tails and address bounds | Proved with checkpoint 2 |
| B: concatenation, distinction, input preservation, external vectors | Done: composition proofs,12 Osaka vectors, independent reviews and focused gates |

`Input` distinguishes empty failure, panic (bounded machine code), Error
reason bytes, already encoded custom-error bytes and ordinary return bytes.
Its `bytes` function reuses the existing ABI functions. Custom bytes include
the already evaluated selector and arguments: this is not a declaration or
ABI encoder. `digits` is only a machine-immediate encoder.

`writes` emits PUSH1 byte, PUSH32 address, MSTORE8 per byte, in increasing
address order. The final instructions are PUSH32 length, PUSH32 offset,
RETURN or REVERT. `writes_decompose` pins each selected byte and address
after exactly three instructions per preceding byte (`writes_length`).
`writes_append` proves arbitrary chunk concatenation and offset advancement;
`emit_length`, `panic_length` and `reason_length` pin lengths without a small
payload cap. `Fits` records machine-word/half-open-address bounds for the
later execution theorem. MSTORE8 deliberately introduces no padding writes;
the unused final word bytes must retain their initial values.

`Gap.lean` was checked against only pre-existing modules before payload
emission: Panic(1) has 36 bytes, crosses a word boundary, ends `[0,0,0,1]`,
and differs from Panic(0); bare backend REVERT encodes only `fd`.
`EmissionChecks` adds empty/custom exact byte vectors (custom at offset 5),
panic selector/tail, a 33-byte crossing at nonzero address, Error length,
return, wrong endian/offset/order/terminal and concatenation controls.
These are kernel proofs, not external-EVM agreement tests.

Independent read-only finder and skeptic reviews used no Lean server.
Both confirmed operand order and existing ABI reuse. They identified missing
emitter controls, exact byte vectors and handoff/registrations. Finder also
identified the unfinished offset arithmetic proof and requested an exact
per-byte decomposition theorem. Those findings have been addressed; follow-up
read-only finder and skeptic reviews both cleared checkpoint 1. A concrete Error-length reduction hit the default recursion
budget; it was replaced by `reason_length`, without raising any budget.

## Runtime and evidence

Read AGENTS, intrinsic Gate G0, parallelism/contributing, the local
lean-verify skill, current G01/G04/G06/G02, the actual scope decisions and
roadmap impact document. No Lean MCP or get_goal tool is exposed, so per-file
checks use actual Lean CLI with `--tstack=131072 -j1`.

Actual tools: Lean 4.24.0, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake 5.0.0-src+797c613.
The VM enclosing cgroup is 16 GiB; host swap is zero. systemd scopes are
unavailable and direct child-cgroup creation is denied. An offline Debian
container enforces `memory.max=12884901888`, `memory.swap.max=0`, one CPU,
`LEAN_NUM_THREADS=1`, with only assigned source and the read-only toolchain
mounted. The broad initial mount was rejected by automatic review; the
narrow offline alternative was accepted. Repository writer lock is held by
the runner throughout each check. The original work checkout is not mounted.

`lake -f .failure-emission.lakefile.toml build Solidity.KeySort` passed:
`Build completed successfully (2 jobs).`, exit 0, elapsed 1 second,
cgroup peak 25,534,464 bytes (warm repeat with explicit `-j1`).
The cold preceding KeySort run reported `Built Solidity.KeySort (1.0s)`
and `Build completed successfully (2 jobs).`, peak 158,109,696 bytes.
RUNTIME_GATE_PASS applies only to this actual toolchain/runtime check.

Exact logs and the capped runner are saved under
`/workspace/scratch/failure-emission-evidence`.
The alternate lakefile changes only weak Lean arguments to add `-j1`, and
is not a tracked package/configuration change. Full closure gates, final artifacts and later checkpoint commit IDs will be recorded as they run.
No inherited failure is waived by historical results.

Checkpoint 1 gate record (2026-10-29):

| Command | Actual result / evidence |
|---|---|
| `lake -f .failure-emission.lakefile.toml build Solidity.Backend.Failure.EmissionChecks` | Pass, 11 jobs, exit 0, 5s, cgroup peak 300,802,048 B; `cp1-build.log` |
| `lake ... env lean -j1 --tstack=131072 Solidity/Backend/Failure/EmissionChecks.lean` | Clean, exit 0, 3s; sampled aggregate RSS 431,192 KiB, cgroup peak 253,952,000 B; `cp1-rss-check.log`. Summed RSS includes shared mappings. |
| `node scripts/check-layers.mjs` | Pass: 168 core modules, 0 reach the elaborator; `cp1-layers.log` |
| `node scripts/check-orphans.mjs` | Pass: 770 reachable, 0 orphaned, 0 not allowed; `cp1-orphans.log` |
| `bash scripts/check-trust.sh` | Pass: 785 sources, 241 inventoried sites, 0 findings; `cp1-trust.log` |
| `bash scripts/check-doc-paths.sh` | Fail: 46 missing references; `cp1-doc-paths.log`; identical output from untouched exact base in `base-doc-paths.log` (diff exit 0). No new findings; inherited failure is not called passed. |

Headline axiom sets are pinned with `#guard_msgs`: only `propext` and
`Quot.sound`; no new axiom, recovery hook or proof-budget override.
The final CLI checks supplement the focused module build because no MCP exists.
Independent review summaries are saved in `cp1-reviews.md` in the evidence
directory. At checkpoint 1, checkpoints 2–4 and final closure validation were still outstanding; their later results are recorded below.

## Checkpoint 2 and backfill A handoff

`Slice` imports only existing Opcode and Roadmap.Contracts. Its memory
functions, PUSH decoder, `step` and `run` do not import or mention the emitter.
Stack entries are existing intrinsic `Roadmap.Word` values. MSTORE8 truncates
the value to its low byte; RETURN/REVERT pop offset then length and read exact
bytes. Unsupported instructions/underflow produce none; a terminal ignores
all remaining instructions. Arbitrary initial memory and stack tails survive.

`putBytes_frame`, `getBytes_putBytes`, `putBytes_append`, `getBytes_congr`
and `getBytes_suffix_write` prove the independent memory laws. `run_writes`
then proves actual emitted writes against those semantics, with only
`a + payload.length ≤ wordLimit`. `run_emit_suffix` and `run_emit` yield the
exact state and existing Outcome observation for `Fits`: base and length
are representable machine words, and the entire half-open interval fits.
The suffix theorem quantifies over arbitrary code, including another emitter.
`address_in_bounds`, `tail_untouched`, `chunkWrites_eq` and `run_chunkWrites`
cover all chunk counts/sizes, empty chunks, allocation endpoints and arbitrary
untouched tail bytes. No 32/64/4096-byte payload cap is assumed. The last byte
may be at wordLimit-1; the terminal length itself must fit one word.

A skeptic found that the first generic run theorem alone omitted the real
stack-capacity boundary. The generic theorem remains unchanged, but `Slice`
now independently checks every reached pre/post height in `stackSafe` and
exposes `checkedRun`. `stackSafe_writes`, `stackSafe_emit_suffix` and
`checkedRun_emit_suffix` prove checked execution given two free slots:
`initial.stack.length + 2 ≤ 1024`. `empty_stack_boundary` proves that boundary
is exact for empty emission. The controls include 1022-word success and a
1023-word rejection. This is an architectural boundary, not a scope exclusion.
Neither interpreter models gas/expansion charges, code loading/PC execution,
whole-world state or catching. The exact byte semantics and the stack check
are local instruction-list results; external pinned-EVM composition stays open.

`SliceChecks` includes a literal instruction program independent of `emit`,
a nonzero patterned initial memory and a two-word tail; underflow and reversed
operand negatives; an independent 0x01aa-to-aa truncation; crossing writes;
untouched before/end/final-word bytes; nonobservable zero padding after the
slice; arbitrary chunk combination; and checked terminal suffix noninterference.
Headline axiom pins admit only Lean's standard `propext`, `Quot.sound` and,
for the checked stack proof, `Classical.choice`. No new axioms are introduced.

Actual focused target:
`lake -f .failure-emission.lakefile.toml build Solidity.Backend.Failure.SliceChecks`:
12 jobs, exit 0, 3s, sampled aggregate RSS 318,328 KiB, cgroup peak 149,315,584 B
(`cp2-build.log`). Correct and Slice were separately checked/built clean;
the earlier failed diagnostics are retained as failed attempts rather than
rewritten to green. Fresh final per-file diagnostics and static gate outputs
are saved with the checkpoint. Finder and skeptic reviews are read-only
and use no Lean server; both follow-ups cleared the stack-bound fix and all remaining concrete findings.

Final checkpoint-2 diagnostics: Slice exit 0 (1s, RSS 286,932 KiB,
cgroup peak 93,937,664 B); Correct exit 0 (2s, RSS 321,908 KiB,
peak 123,232,256 B); SliceChecks exit 0 (4s, RSS 298,148 KiB,
peak 104,697,856 B). Logs: `cp2-Slice-diagnostics.log`,
`cp2-Correct-diagnostics.log`, `cp2-SliceChecks-diagnostics.log`.
Static gates (`cp2-static.json`): layers exit 0 (168 core, none reach frontend),
orphans exit 0 (773 reachable, 0 orphaned), trust exit 0 (788 sources,
241 inventoried sites, 0 findings); doc paths exit 1, output byte-identical
to exact base (46 inherited missing references). No inherited failure is green.
Independent final reviews are saved in `cp2-reviews.md`.

## Checkpoint 3 handoff

`Observe` imports the existing `Solidity/Semantics/Run.lean` read-only.
`HaltObserves` and `ResultObserves` are observation relations on the committed
`THalt`/`TRes`, not replacement source semantics. `HaltObserves.functional`
and `ResultObserves.functional` prove uniqueness. Primitive `.panic` is the
existing assert tag and observes Panic(1); all other panic codes already
arrive as `revertWith` data. Empty require/revert preserves empty bytes;
`revertWith` preserves every byte, including malformed payloads. Divergence
and exhaustion have no adapter result; full resource/session behavior is
not silently reinterpreted. Ordinary success starts from already ABI-encoded
bytes. General source return encoding and modifier continuation composition
remain parent obligations.

`assert_false_intrinsic`, `require_false_intrinsic`, `revert_bytes_intrinsic`
and `custom_parts_intrinsic` prove equations against actual source functions.
The custom proof retains existing `customSelector`, `selectorBytes` and ABI
argument bytes without a new encoder. Observation corollaries keep that
exact selector and arguments. `inputOfResult_sound` and `intrinsic_emission`
connect existing finite byte results to checked instruction execution under
`Fits` and two-free-slot boundaries. The output equals the original immutable
input payload for every initial machine memory; no mutable alias can change
the input List. Return and revert with identical bytes are distinguished.

`ObservationChecks` instantiates a real empty Contract and `State.init`;
uses actual typed false/true expressions, evaluated custom parts, Error(boom)
and ordinary return bytes; and combines actual assert evaluation with the
checked emitter. Existing decoders have inhabited positives and malformed
negatives. Wrong selectors retain full otherwise valid Panic and Error
bodies, so rejection cannot be explained by truncation. Reviewer-requested
`wrong_observation` and source-level negatives refute assert-as-empty,
Panic(0), require-as-panic, swapped custom arguments and return-as-revert.
Malformed bytes still observe exactly even when catch decoders reject them.
Adapter rejection of diverge/exhausted is pinned explicitly.

Focused target: `lake -f .failure-emission.lakefile.toml build
Solidity.Backend.Failure.ObservationChecks`, 38 jobs, exit 0, 2s;
aggregate RSS 736,816 KiB, cgroup peak 185,835,520 B (`cp3-build.log`).
The unchanged AST module replays its existing unused-variable k warning;
new modules are clean. Current intrinsic Run prerequisite built in 89s,
peak aggregate RSS 965,028 KiB, cgroup peak 572,313,600 B.

G02's cache A1 issue was reproduced: bare per-file elaboration could not
find a fetched Eqns olean. Lake lean reproduced it too. The current
Lake-selected synthetic trace artifacts for Eqns and Hashes were materialized
from the private cache; paths and SHA256 hashes are recorded in
`materialized-current-artifacts.json`. No source artifact was selected by
name alone. The failed attempt is retained as `observe-cache-missing.log`.
Fresh per-file diagnostics, guarded axiom pins, independent final reviews
and static gate outputs accompany this checkpoint. `tests/failure-emission/check-imports.mjs`
checks every owned module's closure and the independence of Slice/Gap,
supplementing the shared checker without editing its closed CORE list.

Final checkpoint-3 per-file diagnostics: Observe exit 0 (1s, aggregate RSS
703,176 KiB, cgroup peak 152,326,144 B); ObservationChecks exit 0 (2s,
RSS 715,332 KiB, peak 162,500,608 B). New files have no errors or warnings.
Static gates in `cp3-static.json`: shared layers pass (168 core, none reach
frontend); task-local imports pass (9 owned modules, 0 findings); orphans pass
(775 reachable, 0 orphaned); trust pass (790 sources, 241 inventoried sites,
0 findings). Docs exit 1, output still byte-identical to exact base's 46
missing references, never classified passed. Both independent follow-ups
cleared all concrete source/control findings; `cp3-reviews.md` records them.

## Checkpoint 4 handoff

`Checkpoint` imports only independent Slice. `Local.Journal P T` and
`Local.Checkpoint P T` retain separately typed persistent/transient snapshots
and an explicit caller machine. They are local snapshot records, not source
state/term IR. Instantiating P/T with the source/world owners' actual store
projections, their mutation journal and real frame boundaries remains open.
`CheckpointRel` independently states success commit and revert restore;
`finish_rel`, functionality, snapshot projections, idempotence, outer rollback
dominance and success-after-inner-rollback are proved without emitter imports.

`Local.execute` first runs the actual checked instruction slice and captures
its Outcome, then applies those rules. `execute_emitter` and
`execute_checkpoint` compose both results. `execute_failure` restores the
named P and T snapshots and the caller's entire machine, while retaining the
exact copied payload; `execute_return` retains live stores and emitted memory.
`nested_failure` composes two actual failed emissions through an explicit
intervening local continuation. It does not implement or assume source catch,
call or whole-world rollback semantics. Those remain G37/G42/G47 obligations.

`UnwindChecks` instantiates different store types Fin17/Fin19, outer values
(1,2), middle (7,11), deep (13,17), resumed (15,18), and four distinct memory
markers. It proves the inner and outer executions and their nested composition,
including inner payload de-ad and different outer payload be-ef-00-ff. The
caller memory at address31 is restored to48 while the copied failure payload
still contains de-ad. Separate relation negatives reject a wrong persistent
and a wrong transient snapshot. Success commits the live state and success
after an inner rollback retains the intermediate snapshot.

The local relation and outer-rollback axioms are empty; actual execution and
nested witnesses use only Lean's standard propext, Classical.choice and
Quot.sound, with exact guarded pins. A record layout parse error in the
initial witness was repaired with an explicit constructor; the memory marker
control then passed. No statement, budget or exclusion was weakened.
Focused target `lake -f .failure-emission.lakefile.toml build
Solidity.Backend.Failure.UnwindChecks`:15 jobs, exit0, elapsed0 seconds
(subsecond module check), aggregate RSS293,036 KiB, cgroup peak103,899,136 B
(`cp4-build.log`). Both read-only reviews found no semantic defect; both final
follow-ups cleared guarded pins and the corrected concrete witness.

Final CP4 per-file diagnostics: Checkpoint exit0 (subsecond, RSS232,708 KiB,
peak80,351,232 B); Unwind exit0 (subsecond, RSS242,872 KiB, peak79,593,472 B);
UnwindChecks exit0 (1s, RSS271,924 KiB, peak83,922,944 B). Logs are
`cp4-Checkpoint-diagnostics.log`, `cp4-Unwind-diagnostics.log`,
`cp4-UnwindChecks-diagnostics.log`. Static gates (`cp4-static.json`):
shared layers pass; owned closure pass (12 modules,0 findings); orphans pass
(778 reachable,0 orphaned); trust pass (793 sources,241 inventoried sites,
0 findings). Docs exit1 is byte-identical to exact base's46 missing references.
Independent final review record: `cp4-reviews.md`. No whole-group claim follows.

## Backfill B handoff and external vectors

`run_two_writes` proves that both write blocks execute while
preserving the stack tail. `disjoint_payloads` proves both original immutable
input lists can be read back exactly, for either ordering of disjoint regions.
`concatenated_emitters` proves that any second complete emitter, including one
with overlapping addresses/different class, is unreachable after the first
terminal. `return_revert_execution_distinct` proves different execution results
for identical payload bytes and initial memory. No global source/world state
is assumed or inferred. `CompositionChecks` includes a genuine overlapping
write negative, two executed regions, ignored overlapping complete emitter,
and same-bytes/different-terminal control. Headline axioms are guarded.

Focused target `lake -f .failure-emission.lakefile.toml build
Solidity.Backend.Failure.CompositionChecks`:14 jobs, exit0,1s,
aggregate RSS284,860 KiB, cgroup peak101,949,440 B (`backfill-build.log`).

The optional external test was possible. `tests/failure-emission/Export.lean`
exports actual Backend.encode output; vectors.json contains exact byte arrays,
not an independently reimplemented compiler. The runner independently states
finite expected Panic/Error/custom/return payloads and expected terminal status.
All12 cases pass on Osaka: empty revert/return; Panic(1)/Panic(0x12);
Error(boom)/33-byte reason; Denied(uint256) with word7;65-byte raw failure/return;
overlapping ignored suffix;1022-word tail completion;1023-word stack overflow.
The Denied selector is also independently checked with pinned noble Keccak.
Every case checks output bytes, exception/status, stack contents/height and
every applicable before marker (nonzero offsets) and every after marker, so a rounded overwrite is discriminated.

Reference versions: EthereumJS EVM10.1.3, Common10.1.2, util10.1.2,
noble/hashes2.4.0; Nodev24.19.0. Existing lock SHA256:
`fd223698b68dd5cf9dc1b59589c61da6c0131c3f68af65f7c26a3d5ac0498829`.
Actual vectors SHA256:
`1be88148266f4c7e7a438d399b1731f55ac62a02d0fa245c372a75c339323899`.
The dependency install was task-local, lifecycle scripts disabled; core has
no new dependency. Replay is offline under the same12 GiB/no-swap cap,
100,000,000 gas,5,000,000 host steps and120-second timeout, matching existing
reference budgets. Actual replay:exit0,1s, aggregate RSS58,908 KiB,
cgroup peak72,687,616 B (`osaka-replay.log`). Exact result/provenance files live
in tests/failure-emission and the evidence directory. These are bounded
external emission tests, not source-to-bytecode, full ABI or whole pinned-EVM
proofs. Full generic byte-memory and world/call bridges remain open.

Final backfill-B per-file diagnostics: Composition exit0 (subsecond,
RSS135,716 KiB, cgroup peak80,404,480 B); CompositionChecks exit0
(subsecond,RSS267,112 KiB,peak81,424,384 B). Static gates
`backfill-static.json`: layers pass; owned imports pass (14 modules,0 findings);
orphans pass (780 reachable,0 orphaned); trust pass (795 sources,241 sites,
0 findings). Doc paths exit1 is byte-identical to exact base's46 missing
references. Both independent final reviews cleared source/proofs/replay and
verified saved source/vector/provenance hashes. Their wording fixes (module
versus namespace, and offset-zero marker applicability) were applied.
Review record: `backfill-reviews.md`. All assigned implementation/backfill
items were covered at this checkpoint; final full/import-closure validation
and committed final handoff were still pending then. Their completed results
are recorded in the final section below.


## Final assignment handoff

All four component checkpoints and backfills A/B are complete against the
assigned base. This completes this preparation lane only. No global manifest,
coverage verdict, source semantics, Evm implementation, approved profile,
refusal or target predicate was changed. Whole source-to-bytecode composition,
gas/memory-expansion correspondence, generic byte-memory integration, general
return ABI encoding and real call/world/catch rollback remain open integration
obligations with G37/G42/G47 and the prerequisite owners.

Committed checkpoints (full hashes):

| Item | Commit |
|---|---|
| 1 | `af931bab70fbf1babd753ca9880f6427348b0e52` |
| 2 and A | `4cb5d0aff8b4e71e2de0726869bb408a69b4719b` |
| 3 | `5a0af45cac74d2003afdf6e8b42618b86373f123` |
| 4 | `43e72020157130cf982e5158a5e992f5416ab392` |
| B and external vectors | `24f0937d7e61cbc8f9ee02d6c7fe235829a51c0b` |

The final documentation commit and full committed head are recorded in the
external absolute-path HANDOFF.md after committing this section; no empty
result-marker commit is needed. The component's exact current source anchors
are Run.lean THalt:58, THalt.ofData:70, require:799, assert:803,
RevPart.evalT:936 and TRun.revertData:948; Roadmap/Contracts.lean Outcome:367;
RevertBytes.lean selectorBytes:33, encodeError:50 and encodePanic:54.
The earlier sections give the theorem names and premises. In particular,
`checkedRun_emit_suffix` needs `Fits` and two free operand-stack slots;
`intrinsic_emission` additionally needs the existing intrinsic result's
`inputOfResult` equation, and `Local.nested_failure` needs both emitted slices'
address/stack side conditions. CheckpointRel is independently stated over
separately typed persistent/transient snapshots; it is not a theorem about
whole Solidity worlds. No small fixed payload bound appears in the arbitrary
write/chunk/frame/composition theorems.

Final commands run in the saved offline runner with actual Lean4.24.0,
Lake5.0.0-src+797c613, LEAN_NUM_THREADS=1, explicit -j1 and the real12 GiB
aggregate/no-swap cap. The saved alternate lakefile adds only -j1 to weak Lean
arguments; the private toolchain wrapper serializes actual Lean processes.
It changes no proof or test budget. The package remains dependency-free.

| Final gate command | Actual result / decisive evidence |
|---|---|
| `./run-lean.sh` through `run-capped.sh` | Pass, exit0,9734s. Default build:765 jobs; SolkeyTestSuite:262 jobs; `solkeycheck: parsed 377 taclets, 131 read-bearing, table covers 131`; `solkeycheck: OK — annotations match /reference-solkey.key`. Peak sampled aggregate RSS11,276,044 KiB; cgroup peak12,884,901,888 B, cap12 GiB, swap.max0. `final-run-lean-recovered.log`. Derived17 actually passed157s; no historical OOM or37 mismatches were waived. |
| For each of14 owned modules, Solidity.lean and tests/failure-emission/Export.lean: `lake -f .failure-emission.lakefile.toml env lean -j1 --tstack=131072 <file>` | All16 passed, no warning/error diagnostics, exit0,18s; RSS1,390,996 KiB, cgroup peak1,852,895,232 B; `final-diagnostics-materialized.log`. Guarded headline axiom pins passed, using only standard propext/Quot.sound/Classical.choice where applicable, no new axiom. |
| `node scripts/check-layers.mjs` | Pass:168 core modules,0 reach elaborator; `final-layers.log`. |
| `node tests/failure-emission/check-imports.mjs` | Pass:14 modules,0 import/independence findings; `final-imports.log`. |
| `node scripts/check-orphans.mjs` | Pass:780 reachable,0 orphaned,0 not allowed; `final-orphans.log`. |
| `bash scripts/check-trust.sh` | Pass:795 sources,241 inventoried implementation/recovery sites,0 findings; `final-trust.log`. |
| `bash scripts/check-doc-paths.sh`, final and untouched exact base | Raw checker fails exit1 on46 missing references on both. Outputs byte-identical: no-new-findings gate passes. `final-docs.log`, `final-base-docs.log`, `final-static.json`. The raw inherited failure is not called a pass. |
| Fresh Export.lean JSON versus committed vectors.json | Pass:all12 exact vector objects identical; `final-static.json`. |

The first final direct sweep passed all14 owned files but failed at the root
because Lake's synthetic cache traces did not materialize11 import .olean files.
Those exact current trace-selected artifacts were materialized from the private
source/toolchain-keyed cache, with hashes recorded in
`materialized-final-artifacts.json`; the complete16-file repeat then passed.
`final-diagnostics.log` remains a failed attempt, not relabeled green.

Polling/environment interruptions left the Docker build alive but cleaned up
its host log/lock clients. No source writes or other heavy checks occurred in
those intervals. The same container's complete log was recovered, its initial
bytes matched the original log exactly, and a foreground canonical writer-lock
and log client was reattached. No build step was restarted or skipped. Actual
container limits and serial compiler execution remained in force throughout.
The original partial log and lock-guard attempt are retained as evidence.

Final independent finder/skeptic audits used no Lean server or builds and
found no further implementation/control/ownership blocker. Finder's namespace
and historical-status wording corrections are fixed here; its fresh Emit
check request is satisfied by the complete final sweep. Every checkpoint's
review findings/fixes remain in its saved review record. Final review follow-up
and exact ownership/source-hash audits are saved with the external handoff.

Absolute saved artifact locations:
`/workspace/scratch/failure-emission-artifacts/original.patch`,
`/workspace/scratch/failure-emission-artifacts/HANDOFF.md`,
`/workspace/scratch/failure-emission-evidence`, and
`/workspace/scratch/failure-emission-artifacts/SHA256SUMS`.
The evidence archive excludes private caches, node_modules and toolchain
symlinks; those caches remain on this VM for reuse. The external handoff records
actual final head, observed elapsed interval, final review results and checksums.
No scope question is outstanding. No push, merge or PR was performed.
