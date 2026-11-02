# V15 P10: fetched CALL/RETURNDATA/JUMP consumer

Human H10 authorizes this helper branch from published master
`e7cc378c275eafe7a047c63f672bedbed2fec6ff`, for V14 Q31 and the V13/V16/VY3/VY4
consumers. Original V15 branches/goal and all semantic/proof/resource holds remain
unchanged. Reserved Bridge adapters, core and vendor definitions are read only.

## Early typed interface checkpoint

New module: `Bridge/SolidityBridge/RoadmapV15/P10/Interface.lean`. Namespace
`SolidityBridge.RoadmapV15.P10`. `Site op` uses existing Backend.Op/Program and
actual EVM.State, with typed prefix/suffix and an explicit nonwrapping byte-PC
bound. It constructs the complete ordered Backend.encode code in an actual
reference state; other seed fields are retained. No decoder, execution, source
frame-origin or successful call result is a premise.

Public facts: Site.code_bytes, Site.pc_nat; decode_call, decode_return_size,
decode_return_copy, decode_jump, decode_jump_if, decode_jump_dest; corresponding
fetch_call/fetch_return_size/fetch_return_copy/fetch_jump/fetch_jump_if/
fetch_jump_dest. Fetch facts equate actual on-demand EVM.step to its actual
supplied dispatch; they retain its fuel, account-call and error semantics.
They do not yet establish charged driver gate adequacy or world correspondence.

`Bridge/SolidityBridge/RoadmapV15/P10/Controls.lean` inhabits a PC3 site after a
PUSH1 containing an embedded0xf1 byte and POP, with a nonzero nine-word caller
stack, memory and distinct buffers/context. Complete encoded bytes, all six
decoders, wrong instruction/PC, zero fuel and positive-outer/zero-nested-CALL
fuel are checked. A finder/skeptic request to audit all fourteen public facts
was fixed by adding the six decoder axiom reports.

Focused interface04 and controls02 pass under Lean-j1/LEAN_NUM_THREADS1,
12GiB/no-swap/4GiB admission reserve and unchanged300s per-file budget. All14
axiom reports use only propext/Classical.choice/Quot.sound. Exact cached source
identity for EvmYul/Conform, Backend.Opcode and package manifest was verified
against the existing checked cache; no new dependency/pin/toolchain was used.
Earlier proof/output-directory failures and guard02 headroom rejection remain
raw evidence. Repository-wide registered/full gates remain PENDING for this
early relay checkpoint; the next checkpoint adds charged execution consumers.

Independent read-only finder/skeptic reviews cleared source and controls without
Lean/build/server use. No reference success/driver/world/transaction/Osaka or
full G46/G47 completion is claimed. This is an early typed interface for relay.

## Remaining P10 work

Expose actual charged/fetched CALL through EVM.call, preserving its complete
state/outcomes rather than a payment Boolean. Expose return-data size/copy and
JUMP/JUMPI using original gate ordering, bounds, jump membership and state.
Run populated/negative/combination controls, scoped axioms and bounded registered
closure/full gates; distinguish supplied dispatcher fuel from nested-call fuel.
Actual source-lowering/ABI/physical frame/allocator/driver resource and full
world/transaction/trace/Osaka adequacy remain original open obligations.

## Runtime ownership evidence

Automatic approval review rejected a broad stopped-container cleanup because a
name prefix alone did not establish ownership. It did not execute. Exact
current-turn P10 container IDs were then individually verified against their
receipt hash, full workload command, unique barrier, working directory and
exited state before H1 cleanup; each removal has a retained receipt. No force,
unrelated process/container, cache, source or sealed artifact was removed.
Denied page-cache reclaim and the unchanged admission floor remain recorded.

## Charged execution checkpoint

New modules: `Bridge/SolidityBridge/RoadmapV15/P10/Execution.lean` and
`Bridge/SolidityBridge/RoadmapV15/P10/ExecutionControls.lean`. Nineteen further
facts give Site.recover, six dispatch equations, six checked encoded-site
transitions and six X-continuation equations. Combined with the early fourteen
facts, the helper has33 general public facts; controls are counted separately.

Site.recover requires exact actual code and PC representation, never a desired
execution/frame-origin property. checked_call matches the real original
driverGate, then actual stack.pop7 and EVM.call, returning the real whole
account state and UInt256 result. No gate-success, call outcome, decoder result
or desired simulation is an input hypothesis. Return-data copy invokes actual
MachineState.returndatacopy; jumps use the real stack/PC operations. All original
ordered gate errors propagate. Six X equations compose each checked instruction
with its actual continuation, retaining the precise dispatcher/nested-call fuel.
No new machine, opcode AST, source semantics or reserved adapter is defined.

Ten populated18-field execution controls cover a real successful nonzero-value
CALL, actual underfunding and inherited-static zero-value success; return-data
size and empty/nonempty copy; JUMP, both JUMPI branches and JUMPDEST. The funded
call debits account7 from29 to22 and credits non-precompile account31 with7;
context accounts11/19 retain distinct balances41/43. Underfunding30 tests the
actual funding root, not those context balances. Code/PC/stack/gas/count, complete
ordered buffers, account balances/nonce, active words and caller context remain
explicit. Nonempty-copy expected memory stays the actual opaque ByteArray.write
expression: this is not a proof that allocator zeroes0 is empty or a physical
byte-copy witness. Empty copy at the exact return-data boundary needs no such
premise. Invalid bounds, gas-before-arity/bounds, stack underflow/overflow, static
value refusal, wrong PUSH-data jump target and low dispatcher/nested fuel are
negative controls. The supplied jump array matches Backend.jumpdests for the
concrete jump images; equality to opaque reference D_J is NOT proved.

Finder requests for a populated JUMPDEST and actual RETURNDATASIZE overflow
were fixed; both independent read-only reviews cleared final source and controls
without Lean/build/server use. Focused execution08 and execution-controls03
pass, including19 new general-fact and10 populated-control standard-only axiom
reports. Together with the early fourteen reports, all33 general facts are
audited. Earlier bounded structural proof failures, including unchanged200000
heartbeat failures, remain raw evidence; successful proofs use structural
state/list cases without increased limits.

Current-master runtime evidence confirms Lean4.24.0 (797c613) and
Lake5.0.0-src+797c613; lake build Solidity.KeySort reports two successful jobs.
The first driver invocation failed only JSON encoding of the already pinned
hyphenated core package name, after KeySort passed. Corrected master-driver02
builds the reserved actual Driver closure successfully:1081jobs/110.365s,
guardnull,12GiB/no-swap, serial-j1. Only runtime config/workdir/PATH bindings
changed; package/toolchain pins and all proof/test/fuel budgets are unchanged.
The original shared cache now contains master-dependent artifacts; later old
branch checks must use normal source-keyed Lake validation, not assume its
previous transitive oleans still match. Old committed proof/evidence seals stay
unchanged. Final registered/full/structural/docs gates are recorded separately.

Remaining original obligations include source/ABI/compiler frame origin and
production-world correspondence, physical allocator/padding/read-value adequacy,
exact whole-driver/resources, canonical D_J/Osaka approval, arbitrary permitted
callee source agreement, transactions/fees/nonce/log rollback and finite/infinite
source trace transport. No parent G46/G47 closure or fresh native compiler/EVM
test is claimed. The original queue remains parked under H10 pending its
producers; this helper supplies concrete fetched execution interfaces for relay.


Registered validation on the unchanged source now passes all four mandatory
Bridge targets: `lake build SolidityBridge Velvet VelvetExamples SolidityVelvet`
(2136 jobs, exit0,2463.471s; aggregate Lean/Lake RSS3996930048bytes,
cgroup peak5589319680bytes). All43 P10 reports are standard-only:33 general
facts and10 named execution witnesses. The inherited property suite also passed
36 rule cases ×200 samples with seed20261025; this is separate evidence.

The independent `lake build SolkeyTestSuite` succeeds (286 jobs), followed by
`./scripts/check-solkey.sh`:377 taclets parsed,131 read-bearing, table covers131,
annotations match the unchanged pinned rules. Their bounded combined run exits0
in1466.318s, cgroup peak6175383552bytes, guardnull. These are kernel/import and
existing native summary/property checks, not lane-specific external compiler/EVM
differential execution.

The required `timeout 5400 ./run-lean.sh --bridge` DOES NOT PASS:full02 stops at
the unchanged300s per-file guard in Solidity.Source.Horizon, wrapper125,
container137,1161.535s. Its source SHA256 is
f579466b9b961c899a4cb2bbe3948a8143284b186e8035c30395c6b89a7d9cd4,
identical to helper-base e7cc378c275eafe7a047c63f672bedbed2fec6ff;
all core sources have zero diff against that base. That source differs from the
original frozen base; this comparison is NOT a passing baseline execution.
No unchanged failed full run or reserved repair is attempted. The owner must
restore this target's checkability within the original budget (or provide a
verified same-source/toolchain checked cache); no larger budget is requested.

Full01 was rejected before launch for a36MiB headroom shortfall. H1 advisory
clean-page-cache release, without deleting or changing files, restored4.55GiB
and full02 passed fresh admission. Direct memory.reclaim/drop_caches remained
permission denied. Caps12GiB/swap0, reserve4GiB, serial-j1,300s per Lean file and
5400s per full command remain unchanged. Earlier raw failed attempts remain;
source snapshots for P10 execution retries begin at05 (earlier retries retain
hash metadata/raw errors). Historical5400s124,403 and disclosed lost early
unsealed retry evidence remain separate and are not reconstructed.

Evidence is /workspace/v15-evm-agreement-evidence/p10-help-20261102.
Staged-file structural, vendor and complete documentation finding comparisons
are recorded separately. Raw documentation exit1 remains a failure:the helper
base already adds three findings against the frozen base (one Arms ambiguity,
two inline-assembly missing paths). Only a zero-new comparison against the exact
helper base can pass; the frozen comparison remains failed, with inherited debt.
Proposed ledger scope is G46.06/G47 P10,V14Q31:partial fetched execution clauses
for six opcodes. No generated ledger or full150-row status is changed.


Final staged checks pass:188 core modules/zero elaborator reach,1302 reachable
modules/zero orphans, trust scan, whitespace and all three vendor checksum sets.
The complete missing/ambiguous multiset comparison against helper-base master
has zero additions/removals. Raw docs still exits1 with48 missing references;
against the frozen base the same three inherited master findings remain added.
The first lightweight wrapper stopped before trust execution because its script
is non-executable; the supported bash invocation then passes without chmod.
All partial logs, invocation failure and final command receipts are retained.
