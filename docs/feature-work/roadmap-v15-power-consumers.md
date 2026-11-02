# V15 power consumers

This independent G46.01/Backfill A increment continues the same helper branch
from462937fd2a4cd517b5cafc9a66ab94c573ba2175. Published helper base is
e7cc378c275eafe7a047c63f672bedbed2fec6ff; original frozen base remains
2fe1f8932f96be15b00df03ba2cde46f64a87758. Original/private work is preserved.

Owned modules are `Bridge/SolidityBridge/RoadmapV15/P10/ExponentConsumer.lean` and
`Bridge/SolidityBridge/RoadmapV15/P10/PowerControls.lean`. Seven general facts
reuse the published ExternalEvm.Power.reference_pow, intrinsic Scalar.Word/step,
actual UInt256.exp, Backend.encode, pinned decoder, charged driver and X.
No arithmetic machine, decoder, source semantics or desired execution oracle
is introduced. The arbitrary typed operands and tail theorem discharges actual
decoding, EXP gas calculation, memory expansion, arity/capacity/static checks
and whole-State execution. Explicit premises retain input tail.length+2≤1024
and adequate seed gas. A separate theorem proves the actual local EXP charge
is at most1610 for every256-bit exponent, yielding a uniform-gas consumer.
The exponent is the second stack word; its zero case costs10 and its nonzero
byte length costs10+50*(1+log256 exponent). This local bound is not compiler
resource adequacy, approved Osaka correspondence or a general driver theorem.

Twelve named controls and seven general facts have standard-only axiom reports
(propext, Classical.choice, Quot.sound). Nonzero2^3,0^0,2^255,2^256 wrap,
maximum-word square and1^maximum-exponent exercise the actual representation.
A complete1022-word spill inhabits the admitted1024 input bound. Actual fetched
EXP→ADDMOD preserves complete ordered state: memory aa,bb; returnData cc,dd;
H_return ee,ff; source/sender/accounts, spill258,513 and full emitted code,
with exact gas/PC/execLength changes. No observation projection is substituted.
Wrong byte-length gas, wrong operand order, gas-before-arity, underflow and
fuel negatives preserve the real errors. The capacity negative uses1024tail
and1025output, outside the admitted input profile:1023tail would not overflow
this local output-only gate. It grants no expanded compiler profile.

Focused power06 and power-controls06 pass with seven and twelve standard-only
reports respectively, no warnings. Prior proof failures, source snapshots and
raw receipts remain in /workspace/v15-evm-agreement-evidence/power-resume-20261102.
Power03 had compiler exit0 but monitor125 and is NOT a passing kernel gate;
a dependent controls attempt was mistakenly launched before inspecting that
receipt and failed, also retained. Power04 admission125 ran no Lean. Runtime
completion-fence repair462937fd subsequently passed independent synthetic,
positive and negative probes; current checks use its unchanged fail-closed
active monitoring,12GiB/no swap,4GiB reserve,serial-j1,300s/5400s bounds.
Only exact receipt-bound exited owned containers were removed under human H1;
no caches, source, commits or sealed evidence were deleted. Direct reclaim
remains denied. No proof/stack/heartbeat/fuel/time limit was increased.

Registered import, structural/docs comparisons and independent finder/skeptic
results are recorded in the exact-head handoff. The unchanged whole-core
Source.Horizon300s failure stays failed and is not rerun. Earlier SolKey and
TestSuite passes stay historical. Raw docs exit1 and complete frozen-base
finding comparison remain distinct from zero-new-findings versus helper base.
Finder requested the real output-capacity negative; it is included with its
out-of-profile limitation. Skeptic confirmed EXP representation, charge order,
whole-State preservation and the finite counted-step lemma's terminal limitation.

All150 full opcode rows stay OPEN. Proposed G03 entry is G46.01 partial EXP
scalar/fetched/local-resource clauses and Backfill A, not a generated ledger
edit or parent closure. Work1/2/3/5 and Backfill A/B remain partial; Work4/G47
needs production source/ABI/V13/V14/frame/world/resource/Osaka interfaces.
Memory.PaddingCorrect has no witness; physical allocation/read-value/calldata,
canonical jump driver, arbitrary calls/accounts/create/return/revert and full
transaction/finite/infinite trace composition remain open. Approved per-run
hash premises, observations, refusals, pins and profile are unchanged. No new
external compiler/EVM differential test or automatic goal reactivation is claimed.

The first registered gate passed2142jobs in21.77s. Its predecessor failed
before admission due to an existing Docker name; no workload ran. The first
docs comparison found a new basename ambiguity from Power.lean; the owned
module was renamed ExponentConsumer.lean rather than editing reserved docs.
Renamed-source and registered confirmation are recorded separately below.

Renamed confirmation: exponent-renamed02 PASS11.80s; controls-renamed02
PASS8.88s; registered03 PASS12.18s/2142Bridgejobs and KeySort2jobs, guardnull.
Layers/orphans/trust/whitespace02 pass. Raw docs02 exit1 retains48missing;
complete helper-base finding multiset comparison passes zero additions/removals.
Frozen-base comparison remains failed with the same three inherited findings.
Independent finder and skeptic cleared final code, rename, statements, controls
and snapshot identity; neither ran Lean/server/build/tests.
