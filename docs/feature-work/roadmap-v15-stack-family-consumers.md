# V15 stack-family consumers

This G46.01/Backfill A consumer checkpoint continues helper13a4b7b8d54d8e769617abf28b17987347ebd57b,
published helper base e7cc378c275eafe7a047c63f672bedbed2fec6ff and original frozen
base2fe1f8932f96be15b00df03ba2cde46f64a87758. Original/private trees and goal are
preserved; existing raw StackOps adapter is consumed read only.

Owned `Bridge/SolidityBridge/RoadmapV15/P10/StackFamilyConsumer.lean` proves six
public facts: decode_dup_family, decode_swap_family, scalar_dup_split,
scalar_swap_split, dup_family_agreement and swap_family_agreement. Every legal
Fin16 index uses real Backend.encode bytes, pinned decoder, intrinsic Scalar
operations and published reference_dup_pre/reference_swap_pre. Charged dispatch
and actual driverGate checks discharge gas3, zero memory expansion, arity,
output capacity and static checks; actual fetched driver and X follow. No
source frame origin, desired decode/gate/result or simulation is assumed.
DUP selects pre.length=n.val at depth n+1; SWAP exchanges top with depth n+1
across n middle words. Typed scalar representation is transported to actual
UInt256 lists without a second stack machine or reserved producer edit.

Explicit bounds: pre.length+tail.length+2≤1024 for both split shapes and
3≤seed.gasAvailable.toNat. DUP adds one word (maximum admitted input1023,
output1024); SWAP preserves height (maximum input/output1024). Arbitrary seed
accounts, caller/context, ordered memory/return buffers, complete code and
all other State fields are retained by whole-State equalities. Charge/PC/
execLength changes are exact. No whole-source resource adequacy follows.

Owned `Bridge/SolidityBridge/RoadmapV15/P10/StackFamilyControls.lean` has thirteen
named controls, including a full-State inhabited DUP and SWAP client for EVERY
legal index, with increasing distinct prefix, top1025, selected511 and
spill258,513. Inherited-static permission, owner/source/sender, nonzero nonce/
balance accounts, memory aa,bb; returnData cc,dd; H_return ee,ff and emitted
PUSH1 data0x80/POP prefix are preserved. Depth0/15, both capacity boundaries,
actual input1024/output1025 DUP refusal, depth-specific underflow, ordered gas
before arity, fuel, wrong depth/order/opcode-byte negatives are checked. Actual
fetched DUP16→SWAP1 composition has the complete ordered19-word result and
wholeState gas6→0,PC3→5,execLength41→43. No favorable decoder or frame oracle.

Focused stack-family03 PASS29.91s, six standard-only axiom reports. Controls02
PASS11.28s, thirteen standard-only reports. Earlier source/elaboration failures
and exact snapshots remain in /workspace/v15-evm-agreement-evidence/stack-families-20261102.
No MCP diagnostics tool is available; checks use the actual serial bounded
Lean route.12GiB/no swap,4GiB reserve,-j1,300s file/5400s full and all proof
budgets remain unchanged. Only exact receipt-bound exited owned containers are
released under H1; prior seals, sources, caches and commits remain intact.

Import/structural/docs confirmations and independent finder/skeptic reviews
are recorded in the exact-head handoff. The unchanged full-core Source.Horizon
300s failure is not rerun or waived. Raw documentation exit1 and complete
finding comparisons against helper/frozen bases remain separate. Published
reference numeric semantics does not establish approved full Osaka agreement.
All150 full opcode rows remain OPEN despite these32 family primitive clauses.
Proposed G03 entry: G46.01 partial legal DUP/SWAP emitted/scalar/fetched/local
resource clauses, Backfill A; no generated ledger change or parent closure.
Work1/2/3/5 and Backfill A/B remain partial; Work4/G47 requires production source/
ABI/V13/V14/world/frame/resource/Osaka/transaction/trace facts. Memory.PaddingCorrect
has no witness; physical allocation/read-value/calldata and symbolic compiler
paths remain open. No profile/refusal/observation/pin/hash premise changed,
no new axiom/sorry/native proof shortcut and no fresh external compiler/EVM test.

Registered01 PASS36.74s/2144Bridgejobs, KeySort2jobs, actual Lean4.24.0 and
Lake5.0.0-src+797c613; guardnull. Layers/orphans/trust/whitespace01 PASS.
Raw docs01 exit1/48missing retained; complete helper-base findings equality
PASS0, frozen-base equality FAIL1 with the same three inherited additions.
Independent finder/skeptic source and control reviews cleared; actual snapshots
match passing source. Neither reviewer ran Lean/server/build/tests or wrote files.
