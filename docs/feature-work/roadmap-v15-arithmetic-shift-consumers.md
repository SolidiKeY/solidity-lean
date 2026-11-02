# V15 arithmetic shift consumers

This in-flight G46.01/Backfill A leaf continues helpera4b0818250d887fdea76e88008c5ba0708b31956,
published helper base e7cc378c275eafe7a047c63f672bedbed2fec6ff, frozen original
base2fe1f8932f96be15b00df03ba2cde46f64a87758. The coordinator changed the next
queue during its actual bounded execution; this checkpoint finishes the active
leaf before returning to P10. No subsequent numeric item is started.

Owned `Bridge/SolidityBridge/RoadmapV15/P10/ArithmeticShiftConsumer.lean` proves
sar_bitvec, sar_word, decode_sar and sar_agreement. Actual pinned UInt256.sar,
complement/shift and published signed comparison agree with intrinsic BitVec
arithmetic right shift and actual Scalar.SAR result. Existing BitVec identities
supply the complement/logical-shift/sign relation, without a new arithmetic
machine or reserved adapter edit. Count is on top, value second. Negative odd
values use floor division by positive powers, unlike SDIV's truncation toward
zero. Counts≥256 saturate by sign; their proof never constructs2^count.

Arbitrary typed Site/operands/tail consumer derives actual complete emitted
decoding, zero memory expansion, gas3/arity/capacity/static gate, whole charged
fetched State and X continuation. Explicit input tail.length+2≤1024 and3≤gas
remain unchanged. No desired decode/gate/run/frame-origin hypothesis exists.
This local reference/scalar fact is not source signed-count clamping, checked
source-language arithmetic, full resource adequacy or approved Osaka agreement.

Owned `Bridge/SolidityBridge/RoadmapV15/P10/ArithmeticShiftControls.lean` has
sixteen named controls: counts0,1,255,256,257 and maximum word; negative odd,
positive odd, minimum identity/sign fill, maximum positive saturation, full
1024-word input, ordered gas-before-arity/fuel and wrong SDIV-rounding/logical
shift/operand-order negatives. Actual fetched SAR→SMOD takes-7 shifted1 to-4,
then remainder3 to-1, gas8→0,PC3→5,execLength41→43. Complete ordered state
retains memory aa,bb; returnData cc,dd; H_return ee,ff; caller/context/nonzero
nonce/balance accounts, inherited-static permission, spill258,513 and complete
emitted PUSH1 immediate0x1d/POP prefix/code. No observation projection replaces
whole-State equalities. Maximal-count control follows the finite saturation
branch without a native evaluator or raised proof budget.

Focused execution01 PASS5.88s/four standard-only reports, controls01 PASS6.68s/
sixteen standard-only reports, warning-free. Earlier typed elaboration failures
and exact source snapshots remain in
/workspace/v15-evm-agreement-evidence/arithmetic-shift-20261102. No MCP tool is
available; actual bounded checks retain12GiB/no swap,4GiB reserve,serial-j1,
300s file/5400s full and all proof/stack/fuel/heartbeat/recursion limits. Only
exact receipt-bound exited own containers were released under H1; caches,
source, commits and prior sealed evidence remain intact.

Final registered/structural/docs gates and independent finder/skeptic reviews
are recorded in the exact-head handoff. Unchanged full-core Source.Horizon300s
failure is not rerun or waived; raw docs1 and complete helper/frozen finding
comparisons remain separate. Historical5400s124/CONNECT403/monitor failures and
disclosed lost early unsealed retry raw/timing evidence remain retained failures.
All150 full opcode rows remain OPEN. Proposed G03: G46.01 partial SAR typed/
emitted/fetched/local-resource clauses and Backfill A; no generated ledger edit.
No source/world/account/ABI/physical/padding/transaction/trace closure, new axiom/
sorry/native shortcut, global hash injectivity or profile/refusal/pin change.
No fresh external compiler/EVM test or existing-goal reset/reactivation/completion.

Latest2026-11-02 registry: current P10 fetched CALL/RETURNDATA/JUMP should consume
G45.03 execution meaning from revert-outcome-specs as an explicit typed premise;
next memory/storage G46.02/.03, environment G46.04, then newly assigned decoder
agreement G45.05-BR. Hash G46.05 and execution meaning G45.03 belong to
revert-outcome-specs, read only here. Before each new item fetch origin/master
and inspect actual publication/relayed interfaces; no foreign branch adoption.
Missing producer facts stay open and a typed premise never closes its producer.

Registered01 PASS15.80s/2165Bridgejobs and KeySort2jobs, actual Lean4.24.0/
Lake5.0.0-src+797c613; guardnull. Layers/orphans/trust/whitespace01 PASS.
Raw docs01 exit1/48missing retained; complete helper-base equality PASS0,
frozen-base equality FAIL1 with the same three inherited findings. Independent
finder/skeptic cleared final source/controls/docs/queue and passing snapshot
identity without Lean/server/build/tests. This seals the active numeric leaf;
next action is the required origin/master fetch and concrete P10 producer read.
