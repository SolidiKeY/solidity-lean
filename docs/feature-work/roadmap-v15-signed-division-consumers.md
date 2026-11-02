# V15 signed division consumers

This independent G46.01/Backfill A increment continues helper57764018b213c60c5a03451f9921464c7ea21bfb,
published helper base e7cc378c275eafe7a047c63f672bedbed2fec6ff and original
frozen base2fe1f8932f96be15b00df03ba2cde46f64a87758. Existing private signed
comparison rows contain SLT/SGT; they do not prove these division/remainder
consumers. Their sources stay read only, neither copied nor adopted.

Owned `Bridge/SolidityBridge/RoadmapV15/P10/SignedDivisionConsumer.lean` proves
six public facts: signed_div_word, signed_mod_word, decode_sdiv, decode_smod,
sdiv_agreement and smod_agreement. Published SignedOps.sdiv_step/smod_step
supply arithmetic against the actual UInt256 operations. Pure word observation
of their existing intrinsic numeric machine result, explicit quotient/remainder
range theorems and Scalar.sgn_word/toWord_ofInt transport to the actual typed
BitVec scalar representation. No arithmetic semantics is reimplemented. The
bounded toWord representation is NOT extended to arbitrary negative integers
below -2^256. No account/payment/world consequence follows from the arithmetic
projection. Reserved numeric/Widths producers remain unchanged.

Both arbitrary-Site/operand/tail theorems derive actual emitted decoding,
zero memory expansion,5-gas/arity/capacity/static gate, whole charged fetched
State and X continuation. Original input tail.length+2≤1024 and5≤seed gas
remain explicit. Complete seed account/context, code, ordered memory and both
return buffers survive; no desired execution/frame-origin/decoder supplied.
The first stack word is dividend. Raw SDIV truncates toward zero and SMOD has
the dividend sign. Raw divisor zero yields0; minimum divided by -1 wraps. These
facts do NOT prove Solidity zero/overflow exception policy or source lowering.

Owned `Bridge/SolidityBridge/RoadmapV15/P10/SignedDivisionControls.lean` checks
twenty named controls: all four sign combinations for both operations using
nonexact7/3; zero; minimum wrap/identity/remainder; raw int8-boundary128 followed
by the EXISTING pure signedClean result-128; full1024 input; actual fetched
negative SDIV→SMOD; ordered gas-before-arity/fuel and wrong floor-division,
remainder-sign and operand-order negatives. The width-cleanup equality is a
separate pure consequence, not a physical or source-checked execution claim.
Every successful fetched fixture retains full State with memory aa,bb;
returnData cc,dd; H_return ee,ff; nonzero nonce/balance accounts, caller/context,
inherited-static permission, spill258,513 and emitted prefix with immediate
byte0x05. The sequence -17/3=-5 then -5 remainder3=-2 has exact gas10→0,
PC3→5,execLength41→43 and complete ordered stack[-2,258,513].

Focused signed-execution01 PASS6.80s/six standard-only reports, warning-free.
Controls03 PASS7.41s/twenty standard-only reports, warning-free. Early failed
word elaborations, controls parser failure and pre-admission container-name
conflict remain with exact snapshots in
/workspace/v15-evm-agreement-evidence/signed-consumers-20261102. No other
container was touched after that collision; globally unique labels were used.
No proof/heartbeat/recursion/stack/fuel/process/time budget changed. Checks use
the actual bounded serial route (no MCP available),12GiB/no swap,4GiB reserve,
-j1,300s file/5400s full. Only exact receipt-bound exited own containers were
released under H1; source/caches/commits/sealed evidence remain intact.

Final registered/structural/docs gates and independent finder/skeptic reviews
are recorded in the exact-head handoff. The unchanged full-core Source.Horizon
300s failure remains failed, not rerun. Raw docs exit1, helper-base zero-new
findings and frozen-base inherited findings stay separate. Earlier full5400s124,
CONNECT403, monitor failures and disclosed missing early unsealed retry raw/
timing evidence remain historical failures, not reconstructed or relabelled.

All150 full opcode rows stay OPEN. Proposed G03 entry: G46.01 partial SDIV/SMOD
scalar/emitted/fetched/local-resource clauses and Backfill A; no generated
ledger edit. Work1/2/3/5 and Backfill A/B partial; Work4/G47 blocked on actual
production source/ABI/V13/V14/world/frame/Osaka/resource/transaction/trace
producers. Memory.PaddingCorrect still has no witness; physical allocation/
read-value/calldata/compiler-path adequacy remain open. Shared reference
arithmetic is not full approved Osaka correspondence. No global hash injectivity,
new axiom/sorry/native shortcut, changed profile/refusal/pin/expected observation,
new external compiler/EVM differential test or goal reset/reactivation/completion.

Registered01 PASS44.87s/2162Bridgejobs and KeySort2jobs, actual Lean4.24.0/
Lake5.0.0-src+797c613, guardnull. Layers/orphans/trust/whitespace01 PASS.
Raw docs01 exit1/48missing retained; complete helper-base equality PASS0,
frozen-base equality FAIL1 with the same three inherited findings. Finder and
skeptic independently cleared statements, controls, bounded representation,
source snapshot identity and documentation; neither used Lean/server/build/tests.
