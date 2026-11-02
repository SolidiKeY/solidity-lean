# V15 full-precision modular consumers

This resumes independent G46.01/Backfill A on the existing helper branch from
74f949c3ccaccf9a6a7605ddc11bfc3d3d7fa0e8, whose published base is
e7cc378c275eafe7a047c63f672bedbed2fec6ff. Frozen original base remains
2fe1f8932f96be15b00df03ba2cde46f64a87758. No original goal or branch is reset.
The five private NumericRows batches contain18 numeric/control row theorems;
ReadyNumeric separately proves ADD and CalldataExtent separately CALLDATASIZE.
None of these covers ADDMOD/MULMOD;
those original files are read only, neither copied nor adopted on this branch.

New modules are `Bridge/SolidityBridge/RoadmapV15/P10/Modular.lean` and
`Bridge/SolidityBridge/RoadmapV15/P10/ModularControls.lean`. Existing intrinsic
Backend.Scalar.step/Word, Backend.encode, UInt256.addMod/mulMod, EVM.decode/step/X
and Assembly.driverGate/driverSteps are reused unchanged. No second arithmetic
machine, decoder, source semantics or reserved adapter is defined.

Six general facts: addMod_word, mulMod_word, decode_addmod, decode_mulmod,
addmod_agreement and mulmod_agreement. The two agreement theorems quantify any
typed backend Site, any256-bit operands and complete scalar caller tail. They
prove the actual scalar result, complete charged fetched State and exact X
continuation. Gas8≤seed.gasAvailable.toNat and tail.length+3≤1024 are explicit.
Actual decoding, zero memory expansion, opcode gas/arity/output-capacity and
static-permission checks are discharged; no desired decoder, gate, execution,
frame origin or compiler simulation is supplied as a hypothesis. Seed memory,
return buffers, accounts/context and code remain in the whole resulting State.
Raw zero modulus yields0; it is not a Solidity guarded zero-division theorem.

Seven populated/boundary/combination controls plus three named negatives audit
all16 new facts/controls with only propext/Classical.choice/Quot.sound. Nonzero
maximum-word add/multiply modulo7 produce2, while premature word truncation
would produce0. Zero/max modulus, inherited-static permission, full1021-word
spill and an actual fetched ADDMOD→MULMOD sequence are checked. The sequence
retains complete ordered memory aa,bb; returnData cc,dd; H_return ee,ff; typed
caller/context/accounts and spill258,513, with precise gas/PC/execLength updates.
Whole-State equalities preserve every remaining field, not an observation subset.

Review requested an overflow negative. The suggested1022-tail does NOT overflow
this pinned local gate: its output has1023 words, although its initial1025-word
stack is outside the admitted input bound. The real negative uses1024tail and
1025output, giving actual StackOverflow; original input bound stays unchanged.
Other negatives preserve gas-before-arity, underflow, fuel and modulus-position
behavior. No state-origin claim follows from the out-of-profile guard fixture.

Focused modular03 and modular-controls07 PASS, warning-free. Earlier raw failed
proof/check attempts and exact source snapshots are retained in
/workspace/v15-evm-agreement-evidence/modular-resume-20261102. A private
arbitrary-tail proof avoids concrete-list unfolding; named boundary witness
still contains the entire original1021-word list and whole expected State.
No heartbeat/recursion/memory/fuel/test/time budget was increased.

Registered import confirmation and final structural/docs results are recorded in
this checkpoint handoff. The unchanged whole-core gate failure at Source.Horizon
300s remains failed; it is not rerun. Prior Bridge2136jobs/TestSuite286jobs and
SolKey377/131/131 passes remain separate historical gates. Runtime remains
Lean4.24.0/Lake5.0.0-src+797c613,12GiB cap/no swap, H1 reserve4GiB, serial-j1,
300s file/5400s full. Advisory clean build-output page-cache release modified or
deleted no file; direct reclaim remains denied and no guard is lowered.

All150 full opcode rows remain OPEN. Proposed G03 ledger entry: G46.01 partial
ADDMOD/MULMOD scalar/fetched/resource clauses, Backfill A; no parent closure or
generated ledger edit. Shared Cancun arithmetic is not full approved Osaka
agreement; G06B01/B02/B27, canonical driver/source/compiler frame/representation,
physical allocator/padding/read-value/calldata, account/world/call/create/return/
revert, resource adequacy and transaction/finite/infinite trace transport remain.
No new axiom, sorry, native proof shortcut, global hash injectivity, modified
profile/refusal/observation/pin or reserved source edit is introduced. No new
external compiler/EVM differential test is claimed. Work1/2/3/5 and Backfill A/B
remain partial; Work4 remains blocked on exact production prerequisites.


Registered02 PASS26.0s/2140Bridge jobs after KeySort2jobs and actual versions.
Its initial registered01 predecessor fails only the build wrapper's unsupported
Lake --version invocation before any build; raw exit1 remains retained.
Registered axioms are standard-only. Finder/skeptic source reviews cleared;
finder's proposed1022-tail error was corrected against the actual gate, and
module-map table continuity/precise prior-row counts were fixed. Next ready
Work1 leaf is EXP via published ExternalEvm.Power.reference_pow; no whole-lane
exhaustion or goal reactivation/completion is claimed by this checkpoint.
