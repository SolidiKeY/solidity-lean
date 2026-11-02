# V15 Bridge decoder agreement

G45.05-BR was explicitly assigned to this lane on2026-11-02. Before starting,
fresh fetch inspected master4b80f466ae153f1bdb7e74a85a6c18db4eb4d521: Backend
and Bridge sources unchanged from helperbase e7cc378c275eafe7a047c63f672bedbed2fec6ff.
No unrelated publication or foreign branch adopted. This follows BALANCE
checkpointa9ce069400b857baf48505adff0cbc3ad969aadd; frozen original base remains
2fe1f8932f96be15b00df03ba2cde46f64a87758. Core/reserved/vendor/pins stay read only.

Owned `Bridge/SolidityBridge/RoadmapV15/P10/DecoderAgreement.lean` gives six
public laws: parser_agreement, invalid_iff, no_immediate, decode_all,
fetched_dispatch and clz_invalid. referenceOp maps existing intrinsic Backend.Op
to the existing reference Operation.EVM datatype, covering80 fixed instructions
and all16DUP/16SWAP/5LOG indices. Actual emitted bytes at arbitrary typed Site
and nonwrapping PC derive decoding and fetched dispatch without a desired decode,
execution, scanner or source-frame premise. Every other state/fuel/cost component
remains native. This is decoding/dispatch, not gas/gate/execution adequacy.

The pinned parser has no CLZ constructor or entry. Its actual default is SOME
INVALID for undefined bytes, including Backend CLZ byte0x1e. invalid_iff proves
exactly CLZ and INVALID map to native INVALID. CLZ is NOT excluded from Backend
or the admitted profile, and this is NOT Osaka semantic correspondence. The
first uncompiled draft wrongly expected parser none; failed source/raw evidence
are retained and the actual source proved the INVALID behavior. No vendor edit,
new premise, decision, exclusion or favorable interpretation repairs this mismatch.

Owned `Bridge/SolidityBridge/RoadmapV15/P10/DecoderAgreementControls.lean`
has16 named controls. Nonzero stack258,513, gas2600, exec41, owner7/source11,
static permission, memory aa,bb, returnData cc,dd, H_return ee,ff and calldata
11,22,33 inhabit actual Site. Complete ordered code is
[0x60,0x1e,0x50,0x01,0xf1,0x5b], PC3; embedded CLZ byte is PUSH1 data30,
while starting at that data byte gives INVALID. All DUP/SWAP/LOG depths have
exact packets. Wrong opcode, undefined byte, empty decode versus implicit STOP,
and core CLZ acceptance versus native INVALID are meaningful controls.

Focused nonpush04 PASS37.08s/six standard-only axiom reports; controls02 PASS5.13s/
16 reports. The core well-founded decoder did not reduce via decide in an earlier
new control; it now consumes the published decode_encode theorem. Finder asked
for exact LOG packets rather than isSome: corrected. Namespace/option/finite-case
failed drafts remain raw. No axioms/sorry/native shortcut or budget increases.
MCP is unavailable; serial supported bounded checks retain -j1, original proof/
stack/recursion/fuel,300s file/5400s full,12GiB/no swap and H1 fourGiB OS reserve.

General PUSH0..32 immediate agreement is the next adapter increment, not claimed
by these117 non-immediate instructions. Charged execution, scanner/compiler source,
physical memory/padding/allocator, world/frame/resource/Osaka/V13/V14/G45.03/
transaction/finite-infinite trace obligations remain open. P10 awaits exact G45.03
execution-meaning packet QG45. Hash G46.05 is owned by revert-outcome-specs.
All150 full opcode rows remain OPEN; no fresh external compiler/EVM tests ran.
Original main/private branches and blocked persistent goal remain unchanged.

Registered/structural/docs gates and independent source/artifact reviews are
recorded in exact-head handoff. Raw docs1, helper/frozen complete comparisons,
unchanged Source.Horizon300s full failure, original5400s124/CONNECT403/OOM/monitor
failures and disclosed lost early unsealed retry raw/timing remain distinct.
Proposed G03: partial G45.05-BR actual non-immediate decoder targets only;
no generated ledger or global coverage edits.

Final registered01 PASS46.47s/2185Bridgejobs, KeySort2jobs, Lean4.24.0/
Lake5.0.0-src+797c613, guardnull. Layers/orphans/trust/whitespace PASS.
Raw docs exit1 retained; helper complete equality PASS0, frozen equality FAIL1
with same three inherited findings. Independent finder/skeptic source reviews
cleared; count wording corrected to six laws covering117 instructions.
