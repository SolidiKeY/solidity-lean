# G35-ADDR-RAW-1105: raw address calldata packet

Assigned published base: `b86ae4568cef6d6226f4d170360bbb089debe3fb`.
Owned checkout: `/workspace/solidity-lean`; existing branch
`codex/solidity-fullscope-20261104/vx1-contracts-environment`.
Work starts from preserved VX1 head `ea7d38a35797a58487ea878dad380b665b2308ae`.
Original VX1 base, queue, H38 producer-review holds, G07 failures and seals are
unchanged. This rebalance is a separate bounded packet for V11 integration.

## Implementation and exact premises

Execution imports only existing Source Eval/Hoare. `ArrayTy payable` is an
intrinsic dynamic memory array of address values; `payload` computes the actual
published `decodeWord` traversal of 32-byte words from the raw frame. No desired
successful run or target representation is supplied to the operation.

`decode_clean` requires the actual word below 2^160; `decode_dirty` requires
2^160 <= word and proves empty-data revert. `copy_run` is unconditional over
all frames, offsets, lengths, states and payable flags: decoder failure retains
the entire initial state; success allocates exactly its computed typed values.
`copy_dirty` quantifies every selected index and requires only index bounds and
that raw word's dirty high bits; no successful-prefix result is assumed.
`copy_observations` derives allocation, old-address preservation and all other
state preservation from the computed decoder result. `copy_zero` ignores unused
dirty words. `guarded_frame_run` requires the actual selector length four and
F.cd = selector ++ argument bytes, retaining the original ordered entry guards.
`eval_copy` requires only the typed local's actual calldata reference, and
relates the existing resolved conversion at every horizon n+2 to cdToMem.

Controls execute actual raw bytes: nonempty old heap, unequal ordered values,
clean/dirty 160-bit boundaries, maximal dirty word, dirty second element after
a valid prefix with exact state retention, both payable flag outcomes, right
padding rejection/empty zero padding, zero length, bound selector frame,
truncated/missing/oversized entry guards, local conversion and horizons 0/1.
No compiler/EVM execution or physical-memory agreement is claimed by this packet.

## Verification and resources

Lean 4.24.0/797c613, Lake 5.0.0-src+797c613. KeySort passed. Execution kernel
check passed (8.145s); Controls per-file MCP passed (11.691s), then kernel check
passed (3.742s). All observed inventories use standard propext/Classical.choice/
Quot.sound only. Full public inventory is tests/calldata-packets-1105/RawAddress/Audit.lean.
Commands, exact gate HEADs, exit/wall/RSS logs and failed attempts are retained
under tests/calldata-packets-1105/RawAddress/evidence (sealed separately).

One missing-prerequisite group stopped at 180.006s in Source.Value. Source.Ctor
was the only completed module above 60s: 74.304s. No heartbeat/recursion limit
was raised. Initial `lake build -j1` failed because this Lake has no -j option.
Lean checks use explicit -j1 and LEAN_NUM_THREADS=1. Lake gate builds are
serialized by a recorded wrapper: cached dependencies are restored with
--no-build, owned targets compile individually; foreign cache misses block
instead of starting another prerequisite rebuild. Thus a failed cache-admission
checkpoint is not a passing full library build. MCP later prepared the narrow
Eval/Hoare import closure during its bounded 79.509s initial diagnostic call;
that fact is retained rather than concealing it as cached provenance.
All calls run serially in a verified 12GiB/no-swap container with continuous
4GiB parent admission reserve. No unbounded build or concurrent Lean server.

## Reviews and integration handoff

Initial independent read-only finder/skeptic identified missing St.init import,
missing general frame binding, resolved conversion/horizon coverage and positive
payable coverage. The fixture now constructs its explicit empty Source state;
the other coverage is implemented. The private pure List/Except lifting lemma
uses the template's elementary proof, attributed locally to the published helper;
this avoids the unrelated representation/transfer closure and defines no Source
operation, compiler, allocator or owner contract. No indexed-family match was
introduced. Final independent review and actual gate outcomes are recorded in
the sealed handoff before readiness is claimed.

Coordinator registration/pins/map proposal only (no shared files edited):
- Solidity.Backend.CalldataPackets.RawAddress.Execution
- Solidity.Backend.CalldataPackets.RawAddress.Controls

Whole-lane VX1/X01/X02 completion and original H38 freeze remain open. Source
proofs are separate from native compiler/EVM tests; no external execution claim.

Final read-only finder and skeptic report no remaining semantic defect in this
bounded packet. Both confirm earlier findings resolved and the private elementary
lifting proof is reasonable within the authorized template-copy scope. Finder
verified all 37 public theorems appear exactly once in Audit.lean and no forbidden
proof/trust/budget additions. Neither review used Lean/server. Full 37-theorem
kernel inventory passed in 1.810s; standard axioms only. Final gate HEAD/outcomes,
checksums and integration blockers are recorded in the sealed handoff. No full
checkpoint or lane readiness is inferred from these focused passes.

## Adoption of scheduled 1422Z publication

Published `8bf8321873befa3f35ca31e97e5339a1baee93e6` was fetched and adopted by
merge `de78ff2369e29c5a75c4d3d64f8bbb1c0cf3e5e3`, preserving owned parent
`5d40125c420f7e453706d163e12a02729e3e573d`. All15 existing owned files are
byte-identical across adoption; the only two overlapping new paths are the
identical RawAddress modules. Source/Scoped, direct dependencies, toolchain,
Roadmap contracts and catalog generator are unchanged. Exact union/no conflict.

Both RawAddress modules are now published and centrally registered in the root
and module map; the former registration request is fulfilled. There are no
RawAddress guarded G07 pin entries: the plain #print outputs and standalone
37-theorem audit remain separate evidence. Do not report installed guarded pins.

Coordinator notice reports passing combined full/core/Bridge/CLI/axiom gates and
separate area/combined reviews under receipt sched-20261105T1422Z. That host
receipt was not read on this VM; the integration leaf document retains prospective
review wording. This is reported upstream evidence, not reconstructed local logs
or a current-branch full-build/cache receipt.

Actual adoption-head bounded runtime/KeySort and all37 theorem inventories PASS,
5.128s. Lean4.24.0/Lake5.0.0-src+797c613 and verified12GiB/no-swap/4GiB parent
reserve are recorded in evidence/publication-8bf83218. Source proofs are unchanged;
no integrated implementation was duplicated or cold foundation build repeated.
Separate read-only finder and skeptic confirm identity/union and registration;
neither used Lean/server or found a preservation defect.

No H38 approval or producer adapter arrived. InvocationEnvironment's bounded
charged ADDRESS/CALLER/CALLVALUE steps supply no Source-frame relation or Osaka
approval. Original X01 freeze/all30 catalog rescope and X02 production obligations
remain blocked. Existing original failures/seals remain unchanged.
Full-library cache/admission is checked separately at the saved handoff HEAD;
publication alone establishes neither this VM's cache freshness nor full readiness.
H41 partial owned packet remains preserved at the earlier handoff with its verified
SHA; no new delivery receipt and no on-VM ship-cache. No goal/VM reset, push or PR.

## Subsequent 1608Z prerequisite adoption

Published3ad22f66d8fc6431378c22e71823436c79dede7f was adopted by merge
2600ba7046d53a41c24046991ec04c59673a3074 from74d7e69c888f28f9f31c9128a964c8dbcd61d79d.
RawAddress source/controls, audit and direct dependencies are unchanged; no new
packet implementation was needed. Separate read-only finder/skeptic confirm
preservation and no new H38/X01/X02 producer interface. Runtime/KeySort/all37
inventories passed3.844s. Saved-head checkpoint/cache results are retained in
evidence/publication-3ad22f66; upstream full-gate reports are separate coordinator
evidence. Original partial cache packet and previous seals remain preserved.
