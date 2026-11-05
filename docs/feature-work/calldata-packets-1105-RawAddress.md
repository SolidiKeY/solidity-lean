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
