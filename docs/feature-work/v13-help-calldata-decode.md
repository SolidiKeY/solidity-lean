# G21 existing calldata abi.decode consumer

New modules Solidity.Lowering.V08.LiteralFailureCalldataDecode and Controls.
Only owned new files; Source.Calldata/Decode/Eval stay read-only. Coordinator
registers modules, Solidity.lean untouched. Published master6510c302 was fetched
and inspected before the helper rebase. Original base2fe1f893 unchanged.

The published memory-byte abi.decode arm already has a preservation/progress
proof. This new consumer proves its existing calldata-byte counterpart:
bytes_ok derives byte extraction preservation from the intrinsic cdRef shape;
arm composes actual evalE, bytesOfRV and abiDecodeData_ok with an explicit
relative data-expression triple. local_ok closes that premise using the
published typed-local law. local_run is an exact actual evaluation equation
through drop/take into abiDecodeData, not an assumed successful decoder result.

Original types.all decodable premise and original n+2 local horizon remain.
No new accepted-profile, span/wrap bound, fuel default or calldata decoder is
introduced. Logical reference length does not imply input extent; extraction
can be shorter, and the existing decoder then classifies its own failure.
Hoare results retain MemOK and NotStuck conditions; they do not promise every
input succeeds or refine the existing frontend's admitted syntax.

Concrete clients use the populated published caller/frame/heap/global state.
Actual uint8 success7, invalid300, invalidbool2,31-byte shorthead, accepted
trailingbytes, missinginput and insufficienthorizon are distinct. Memorybytes
[0,255] allocates fresh address1 and preserves old address0. Actual Source
2^64 length yields Panic.alloc before payload validation; missing length and
truncated payload revert empty. These preserve Source's actual tailBytes
ordering; no stronger native finalize_allocation agreement is claimed.
All current input bytes are losslessly rendered; byte vectors are kernel
controls, not external compiler/EVM observations. No previous output changed.

Automation first attempts retained. A wrong checkout-keyed MCP socket failed;
that transport was stopped and corrected. A45-second diagnostic after adding
an unused cold slice import timed out; removing that unused import yielded
complete minimal-closure success. No time/proof/node/fuel limit increased.
All final per-file diagnostics pass. Focused toolkit gates, scoped axioms and
complete observation validation accompany the sealed handoff. Source and
exact-artifact finder/skeptic reviews are independent/read-only, without Lean.

This is source intrinsic preservation/progress and actual execution control,
not emitted runtime decoder/bounds checking, calldata physical-memory relation,
unknown-memory ABI encoder, source/native/EVM/world/frame adequacy or closure
of full G21. Generic slice-data progress and storage-data decode consumers
remain separate ready owned proof obligations; slices/copies semantics already
exist with their original owner. G40/G41/G42 and A/B stay partial. P3/G42.03
remain readonly-external; actual arbitrary callees/world/resource and final
mandatory gates stay open. P1/P2/P3/P6/P10 published interfaces retain their
real premises. Historical Suite124/full1/cold124/docs1/frozencomparison1 and
bodyexport1 remain failures, not retried. Prior/publication documentation
multiset equality is separate. Original goal unchanged blocked; no goal admin.
