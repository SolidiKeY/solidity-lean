# G21 typed storage bytes decoding consumer

New modules LiteralFailureStorageDecode and Controls under Solidity.Lowering.V08.
Source definitions are read-only; coordinator registration only. Master6510c302
was fetched/inspected before work. Frozen base2fe1f893, prior seals and goal
remain unchanged. No new peers/imported worker branches.

read_cell/read_at combine existing storage default/read progress facts with
arbitrary-invariant Hoare preservation (readAt_ns/readAt_keep already exist
separately). bytes_cell/index_cell derive actual length/byte layout from the
declared bytes.storage path; length_read/byte_read discharge correct/default
premises. Raw byte-cell reads include defaults beyond logical length; these
are not accepted source index expressions or source bounds checks.

The new substantive storage family is load_bytes for every original fuel,
count and start index: actual byte recursion preserves arbitrary P and halts
only NotStuck. Fuel0/count0 is still timeout. load_memory proves the returned
actual Data is bytes-shaped. stored_bytes and bytes_ok compose that result;
bytes_ok obtains the path proof from the real storage reference's RValOK.
arm is the actual storage abi.decode expression relative to its data triple;
local_ok closes that premise with the existing typed-local law. No assumed
successful read/decoder result or alternate evaluator/codec is introduced.
Original decodable and MemOK/RefOK conditions and fuel remain. This is
preservation/progress, not guaranteed successful termination on every input.

Actual persistent-storage fixture declares bytes packet, stores length2 and
bytes255,7, has a nonempty old heap object0 and caller memory alias/bool.
Kernel controls prove length/byte/default-cell reads, wrong-type stuck,
copy255,7 success, exhausted copy, zero-fuel-empty timeout, and actual storage
abi.decode short-head revert versus copy-timeout priority, preserving complete
state/locals. Persistent witness is inhabited; the transient read branch is
covered generically, not by an additional transient profile fixture.

Canonical32word→booltrue is HOST #eval testing only: the finite kernel
control hit maxRecDepth, and remains deferred in TERRA-TODO.md (short-block
proof decomposition, no increased limit). No Lean placeholder/axiom stands
for it. Generic local_ok is proved independently; no success-control theorem
is inferred from host testing. All complete host output bytes/statuses are
retained. No native Solidity/EVM or all-profile compiler agreement is claimed.

Initial generic load_bytes proof failed at generated dependent match equations.
The existing loadBytes_keep proof supplied the correct explicit bind/match
reduction and zero-count split; the repaired generic theorem passes MCP.
All initial failures, bad tactic-location attempts, recursion-limit failures
and deferred control are retained as evidence, not green gates. Final main
and accepted controls MCP pass with unchanged budgets. Focused checks and
actual scoped axiom outputs accompany seal. Finder/skeptic source and artifact
reviews are read-only, without Lean/server/builds; their earlier draft-success
review is superseded by the explicit final control deferral.

FullG21 and G40/G41/G42/A/B stay partial; runtime target decoder/encoder,
unknown memory, source/native/frame/world/resource adequacy, arbitrary calls,
transaction composition and mandatory final gates remain open. P3/G42.03 RO
ownership retained. Published P1/P2/P3/P6/P10 interfaces retain real premises;
old9V12 staging is preserved and not in this closure. Historical Suite124,
full1/cold124, rawdocs1/frozencomparison1, bodyexport1 stay failed. Prior/pub
doc equality is separate. No unchanged failed full retry or goal admin.
