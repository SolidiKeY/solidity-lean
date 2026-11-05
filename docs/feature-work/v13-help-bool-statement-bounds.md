# G21/Backfill A-B: exact architectural bounds for existing Boolean errors

Modules Solidity.Lowering.V08.LiteralFailureBoolStatement and Controls now contain
bound consumers ONLY. They reuse BoolErrorStatement/BoolErrorCompleteness; the
existing parser, compiler, syntax family and admitted Source profile are unchanged.
Coordinator registration only; no reserved implementation/registry edits.

fits_iff_span proves the original Failure.Fits conditions equivalent to the
single NATURAL bound offset+4+32*bits.length <= Failure.wordLimit. Payload length
is actually4+32*n, positive and congruent4mod32; the architectural limit is a
multiple32. Thus length cannot equal the word limit: the weak total-span bound
implies BOTH strict component guards, plus no-wrap. No modulo-word load or mere
list-length<W premise substitutes for this argument. This is an auxiliary
architectural bound, not an added Source admission predicate.

fits_at_end consumes payloadroom and proves exact endpoint safety. not_fits_one_past
proves originalFits false one byte later. It asserts no checkedRun/native failure
outsideFits. bounded_lowered derives actual Source error execution and actual
existing selected-emitter checked execution from the raw span/stack conditions.
bounded_frame adds arbitrary outside-byte noninterference for the same program.
Original Fits, stack1024, payload semantics and bounds are unchanged.

Controls use registered Flags3 and Empty declarations, nonempty caller, oldmemory
object0, accountjournal, nonempty target stack and memory sentinel7. joint directly
instantiates NEW bounded_lowered, with span/stack discharged. bounded_old_byte
instantiates bounded_frame. Exact-end cases use the existing independent Slice
at high256-bit offsets; no native gas/expansion or physical allocation claim.
Actual Source/checked-Slice payloads, empty/nonempty and unchanged unsupported
local/skip cases are captured in full. Emitted instruction count is separate from
bytecode length/gas. Source/native/world/entry/profile closure remains open.

Review caught a substantive duplication: the initial draft reimplemented the
already existing BoolErrorStatement parser/compiler. Early commit2d31533 is kept
in history; the rejected proof draft is archived as evidence. The duplicate is
removed from the FINAL working module. Both reviews confirm resolution. This
checkpoint adds bounds/registered consumers, NOT new syntax coverage. Earlier
projection/control using the lower-level theorem was replaced with direct new
bounded-consumer application. Initial parser/elaboration/heartbeat failures remain
raw evidence; no budget was raised. Final bounds/main/control MCP checks pass.

All exact helper/private dependencies, prior seals, actual vectors, scopes and
independent source/artifact reviews are exported. Private combined validation is
not standalone/full integration. Master6510c302 unchanged after fresh fetch.
Single cache retained; clean-page eviction of stopped own build outputs reclaims
RAM without deleting/modifying file contents. Original4GiB reserve/12GiB cap/no
swap and serial-j1/LEAN_NUM_THREADS1 remain. Previous resource failures stay failed.

G21/G40/G41/G42.01-.02/G42.04/G42.06/Backfills A-B remain partial. G42.03/P3 stays
readonly-external; G42.05 awaits producer. Native/runtime ABI decoding/dispatch,
unknown-memory target encoding, CALL/RETURNDATA/arbitrary worlds/static frames,
physical resources and mandatory whole-lane gates remain unresolved. Original
goal unchanged blocked. Historical Suite124/181.061s, full1/5038.87s,
cold124/5400.579s, bodyexport1 and rawdocs1/frozen86vs83 comparison1 remain failed;
prior/publication finding equality is separate. No unchanged failed heavy retry.
