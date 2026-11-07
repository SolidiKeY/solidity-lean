# Typed packet materialization

TypedPacketMaterialize.execute composes actual indexed encodeArgs with the
published literal byte materializer. A nonempty supplied packet has exact
checked REVERT guard tail.length+4≤1024: two existing offset/length operands,
plus two transient pushes. This sufficient canonical observation does not
restrict any Source admission. Empty output has a separate baseline.

Initial numeric WordFrame cells disjoint from the packet interval survive;
all exterior bytes and caller tails are preserved. The unguarded Environment
runSlice result is separate and does not assert hardware stack bounds.

The scalar42/bytes[0,255] client has128complete bytes at0, disjoint old cells18/21.
It proves tail1020 success,1021 refusal, empty REVERT and wrong-offset32 negative.
This materializes bytes specialized from supplied typed Vals; it does not load
unknown runtime memory, prove Source lowering or external world/rollback/gas.

Proposed registrations/abi-world rows: Solidity.Backend.AbiWorld.TypedPacketMaterialize
(generic typed packet execution/frame/guard consumer) and
Solidity.Backend.AbiWorld.TypedPacketMaterializeControls (populated client/boundary
controls). Roots/maps unchanged pending coordinator integration.
Original G21/G41/G42/Backfill queues remain partial and blocked on their actual
Source/runtime/byte-load/call/world/resource producers. Prior failures retained.
