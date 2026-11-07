# G21 packed byte-reference expression

New modules Solidity.Lowering.V08.LiteralFailurePackedBytes and its Controls
consume the existing Source encoder and typed argument/value representations.
No semantic/decoder/registry edits; coordinator registers new modules.

`part_run`/`parts_run` prove actual packed-mode heap reads. The prior ordinary
encoder theorem could not be reused directly because its mode is false; the
initial attempted reuse failed and is retained. `encoding_run` derives ordered
concatenation without offsets/length headers/padding, preserving both contexts.
`args_run` evaluates actual RArgs local expressions with original count-derived
fuel. `expression_run` evaluates the actual RExpr.abiEncode encodePacked branch,
returning a reference at state.heap.next and the exact Heap.alloc result. No
encoder-result or evaluator-success premise is assumed: only ordered actual
local-pointer/heap-object equations. Aliases and bytes/string memory objects
remain allowed. Fuel is count+extra+4; no default or proof budget changes.

`populated` discharges all representation facts for alias1/2/1 in a caller with
old object0, account journal and nonempty locals. `fresh_output` observes output
object3, preserved old object0 and next4. Full state equality comes from actual
expression execution. Packed collision [1],[2] vs [],[1,2] is positive; ordinary
ABI distinguishes them. A wrong padded-result claim is rejected. Empty and
0/255/128,31/32/33byte controls produce complete concatenation vectors. These
host-rendered vectors are codec observations, not a new native pipeline.

This Source family does not prove target unknown-memory encoding, Source/native
agreement, arbitrary callees, CALL/RETURNDATA, world/static frames or physical
resource adequacy. G21/G40/G41/G42.01-.02/G42.04/G42.06/Backfills A/B remain partial;
G42.03/P3 remains readonly-external and G42.05 awaits its producer. Full lane gates
remain unresolved. Original goal unchanged blocked. Historical Suite124,
full1/cold124/bodyexport1/docs1/frozen86vs83 comparison1 remain failures, separate
from prior/publication equality. No unchanged failed heavy gate was repeated.

Validation uses the existing capped private tree with exact published SourceAbi
and SourceCustomErrors proof-hygiene inputs6510c302; source bindings are exported.
This is private combined development validation, not standalone/full integration.
Prior seals and vectors are immutable. Separate finder/skeptic source and final
artifact reviews are exported; no reviewers use Lean/server/builds.
