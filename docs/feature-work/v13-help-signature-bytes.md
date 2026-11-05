# G21/G41 heap-backed encodeWithSignature

New modules Solidity.Lowering.V08.LiteralFailureSignatureBytes and its Controls.
Coordinator registers; no reserved implementation or registry edits.

`signature_read` consumes actual local-pointer/heap-object fields, including
existing bytes/string memory compatibility. `expression_run` derives all three
premises of published SourceAbi.signature_execute: actual ordered RArgs execution,
signature read and ordinary tail encoding. Its actual RExpr.abiEncode expression
returns a fresh memory reference and exact SourceKeccak.afterLiteral allocation
of four hash bytes followed by AbiEntry.encodeArgs of the arbitrary byte-list.
Fuel is refs.length+extra+5 under original semantics, not a default/budget change.
No encoder/evaluator-success premise or new decoder is introduced.

`object_preserved` derives non-freshness from an actual present object and
Heap.bounded, then uses published alloc_other. `reference_preserved` retains the
actual local/heap identity of old byte references. These allow repeated aliases
and signature/argument aliases, with no disjointness hypothesis. These are Source
heap facts, not target physical frame or world transport adequacy.

The populated client has signature/argument alias1 and tail aliases1/2/1, old
object0, nonempty caller and account journal. Actual output is object3. A separate
signature-only client proves actual execution with zero encoded arguments.
`pinned_prefix` consumes and discharges the existing toyFixed Keccak pin via the
published byte-prefix transport. It makes no collision/native-call assumption.
Wrong32-byte-hash prefix and swapped ordered body are rejected; one unit of
expression fuel times out before argument effects. Six complete normal-form
packets include signature-only, empty, embedded0/255/128 and31/32/33byte payloads.
The packets are host observations of the proved result, not additional native
execution or compiler/EVM evidence. Exact sizes/bytes/axioms are exported.

Automation failures are retained. Initial controls used a reserved identifier and
hit200000 heartbeats normalizing the empty-codec application; explicit codec
normalization fixed elaboration without a raised budget. MCP diagnostics and
focused checks validate the actual final files. Separate read-only source and
artifact reviews use no Lean/server/builds; final results are exported.

Published master6510c302 is unchanged after fetch. Validation remains the existing
private combined tree with exact published SourceAbi/SourceCustomErrors proof
hygiene inputs and hash-bound semantic sources. No new peer input is used.
Older seals/observations and unrelated untracked serial configs are preserved.

G21/G40/G41/G42.01-.02/G42.04/G42.06/Backfills A/B remain partial. G42.03/P3 is
readonly-external; G42.05 awaits its producer. Full Source/native/target dispatch,
unknown-memory target ABI encoder, CALL/RETURNDATA, arbitrary-world/static-frame
and resource composition and mandatory final gates remain unresolved. Original
goal unchanged blocked. Historical Suite124/181.061s, full1/5038.87s,
cold124/5400.579s, bodyexport1, rawdocs1/frozen86vs83 comparison1 stay failed.
Prior/publication complete finding equality is separate. No unchanged failed
heavy command was repeated; no source/profile/pin/observation/budget change.
