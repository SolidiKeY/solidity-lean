# G21/G41 typed selector-local byte arguments

Modules Solidity.Lowering.V08.LiteralFailureSelectorBytes and Controls are new
owned files. Coordinator registration only. No reserved implementation edits.

`args` builds existing intrinsic RArgs with a fixedBytes4 local followed by an
arbitrary indexed list of byte-reference locals. `arguments_run` proves actual
left-to-right evaluation using the prior checked bytes-list tail. `selector_extent`
derives four-byte length from actual Source.Val constructors and excludes impossible
reference constructors. `conversion_run` proves actual same-type convRV identity.
`expression_run` discharges all published SourceAbi.selector_execute premises:
arguments, conversion and ordinary encoder output. Only actual local/heap fields
are hypotheses; no desired execution/encoding or simulation premise. Fuel is
refs.length+extra+5, using original semantics/defaults/budgets.

The actual expression allocates a fresh byte object containing the selector's
exact bytesOf followed by the existing indexed AbiEntry encoding. No hashing,
selector reinterpretation, truncation or uint8/uint32 admission is introduced.
`prefix_readback` and `body_readback` derive exact take4/drop4 results from the
intrinsic four-byte invariant. This is expression encoding, not runtime selector
matching, receive/fallback dispatch or callee execution.

A populated typed client uses selector+nonempty prior caller, byte/string objects,
tail aliases1/2/1, old object0, account journal and fresh output3. A selector-only
client proves zero-tail-argument execution. Old-object preservation consumes the
previous proved heap-bound/allocation law. Wrong selector and head-offset32
claims are rejected (actual first offset96); insufficient argument fuel times out
before allocation. Six complete normal-form packets cover selector-only, empty,
embedded0/255/128 and31/32/33byte boundaries. They are host observations of the
proved result, not external compiler/EVM tests. Actual scopes/byte totals exported.

MCP per-file diagnostics pass; focused exact-head checks, scoped axioms and
independent read-only source/artifact reviews are exported. Initial automation
and a Source.Val namespace resolution failure are retained; no limits increased.
Private validation uses the existing source/toolchain cache and exact published
SourceAbi/CustomErrors/Keccak proof-hygiene copies6510c302. Original nine V12 inputs
remain immutable development inputs and are not imported by this new Source leaf.
Published master is unchanged after fetch. Prior packets/seals are preserved.

G21/G40/G41/G42.01-.02/G42.04/G42.06/Backfills A/B remain partial. G42.03/P3 is
readonly-external; G42.05 awaits producer. Full Source/native/target decoding and
dispatch, unknown-memory target encoder, CALL/RETURNDATA, arbitrary callees/worlds,
static frames and physical resource composition and mandatory whole-lane gates
remain open. Original goal unchanged blocked. Historical Suite124/181.061s,
full1/5038.87s, cold124/5400.579s, bodyexport1 and rawdocs1/frozen86vs83 comparison1
remain failed; prior/publication finding equality is separate. No unchanged failed
heavy gate was repeated, no new peer input or profile/observation/pin change.
