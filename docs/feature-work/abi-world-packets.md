# ABI result and failure packet consumers

These modules prove observations of the existing intrinsic ABI and failure
codecs. They provide reusable G41 consumers; they do not complete ABI compilation.

## Error and Panic packets

`Backend/AbiWorld/ErrorLayout` proves exact Error selector, offset, length,
payload and padding observations. Its word-length compatibility name delegates
to `Backend/Environment/Namespace.wordBytes_length`. The append prefix/index
helpers are List identities, without memory or execution content.
`ErrorRoundtrip` proves Error decoding for representable natural lengths.
`ErrorReadWindow` handles unpadded complete reasons and arbitrary suffixes;
`ErrorOffsetWindow` handles admitted alternative offsets, including unaligned
ones, while retaining the original decoder's checks and failures.

`PanicReadWindow` reads the complete unsigned word with arbitrary trailing
bytes. Its Error rejection law extends the selector fact proved by
`Semantics.decodeError_encodePanic` in `Calculus/SoundCatch`; the core module
uses a local selector argument to avoid importing the calculus layer.
`PanicCallFrame` consumes actual typed self-call and try-call execution with
Panic code binding and clause-local dropping. The callee uses encoded revert
bytes; this does not establish source Panic provenance or arbitrary callees.

## Return observations and emission

`LibraryResultPacket` gives the existing heterogeneous uint/bytes codec layout.
`ReturnWordTransport` constructs actual indexed uint values and proves complete
ordered word readback, including arbitrary suffixes and truncated-word rejection.
Its binder-count premise selects the low-level decoder demand. It does not
prove how Source declared return types determine that count before unused
binders are discarded. Full unsigned words are supported without a byte-range
restriction.

`PacketPrefix` characterizes prefixes of the existing constant-packet emitter,
including pending pushes, reached byte writes and terminal behavior.
`CallerWordBytes` relates restored caller word cells to explicit physical byte
frame observations using the published memory interfaces. These are distinct
word-cell, physical-memory and terminal-slice relations, without an assumed
joint source-to-target simulation.

Emitter applications retain actual Fits and stack-capacity conditions. They
specialize an already supplied packet or indexed value. None reads unknown
runtime memory to encode an arbitrary ABI result; the reserved Failure slice
has not been widened. Native/EVM tests are distinct from these kernel facts.

## Validation and remaining obligations

Companion Controls modules provide inhabited populated frames, ordered byte
observations, boundary values and malformed/truncated/order/fuel controls.
ReturnWordTransport and PanicCallFrame headline axiom outputs are guarded;
`scripts/v13-abi-world-axiom-pins.json` records their scoped inventory. Global
inventory registration remains coordinator-owned.

G41 still requires unknown-memory result/error emission and uniform aggregate
signature compilation. Library and call composition still require concrete
source/frame/world/rollback and resource relations. The published runtime-frame,
readonly-call and fetched-call interfaces retain their explicit provenance and
execution-linkage obligations. These packet facts do not discharge them.
G40 entry/selector work belongs to `Backend/AbiEntry`; external function values
belong to their separate owner. No ABI admission profile is narrowed here.

The public compiler success theorem (H62/H69) and the H68 P1-REVERT status
are in [v13-public-compiler-total.md](v13-public-compiler-total.md).
