# Y10 P6 frame/capture composition

This owned consumer uses exact P6 producer ae7d66366c3555e35bd064548ab3501c23bb7552,
base e7cc378c275eafe7a047c63f672bedbed2fec6ff. The coordinator explicitly authorized
its dependency merge on the help branch. The isolated P21 checkpoint remains
113748a8b793c71e6be5807e6606b911f368f021; HOST1 remains979c744444e47d762efd133c35cfa29db61dd206
for V17/G52. No shared engine or reserved Source implementation was edited.

[Consumer](../../Solidity/Yul/Composition/P6FrameCorrectness.lean) builds actual
WordSpan/ByteSpan values with explicit conversion from Fin words to typed uints.
`store_capture` runs actual Environment.cryptoStep MSTORE, then proves actual
Failure.Slice REVERT captures the complete snapshot from that reached byte memory,
stopping before any suffix. Stack conversion is explicit: the two engines use
different word types. Failure.Slice supports MSTORE8, not MSTORE; refusal of a
purported combined MSTORE Slice run is a deliberate negative control. No new
interpreter or opcode rule is supplied here.

`exterior` preserves every exterior byte. `represented_store` uses actual INITIAL
WordFrame, a selected live cell, explicit32-byte alignment and frame capacity to
preserve the complete reached live footprint. INITIAL WordFrame supplies physical
W-fit; capacity alone never substitutes for it. `capture_restore` takes the exact
initial caller-memory equality and uses actual Local.finish after the real byte
capture. It restores both local persistent/transient snapshots, complete caller
machine and initial represented footprint. This is the existing component-local
checkpoint, not Source/world/outer-transaction rollback or three-journal adequacy.

[Controls](../../Solidity/Yul/Composition/P6FrameControls.lean) construct actual
FrameMem/State.init and INITIAL WordFrame in both retained pipeline tags. A full
32-byte word has high byte1/low byte255; caller stack11/22 differs from live33/44,
both saved journals differ from live99/88, and exterior sentinel170 survives.
Tests distinguish lost high bits, reversed bytes, wrong selected window, wrong
checkpoint with equal payload, omitted restore, invocation identity, empty reads
at arbitrary offsets and an unreachable unsupported suffix. Pipeline tags are
retained identity, not Source evaluation-order or fresh compiler evidence.

The seven foreign producer bodies are byte-identical to the sealed bundle and
source manifest. The sole merge conflict was append-only Solidity root imports;
both complete parent import sets were retained. Focused producer closure175 jobs
passes locally, but the producer's full/Suite timeouts124 and strict/docs/inventory
failures remain in its handoff. This input is PARTIAL_VALIDATED_COMPONENTS.

FrameMem's real scalar-context restriction remains. SourceUintMemoryAt,
ArrayRepr and valid-index premises remain required when connecting Source arrays;
these pure frame laws do not construct that Source object relation. No Source heap
index is identified with a physical pointer, no allocator/gas/extent theorem is
proved, and no raw-to-clean resumption occurs. Logical heap/state is the actual
carried intrinsic State, retained by store32; it is not a new Source execution.

All24 original obligations and six general Source combinations remain open.
The P21 PublicBoundary decoder/world facts are not discharged by these local
window laws. No Source frontend/Yul admission, general compiler/session/world/G01
adequacy, native execution or fresh Source-vs-EVM comparison is claimed. G52 is
V17's. Source/Eval, Source/Machine and Source/Horizon remain read-only.

## Checked milestone

Both owned files and the registered root pass per-file MCP diagnostics. Full
merged library and SolkeyTestSuite pass through ./run-lean.sh, with actual
Lean4.24.0/Lake5.0.0-src+797c613 and KeySort exit0. Sort377taclets/131read-bearing/
131covered; strict491automatic/61budgeted/0manual/11refuted/0pending. Strict is
classification, not a fresh cumulative timing certificate. Complete-input trust
and46 scoped declaration checks pass with standard axioms only, no sorryAx.
Independent read-only finder/skeptic accepted both input integration and owned
consumer/control scope, with no outstanding finding. Raw diagnostics (including
failed first expression-normalization attempts), resource receipts and exact
signatures are retained under /workspace/vy5-composition/p6-composition-20261102/
and /workspace/vy5-composition/evidence/p6-composition-20261102-*.
No native compiler/EVM test was added or rerun; G52 remains with V17.
