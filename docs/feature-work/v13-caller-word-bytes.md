# V13: published caller-word restoration to ABI bytes

New owned modules Backend.AbiWorld.CallerWordBytes and CallerWordBytesControls
consume the actual published InternalFlow.RuntimeFrame.Bytes interface and P6
Physical.WordFrame, plus the unchanged indexed AbiEntry codec. No producer edit,
new evaluator/AST, trust shortcut or source profile change. Coordinator registers.

word/values construct the actual validated uint256 indexed value for every Fin
Evm.W, including300 andmax, without ByteRange. word_encoding proves the existing
32big-endian bytes equal actual encodeArgs. recovered consumes actual numeric
restoration, physical MSTORE execution and initial WordFrame. typed consumes
actual StateRepr/captured ReprV and returns preserved typed representation,
actual byte execution, reached physical frame and complete ABI bytes. Runtime
code depends on destination/temporary, NOT saved: saved arrives on the stack.
This is a runtime scalar store observation, not an unknown-memory array encoder.

raw_revert consumes the published REVERT step over the reached live byte image;
outside_byte preserves bytes outside its physical span. Numeric word machine,
Environment crypto byte machine and Failure slice remain distinct execution
APIs. Their published relation and read agreement are used, never word/byte
identity or an assumed combined fetched execution. No Error/Panic wrapper is
inferred from a raw uint ABI packet;32zero bytes are still nonempty payload.

Uniform inhabited fixture uses the existing populated CompileExamples source
state with two aliased arrays and a distinct object. setLocal/setVal derive
StateRepr for EVERY saved uint. Real numeric mload3 reads it onto the stack;
loaded_then_restored composes actual numeric instructions. Paired physical stack
is explicit INITIAL input, not a claim about byte-MLOAD or arbitrary call origin.
The physical live set covers ONLY scalar cell3; preservation of arrays/aliases
is a typed StateRepr fact, not a whole-heap physical image. Physical W-fit is
explicit/derived from initial image, never from frame capacity alone.

Actual byte-store, rawREVERT and independent encodeArgs observations include
0,9,300,max in full32-byte vectors. Controls reject symbolic-slot representation
and300-to44 truncation; sentinelbyte7 survives. Symbolic rejection is not an
ABI/runtime revert or source admission decision. All generic conditions are
discharged in typed_application; physical and numeric tails remain nonempty.

Published master advanced70f3f358 then312ed47a. Helper rebased preserving both
pre-rebase heads/old commits in task-backup refs and all sealed artifacts. Replay
conflicts involved earlier already-integrated storage/control drafts: exact
published final files retained. New consumer preserved. No master push/merge.
Validation now runs directly on this rebased helper checkout, using the SAME
cache/toolchain and a capped container on the SAME VM. Old private nine-source
V12 tree and old container preserved/stopped; no new peer transfer or VM/goal.

Per-file diagnostics, focused checks, complete outputs/scoped axioms and separate
read-only finder/skeptic reviews are exported. Reviewers run no Lean/server/builds.
H1clean-page reclamation restores admission without deleting cache contents.
Lean4.24.0/Lake5.0.0-src+797c613 unchanged; original proof/time/node/fuel budgets.

G21/G40/G41/G42.01-.02/G42.04/G42.06/Backfills A/B remain partial; G42.03/P3 stays
readonly-external and G42.05 needs its full producer/consumer closure. Source
lowering/native input/output agreement, all-profile decoder/dispatch, aggregate
runtime encoding, call-world/callback/library/resource composition and mandatory
whole-lane gates remain open. Original goal unchanged blocked. Historical
Suite124/full1/cold124/docs1/frozen-comparison1 and prior failures stay failed;
no unchanged failed heavy gate rerun. Omitted LiteralFailureBytesReadback still
has an unresolved ErrorRoundtrip dependency; this consumer does not import it.
