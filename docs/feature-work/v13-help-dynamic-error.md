# G21/G41 heap-backed mixed custom-error encoding

New modules LiteralFailureDynamicError and Controls under Solidity.Lowering.V08.
Master6510c302 fetched/inspected before work; Source encodeOne/encodeParts,
heapBytes, abiLayout and independent AbiEntry definitions remain read-only.
Coordinator registration only. Originalbase2fe1f893/helper/goal/seals preserved.

This family is the actual intrinsic custom-error statement with arguments
[bytes memory,uint256]. arguments_run evaluates existing typed local arguments.
marker_word proves the actual Source uint value keeps every FinW bit; no
ByteRange restriction or truncation. encoding_run reads actual heap.get data,
accepting bytes/string memory shapes exactly as heapBytes does. Its heap
representation premise is not a desired encode/evaluation conclusion.
source_run discharges published SourceCustomErrors.execute's argument and
encoding premises, deriving fullselector+payload and unchanged entire state.

layout derives the actual64-byte head, complete fullword marker, length word
and padded byte tail. abi_agreement compares the existing Source encoder with
actual indexed AbiEntry.Vals/encodeArgs; source_typed consumes that equality.
Length metadata retains modulo-word semantics for arbitrary natural lengths;
this byte identity does not prove native input admission/nonwrap/resource bounds.
No alternative AST/heap/encoder/decoder or simulation oracle is introduced.

The concrete declared Mixed error is in environment.decls and parameter typing
is proved. Populated initial state has oldobject0/alias and payloadobject1,
nonempty older locals and account journal. Generic client spans arbitrary
bytes/fullmarker and bytes/string heap tags. A bytes-typed pointer to string
memory is compatible with the existing memShape equality; this is not an
invalid RefOK fixture. Oldobject0/next2 and fullstate are preserved. Wrong
head32 (actual64), wrongmarker44 versus300 and corruptpointer2 are controlled.
The last yields stuck dangling memory outside the representation premise,
NOT certified ABI-validation revert or an admitted native input.

Five complete argument packets each from Source and independent codec cover
empty/3/31/32/33bytes, zeros/255/128, marker300 and maxuint256. Every byte is
retained and audited. These are kernel/host interpreter observations, not
external compiler/EVM pipelines. The Source execution reads supplied heap
contents; target unknown-runtime-memory encoding remains genuinely absent.

Initial combined codec MCP45 timed out; retained. Single ABI prerequisite
check passed2jobs under180s. Proof repair made word extents explicit and applied
total natural-word transport before generic word projection, then the existing
UInt8 modulo lemma. All failed/intermediate diagnostics retained; no budgets
increased. Final per-file diagnostics pass; focused gates/scoped axioms and
independent readonly finder/skeptic source/artifact reviews accompany seal.
Reviewers use no Lean/server/builds. No unchanged failed full/Suite retry.

FullG21/G40/G41/G42 and BackfillsA/B remain partial. All-profile source/target
compiler agreement, unknown-memory emitted encoders/dispatch, native/frame/
world/resource relations and finalmandatory gates remain open. Source aggregate
encoder constructors not supplied by encodeOne are not silently assumed.
P3/G42.03 RO and G42.05 producer boundary unchanged. Published interfaces keep
real premises; old9V12 staging preserved and not imported. Suite124/full1/
cold124/rawdocs1/frozencomparison1/bodyexport1 stay failed. Prior/pub doc
equality is separate. Previous kernel storage success stays resolved. No
semantic/profile/expected-output/pin change; goal unchanged blocked, no admin.
