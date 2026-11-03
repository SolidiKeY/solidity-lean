# G21 closed failure lowering

Source failure expressions with constant payloads, lowered through the
published terminal emitter (`Lowering/V08/`). From the v13-abi-world lane.

## Proved

- `LiteralFailureLowering.lean`: `literalInput` is a syntactic compiler for
  closed `assert(false)`, `revert()`, `revert("…")`, `require(false[, "…"])`
  and literal panics; `emitLiteral` emits the terminal code. `*_source`
  theorems run the actual `evalE`/`execS`; `literalInput_sound` and
  `literal_lowered` (with `assert_lowered`, `reason_lowered`,
  `require_lowered`) give the target terminal bytes. Effectful or non-literal
  arguments are refused.
- `BoolErrorLowering.lean`: custom errors with a closed list of boolean
  arguments. `encoded`/`payload` compute the ABI payload, `source_run` runs the
  source statement, `emitted_run` the target. `emit` takes the boolean list as
  a meta-level input (a constant-payload emitter, not a function of the
  statement); `lowered` pairs the two facts through the shared payload.
- `SliceFailureLowering.lean`: calldata-slice evaluation in the existing
  evaluator (`accepted`, `reversed`, `beyond`, `exhausted`, `accepted_toEnd`).
  `lowered_reversed` pairs the source revert with the empty terminal emitter;
  the target side does not depend on the slice expression, so this is a
  source-side slice result plus an empty terminal, not a lowered bounds check.
- `*Controls.lean`: concrete clients, old-memory and low-horizon controls,
  wrong order/length/byte-order negatives.

## Open

Runtime-value encoders, reading unknown memory or calldata, emitted bounds
checks, catch semantics, source-world simulation.

## Source ABI failure consumers (sched 2026-11-03)

`Lowering/V08/` modules from the V13 help branch, each with a `*Controls`
module. They consume existing Source definitions, ABI codecs and decoder arms;
none adds an AST, evaluator, decoder or admission rule.

- `BoolErrorAbi`, `BoolErrorStatement`, `BoolErrorCompleteness`: closed Boolean
  custom-error payloads agree with the indexed ABI codec; an executable
  selector on existing typed statements; completeness for the supported
  literal family only. `LiteralFailureBoolStatement` adds typed Boolean error
  statement selection with exact error-span bounds.
- `LiteralFailureCalldataDecode`, `LiteralFailureSliceDecode`,
  `LiteralFailureChoiceDecode`, `LiteralFailureEffectDecode`: progress and
  preservation through the calldata `abi.decode` arm, calldata slices,
  conditional data selection, and local-assignment effects surviving a decode
  failure.
- `LiteralFailureStorageDecode`, `LiteralFailureStorageSuccessControls`: storage
  byte copies and typed local decoding; the canonical success case with the
  exact caller state.
- `LiteralFailureDynamicError`, `LiteralFailureDynamicListError`: heap-backed
  custom-error encoding, mixed and arbitrary-length typed reference lists.
- `LiteralFailurePackedBytes`, `LiteralFailureSignatureBytes`,
  `LiteralFailureSelectorBytes`, `LiteralFailureEncodedRethrow`: packed bytes
  reads with fresh allocation, signature encoding with alias preservation,
  selector-local expression execution, rethrow of allocated ABI payloads.

`LiteralFailureBytesReadback{,Controls}` consume the published
`Solidity.Backend.AbiWorld.ErrorRoundtrip` readback facts. No runtime target
encoder, source/target simulation or admission theorem is claimed.


### Tuple-return argument failure

`LiteralFailureTupleAbort` consumes an actual failed `evalConvArgs` execution and derives the exact failed tuple-return statement. Its subcomputation locals are discarded while its actual Source state is retained; this is not transaction rollback. Controls discharge the premise with an assignment followed by division by zero and distinguish a skipped later assignment from a positive divisor-one tuple return. Return-slot extraction, older aliases, timeout and nonempty Panic payload remain explicit. These statement components do not establish complete function admission, target lowering or unknown-memory result encoding.

### Heterogeneous word and byte results

`LiteralFailureMixedEncoding` proves actual Source encoding for arbitrary interleavings of uint256 words and represented byte strings. Its indexed relation records actual values, heap fields and encoder parts; it assumes no encoder execution and defines no admission predicate. The proof derives ordered parts, total head extent and tail assembly agreement with the existing typed ABI codec, then discharges the G38 encoding premise. Controls execute a four-field tuple return before extracting and encoding its values, retain an older alias, permit repeated references and observe full-word values and empty/boundary payloads. Target transport uses the existing bounded known-packet RETURN component. Arrays and other recursive Source reference encodings, unknown-memory target encoding and whole call/world simulation remain open.

### Mixed ABI expression results

`LiteralFailureMixedExpression` derives actual local argument execution, then consumes the mixed encoder proof to execute the existing `abi.encode` expression and allocate its real result object. The intrinsic heap bound proves that allocation preserves all represented input fields without a disjointness premise. The published rethrow boundary consumes the actual fresh pointer and exact bytes. Expression timeout leaves the initial heap; statement timeout after expression success retains the new allocation. Controls inspect complete result objects for both Source pipelines. These are Source-state and expression facts, not whole-function admission, physical target memory, transaction rollback or bytecode correctness.

### Mixed selector-prefixed packets

`LiteralFailureMixedSelector` derives actual `encodeWithSelector` execution for arbitrary represented word/bytes tails, using actual local selector lookup and the existing bytes4 conversion. The four selector bytes precede the existing codec body without changing its relative offsets. Controls execute allocation and raw rethrow in both Source pipeline modes, include an empty tail and post-allocation timeout, and distinguish body-relative offsets from absolute packet positions. Supplied Error-selector bytes with an offset-128 reason are accepted by the existing byte decoder; wrong selectors and selector-only truncation are rejected. These are packet observations, not declared-error agreement, same-invocation catch selection, G40 dispatch or target ABI compilation.

### Mixed signature-prefixed packets

`LiteralFailureMixedSignature` derives actual `encodeWithSignature` execution for arbitrary represented word/bytes tails. It consumes the real signature-memory read and existing hash-prefix semantics, then retains the complete typed codec body. Controls share the signature and first payload reference, prove their preservation across fresh allocation, consume the existing Keccak contract, and distinguish a four-byte prefix from the full hash. Signature-only encoding, raw rethrow and pre-argument versus post-allocation timeout remain explicit. The supplied bytes are not asserted to name an admitted declaration; no new hash implementation, native agreement, dispatch, same-invocation transport or target encoder is provided.

### Declared mixed custom errors

`LiteralFailureMixedCustomError` derives actual converted local argument execution and consumes the mixed encoder proof to execute the existing custom-error statement. Controls include mixed and zero-argument error declarations in their environment, prove parameter types and canonical ASCII/UTF8 selector transport, and retain complete populated state on the Source error result. A dangling reference is stuck; insufficient argument fuel times out. Neither is relabeled an ABI validation revert. The Source statement allocates no result object. These component facts do not establish function-entry admission, transaction rollback, target emission or arbitrary world transport.

### Typed string prefixes

`LiteralFailureStringPrefix` derives encoding and declared custom-error execution for an actual `string memory` argument before an arbitrary represented word/bytes tail. It reuses the existing dynamic byte layout by definitional equality of the encoder computations, while retaining distinct indexed string and bytes values. `encodingAt` discharges the existing G38 premise from actual heap fields. Populated controls retain complete Source state, cover empty and 31/32/33-byte payloads and full words, and execute a string/bytes pair sharing one live object. Dangling references remain stuck and insufficient fuel remains timeout. Arbitrary string bytes here are Source payloads, not a Unicode admission theorem. No function-entry, native/target encoder, catch dispatch, world rollback or resource claim follows.

### Arbitrary memory-string interleavings

`LiteralFailureStringInterleaving` relates existing indexed Source value lists while retaining the original string parameter types and memory addresses. Structural induction proves equality of actual standard and packed encoder computations, including failures; it defines neither an encoder nor a source conversion. The existing mixed field proof then derives complete typed-codec bytes, the G38 encoding premise, declared custom-error execution and real ABI-expression allocation. Controls use multiple non-leading string arguments, distinct and shared references, populated Source state and a separate older object; late dangling reads remain stuck, while insufficient fuel remains timeout. The witness list is an encoding proof device, not equality of typed string/bytes values, Unicode admission, a new accepted profile, target memory encoding or call/world correctness.

### Typed boolean prefixes

`LiteralFailureBoolPrefix` connects an actual boolean local to the existing bool-kind ABI word before an arbitrary supported heterogeneous memory-string/uint256/bytes tail. The standard encoder proof reuses actual computation equality and the existing mixed field relation; the original bool parameter and declaration signature are retained. It derives G38 encoding, custom-error execution and ABI-expression allocation without an assumed run. Controls cover true/false locals, full-word tail values, aliases, older objects, late dangling references and timeout. Packed bool and uint256 executions remain observably different (one versus 32 bytes); the standard-width witness is not a packed-mode theorem. This does not validate raw boolean calldata, enum cardinality, Unicode admission, source entry provenance or target/world execution.
