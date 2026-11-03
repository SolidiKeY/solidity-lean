# P7 transient target

`Solidity/Backend/Transient/**` gives the G39 target a transient-storage model
and connects it to the Source transient operations. It is a selected typed
target/reset/callback input, not full G39 lowering or G42 entry.

## Target

The target extends `Evm.Machine` with a separate owner-indexed word bank and a
write journal; persistent storage is never reused as transient storage.
Backend PUSH/TLOAD/TSTORE code runs on the slice interpreter `Transient.run`;
ordinary code runs on the existing `Evm.exec` and keeps its complete `Out`. A successful zero-skip resume preserves transient state. Reset
clears bank and journal, keeps the ordinary machine and is idempotent.

## Source correspondence

`Source.writeAt`, `readAt`, static refusal and `endTx` are the owner
operations. `BoolSlot` states the declared bool/transient/path/key premises;
`Represents` relates one selected owner/cell. `Code.compiled_write` derives the
Source execution and the emitted-code result without a supplied outcome.
`Frames` proves inner/outer target rollback for any caller prefix;
`SourceFrames` composes an actual two-write Source body with paired Source and
target rollback.

`WordSource` generalizes read/write and emitted TLOAD/TSTORE agreement to
intrinsic Source types through `Val.word`; references without a word are not
represented. Reset uses the typed default and its zero word. `WordControls`
runs uint256 and int8 writes with exact sign extension, reference refusal and
reset.

`SourceCallback` runs the existing `Source.callAddr`/`envLoop`/`instanceAt`/
`enterInstance`/`dispatch`/`runMods` bodies against a registered fallback that
assigns a transient bool, in both pipelines: success, revert, static refusal
and timeout keep the caller heap, locals, function locals, events and logs
(success adds journal entries and writes the owner's cell). Wrong code refuses
entry; a four-step horizon keeps its pending credit and events.
`source_target` pairs this run with a framed target store on an arbitrary
target state and the post-write selected-cell relation; it assumes no initial
relation between the two, so it is not a composition or simulation. `Mixed` shows that reset
keeps ordinary persistent and memory writes while zeroing only transient
state.

## Boundaries

Callbacks keep target bank mutations on success and roll back on static or
empty revert. Unsupported or symbolic adapter failures keep their dirty state
and are not EVM reverts. Nonempty REVERT is refused rather than erased. The
port is full-word: no solc packed layout, dirty padding, return-byte
transport, fresh callee memory, account/code selection, gas/stack/depth
bounds, G24 state relation, G39 compiler lowering or G46 EVM correspondence.

## Callback observation repair (2026-11-03)

`callbackObserved` (namespace `Solidity.Backend.Transient`) executes the existing
callback body once and pairs its existing `finish` result with the successful
body's stack head, observed **before** restoring the caller machine.
`callbackObserved_result` proves its first projection is exactly `callback`.
`callbackObserved_load` proves the complete pair equals the restored entry
and the actual word at the supplied owner/key, for arbitrary caller state
and either static flag. The old `Frames.callback_load` is only a caller-state
restoration law; it cannot certify the loaded word or correct owner.
The controls distinguish owner zero from another owner's `0xcc` even though
both callbacks restore the same entry, and check post-write readback.
`callback_store_endTx` executes a real successful store callback before reset;
the earlier `callback_then_reset` remains merely a write/reset law.

`callbackObserved_source_write` requires the **initial** `Represents` relation,
then derives actual Source read and write execution, observed target read,
actual target callback store and post-write agreement. Its exact premises
are a typed `BoolSlot`, nonstatic frame and that initial selected-cell
relation; it accepts no requested run/outcome equality.

`BoolSlot`/`Represents` and `WordRepresents` remain deliberately selected
full-word compiler ports. Their freely supplied key is not a derived packed
layout address; `Val.word`/`boolWord` is not an arbitrary packed codec. They
cannot replace `Yul.Views.TransientSlots.transientSlotLoad`, which combines
layout codecs with the real residual companion. A layout-aware consumer must
establish `transientSlotLoad ts companion owner key = some (target.bank owner key)`
and retain its actual Source/residual carriers. No such whole-bank agreement,
packed complement framing, layout preparation, G24/G39 compilation or Bridge
EVM correspondence follows from these selected-cell theorems. This separation
avoids duplicating or replacing VY2's layout-aware source-cell relation.

These are local P7 producer repairs, not full original Y07.01/Y07.02/Y09.03
or Backfill A/B completion. Creation/initcode execution still requires V08
P15/SS-NEW and VY5 H16; G51 source effect embedding, universal physical/frame
adequacy, common Source emit/G01, compiler last-source-frame noninterference,
resource and final joint closure remain open. Previous kernel and finite
compiler/EVM evidence remains separate.

Validation: both new modules and a combined import/signature/axiom file pass
serial Lean 4.24.0 per-file checks under the existing 12 GiB/no-swap bound.
All ten declarations have either no axioms or only `propext`,
`Classical.choice`, `Quot.sound`; no `sorryAx` or custom axiom. Independent
read-only finder and skeptic reviews found no confirmed issues. A failed
simplification-only reset fixture was corrected to the already checked `rfl`
candidate; the failing attempt is retained. Layer, root reachability, doc-path
and trust checks pass for this tree. These isolated CLI checks are not a Lake
full build, final TestSuite/strict closure or the required runtime KeySort
build. Historical global G07 failures remain retained, not relabelled passes.
