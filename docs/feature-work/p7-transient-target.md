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
