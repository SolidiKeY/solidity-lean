# P6 physical memory interface

Word-frame to byte-memory correspondence for the memory backend
(`Backend/MemoryOps/Physical*.lean`), from the v11-memory-operations lane.
Producers quantify over arbitrary states; their post-relations are derived.

## Proved

- `PhysicalWordFrame.lean`: `WordFrame` relates numeric word cell `c` to bytes
  `[32c, 32c+32)`; `WordFrame.write`/`mstore` pair a word write with byte MSTORE.
- `PhysicalByteJournal.lean`: `readMemory`/`getBytes` and `writeBytes`/`putBytes`
  agree; REVERT reads live bytes before the local restore. The local unwind
  result is transport by definitional restore (the saved caller by `rfl`).
- `PhysicalSourceUint.lean`, `PhysicalUintWrite.lean`, `PhysicalUintDelete.lean`:
  `UintArrayAt` relates Source, intrinsic, word and byte views of a dynamic
  `uint` array; `read`, `write_cell` and the delete forms (a zero write).
  `delete_typed` runs `writeArrayCode`, not the compiled `deleteLocalCode`.
- `PhysicalArrayReframe.lean`: two `ArrayRepr`s of one array agree on header
  and element cells (`uint_array_cells_eq`).
- `PhysicalReferenceStore.lean`, `PhysicalPointerFrame.lean`: reference-array
  store (typed, word and scaled-pointer byte MSTORE; `reference_store`,
  `reference_store_frames`); `PointerFrame` maps `b` to `wordBytes (32 b)` and is
  preserved alongside `WordFrame`.
- `PhysicalFrameImage.lean`: a frame-memory byte image; `frameBytes_store32`,
  `frame_snapshot_read` and zero expansion commute.
- `PhysicalWorldUnwind.lean`: Source world journal, ABI reason emitter and local
  checkpoint (`world_reason_unwind`, `source_rollback_to`); rollback keeps the
  heap. As above, the restored word frame is passed through by definition.
- `Physical{Memory,FrameImage,WorldUnwind}Controls.lean`: concrete `WordFrame`,
  `UintArrayAt` and frame-image instances.

## Unproved targets

`PhysicalLocalDeleteGoal.lean` and the `*ClientGoal` definitions in
`PhysicalReferenceStore`, `PhysicalPointerFrame` and `PhysicalMemoryControls`
are type-checked statements, not facts; nothing assumes them. In particular
`reference_store`, `reference_store_frames` and `uint_array_cells_eq` have no
proved client yet, and the compiled local delete (`ResolvedDeletePhysicalGoal`)
is open.

## Open

General compiled delete and reframe, journal/world/ABI unwind beyond the local
checkpoint (P6b), a physical encoding of Source accounts and storage.
