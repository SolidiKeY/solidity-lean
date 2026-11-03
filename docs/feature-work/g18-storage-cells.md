# G18 operation-level storage cells

The new modules [G18StorageValues](../../Solidity/Backend/Aggregates/G18StorageValues.lean), [G18StorageClient](../../Solidity/Backend/Aggregates/G18StorageClient.lean) and [G18StorageCellControls](../../Solidity/Backend/Aggregates/G18StorageCellControls.lean) relate existing Source.Storage cells to existing intrinsic SVal paths. They do not introduce an execution semantics.

`save_isSome_eq_find` proves actual target save availability from actual find availability across intrinsic struct, dynamic/fixed-array and mapping constructors, including defaults and allocated shadow slots. `IntCellAt` records one width-correct source integer read and target integer read. `int_cell_write` derives a successful target save and updated point relation from that initial relation and a source-width range proof. `int_cell_write_other` requires BOTH distinct logical source paths and diverging intrinsic paths; it preserves their old relation through the same writes. No desired target execution or final relation is assumed.

The inhabited client declares Basket with a uint8 dynamic-array field and resolves the logical cell types through the actual Source.Env. The target path is a manually constructed typed fixture, not extracted declaration lowering. Two written cells contain 7 and 11. `StorageClient.updated` composes the NEW operation laws to derive the target save of 8, its actual resulting value, and the updated/untouched relations. Although `targetAfter` is expressed with Option.getD, the theorem proves the save is some targetAfter, discharging the fallback. `ordered_observations` retains all four declared observations in order: source first/second then target first/second, from [7,11,7,11] to [8,11,8,11]. This is the complete observer chosen for this finite client, not a full storage/world trace.

`negative_controls` rejects wrong output, order, modification of the untouched cell and a stale target phase. It also checks wrong source step order, the distinction between typing index99 and having an allocated target slot, actual find/save Option failures at that slot, and uint8 overflow. Option failure is not an EVM revert, source exhaustion or divergence. No external compiler or EVM replay is claimed.

This is partial G18.02 preparation. Mapping/fixed-array inhabited applications, a whole aggregate source-value relation, source expression bounds/admission and lowering simulation remain open; G18.03 and G18.06 are not closed by these cell laws. The published V07 declaration graph remains the shape producer, not a value-preservation oracle. Physical storage/hash/world/ABI and compiler coverage obligations remain separate.



Routine derived frame-law statements remain open obligations; no missing routine proof is assumed by the checked updated theorem. The nine generated #guard_msgs pins check the scoped standard axiom observations.
